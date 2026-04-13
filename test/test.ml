(*
 * Copyright (C) 2013 Anil Madhavapeddy <anil@recoil.org>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
 * REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
 * INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
 * LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
 * OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 *)

open Lwt
open Printf

let run test =
  Lwt_main.run (test ())

let test_open () =
  Netif.connect "tap0" >>= fun _t ->
  printf "connected\n%!";
  Lwt.return_unit

let test_close () =
  Netif.connect "tap1" >>= fun t ->
  printf "connected\n%!";
  Netif.disconnect t >>= fun () ->
  printf "disconnected\n%!";
  Lwt.return_unit

let test_write () =
  Netif.connect "tap2" >>= fun t ->
  let mtu = Netif.mtu t in
  Netif.write t ~size:mtu (fun _data -> mtu) >>= fun _t ->
  Netif.write t ~size:(mtu + 14) (fun _data -> mtu + 14) >>= fun _t ->
  Lwt.return_unit

let with_alarm ?(timeout=2) f =
  (* ensure we don't get stuck in an infinite loop,
     kill the process with SIGALRM after 2 seconds
   *)
  let _: int = Unix.alarm timeout in
  let t = f ()
  in
  Lwt.on_termination t (fun () ->let _:int = Unix.alarm 0 in ());
  t


let test_close_listen () =
  let open Lwt.Syntax in
  with_alarm @@ fun () ->
  Netif.connect "tap3" >>= fun t ->
  printf "connected\n%!";
  let listener = Netif.listen t ~header_size:14 (fun _ -> Lwt.return_unit) in
  Netif.disconnect t >>= fun () ->
  printf "disconnected\n%!";
  let+ listener in match listener with
    | Ok () | Error `Disconnected -> ()
    | Error e ->
        Alcotest.failf "Netif.listen failed: %a" Netif.pp_error e

let () =
  (* required for IP fragmentation *)
  Mirage_crypto_rng_unix.use_default ()

open Lwt.Syntax

let cidr = Ipaddr.V4.Prefix.(of_string_exn "192.0.2.200/24")
let gateway = Ipaddr.V4.Prefix.first cidr

module Eth = Ethernet.Make(Netif)
module ARP = Arp.Make(Eth)

let with_connection connect disconnect f =
  let* t = connect () in
  Lwt.finalize (fun () -> f t) (fun () -> disconnect t)

let setup_example_network ?cidr:_ device =
  let* t = Netif.connect device in
  (* setup the host side *)
(*  Tuntap.set_ipv4 ~netmask:cidr device gateway;*)
  let mac = Tuntap.get_macaddr device in
  Logs.info (fun m -> m "initial gateway MAC: %a" Macaddr.pp mac);
  (* There is a race condition here, if we start sending packets too soon
     then we'll receive the wrong MAC for the gateway.
     This will result in being able to send just 1 ICMP packet,
     all the rest will be lost because it'd use the old cached MAC address.
     This is probably because of scripts that are still running triggerred from udev,
     so wait for these to complete. If the race condition was avoided then
     the 2 printed MAC addresses will be different.
     This is Linux specific though, so ignore failures.
   *)
  let+ _ : Unix.process_status =
    Lwt_process.exec ("udevadm", [|"udevadm"; "settle"|])
  in
  let mac = Tuntap.get_macaddr device in
  Logs.info (fun m -> m "new gateway MAC: %a" Macaddr.pp mac);
  (* resolve this before the flood starts, otherwise ARP packets could get dropped and time out *);
  t

let pings_sent = ref 0

let icmp_stress_sender ?(cidr=cidr) ~id ~src ~dst t =
  let module IPv4 = Static_ipv4.Make(Eth)(ARP) in
  let module ICMPv4 = Icmpv4.Make(IPv4) in
  with_connection (fun () -> Eth.(connect t)) Eth.disconnect @@ fun eth ->
  with_connection (fun () -> ARP.connect eth) ARP.disconnect @@ fun arp ->
  with_connection (fun () -> IPv4.connect ~cidr eth arp) IPv4.disconnect @@ fun ipv4 ->
  with_connection (fun () -> ICMPv4.connect ipv4) ICMPv4.disconnect @@ fun icmpv4 ->
  let handler pkt =
    Eth.input
      ~arpv4:(ARP.input arp)
      ~ipv4:(fun _ -> Lwt.return_unit)
      ~ipv6:(fun _ -> Lwt.return_unit) eth pkt
  in
  let _ = Netif.listen t ~header_size:Ethernet.Packet.sizeof_ethernet handler in
  (* preallocate all packets *)
  let packets =
    List.init 65536 @@ fun seq ->
      (* avoid fragmentation, because we send so many packets,
         the packet drop rate will be high, and we may not be able to reassemble
         packets after a while
       *)
    let payload = Cstruct.create 1400 in
    let header =
      Icmpv4_packet.{
        code = 0;
        ty = Echo_request;
        subheader = Id_and_seq (id, seq)
      } |> Icmpv4_packet.Marshal.make_cstruct ~payload
    in
    Cstruct.append header payload
  in
  Logs.info (fun m -> m "icmp_stress_sender: %a -> %a"
    Ipaddr.V4.pp src Ipaddr.V4.pp dst
  );
  let write = ICMPv4.write icmpv4 ~src ~dst in
  let send packet =
    let+ outcome = write packet in
    Logs.on_error ~pp:ICMPv4.pp_error ~use:(fun _ -> Alcotest.fail "cannot send ping") outcome;
    incr pings_sent
  in
  let rec loop () =
    let* () = packets |> Lwt_list.iter_s send in
    (loop[@tailcall]) ()
  in
  loop ()

let icmp_received = ref 0
let icmp_stress_receiver ~id ~src =
  with_connection (fun () -> Icmpv4_socket.connect ()) Icmpv4_socket.disconnect @@ fun icmp ->
  Icmpv4_socket.listen icmp src @@ fun pkt ->
  match Ipv4_packet.Unmarshal.of_cstruct pkt with
  | Error e ->
      Logs.warn (fun m -> m "bad IP packet: %s" e);
      Lwt.return_unit
  | Ok (_, pkt) ->
    match Icmpv4_packet.Unmarshal.of_cstruct pkt with
    | Error e ->
        Logs.warn (fun m -> m "error %s" e);
        Lwt.return_unit
    | Ok (Icmpv4_packet.{code = 0; ty = Echo_reply; subheader = Id_and_seq (id', seq)}, _)

      when id = id' ->
        Logs.debug (fun m -> m "received echo reply %d" seq);
        incr icmp_received;
        Lwt.return_unit
    | Ok (pkt, _) ->
        Logs.debug (fun m -> m "received %a" Icmpv4_packet.pp pkt);
        Lwt.return_unit
let handler_pending = ref 0
let handler_pending_max = ref 0

let icmp_receiver ~cidr t =
  let module IPv4 = Static_ipv4.Make(Eth)(ARP) in
  let module ICMPv4 = Icmpv4.Make(IPv4) in
  let nop _ = Lwt.return_unit in
  with_connection (fun () -> Eth.(connect t)) Eth.disconnect @@ fun eth ->
  with_connection (fun () -> ARP.connect eth) ARP.disconnect @@ fun arp ->
  with_connection (fun () -> IPv4.connect ~cidr eth arp) IPv4.disconnect @@ fun ipv4 ->
  with_connection (fun () -> ICMPv4.connect ipv4) ICMPv4.disconnect @@ fun icmpv4 ->
  let ip_nop ~src:_ ~dst:_ _ = Lwt.return_unit in
  let default ~proto  ~src ~dst pkt =
    if proto = 1 then (
      incr handler_pending;
      (* simulate slow packet processing, e.g. log IO *)
      (* simulate having to wait for an event, 
        such as space in an output buffer or a DNS lookup *)
      Logs.debug (fun m -> m "received ICMP packet from %a" Ipaddr.V4.pp src);
      let+ () = ICMPv4.input icmpv4 ~src ~dst pkt in
      decr handler_pending;
      handler_pending_max := max !handler_pending_max !handler_pending;
    )
    else
      Lwt.return_unit
  in
  let handle_packet pkt =
    Eth.input
      ~arpv4:ARP.(input arp)
      ~ipv4:IPv4.(input ipv4 ~tcp:ip_nop ~udp:ip_nop ~default) ~ipv6:nop eth pkt
  in
  Lwt.both
  ((* resolve this before the flood starts, ARP packets may get dropped and time out otherwise.
      For this to work the listener must be active.
    *)
    let+ outcome = ARP.query arp gateway in
    let addr = Logs.on_error ~pp:ARP.pp_error ~use:(fun _ -> Alcotest.fail "Could not resolve gateway MAC address") outcome in
    Logs.info (fun m -> m "gateway MAC: %a" Macaddr.pp addr)
  )
  (
    let+ outcome = Netif.listen t ~header_size:Ethernet.Packet.sizeof_ethernet handle_packet in
    match outcome with
    | Ok () | Error `Disconnected -> ()
    | Error _ ->
        Logs.on_error ~pp:Netif.pp_error ~use:(fun _ -> Alcotest.fail "Netif.listen failed") outcome
  )

let test_flood () =
  let open Lwt.Syntax in
  let dst = Ipaddr.V4.Prefix.address cidr in
  let id = Random.int 65536 in
  let* t = setup_example_network "tap4" in
  let* () = Lwt_io.flush_all () in
  Lwt.catch
  (fun () ->
    match Lwt_unix.fork () with
    | 0 ->
        let* t = setup_example_network ~cidr:Ipaddr.V4.Prefix.(of_string_exn "192.0.2.201/24") "tap5" in
        let _ : int list = [
          Sys.command "ip link add name virbrtest type bridge";
          Sys.command "ip addr add 192.0.2.1/24 dev virbrtest";
          Sys.command "ip link set dev virbrtest up";
          Sys.command "ip link set tap4 master virbrtest";
          Sys.command "ip link set tap5 master virbrtest"
        ] in
        icmp_stress_sender ~cidr:Ipaddr.V4.Prefix.(of_string_exn "192.0.2.201/24") ~id ~src:(*Ipaddr.V4.(of_string_exn "192.0.2.201"*)(Ipaddr.V4.Prefix.last cidr) ~dst t
    | sender_child ->
      match Lwt_unix.fork () with
      | 0 ->
        icmp_stress_receiver ~id ~src:gateway
      | receiver_child ->
        let receiver = icmp_receiver ~cidr t in
        let* () = Lwt_unix.sleep 1000. in
        Lwt.cancel receiver;
        Unix.kill sender_child Sys.sigterm;
        Unix.kill receiver_child Sys.sigterm;
        Lwt.return_unit
  ) (fun e ->
    Printexc.print_backtrace stderr;
    raise e;
  )

let suite = [
  "connect", `Quick, (fun () -> run test_open) ;
  "disconnect", `Quick, (fun () -> run test_close);
  "listen+disconnect", `Quick, (fun () -> run test_close_listen);
  "write", `Quick, (fun () -> run test_write);
  "flood", `Slow, (fun () -> run test_flood)
]

let _ =
  Logs.set_level (Some Logs.Info);
  Logs.set_reporter (Logs_fmt.reporter ());
  Alcotest.run "mirage-net-unix" [ "tests", suite ]
