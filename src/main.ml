open Core
open Lib

let res = Examplecaml.add 1 2
let buf = Examplecoqinst.NetworkBuffer.{capacity=10;offset=0;data=[]}
let buf' = Examplecoqinst.NetworkBuffer.{capacity=10;offset=0;data=["this";"was";"defined";"in";"coq"]}

let print_buffer buf =
            print_endline (sprintf "NetworkBuffer{capacity = %d; offset = %d; data=%s}"
                   Examplecoqinst.NetworkBuffer.(capacity buf)
                   Examplecoqinst.NetworkBuffer.(offset buf)
                   Examplecoqinst.NetworkBuffer.(List.to_string ~f:(fun x -> x) (data buf)))



let _ = print_endline "Hello world!";
        print_buffer buf;
        print_buffer buf';
        print_endline (Bool.to_string (Examplecoqinst.NetworkBuffer.is_full buf));
        print_endline (Bool.to_string (Examplecoqinst.NetworkBuffer.is_equal buf buf'))
