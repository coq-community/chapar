open Pervasives
(* open Printf *)
open Configuration
open ReadConfig
open String

let _ =
(*    let conf = readConfiguration "Settings.txt" in *)   
(*   List.iter
      (fun (n, {ip; port}) ->
            print_int n;
            print_newline ();
            print_string ip;
            print_newline ();
            print_int port;
            print_newline ())
      conf*)

    let mysub ms = (
      let i = (index ms '@') in
      String.sub ms (i + 1) (String.length ms - i - 1)) in
      print_string (mysub "AName@12.232.232.3") 
      
   
   
   
   
   
   
(*
open Printf
open BatDllist


let _ =
   let h = create 0 in
   add h 3;
(*   add h 1;
   add h 2;
   add h 3;
   add h 4;
   add h 5;
   add h 6;
   add h 7;*)
   let c = ref (next h) in
   let p = ref h in
   while not (!c == h) do
      let n = get !c in
      p := !c;
      c := next !c;
      if (n = 3 || n = 4) then (
         remove !p;
         printf "%d\n%!" n
      )
   done;
   printf "\n%!";
   let c = ref (next h) in
   let p = ref h in
   while not (!c == h) do
      let n = get !c in
      printf "%d\n%!" n;
      p := !c;
      c := next !c;
   done;   
   0*)
   
(*
   iter
      (fun n ->
         printf "%d\n%!" 
         if n = 2 || n = 3 then
            remove 
      )
      h
*)
      


(*
open Printf
open PriorityQueue
type clock = int

let clock_oder: clock order =
   fun a b -> a <= b
   

let _ =
   let pq = make clock_oder in
   add pq 3;
   add pq 1;
   add pq 4;
   add pq 5;
   add pq 0;
   add pq 2;
   while not (is_empty pq) do
      let e = first pq in
      remove_first pq;
      printf "%d\n%!" e
   done;
   0
*)

   









(*
open Util
open Printf



let _ =
   let l = [0;1;2;3;4;5] in
   List.iter (printf "%d ") l;
   printf "\n";
   List.iter (printf "%d ") (take 3 l);
   printf "\n"

*)
