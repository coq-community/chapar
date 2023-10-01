open Printf

open Commonbench

  
let () =
   Random.self_init ();
(*   printf "%s\n%!" Sys.argv.(1);
   printf "%s\n%!" Sys.argv.(2);
   printf "%s\n%!" Sys.argv.(3);
   printf "%s\n%!" Sys.argv.(4);*)
   let filename = Sys.argv.(1) in
   let op_count = int_of_string Sys.argv.(2) in
   let key_range = int_of_string Sys.argv.(3) in
   let put_percent = int_of_string Sys.argv.(4) in
   
   let oc = open_out filename in

   fprintf oc "%d\n" op_count;   
   for i = 0 to op_count - 1 do
      let op_p = Random.int 100 in
      let op = if op_p < put_percent then put_num else get_num in
      let k = Random.int key_range in
      let v = Random.int key_range in
      fprintf oc "%d\n" op;
      fprintf oc "%d\n" k;
      fprintf oc "%d\n" v
   done;
   close_out oc
  

  
  
  
  
  
  