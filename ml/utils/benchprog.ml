open Common
open Commonbench



let prog_of_bench filename =

   let ic = open_in filename in
   try
      let op_count = int_of_string (input_line ic) in
      let rec prog_of_rec i prog =
         if i = op_count then
            prog
         else      
            let op = int_of_string (input_line ic) in
            let k = int_of_string (input_line ic) in
            let v = int_of_string (input_line ic) in
            if op = put_num then
               prog_of_rec (i+1) (Put (k, v, prog))
            else
               prog_of_rec (i+1) (Get (k, fun v -> prog)) in
      
      let p = prog_of_rec 0 Skip in
      close_in ic;      
      p

   with e ->
      close_in_noerr ic;
      raise e
   
