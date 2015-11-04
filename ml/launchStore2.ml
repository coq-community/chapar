open Printf
open Util
open Common
open Runtime
open Algorithm2
open ReadConfig
open Benchprog

module Alg1RunSys = RuntimeSystem (Algorithm2)
open Alg1RunSys



let _ =
   let count = int_of_string Sys.argv.(1) in
   let node = int_of_string Sys.argv.(2) in
   let info = take (count + 1) (readConfiguration "Settings.txt") in
   if node <> -1 then (
      let bench_file = Sys.argv.(3) in
      let p = prog_of_bench bench_file in
      main info node p
      
   ) else
      main info node Skip

