Require Import Arith.
Require Import NPeano.
(* Require Import PeanoNat. *)

Require Import List.
(* Require Import Util. *)
Require Import Ascii.
Require Import String.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

From Chapar Require Import KVSAlg1.
From Chapar Require Import KVSAlg2.
From Chapar Require Import KVSAlg3.

Extract Inlined Constant length => "List.length".
Extract Inlined Constant negb => "not".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant fold_left => "(fun a b c -> List.fold_left a c b)".
Extract Inlined Constant in_dec => "(fun h -> List.mem)".
Extract Inlined Constant leb => "(<=)".
Extract Inlined Constant ltb => "(<)".
Extract Inlined Constant pred => "(fun n -> if n <= 0 then 0 else n - 1)".

Extraction "coq/KVSAlg1.ml" KVSAlg1.KVSAlg1.
Extraction "coq/KVSAlg2.ml" KVSAlg2.KVSAlg2.
Extraction "coq/KVSAlg3.ml" KVSAlg3.KVSAlg3.
