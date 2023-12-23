From Coq Require Import Arith.
(* Require Import PeanoNat. *)
From Coq Require Import List Ascii String.
From Coq Require Export ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

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
