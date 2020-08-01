Require Coq.extraction.Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import ImpCEvalFun.

Extraction "imp1.ml" ceval_step.

(* Controlling Extraction of Specific Types *)

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".


Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".


Extract Constant minus => "( - )".

Extraction "imp2.ml" ceval_step.
