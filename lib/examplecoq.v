From Lib Require Import extraction.

Set Extraction File Comment  "Generated Automagically using Coq-extract - see corresponding .v file for proofs*)
open Core
(*".
Unset Extraction SafeImplicits.



From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool seq tuple eqtype .


Module Type NetworkBufferParams.

  Parameter Data: Set.
  Axiom Data_eqMixin : Equality.mixin_of Data.

End NetworkBufferParams.


Module AbstractNetworkBuffer (Params: NetworkBufferParams).


  Canonical Data_eqType := Eval hnf in EqType Params.Data Params.Data_eqMixin.

  Extraction Inline Data_eqType.

  Record t :=  mkNetworkBuffer {
                     capacity: nat; offset: nat; data: seq Params.Data;
                   }.

  Definition has_free_space (buf: t) : bool := (capacity buf) > (offset buf).
  Definition is_full (buf: t) : bool := (capacity buf) <= (offset buf).

  Definition is_equal (buf buf': t) : bool := [&&
                                                 (capacity buf) == (capacity buf'),
                                                 (offset buf) == (offset buf') &
                                                 (data buf) == (data buf')
                                              ]  .

  Extraction Inline capacity offset data.

End AbstractNetworkBuffer.




Cd "lib".

Extraction "examplecoq" AbstractNetworkBuffer.

Cd "..".
