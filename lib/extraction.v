


From mathcomp.ssreflect Require Import ssreflect ssrnat ssrbool seq tuple eqtype .

(* This solves an error where the implementation of ssrbool.ml
   doesn't match the interface *)
Require Extraction.
Extraction Inline ssrbool.SimplPred.



Extraction Language OCaml.
(* Extraction Blacklist string list nat. *)
Set Extraction Optimize.
Unset Extraction AccessOpaque.
Set Extraction AutoInline.
Unset Extraction SafeImplicits.

Set Extraction File Comment  "Generated Automagically using Coq-extract - see corresponding .v file for proofs*)
open Core
(*".







(* Constants to inline:
 Set Extraction Inline <constant-name>
 *)

(* Implicit parameters
Fixpoint len (A: Type) (xs: list A) : nat := match xs with | nil => 0 | cons h t => 1 + len _ t end.
Extraction Implicit lezn [ A ].
Extraction len.

let rec len = function
| Nil -> O
| Cons (_, t) -> add (S O) (len t)
*)

(* Realizing axioms
Extracting Constant <name> => <item>
 *)


Extract Inlined Constant Nat.zero => "0".
Extract Inlined Constant Nat.one => "1".
Extract Inlined Constant Nat.two => "2".

Extract Inlined Constant Nat.succ => "succ".
Extract Inlined Constant Nat.pred => "pred".
Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.sub => "(-)".



Extract Inlined Constant Nat.mul => "(*)". 
Extract Inlined Constant Nat.eqb => "Int.(=)".

Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".

Extract Inlined Constant Nat.modulo => "(%)".
Extract Inlined Constant Nat.double => "(fun x -> x * 2)".


Extract Inductive comparison => int [ "0" "-1" "+1" ] "(fun feq flt fgt n -> match n with | 0 -> feq () | -1 -> flt () | 1 -> fgt ())".
Extract Inlined Constant Nat.compare => "compare".
Extract Inlined Constant Nat.max => "max".
Extract Inlined Constant Nat.min => "min".
Extract Inlined Constant Nat.even => "(fun x -> x % 2 = 0)".
Extract Inlined Constant Nat.odd => "(fun x -> not ( x % 2 = 0))".
Extract Inlined Constant Nat.pow => "Int.( ** )".

     (* Definition of_uint_acc : Decimal.uint -> nat -> nat. *)
     (* Definition of_uint : Decimal.uint -> nat. *)
     (* Definition to_little_uint : nat -> Decimal.uint -> Decimal.uint. *)
     (* Definition to_uint : nat -> Decimal.uint. *)
     (* Definition of_int : Decimal.int -> option nat. *)
     (* Definition to_int : nat -> Decimal.int. *)
     (* Definition divmod : nat -> nat -> nat -> nat -> nat * nat. *)
Extract Inlined Constant Nat.div => "Int.(/)".

Extract Inlined Constant Nat.modulo => "Int.(%)".
     (* Definition gcd : nat -> nat -> nat. *)
     (* Definition square : nat -> nat. *)
     (* Definition sqrt_iter : nat -> nat -> nat -> nat -> nat. *)
     (* Definition sqrt : nat -> nat. *)
     (* Definition log2_iter : nat -> nat -> nat -> nat -> nat. *)
     (* Definition log2 : nat -> nat. *)
     (* Definition iter : nat -> forall A : Type, (A -> A) -> A -> A. *)
Extract Inlined Constant Nat.div2 => "(fun x y -> x / y)".
     (* Definition testbit : nat -> nat -> bool. *)
     (* Definition shiftl : (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n. *)
     (* Definition shiftr : (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n. *)
     (* Definition bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat. *)
     (* Definition land : nat -> nat -> nat. *)
     (* Definition lor : nat -> nat -> nat. *)
     (* Definition ldiff : nat -> nat -> nat. *)
     (* Definition lxor : nat -> nat -> nat. *)
Extract Inlined Constant addn => "(+)".
Extract Inlined Constant eqn => "Int.(=)".

Extract Inlined Constant addn_rec => "(+)".
Extract Inlined Constant addn => "(+)".
Extract Inlined Constant subn_rec => "(-)".
Extract Inlined Constant subn => "(-)".

Extract Inlined Constant leq => "(<=)".
Extract Inlined Constant geq => "(>=)".
Extract Inlined Constant ltn => "(<)".
Extract Inlined Constant gtn => "(>)".
Extract Inlined Constant maxn => "max".
Extract Inlined Constant minn => "min".
Extract Inlined Constant iter => "Fn.apply_n_times".
Extract Inlined Constant iteri => "(fun n f a0 -> fst (Fn.apply_n_times ~n (fun (x,n) ->  (f (n-1) x, n - 1)) (a0, n)))".
Extract Inlined Constant muln_rec => "Int.( * )".
Extract Inlined Constant muln => "Int.( * )".

Extract Inlined Constant expn_rec => "Int.( ** )".
Extract Inlined Constant expn => "Int.( ** )".
Extract Inlined Constant nat_of_bool => "Bool.to_int".

Extract Inlined Constant odd => "(fun x -> not ( x % 2 = 0))".

Extract Inlined Constant double_rec => "(fun x -> x * 2)".
Extract Inlined Constant double => "(fun x -> x * 2)".
Extract Inlined Constant half => "(fun x -> x / 2)".
Extract Inlined Constant uphalf => "(fun x -> (x + 1) / 2)".


Extract Inlined Constant unit_eqMixin => "unit".
Extract Inlined Constant unit_eqType => "unit".
Extract Inlined Constant eqb => "Bool.(=)".
Extract Inlined Constant pred1  => "(fun x y -> Poly.(x = y))".

Extract Inlined Constant pair_eq => "Poly.(=)".
Extract Constant prod_eqMixin "'a" "'b" => "('a * 'b)".
Extract Constant prod_eqType "'a" "'b" => "('a * 'b)".
Extract Inductive option  => "option" [ "Some" "None"].
Extract Inlined Constant opt_eq => "Poly.(=)".
Extract Constant option_eqMixin "'a" => "'a option".
Extract Constant option_eqType "'a" => "'a option".

Extract Inductive sum => "Either.t" ["First" "Second"].
Extract Inlined Constant sum_eq => "Poly.(=)".
Extract Constant sum_eqMixin "'a" "'b" => "('a, 'b) Core._either".
Extract Constant sum_eqType "'a" "'b" => "('a, 'b) Core._either".




Extract Inductive nat => int [ "0" "succ" ] "(fun f0 fs n -> if n = 0 then f0 () else fs (n - 1))".
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ]. 
Extract Inductive reflect => "bool" [ "true" "false" ].


Extraction Inline Equality.axiom.
Extraction Inline Equality.op.
Extraction Inline Equality.sort.
Extraction Inline Equality.class.

Extraction Implicit Equality.axiom [T e].
Extraction Implicit Equality.mixin_of [T].
Extraction Implicit Equality.Mixin [T  ].
Extraction Implicit Equality.Pack [ sort].
Extraction Implicit Equality.op [T].
Extraction Implicit Equality.clone [T].
Extraction Implicit Equality.class [].
Extraction Implicit Equality.sort [t].


Extract Constant Equality.axiom "'a" => "unit" .

Extract Inlined Constant eqnP => "()".
Extract Inlined Constant Bool.eqb_spec => "()".
Extract Inlined Constant fintype.subset_eqP => "()".
Extract Inlined Constant fintype.subset_eqP => "()".
Extract Inlined Constant Equality.class => "".




Extract Inlined Constant size => "List.length".
Extract Inlined Constant nilp => "(fun x -> List.length x > 0)".
Extract Inlined Constant ohead => "List.hd".

Extract Inlined Constant eqseqP => "()".
Extraction Implicit eqseqP [T].



     (* Definition head : forall T : Type, T -> seq T -> T. *)
     (* Definition behead : forall T : Type, seq T -> seq T. *)
     (* Definition ncons : forall T : Type, nat -> T -> seq T -> seq T. *)
     (* Definition nseq : forall T : Type, nat -> T -> seq T. *)
     (* Definition seqn_type : Type -> nat -> Type. *)
     (* Definition seqn_rec : forall T : Type, (seq T -> seqn_type T 0) -> forall n : nat, seqn_type T n. *)
     (* Definition seqn : forall (T : Type) (n : nat), seqn_type T n. *)
     (* Definition cat : forall T : Type, seq T -> seq T -> seq T. *)
     (* Definition rcons : forall T : Type, seq T -> T -> seq T. *)
     (* Definition last : forall T : Type, T -> seq T -> T. *)
     (* Definition belast : forall T : Type, T -> seq T -> seq T. *)
     (* Definition nth : forall T : Type, T -> seq T -> nat -> T. *)
     (* Definition set_nth : forall T : Type, T -> seq T -> nat -> T -> seq T. *)
     (* Definition find : forall T : Type, pred T -> seq T -> nat. *)
     (* Definition filter : forall T : Type, pred T -> seq T -> seq T. *)
     (* Definition count : forall T : Type, pred T -> seq T -> nat. *)
     (* Definition has : forall T : Type, pred T -> seq T -> bool. *)
     (* Definition all : forall T : Type, pred T -> seq T -> bool. *)
     (* Definition drop : forall T : Type, nat -> seq T -> seq T. *)
     (* Definition take : forall T : Type, nat -> seq T -> seq T. *)
     (* Definition rot : forall T : Type, nat -> seq T -> seq T. *)
     (* Definition rotr : forall T : Type, nat -> seq T -> seq T. *)
     (* Definition catrev : forall T : Type, seq T -> seq T -> seq T. *)
     (* Definition rev : forall T : Type, seq T -> seq T. *)
     (* Definition eqseq : forall T : eqType, seq T -> seq T -> bool. *)
     (* Definition seq_eqMixin : forall T : eqType, Equality.mixin_of (seq T). *)
     (* Definition seq_eqType : eqType -> eqType. *)
     (* Definition mem_seq : forall T : eqType, seq T -> T -> bool. *)
     (* Definition seq_eqclass : eqType -> Type. *)
     (* Definition seq_of_eqclass : forall T : eqType, seq_eqclass T -> seq T. *)
     (* Definition pred_of_seq : forall T : eqType, seq_eqclass T -> predPredType T. *)
     (* Definition seq_predType : forall T : eqType, predType T. *)
     (* Definition mem_seq_predType : forall T : eqType, predType T. *)
     (* Definition constant : forall T : eqType, seq T -> bool. *)
     (* Definition uniq : forall T : eqType, seq T -> bool. *)
     (* Definition undup : forall T : eqType, seq T -> seq T. *)
     (* Definition index : forall T : eqType, T -> seq T -> nat. *)
     (* Definition inE : *)
     (* Definition bitseq : Set. *)
     (* Definition bitseq_eqType : eqType. *)
     (* Definition bitseq_predType : predType bool_eqType. *)
     (* Definition incr_nth : seq nat -> nat -> seq nat. *)
     (* Definition perm_eq : forall T : eqType, seq T -> seq T -> bool. *)
     (* Definition mask : forall T : Type, bitseq -> seq T -> seq T. *)
     (* Definition subseq : forall T : eqType, seq T -> seq T -> bool. *)
     (* Definition rem : forall T : eqType, T -> seq T -> seq T. *)
     (* Definition map : forall T1 T2 : Type, (T1 -> T2) -> seq T1 -> seq T2. *)
     (* Definition pmap : forall aT rT : Type, (aT -> option rT) -> seq aT -> seq rT. *)
     (* Definition iota : nat -> nat -> seq nat. *)
     (* Definition mkseq : forall T : Type, (nat -> T) -> nat -> seq T. *)
     (* Definition foldr : forall T R : Type, (T -> R -> R) -> R -> seq T -> R. *)
     (* Definition sumn : seq nat -> nat. *)
     (* Definition foldl : forall T R : Type, (R -> T -> R) -> R -> seq T -> R. *)
     (* Definition pairmap : forall T1 T2 : Type, (T1 -> T1 -> T2) -> T1 -> seq T1 -> seq T2. *)
     (* Definition scanl : forall T1 T2 : Type, (T1 -> T2 -> T1) -> T1 -> seq T2 -> seq T1. *)
     (* Definition zip : forall S T : Type, seq S -> seq T -> seq (S * T). *)
     (* Definition unzip1 : forall S T : Type, seq (S * T) -> seq S. *)
     (* Definition unzip2 : forall S T : Type, seq (S * T) -> seq T. *)
     (* Definition all2 : forall S T : Type, (S -> T -> bool) -> seq S -> seq T -> bool. *)
     (* Definition flatten : forall T : Type, seq (seq T) -> seq T. *)
     (* Definition shape : forall T : Type, seq (seq T) -> seq nat. *)
     (* Definition reshape : forall T : Type, seq nat -> seq T -> seq (seq T). *)
     (* Definition flatten_index : seq nat -> nat -> nat -> nat. *)
     (* Definition reshape_index : seq nat -> nat -> nat. *)
     (* Definition reshape_offset : seq nat -> nat -> nat. *)
     (* Definition allpairs_dep : *)
     (* Definition allpairs : forall S T R : Type, (S -> T -> R) -> seq S -> seq T -> seq R. *)
     (* Definition incr_tally : forall T : eqType, seq (T * nat) -> T -> seq (T * nat). *)
     (* Definition tally : forall T : eqType, seq T -> seq (T * nat). *)
     (* Definition wf_tally : forall T : eqType, qualifier 1 (seq (T * nat)). *)
     (* Definition tally_seq : forall T : eqType, seq (T * nat) -> seq T. *)
     (* Definition cons_perms_ : *)
     (*   forall T : eqType, *)
     (*   (seq T -> seq (T * nat) -> seq (seq T) -> seq (seq T)) -> *)
     (*   seq T -> seq (T * nat) -> seq (T * nat) -> seq (seq T) -> seq (seq T). *)
     (* Definition perms_rec : *)
     (*   forall T : eqType, nat -> seq T -> seq (T * nat) -> seq (seq T) -> seq (seq T). *)
     (* Definition permutations : forall T : eqType, seq T -> seq (seq T). *)
     (* Definition all_iff_and_rect : *)
     (*   forall (P Q : Prop) (P0 : Type), (P -> Q -> P0) -> all_iff_and P Q -> P0. *)
     (* Definition all_iff_and_ind : forall P Q P0 : Prop, (P -> Q -> P0) -> all_iff_and P Q -> P0. *)
     (* Definition all_iff_and_rec : *)
     (*   forall (P Q : Prop) (P0 : Set), (P -> Q -> P0) -> all_iff_and P Q -> P0. *)
     (* Definition all_iff : Prop -> seq Prop -> Prop. *)









(* Example coq:

(* Getting rid of reflect and other proof related equalities *)


Module Type NetbufTypes.
Parameter A:Set.
(* These need to be types that can be coerced into ordType *)
Axiom A_eqMixin : Equality.mixin_of A.


End NetbufTypes.


Module Netbuf (Params: NetbufTypes).
  Section Netbuf.


  Canonical A_eqType := Eval hnf in EqType Params.A Params.A_eqMixin.

  Record t :=  mkNetBuffer {
                     x: nat; y: nat; z: seq Params.A;
                   }.
  Definition updateNetBuffer (buf: t) : t := mkNetBuffer (x buf + 1) (y buf) [::].
  Definition eqNetBuffer (buf: t) (buf': t) : bool := (x buf) == (x buf').



  Definition eq_netBuf  (v v': Params.A) (buf buf': t)  := if  v == v' then buf else buf'. 

  Definition len_netBuf (buf: t) := size (z buf).
  

  Extraction Inline x y z.
  End Netbuf.
End Netbuf.
*)












