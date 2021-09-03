From CompCert Require Export Maps Coqlib Errors Zbits Integers.
From Utils    Require Export Values.
Import ListNotations.
Import Int64.
Set Implicit Arguments.


(** We want a unified notion of value, since we're operating under the notion  of a C-like toolchain *)




Definition ident  := positive.
Definition symbol := positive.
    



Inductive boperation : Type :=
  | Oadd
  | Osub
  | Oand
  | Oor
  .

Definition bop_to_int64op b :=
  match b with
  | Oadd => Int64.add
  | Osub => Int64.sub
  | Oand => Int64.and
  | Oor  => Int64.or
  end.

Inductive uoperation : Type :=
  | Onot.

Definition uop_to_int64op u :=
  match u with
  | Onot  => Int64.not
  end.

Parameter eval_bop : boperation -> val -> val -> val.
Parameter eval_uop : uoperation -> val -> val.
Parameter eval_comp : comparison -> val -> val -> val.
(* Definition eval_op (op: operation) (x y: val) : val := 
  match op with
  | Oadd => Int64.add x y
  | Osub => Int64.sub x y
  | Onot => x
  end. *)



Definition obind {A B : Type} (a : option A) (f : A -> option B) : option B :=
match a with
  | Some x => f x
  | None => None
end.

Notation "t ! k <- v" := (PTree.set k v t) (at level 1, k at next level).
Notation "t '!f' k '<-' v" := (PTree.set_only_fresh k v t) (at level 1, k at next level).

(* Local Open Scope positive. *)

(* Fixpoint length_and_max (is: list ident) : nat * ident :=
  match is with
  | h :: t => let (n, mx) := length_and_max t in
              (S n, if h <? mx then mx else h)
  | []     => (O, 1)
  end. *)
(* Local Close Scope positive. *)