From CompCert Require Import Coqlib Integers.

Definition block  := positive.
Definition eq_block := peq.

Definition ptrofs := int64.



(* Inductive typ : Type :=
  | Tint64 (* 32-bit integers or pointers *)
  | Tfloat (* 64-bit double-precision floats *)
  | Tlong (* 64-bit integers *)
  | Tsingle (* 32-bit single-precision floats *)
  | Tany32 (* any 32-bit value *)
  | Tany64.  *)


Inductive val : Type :=
  (* | Vundef *)
  | Vint : int64 -> val
  (* | Vptr : block -> ptrofs -> val *)
  .

Definition Vzero: val := Vint Int64.zero.
Definition Vone : val := Vint Int64.one.
Definition Vmone: val := Vint Int64.mone.

Definition Vtrue : val := Vint Int64.one.
Definition Vfalse: val := Vint Int64.zero.

Definition Vnullptr : val := Vzero.
Definition Vptrofs (n: ptrofs) := Vint n.

Definition def_val : val := Vnullptr.

Module Val.

Definition eq (x y: val): {x=y} + {x<>y}.
Proof.
  decide equality.
  apply Int64.eq_dec.
  (* apply Int64.eq_dec. *)
  (* apply eq_block. *)
Defined.
(* Global Opaque eq. *)


Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int: forall n,
      bool_of_val (Vint n) (negb (Int64.eq n Int64.zero)).

End Val.
(* Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vlong _, Tlong => True
  | Vfloat _, Tfloat => True
  | Vsingle _, Tsingle => True
  | Vptr _ _, Tint => Archi.ptr64 = false
  | Vptr _ _, Tlong => Archi.ptr64 = true
  | (Vint _ | Vsingle _), Tany32 => True
  | Vptr _ _, Tany32 => Archi.ptr64 = false
  | _, Tany64 => True
  | _, _ => False
  end. *)

(* Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end. *)




