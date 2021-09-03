From Utils Require Import Defns.
Import ListNotations.

Declare Scope goto_scope.
Delimit Scope goto_scope with gotop.

(** * Abstract syntax *)

(** We elide complexity in expressions, including types *)
Inductive expr : Type :=
  | Evar   : ident -> expr                      (**r variables*)

  | Evalue : val -> expr                        (**r literals *)
  | Euop   : uoperation -> expr -> expr
  (* | Eaddrof: expr -> expr                       (**r [&x] *)
  | Ederef : expr -> expr                       (**r [*x] *)
  | Euop   : uoperation -> expr -> expr
  | Ebop   : boperation -> expr -> expr -> expr
  | Ecomp  : comparison -> expr -> expr -> expr *)
  .

Inductive instr : Type :=
  | Gskip
  | Gassign : forall (lhs: ident) (rhs : expr)  , instr
  | Ggoto   : forall (guard: expr) (target: nat), instr
  | Gdecl   : forall (x : ident)                , instr
  | Gdead   : forall (x : ident)                , instr
  | Gassume : forall (guard: expr)              , instr
  | Gassert : forall (guard: expr)              , instr

  | Gcall : forall (dst: ident) (cee: ident) (args: list expr)
                   (use_contract: bool), instr
  | Greturn : expr -> instr


  | Gwhile : forall (condition    : expr     ) (**r experimental *)
                    (body         : instrlist)
                    (term_measure : list expr)
                    (invariant    : list expr),
                    instr
  | Gend_fun
with instrlist : Type :=
  | Gcons : instr -> instrlist -> instrlist
  | Gnil  : instrlist
  .

Definition code := list instr.

Record function : Type := mkFunction
  (* presumably only params can show up in requires clauses,
  do I want to enfore this by construction? *)

{ params   : list ident
; requires : list expr (* side condition: only [params] are allowed to be variables *)
; ensures  : list expr (* side condition: *)
; body     : list instr }.

Definition program := list (ident * function).


(* Section utility_functions.

  Definition bool_of_value (v: val) : bool :=
    if val_eq_dec v NULL then false else true.

  (* bool_of_expr *)

  (* Definition expr_of_assign (i: instrt) : expr :=
    match i with
    | Gassign _ e => e
    | _           => Evalue def_val
    end. *)

  Definition expr_of_block (b: block) : expr :=
    expr_of_instrt (List.last b Gskip).

  (* Typeclass defn for casting various abstract syntax to [expr] *)
  Class Expr_of A : Type := {
    expr_of : A -> expr
  }.

  Instance Expr_of_instrt : Expr_of instrt := {
    expr_of := expr_of_instrt
  }.

  Instance Expr_of_block : Expr_of block := {
    expr_of := expr_of_block
  }.

End     utility_functions. *)


(* Coercion Evar : ident >-> expr. *)

(* Notation "a == b" := (Ecomp Ceq a b) (at level 70) : goto_scope.
Notation "a != b" := (Ecomp Cne a b) (at level 70) : goto_scope.
Notation "a <  b" := (Ecomp Clt a b) (at level 70) : goto_scope.
Notation "a <= b" := (Ecomp Cle a b) (at level 70) : goto_scope.
Notation "a >  b" := (Ecomp Cgt a b) (at level 70) : goto_scope.
Notation "a >= b" := (Ecomp Cge a b) (at level 70) : goto_scope. *)