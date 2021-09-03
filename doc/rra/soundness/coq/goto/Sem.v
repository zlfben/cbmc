From CompCert Require Import Coqlib Maps.
From Utils    Require Import Defns Values.
From GOTO Require Import Language.
Import Val ListNotations.



Definition env  := PTree.t val.
Definition genv := PTree.t function.

Inductive stack : Type :=
  | Stackframe: 
      forall (dst_in_caller   : ident   )
             (caller          : function)
             (returnsite      : code    )
             (callers_env     : env     )
             (stk             : stack   ),
      stack
  | Stknil.

Inductive state : Type :=
  | State :
      forall (curr_fn          : function)
             (pc               : code    )
             (callstk          : stack   )
             (environment      : env     ),
      state
  | Callstate :
      forall (callee           : function)
             (args_to_cee      : list val)
             (callstk          : stack   ),
      state
  | Returnstate :
      forall (ret_val          : val  )
             (callstk          : stack),
      state
  | Failure : (* for assertions as well as assumptions? *)
      forall (environment : env )
             (gd          : expr),
      state.


Inductive initial_state (p : program) : state -> Prop :=
  | initial_state_intro : forall main_id main,
      List.hd_error p = Some (main_id,main) ->
      initial_state p (Callstate main [] Stknil).

Inductive final_state : state -> val -> Prop :=
  | final_state_intro : forall v,
    final_state (Returnstate v Stknil) v.

Section EVAL_EXPR.
  Variable E: env.
  (* Parameter m: mem. *)



  Inductive eval_expr : expr -> val -> Prop :=
    | eval_Evar : forall x v,
        Some v = E ! x ->
        eval_expr (Evar x) v
    | eval_Evalue : forall v,
        eval_expr (Evalue v) v
    (* | eval_Eaddrof : forall ,
        eval_expr (Eaddrof ) v
    | eval_Ederef : forall ,
        eval_expr (Ederef ) v *)
    | eval_Euop : forall op e v v1,
        eval_expr e v1 ->
        v = eval_uop op v1 ->
        eval_expr (Euop op e) v.
    (* | eval_Ebop : forall op e1 e2 v v1 v2,
        eval_expr e1 v1 ->
        eval_expr e2 v2 ->
        v = eval_bop op v1 v2 ->
        eval_expr (Ebop op e1 e2) v
    | eval_Ecomp : forall cmp e1 e2 v v1 v2,
        eval_expr e1 v1 ->
        eval_expr e2 v2 ->
        v = eval_comp cmp v1 v2 -> 
        eval_expr (Ecomp cmp e1 e2) v. *)

  Inductive eval_list_expr : list expr -> list val -> Prop :=
    | eval_list_expr_nil :
        eval_list_expr [] []
    | eval_list_expr_cons : forall e es v vs,
        eval_expr e v ->
        eval_list_expr es vs ->
        eval_list_expr (e :: es) (v :: vs).

  Inductive bool_of_expr : expr -> bool -> Prop :=
    | bool_of_expr_intro : forall e b v,
        eval_expr e v ->
        bool_of_val v b -> 
        bool_of_expr e b.

End     EVAL_EXPR.

Fixpoint set_params (params: list ident) (vargs: list val) : env :=
  match params, vargs with
  | i :: is, v :: vs => PTree.set i v (set_params is vs)
  | _, _             => @PTree.empty val
  end.

(* Section RELSEM.
  (* Open Scope error_monad_scope. *)

  Variable ge: genv.
  Inductive step : state -> state -> Prop :=

    | step_Gskip : forall f pc pc' cs E,
        pc = Gskip :: pc' ->
        step (State f pc  cs E)
             (State f pc' cs E)
    | step_Gassign_local : forall f pc pc' cs E x v e,
        pc = Gassign x e :: pc' ->
        eval_expr E e v ->
        step (State f pc  cs  E          )
             (State f pc' cs (E ! x <- v))
    | step_Ggoto : forall f pc pc' cs E e lbl pc_then pc_else b,
        pc = Ggoto e lbl :: pc_else ->
        bool_of_expr E e b ->
        pc_then = List.skipn lbl (f.(body)) ->
        pc' = (if b then pc_then else pc_else) ->
        step (State f pc  cs E)
             (State f pc' cs E)
    | step_Gassume : forall f pc pc' cs E gd b,
        pc = Gassume gd :: pc' ->
        bool_of_expr E gd b ->
        step (State f pc  cs E)
             (if b
             then State f pc' cs E
             else Failure E gd)
    | step_Gassert : forall f pc pc' cs E gd b,
        pc = Gassert gd :: pc' ->
        bool_of_expr E gd b ->
        step (State f pc  cs E)
             (if b
             then State f pc' cs E
             else Failure E gd)
    | step_Gdecl : forall f pc pc' cs E E' x,
        pc = Gdecl x :: pc' ->
        E' = PTree.set_only_fresh x Vundef E ->
        step (State f pc  cs E )
             (State f pc' cs E')
    | step_Gdead : forall f pc pc' cs E E' x _xx,
        pc = Gdead x :: pc' ->
        E ! x = Some _xx ->
        E' = PTree.remove x E ->
        step (State f pc  cs E )
             (State f pc' cs E')
    | step_call : forall f pc cs E cee vargs dst cee_id args use_con ret_site,
        pc = Gcall dst cee_id args use_con :: ret_site ->
        eval_list_expr E args vargs -> 
        step (State f pc  cs E)
             (Callstate cee vargs (Stackframe dst f ret_site E cs))
    | step_pass_control : forall f args cs E,
        E = set_params f.(params) args ->
        step (Callstate f args cs)
             (State f f.(body) cs E)
    | step_return : forall pc cs v e E _x1 _x2,
        pc = Greturn e :: _x2 ->
        eval_expr E e v ->
        step (State _x1 pc cs E)
             (Returnstate v cs)
    | step_return_control : forall v dst cer ret_site E cs,
        step (Returnstate v (Stackframe dst cer ret_site E cs))
             (State cer ret_site cs (E ! dst <- v)).

End     RELSEM. *)