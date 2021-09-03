From CompCert Require Import Coqlib Maps.
From Utils    Require Import Defns Values.
From GOTO Require Import Language Sem.
Import Val ListNotations.

(* Definition abstset := PMap.t bool.

Definition is_abst_ident (id : ident) (Abs : abstset) : bool :=
(* how to define id is in abstenv? *)
PMap.get id Abs. *)

(* Define whether an ident is abstracted *)
Parameter abstset : Type.
Parameter is_abst_id_bool : ident -> abstset -> bool.
Definition is_abst_id (id : ident) (Abs : abstset) : Prop :=
    is_abst_id_bool id Abs = true.


(* The abstract prop maps values in the 
   concrete domain into the abstract domain *)
Parameter abstract : val -> val -> Prop.
(* The concretize prop maps values in the 
   abstract domain into the concrete domain *)
Parameter concretize : val -> val -> Prop.


(* Define env2 is an abstraction of env1 *)
Section ENVABST.
    Variable Abs: abstset.
    Inductive env_abstract : env -> env -> Prop :=
    | envabs_def : forall E1 E2,
        (forall x, E1 ! x = None <-> E2 ! x = None) ->
        (* (forall x _1 _2, Some _1 = E1 ! x <-> Some _2 = E2 ! x ) -> *)
        (forall id1 v_e1 v_e2, is_abst_id id1 Abs ->
          E1 ! id1 = Some v_e1 ->
          E2 ! id1 = Some v_e2 ->
          abstract v_e1 v_e2) ->
        (forall id2, ~is_abst_id id2 Abs -> E1 ! id2 = E2 ! id2) ->
        env_abstract E1 E2.
End ENVABST.


(* Define expressions in abstracted programs *)
Inductive absexpr : Type :=
    | AEvar   : ident -> absexpr                      (**r variables*)
    | AEvalue : val -> absexpr                        (**r literals *)
    | AEconc   : absexpr -> absexpr
    | AEuop   : uoperation -> absexpr -> absexpr
    .


(* Define how we evaluate expressions in the abstracted program *)
Section ABS_EVAL_EXPR.
  Variable E: env.
  (* Parameter m: mem. *)
  Inductive abs_eval_expr : absexpr -> val -> Prop :=
    | eval_AEvar : forall x v,
        Some v = E ! x ->
        abs_eval_expr (AEvar x) v
    | eval_AEvalue : forall v,
        abs_eval_expr (AEvalue v) v
    | eval_AEconc : forall x v v_abs,
        abs_eval_expr x v_abs ->
        concretize v_abs v ->
        abs_eval_expr (AEconc x) v
    | eval_AEuop : forall op x v_i v,
        abs_eval_expr x v_i ->
        v = eval_uop op v_i ->
        abs_eval_expr (AEuop op x) v.
End ABS_EVAL_EXPR.


(* Tr_read in the soundness proof *)
Fixpoint abstract_expr (Abs : abstset) (orig_expr : expr) : absexpr :=
    match orig_expr with
    | Evalue val => AEvalue val
    | Evar id => if (is_abst_id_bool id Abs) then (AEconc (AEvar id)) else (AEvar id)
    | Euop op exp => AEuop op (abstract_expr Abs exp)
    (* the rest of the expressions remain to be handled *)
    end.

Axiom abst_conc_rev: 
    forall v_abs v_conc, 
        concretize v_abs v_conc <->
        abstract v_conc v_abs.
(* Proof.
Admitted. *)


(* Lemma1 in the soundness proof document *)
Lemma lemma1: 
    forall (orig_expr : expr) (v : val)
            (orig_env : env) (abst_env : env) (Abs : abstset), 
    env_abstract Abs orig_env abst_env ->
    eval_expr orig_env orig_expr v -> 
    abs_eval_expr abst_env (abstract_expr Abs orig_expr) v.

(* example proof *)
Proof with eauto.
  intros. induction H0;
  try solve [econstructor; eauto].
  - (* Evar case *)
    simpl. inversion H; subst.
    unfold is_abst_id in *.
    specialize (H1 x).
    specialize (H2 x v).
    specialize (H3 x).
    assert (exists v', abst_env ! x = Some v') as
    [v_abs B].
    { clear - H0 H1.
      destruct (abst_env ! x).
      - exists v0. auto.
      - exfalso. rewrite <- H0 in H1.

      destruct H1 as [A B].
      clear -B. specialize (B (eq_refl None)).
      inversion B. }
    destruct (is_abst_id_bool x Abs) eqn:xAbs.
    + (* x is abst *)
      econstructor;
      [ econstructor; symmetry; exact B
      | apply abst_conc_rev]...
    + (* x is not abst *)
      clear - H0 H3 B.
      rewrite H3 in H0 by auto.
      econstructor...
Qed.

(* This will be slightly broken now *)
Proof with eauto.
    intros.
    induction H0.
    - subst. simpl. (* this is the Evar case *)
      case_eq (is_abst_id_bool x Abs).
      + intros.
        inversion H.
        subst.
        pose proof (eval_AEvar) as X.
        destruct (abst_env ! x) eqn : bob.
        * symmetry in bob.
          pose proof (H3 _ _ _ H1 H0 bob).
          specialize (X _ _ _ bob).
          pose proof (eval_AEconc _ _ v _ X).
          apply H6.
          apply abst_conc_rev.
          apply H5.
        * specialize (H2 x).
          rewrite bob in H2.
          specialize (H2 v v).
          apply H2 in H0.
          inversion H0.
      + intros.
        inversion H.
        assert (~ is_abst_id x Abs). {
          unfold not, is_abst_id.
          intros A.
          rewrite A in H1.
          inversion H1.
        }
        pose proof (H4 _ H7).
        destruct (abst_env ! x) eqn : bob.
        * constructor.
          rewrite H8 in H0.
          rewrite <- H0 in bob...
          (* symmetry.
          apply bob. *)
        * rewrite H8 in H0.
          inversion H0.
    - constructor. (* this is the Evalue case *)
    - econstructor...
      (* pose proof eval_AEuop.
      eapply H2.
      eauto.
      auto. *)
Qed.