From GOTO Require Import Language SymbEx.
          Require Import List.
Import ListNotations.

Local Open Scope positive.
Local Open Scope gotop.


(** * Introduction*)
(** This file defines the "theory" necessary to reason about contracts.

    It mainly defines the concepts of the sets of values symbolic
    expressions will represent, and overapproximations. In general, A
    will be an overapproximation of B if A is a larger set of values
    than B. We will make this notion precise for symbolic expressions;
    program states, programs etc.

    This is relevant because is it sound (wrt to verification) to
    model check an overapproximation of a program. i.e. If an
    overapproximate program does not fail some assertion,
    neither will the original program fail that assertion.
    *)

Module Functor (sat: Solver).
  Module Import Sem := (SymbEx.Semantics sat).
  Local Notation "M # x"      := (PMap.get x M) (at level 5).
  Local Notation "M # x <- v" := (PMap.set x v M) (at level 5, x at next level).

(** ** Sets

      The following two sections define sets and how to calculate
      the set of values a program variable has, from the path constraint.%\\%

      %\chrc{ Mike, Jim, re the following code.
      let's ignore it for now, it is too gnarly.
      We can do a deep dive next time / further down the road.
      Skip to [End SetsOfVals] after you read the following examples.}\\%
      
      Sets can be defined as predicates.
      The set %$A \triangleq \{x: int\ |\ x < 2\}$% in set-builder
      notation can be rewritten more directly as a predicate
      like so: %$\text{fun } x: \text{int} \Rightarrow x < 2$%.

      In general, the clauses can also mention other, ostensibly,
      unbound variables. e.g.:

      %\[B \triangleq \{x\ |\ x = a + b + c \land 1 < a < 10 \land \ 
      3 < b < 8 \ldots \}\]%

      These variables are really existentially quantified:

      %\[B \triangleq \text{fun } x \Rightarrow \exists a\ b\ c. \
      x = a + b + c \land 1 < a < 10 \land 3 < b < 8 \ldots \]%
      
      So we can describe the set of values a %\texttt{goto}% program
      variable, %$u$%, has:
      %\[\text{values of } u \triangleq \{x\ |\ x = E\ !\ u \land \langle \text{path constraint} \rangle\}\]%
      Where %$E ! u$% denotes the lookup of variable u in the environment, returning some symbolic expression.
      
      To capture relations between multiple program varibles %$t,\ u,\ v$%,
      we can look at the sets of values of tuples of these varibles. e.g.
      %\[ \{ x, y, z\ |\ x = E\ !\ t \land y = E\ !\ u \land z = E\ !\ v \land \langle \text{path constraint} \rangle\}\]%

      To see why this is relevant, consider 2 programs, %$P1$% and %$P2$%, each with variables %$x,\ y \& z$%.
      In both programs each variable belongs to the set %$\{0,\ 1\}$%. Additionally, let %$P2$% have the following
      constraint on its variables: %$x+y+z=1$%. Then %$P1$% is an overapproximation of %$P2$% because in %$P1$%
      all the variables could be 1, while this is not possible in %$P2$%.

      *)

  Section substitutions.
    Definition substitution := PMap.t int64.
    Variable (S: substitution).

    (** Do substitution, treating the [sexpr] as a value.
    *)
    Fixpoint subst_v se : int64 :=
      match se with
      | Ssymbol x       => (S # x)
      | Svalue (Vint x) => x
      | Suop op s       => (uop_to_int64op op) (subst_v s)
      | Sbop op l r     => (bop_to_int64op op) (subst_v l) (subst_v r)
      | Scomp c l r     => if Int64.cmp c (subst_v l) (subst_v r)
                            then Int64.one else Int64.zero
      end.

    (** Do substitution, treating the [sexpr] as a boolean
        (Really, a [Prop]).
        *)
    Definition subst_P se : Prop :=
      match se with
      | Ssymbol x       => Int64.lt (Int64.zero) (S # x)       = true
      | Svalue (Vint v) => Int64.lt (Int64.zero) v             = true
      | Suop _ _
      | Sbop _ _ _      => Int64.lt (Int64.zero) (subst_v se)  = true
      | Scomp c l r     => Int64.cmp c (subst_v l) (subst_v r) = true
      end.

    (** Our subset/inclusion notion.
    *)
    Fixpoint subst_conseq lst :=
      match lst with
      | [x]    => subst_P x
      | h :: t => subst_P h /\ subst_conseq t
      | []     => True
      end.

    Fixpoint subst_antece lst conseq : Prop :=
      match lst with
      | h :: t => (subst_P h) -> subst_antece t conseq
      | []     => conseq
      end.

  End     substitutions.

  Section SetsOfVals.
    Fixpoint setof (n: nat) :=
      match n with
      | S m => int64 -> setof m
      | O   => Prop
      end.

    Definition set := setof 1.

    Definition subsetof n (A B: setof n) : Prop.
    Proof.
      induction n as [| m IH]; simpl in *;
      [ exact (A -> B)
      | exact (forall x, IH (A x) (B x))].
    Defined.
    Definition subset := subsetof 1.

    Fixpoint free_symbols acc (se: sexpr) : substitution :=
      match se with
      | Scomp _ l r
      | Sbop  _ l r => free_symbols (free_symbols acc l) r
      | Suop _ s    => free_symbols acc s
      | Svalue _    => acc
      | Ssymbol i   => acc # i <- Int64.zero
      end.

    Fixpoint free_symbols_lst acc ses : substitution :=
      match ses with
      | h :: t => free_symbols_lst (free_symbols acc h) t
      | []     => acc
      end.

    Definition keys {A:Type} (S: PTree.t A) : list ident :=
      fst (List.split (PTree.elements S)).

    Definition fv (G: list sexpr) : list ident :=
      let (_, fvars) := free_symbols_lst (PMap.init Int64.zero) G in
      keys fvars.
    

    Fixpoint existify (G: list sexpr) (S: substitution) (fv: list ident) : Prop :=
      match fv with
      | h :: t => exists x, existify G (S # h <- x) t
      | []     => subst_conseq S G
      end.


    Definition setify n (se G: list sexpr) : setof n.
      (* let mx1 := max_ident (fv G) + 1 in 
      fun x => existify (Scomp Ceq (Ssymbol mx1) se :: G)
                        ((PMap.init Int64.zero) # mx1 <- x)
                        (fv G). *)
    Admitted.

  End     SetsOfVals.
  
  (** ** Overapproximations ("OA")*)
  Section OVERAPPROX.

    (** As mentioned in the comments above, we
    *)

    (** %\textbf{OAs between two symbolic expressions:}%
        Symbolic expression, [sOA], is an
        overapproximation of symbolic expression [s],
        if the set of values of [s] (wrt to some path
        constraint G), is a subset of the set of values
        of [sOA] (wrt to some p.c. GOA).

        Since we're defining the sets as predicates,
        the subset notion is given by implication.

    *)
    Definition oapprox_point sOA GOA s G : Prop :=
      subset (setify 1 [s] G) (setify 1 [sOA] GOA).

    (** %\textbf{OAs between tuples of symbolic expressions:}%
        Similar to [oapprox_point], but now between a tuples,
        [sesOA] & [ses].
    *)
    Definition oapprox_tuple len sesOA GOA ses G : Prop :=
      subsetof len (setify len ses G) (setify len sesOA GOA).

    (** %\textbf{OAs between states:}%
        We compare the sets of values for the tuple,
        containing all varibles in the original
        (not the OA) state.

        The notion of OA is still given by the subset relation.

        %\chrc{ignore the code for now, it is stale/out-of-date.
        we are in the process of discussing/changing the defn.}%
    *)
    Definition oapprox_vars EOA GOA E G  :=
      let (keys, ses) := List.split (PTree.elements E) in
      let len := length keys in 
      let aux e sd := match EOA ! e, sd with
                      | Some seOA, Some acc => Some (seOA :: acc)
                      | _        , _        => None end in
      match List.fold_right aux (Some []) keys with
      | Some sesOA => oapprox_tuple len sesOA GOA ses G
      | None       => False
      end.


    (** %\textbf{OAs for callstates}%

        Callstates (which abstractly
        represent the passing of control)
        have a list of arguments.

        Callstate X, is an OA of Callstate
        Y, if the tuple of params in X is
        an OA of the tuples of params in Y &
        X & Y have the same params.

        In [oapprox_args aOA GOA a G],
        - [aOA] is the list of args in the OA state
        - [GOA] is the path constraint of the OA state
        - [a] is the list of args in the orig state
        - [G] is the path constraint of the orig state
    *)
    Definition oapprox_args aOA GOA a G : Prop :=
      oapprox_tuple (List.length a) aOA GOA a G.

    (** Over-approximations of states.
    
        %\chrc{\texttt{\_x}s are "don't care"s.}
    *)
    Inductive oapprox_st : relation state :=
      | OA_regular : forall EOA GOA E G _1 _2
                            _3 _4 _5 _6 _7 _8,
            oapprox_vars EOA GOA E G ->
          oapprox_st (State _1 _2 EOA _3 GOA _4)
                     (State _5 _6 E   _7 G   _8)
      | OA_call    : forall f aOA GOA args G _1 _2 _3 _4,
            oapprox_args aOA GOA args G ->
          oapprox_st (Callstate f aOA  _1 GOA _2)
                     (Callstate f args _3 G   _4)
      | OA_return  : forall rOA GOA rv G _1 _2 _3 _4,
            oapprox_point rOA GOA rv G ->
          oapprox_st (Returnstate rOA _1 GOA _2)
                     (Returnstate rv  _3 G   _4)
      | OA_incon   : forall S _1 _2,
          oapprox_st (Inconsistent_with _1 _2)
                     S
      | OA_asstf   : forall S _1 _2,
          oapprox_st S
                     (Assrt_failure _1 _2)
      .

    (* begin hide *)
    (** Typeclass defn for adhoc polymorphism
    *)
    Class OverApproximation A : Type := {
      oapprox : relation A
    }.


    Instance OverApproximation_st
        : OverApproximation state := {
      oapprox := oapprox_st
    }.


    Lemma oa_vars_updatef : forall EOA GOA E G x s1 s2,
      oapprox_vars EOA GOA E G ->
      oapprox_vars (EOA !f x <- s1) GOA
                   (E   !f x <- s2) G.
    Proof with auto. Admitted.
      (* unfold oapprox_env, oapprox_var, PTree.set_only_fresh. intros.
      destruct (peq x0 x) as [->|neq],
      (E ! x) as [Ex|] eqn: A,
      (EOA ! x) as [EOAx|] eqn:B; repeat rewrite A, B in *.
      - apply H in H0. repeat rewrite A, B in *...
      - apply H in H0. repeat rewrite A, B in *... repeat rewrite A, B in *.


    Admitted. *)

    Lemma oa_vars_update : forall EOA GOA E G x s1 s2,
      oapprox_vars EOA GOA E G ->
      oapprox_vars (EOA ! x <- s1) GOA
                   (E   ! x <- s2) G.
    Proof with auto. Admitted.
    Lemma oa_vars_remove : forall EOA GOA E G x ,
      oapprox_vars EOA GOA E G ->
      oapprox_vars (PTree.remove x EOA) GOA
                   (PTree.remove x E  ) G.
    Proof with auto. Admitted.
      (* unfold oapprox_vars. intros.
      destruct (peq x0 x) as [->|neq].
      - admit.
      - unfold oapprox_var. repeat rewrite PTree.gro...
        apply H.

    Admitted. *)
    Lemma oa_vars_symbolized_guard : forall EOA GOA E G gd gd'OA gd',
      oapprox_vars EOA GOA E G    ->
      symbolize EOA gd = OK gd'OA ->
      symbolize E   gd = OK gd'   ->
    oapprox_vars EOA (gd'OA :: GOA)
                 E   (gd'   :: G  ).
    Proof with auto.
    Admitted.

    Lemma oa_vars_foo1 : forall EOA GOA E G x y,
    
    oapprox_vars EOA (x :: GOA)
                 E   (y :: G  ) ->
    oapprox_vars EOA (! x :: GOA)
                 E   (! y :: G  ).
    Proof with auto.
    Admitted.


    Ltac foo :=
      repeat (match goal with
      | H: ?a :: ?b = ?c :: ?d
        |- _ => try inversion H; subst
      end); try solve
      [ constructor; auto
      | constructor; apply oa_vars_update ; auto
      | constructor; apply oa_vars_updatef; auto
      | constructor; apply oa_vars_remove ; auto
      | constructor; eapply oa_vars_symbolized_guard ; eauto].
    
    (* end hide *)



    (** ** Proof Sketch: Contract replacement is sound*)
    (** We want to show that if we replace symbolic execution
        of a function (Original Prog) with a different semantic
        transition that "uses" (asserts preconds, assumes
        postcon) its contract, (OA Prog), verifying the OA prog also
        verifies the orig prog.

        To do so, we'll split the theorem into several lemmas

        - %\textbf{Lemma (OAs step to OAs)}\\%
            %\textbf{If}% state OA overapproximates state S, &
            OA steps to OA' &
            S steps to S' %\textit{under the same transition rule}%
            %\textbf{Then}% OA' overapproximates S'.

          We'll show this for single steps, and an easy induction
          will prove this for the kleene (& other) closure of
          transitions.

        - %\textbf{Lemma (OA is sound wrt to verification)}\\%
            %\textbf{If}% state OA overapproximates state S &
            OA does not step to an assertion failure state
            %\textbf{Then}% neither does S.

        - %\textbf{Lemma (Contract replacement results in an OA.)}\\%
            %\textbf{If}% a state S at a callsite steps through a fn call
            to state S' at the return site, via the regular call transition
            rules
            %\textbf{Then}% under the "check" contract semantics, S steps
            to state OA', where OA' overapproximates S'.

            %\chrc{I don't fully know how to write this down yet, but am
            getting there.}%
    *)
    (** I claim it should be easy to believe these can be extended to whatever closures we need,
        and that it's clear that these lemmas provide a clear path to proving the top level
        theorem. below are versions of the first two lemmas in Gallina (Coq)%\\%
    *)



    (** If a transition takes state S to state S', then
        that (same) transition takes an overapproximation
        of S (state OA) to an overapproximation of S' (state OA').
        Here, the trace t, guarantees that it is the same step.
    *)

    Lemma OA_steps2_OA: forall S S' OA OA' t,
        oapprox OA S ->
        step S t S' ->
        step OA t OA' ->
      oapprox OA' S'.
    (* begin hide *)
    Proof with auto.
      induction 1; inversion 1; inversion 1; subst.
      - foo.
      - foo.
      - foo.
      - foo.
      - foo.
      - constructor. apply oa_vars_foo1.
        eapply oa_vars_symbolized_guard ; eauto.
      - foo.
      - foo.
      - foo.
      - foo.
    Qed.
    (* end hide *)

    (** If a transition takes state A to state B, then
        that (same) transition takes an OA of A to an
        OA of B. Here, the trace t, guarantees that it
        is the same step.
    *)
    Lemma OA_sound_wrt_veri : forall OA S OA' S' t,
        oapprox_st OA S ->
        step S t S' ->
        step OA t OA' ->
        (forall xx1 xx2, OA' <> Assrt_failure xx1 xx2) ->
      forall xx1 xx2, S' <> Assrt_failure xx1 xx2.
    (* begin hide *)
    Proof with auto.
    Admitted.
    (* end hide *)


    (* Parameter ge : genv.
    Theorem oapprox_st_step_IPCF_monotone: forall S1 S2 S1oa S2oa t
      (A: step_IPCF ge S1 t S2)
      (B: step_IPCF ge S1oa t S2oa)
      (C: oapprox S1oa S1),
      oapprox S2oa S2.
    Proof with auto; try solve [apply oapprox_G_cons_monotone;auto].
      induction 1; inversion 1; inversion 1; subst;
      try (match goal with
      | H: ?a :: ?b = ?c :: ?d
        |- _ => try inversion H; subst
      end; try solve [constructor; auto]);
      try (match goal with
      | A: OK ?a :: ?c,
        B: OK ?b :: ?c
        |- _ => rewrite A in B; inversion B; subst
      end);

      try (match goal with
      | A: ?a ! ?b = Some ?c,
        B: ?a ! ?b = Some ?d
        |- _ => rewrite A in B; inversion B; subst
      end); try constructor... admit.
      - rewrite <- H2 in H6. inversion H6. subst.
    Admitted.

    Theorem oapprox_st_step_ConRep_monotone: forall S1 S2 S1oa S2oa t
      (A: step_ConRep ge S1 t S2)
      (B: step_ConRep ge S1oa t S2oa)
      (C: oapprox S1oa S1),
      oapprox S2oa S2.
    Proof.
    Admitted. *)



  End     OVERAPPROX.
End     Functor.


(* 



Section mock.

  Fixpoint make_con (lst : list Prop) :=
    match lst with 
    | h :: t => h /\ make_con t
    | [] => True
    end.

  Fixpoint make_ant (lst: list Prop) (con: Prop) :=
    match lst with 
    | h :: t => h -> make_ant t con
    | [] => True -> con
    end.

  Definition booboo (l1 l2: list Prop) :=
    make_ant l2 (make_con l1).

  Theorem bobo2 : forall (P: Prop) la lc,
    P -> make_ant la lc -> 
    make_ant la (P /\ lc).
  Proof with auto.
    induction la; simpl; intros.
    - split...
    - apply IHla...
  Qed.

  Theorem foo : forall l1 l2 P,
    booboo l1 l2 ->
    booboo (P :: l1) (P :: l2).
  Proof. unfold booboo.
    simpl; intros. apply bobo2; auto.
  Qed.


  Theorem bob : forall lst A B,
  make_ant lst A ->
  make_ant lst B -> 
  make_ant lst (A /\ B).
  Proof with auto.
    induction lst; simpl;intros.
    - split; [apply H|apply H0]...
    -
    apply IHlst;[apply H|apply H0]...
  Qed.

  Theorem bob2 : forall lst A B,
  make_ant lst (A /\ B) ->
  make_ant lst A /\
  make_ant lst B .
  Proof with auto.
    induction lst; simpl;intros.
    - split; intros; destruct (H H0)...
    - split; intros; destruct (IHlst _ _ (H H0))...
  Qed.
End     mock.







Goal forall (P: relation state -> Prop) R1 R2,
P R1 -> P R2 -> P (union _ R1 R2)
.
intros. unfold union.

End    RELSEM.
End    Semantics.












Eval compute in List.fold_left (fun sd e => cons e sd) [1;2;3] [].
  Definition _2ton (params: list ident) : list ident :=
    List.fold_right


  Definition verified_fn (f: function) :=
    forall fS,
    clos_trans state step
      (State f f.(body) Stknil (PTree.empty sexpr)
        [] 1%positive) fS ->
     forall xx1 xx2, fS <> Assrt_failure xx1 xx2.

  Definition verified (p: program) (init_gds: list expr) := 
    forall iS fS,
    initial_state p iS ->
    clos_trans state step iS fS ->
    forall xx1 xx2, fS <> Assrt_failure xx1 xx2.




  End     RELSEM.


  Fixpoint mkge (prog: program) : genv := 
    match prog with
    | (fid,f) :: p => PTree.set fid f (mkge p)
    | []           => PTree.empty function
    end.


End     Semantics.

    Fixpoint add_aux (x: symbol) (orig lst: list symbol) : list symbol :=
      match lst with
      | h :: t => if peq x h then orig else add_aux x orig t
      | []     => x :: orig
      end.

    Definition add x lst := add_aux x lst lst.

    Theorem add__not_in : forall x o l,
    add_aux x o l = x :: o <->
    ~ In x l.
    Proof with auto.
      split;induction l as [|h t IH]; simpl; repeat intro...
      - 
        destruct (peq x h) as [->|A] eqn:B;
        [ clear -H; induction o; inversion H
        | destruct H0; red in IH ]...
      - destruct (peq x h);
        [ destruct H; left
        | apply IH; intro; apply H; right ]...
    Qed.

    Theorem add__in : forall x o l,
      add_aux x o l = o <->
      In x l.
    Proof with auto.
      split.
      - induction l as [|h t IH]; simpl.
        + induction o; inversion 1; subst...
        + destruct (peq x h) as [->|A] eqn:B;
          [left|right]...
      - induction l as [|h t IH]; simpl.
        + inversion 1.
        + destruct (peq x h) as [->|A] eqn:B...
          intros [->|]; [contradiction|]...
    Qed.



    Theorem add_result : forall x lst,
      add x lst = lst \/
      add x lst = x :: lst.
    Proof with eauto.
      induction lst as [| h t IH];
      [ right; cbv
      | ]... unfold add, add_aux in *. fold add_aux in *.
      destruct IH as [IH|IH];
      [ rewrite add__in     in IH
      | rewrite add__not_in in IH].
      - destruct (peq x h) as [->|A] eqn:B...
        left; erewrite add__in...
      - destruct (peq x h) as [->|A] eqn:B...
        erewrite add__not_in...
    Qed.


    Fixpoint appNR (xs ys : list symbol) :=
      match xs with
      | x :: xs => add x (appNR xs ys)
      | []      => ys
      end.

    Theorem appNR_add : forall x xs ys,
      appNR (add x xs) ys = add x (appNR xs ys).
    Proof with auto.
      induction xs; simpl...
      intros. unfold add; simpl. fold add.
      admit.
    Admitted.

    Theorem appNR_assoc : forall xs ys zs,
      appNR (appNR xs ys) zs =
      appNR xs (appNR ys zs).
    Proof with auto.
      induction xs as [|x xs IH]...
      intros. simpl. rewrite appNR_add, IH...
    Qed. *)
