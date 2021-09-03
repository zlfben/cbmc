(** * Introduction *)
(** This file contains the symbolic execution semantics for [goto].
    The semantics are given in a structural operational style and
    use symbolic expressions to represent sets of values. *)

From CompCert Require Export Coqlib Maps Smallstep.
From Utils    Require Export Defns Values.
              Require Export Relations.
From GOTO     Require Import Language.
Import Val ListNotations.

Close Scope Z.
Local Open Scope positive.
Local Open Scope goto_scope.



(** Symbolic expressions are used to represent path constraints.
 *)
(* variable free symbolic expressions *)
Inductive sexpr : Type :=
  | Ssymbol: symbol -> sexpr

  | Svalue : val  -> sexpr
  (* | Sif    : sexpr  -> sexpr -> sexpr -> sexpr *)
  | Suop   : uoperation -> sexpr -> sexpr
  | Sbop   : boperation -> sexpr -> sexpr -> sexpr
  | Scomp  : comparison -> sexpr -> sexpr -> sexpr
  .

(** some definitions/notations for convenience.
 *)
Definition Sfalse := Svalue Vfalse.
Coercion Ssymbol : symbol >-> sexpr.
Notation "! a" := (Suop Onot a) (at level 5) : goto_scope.




(** * The Parameterized SAT solver *)
(** We parameterize our semantics by a solver. This serves two purposes
    - To avoid expensive computation in the Coq system. (Which it is not designed for anyway) 
    - To close the modeling gap, since real SymbEx systems also make calls to external solvers.

    This module type (signature) requires entailment [|=] and then defines several other relavent
    concepts.
    
    %\textcolor{blue}{\textbf{Code elided}}.%
    
*)
Module Type Solver.

  (** [satisfies_single G b] asks if a set of formulas
      ([list sexpr]), G, entails a formula b. [inl]s
      reprsent a "yes" answer (and [inr]s the converse).
      
      This will be the notion upon which we define the others.
      (Sat of a list, validity checking for single sexprs & lists)

  *)
  Parameter satisfies_single : list sexpr -> sexpr -> sum sexpr sexpr.

  (* begin hide*)
  (** Auxillary functions for [satisfies_list]
      - [satisfies_list G B] asks if a set of formulas, G,
        entails every formula the set B.
      - [get_lefts]  returns all the formulas in B that are entailed.
      - [get_rights] returns all the formulas in B that are NOT entailed. *)

  Definition get_lefts (lst: list (sum sexpr sexpr)) : list sexpr :=
    List.fold_left (fun sd e => match e with
                                | inl e => e :: sd
                                | inr _ =>      sd
                                end)
                   lst [].

  Definition get_rights (lst: list (sum sexpr sexpr)) : list sexpr :=
    List.fold_left (fun sd e => match e with
                                | inl _ =>      sd
                                | inr e => e :: sd
                                end)
                   lst [].

  Definition satisfies_list (G assrts: list sexpr) : Prop :=
    get_lefts (List.map (satisfies_single G) assrts) = assrts.


  Definition true_in_single (G: list sexpr) (x: sexpr) :=
    let nx := ! x in
    satisfies_single G nx = inr nx.

  Definition true_in_list (G assrts: list sexpr) :=
    let na := List.map (fun x => ! x) assrts in
    get_rights (List.map (satisfies_single G) na) = na.

  (** Typeclass defn for adhoc polymorphism *)
  Class Satisfies A : Type := {
    satisfies : list sexpr -> A -> Prop
  }.

  Instance Satifies_single : Satisfies sexpr := {
    satisfies := (fun G e => satisfies_single G e = inl e)
  }.

  Instance Satisfies_list : Satisfies (list sexpr) := {
    satisfies := satisfies_list
  }.

  Class True_in A : Type := {
    true_in : list sexpr -> A -> Prop
  }.

  Instance True_in_single : True_in sexpr := {
    true_in := true_in_single
  }.

  Instance True_in_list : True_in (list sexpr) := {
    true_in := true_in_list
  }.

  (** Used for debugging information in the case of an
      [assert]ion failure. *)
  Definition get_failed (G assrts: list sexpr) : list sexpr :=
    get_rights (List.map (satisfies_single G) assrts).


  (* end hide*)
  (** The adhoc polymorphic functions we wanted. See [Satisfies] & [True_in]

  *)
  Notation "x     'satIn' G" := (  satisfies G x) (at level 70) : goto_scope.
  Notation "x 'aintSatIn' G" := (~ satisfies G x) (at level 70) : goto_scope.

  Notation "G |=  x" := (  true_in G x) (at level 70) : goto_scope.
  Notation "G |/= x" := (~ true_in G x) (at level 70) : goto_scope.

End         Solver.


(** * The SymbEx semantics; a functor taking a [Solver].
      
      The semantics are operational, so we define program points/states.
      The two key elements in a state are
      - the environment, which maps program variables to their symbolic
        expressions
      - a [list sexpr], representing the path constraint. This is expressed
        in terms of symbolic expression.

      Example: Say that program variables %$x,\ y,\ \& z$% are mapped to symbols
      %\$a,\ \$b,\ \$c% respectively. If we do the assignment %$x = y+z$%
      then %x% is remapped from %\$a% to %\$b + \$c%. if we then assert
      that %x% is greater than 0, we add %\$b + \$c > 0% to the path
      constraint.

      I make no attempt to perform optimization/be clever over solver
      queries or in building the path constraint. The artefact only ensures
      the modelling of the model checking is sound i.e. asserts fail when they
      should and vice versa. This is mainly because I have no domain expertise.
      It is also not clear whether this is the right artefact to model that
      kind of thing. *)

Module Semantics (Import solver: Solver).
  Open Scope error_monad_scope.
  Definition genv := PTree.t function.
  Definition env  := PTree.t sexpr.


  (** Abstract stack definition *)

  Inductive stack : Type :=
    | Stackframe: 
        forall (dst_in_caller   : ident     )
               (caller          : function  )
               (returnsite      : code      )
               (callers_env     : env       )
               (stk             : stack     ),
        stack
    | Stknil : stack.


    (** We have structural small-step semantics, representing
        transitions between states. There are three main
        program states that appear in the transitions: 

      - [State f pc E cs G i]
        describes intra-function program points.
        [f] is the currently executing function.
        [pc] is a list of instructions, the first of which
        is the next instruction.
        [E] maps variables to their symbolic values at the
        current program point.
      - [Callstate f args cs G i]
        is a liminal a program point in between a caller and
        callee. It is an abstraction of control passing
        between the former and latter.
        [f] is the callee.
        [args] are the arguments passed to the callee.
      - [Returnstate rv cs G i]
        similar to [Callstates] but for returns. An
        abstraction of control passing from callee
        to caller.
        [rv] is the (symbolic) return value.

        Common to all these states are:
        [cs], the (abstract) callstack.
        [G], a [list sexpr] representing the path constraints.
        [i], a fresh symbol. Used to ensure correctness of
        [GDecl]

        We also have two failure states [Inconsistent_with]
        & [Assrt_failure]. The former is the result of an
        [assume gd] instruction when [gd] is inconsistent
        with [G]. The latter is the result of [assert gd]
        where [G |/= gd].

      *)

  Inductive state : Type :=
    | State :
        forall (curr_fn          : function    )
               (pc               : code        )
               (environment      : env         )
               (callstk          : stack       )
               (path_constraints : list sexpr  )
               (symbol_counter   : symbol      ),
        state
    | Callstate :
        forall (callee           : function    )
               (args_to_cee      : list sexpr  )
               (callstk          : stack       )
               (path_constraints : list sexpr  )
               (symbol_counter   : symbol      ),
        state
    | Returnstate :
        forall (ret_val          : sexpr     )
               (callstk          : stack     )
               (path_constraints : list sexpr)
               (symbol_counter   : symbol    ),
        state
    | Inconsistent_with :
        forall (path_constraints : list sexpr)
               (asspn            : sexpr     ),
        state
    | Assrt_failure :
        forall (path_constraints : list sexpr)
               (failed_assrt     : list sexpr),
        state.



  (** Some functions to translate program variables ([expr]s) to
      symbolic expressions ([sexpr]s), given an environment [E].
    
      %\textcolor{blue}{\textbf{Code elided}}.%

      *)

  Section Symbolize.
    (* begin hide *)
    Variable (E: env).

    (** This function takes a general [expr] e, and returns
        one where all variables in e have been replaced with
        their mapped [sexpr]s from the symbolic environment, E.
        The output has no variables. *)
    (* are expressions side effect free? *)
    Fixpoint symbolize (e: expr) : res sexpr :=
      match e with
      (* inline variables with variable-free [expr]s *)
      | Evar x => match E ! x with
                  | Some e' => OK e'
                  | None => Error (msg "[symbolize: variable not declared]")
                  end
      | Ederef _ => Error (msg "mem not done yet")
      | Eaddrof _ => Error (msg "mem not done yet")
      (* recursive cases *)
      | Euop op e     => do s <- symbolize e;
                         OK (Suop op s)
      | Ebop op e1 e2 => do s1 <- symbolize e1;
                         do s2 <- symbolize e2;
                         OK (Sbop op s1 s2)
      | Ecomp c l r   => do l' <- symbolize l;
                         do r' <- symbolize r;
                         OK (Scomp c l' r')
      (* base/leaf cases *)
      | Evalue v => OK (Svalue v)
      end.

    Fixpoint symbolize_list es : res (list sexpr) :=
      match es with
      | h :: t => do h' <- symbolize h;
                  do t' <- symbolize_list t;
                  OK (h' :: t')
      | [] => OK []
      end.

    Fixpoint get_args (args: list expr) : res (list sexpr) :=
      match args with
      | h :: t => do t' <- get_args t;
                  do h' <- symbolize h;
                  OK (h' :: t')
      | []     => OK []
      end.

    Fixpoint init_sparams (params: list ident) (ses: list sexpr) : env :=
      match params, ses with
      | p :: ps, s :: ses => PTree.set_only_fresh p s (init_sparams ps ses)
      | _      , _        => PTree.empty sexpr
      end.

  End     Symbolize.

  Notation "E ## args" := (get_args E args) (at level 1).

  (** 2nd portion of symbolizing functions; Those related to
      function contracts.

      (for Coq-related reasons, we had to split them in two) *)
  Section Sybmolize2.

    (** A new environment is created, in which only the
        parameters are available.
        This means that [symbolize_requires] will fail if
        [clauses] contains variables not mentioned in the
        parameters.

        e.g. If a function [f] has params [a] & [b], its
        requires clause discussing/containing [c] will
        lead to a program that goes wrong. *)

    Definition symbolize_requires
        E (params: list ident) (args: list expr)
        (clauses: list expr) : res (list sexpr) :=
      do sargs <- E ## args;
      let E' := init_sparams params sargs in
      symbolize_list E' clauses.

    (** Utility functions for [build_ensure_env]. *)
    Fixpoint max_ident (params: list ident) : ident :=
      match params with
      | h :: t => let mx := max_ident t in
                  if h <? mx then mx else h
      | []     => 1
      end.

    Definition build_ensure_old_idents (params: list ident)
        : list ident :=
      let mx := max_ident params in
      List.map (Pos.add mx) params.

    (** The ensures clause for function contracts range over
      - The return value
      - Parameters (with symbolic values at the end of the
        function)
      - Paramaters (with symbolic values at the beginning of
        the function) [__CPROVER_old]

      [build_ensure_env E mx params s] 

      Implementation note: [ident]s are implemented as
      positives.
      In ensures clauses, for all [p] in [ident], [p] refers
      to the parameter's value at the end of the function.
      [p+mx] refers the the parameter's ([p]) value at the
      beginning of the function.
      [mx+mx+1] refers to the return value. *)

    Fixpoint fresh_symbols_env E (s: symbol) (lst: list ident) :=
      match lst with
      (* | h :: t => @PTree.set_only_fresh sexpr h s (fresh_symbols_env E (s+1) t) *)
      | x :: xs => fresh_symbols_env (@PTree.set_only_fresh sexpr x s E) (s+1) xs
      | []     => E
      end.

    Definition build_ensure_env (s: symbol) (params: list ident) sargs : env :=
      let mx := max_ident params in
      let E1 := init_sparams (List.map (Pos.add mx) params) sargs in
      let E2 := @PTree.set_only_fresh sexpr (mx+mx+1) s E1        in
      fresh_symbols_env E2 (s+1) params.

    (* end hide *)
  End     Sybmolize2.


  (** We will use events to trace the instructions executed
      in a program.
      
       *)
  Inductive event : Type :=
    | Estep: positive -> instr -> event.
  Definition trace := list event.


  (** ** The transition relations.
        We split these up for clarity and also to be able
        to "mix-&-match" them as we like
        
        *)

  Section RELSEM.
    Variable ge: genv.
    Open Scope goto_scope.

    (* begin hide *)
    Local Definition jump_to_label (f: function) (lbl: nat) : code :=
      List.skipn lbl f.(body).
    (* end hide *)



    (** Transitions for intra-procedural computation & control flow.
    
     *)
    Inductive step : state -> trace -> state -> Prop :=

      (** [Gskip] advances the pc.
      
       *)
      | step_skip : forall f pc pc' E cs G s,
          pc = Gskip :: pc' ->
          step
            (State f pc  E cs G s) [Estep 1 Gskip]
            (State f pc' E cs G s)

      (** [Gdecl] introduces a fresh variable, and maps
          it to a fresh symbol. If the variable is not
          fresh, the machine gets stuck.

          (this is a design decision easily changed.)
          
      *)
      | step_decl : forall f pc pc' cs E E' G s x,
          pc = Gdecl x :: pc' ->
          E' = PTree.set_only_fresh x (Ssymbol s) E ->
          step 
            (State f pc  E  cs G  s   ) [Estep 1 (Gdecl x)]
            (State f pc' E' cs G (s+1))

      (** [Gdead] removes its variable mapping in the environment.
      
       *)
      | step_dead : forall f pc pc' cs E E' G s x _xx,
          pc = Gdead x :: pc' ->
          E ! x = Some _xx ->
          E' = PTree.remove x E ->
          step 
            (State f pc  E  cs G s) [Estep 1 (Gdead x)]
            (State f pc' E' cs G s)

      (** [Gassign] updates the (symbolic) mapping of the variable.
          Let %\$x% denote the symbol %$x$% (which does not necessarily
          have any relation to the variable %$x$%).
          e.g. if %$E\ x \mapsto \$x$% & %$E\ y \mapsto \$z + \$w$%,
          [Gassign x (x + y)] will update E to E', where
          %$E'\ x \mapsto \$x + \$z + \$w$%
          This negates the need to reason about SSA.
          
           *)
      | step_assign : forall f pc pc' cs E E' G s x e e',
          pc = Gassign x e :: pc' ->
          symbolize E e = OK e' ->
          E' = E ! x <- e' ->
          step 
            (State f pc  E  cs G s) [Estep 1 (Gassign x e)]
            (State f pc' E' cs G s)

      (** [Ggoto]s can make two possible transitions.
          This rule makes a jump (of a goto) and adds the
          guard to the path constraints.

          This is one of a pair of a non-deterministic
          (in the TOC sense) rules, where we do make the
          jump. Note we do not evaluate the guard, this is
          the case we assume it is satisfied.
          
           *)
      | step_goto_jump : forall f pc pc' cs E G G' s gd gd' lbl xx,
          pc  = Ggoto gd lbl :: xx ->
          pc' = jump_to_label f lbl ->
          symbolize E gd = OK gd' ->
          G' = gd' :: G ->
          step 
            (State f pc  E cs G  s) [Estep 1 (Ggoto gd lbl)]
            (State f pc' E cs G' s)

      (** [Ggoto]s can make two possible transitions.
          This rule falls through a goto (i.e. does not jump to
          its target) and adds the negation of its guard to the
          path constraints.

          It is one of a pair of non-deterministic rules.
          See [step_goto_jump].
          
           *)
      | step_goto_fall_through : forall f pc pc' cs E G G' s gd gd' xx,
          pc = Ggoto gd xx :: pc' ->
          symbolize E gd = OK gd' ->
          G' = !gd' :: G ->
          step 
            (State f pc  E cs G  s) [Estep 2 (Ggoto gd xx)]
            (State f pc' E cs G' s)



      (* [Gassume] adds an assumption to the path constraints.
      
       *)
      (* | step_assume : forall f pc pc' cs G E gd gd',
          pc = Gassume gd :: pc' ->
          symbolize E gd = OK gd' ->
          step (State f pc  cs         G  E)
               (State f pc' cs (gd' :: G) E) *)


      (** [Gassume] adds an assumption to the path constraints,
          if their conjunction is consistent (according to
          the solver).
          
           *)
      | step_assume : forall f pc pc' cs E G G' s gd gd',
          pc = Gassume gd :: pc' ->
          symbolize E gd = OK gd' ->
          G' = gd' :: G ->
          G' |/= Sfalse ->
          step 
            (State f pc  E cs G  s) [Estep 1 (Gassume gd)]
            (State f pc' E cs G' s)

      (** [Gassume] of an assumption that is inconsistent with
          the path constraints, transitions the machine
          to an error state.
          
           *)
      | step_assume_Incon : forall f pc pc' cs E G s gd gd',
          pc = Gassume gd :: pc' ->
          symbolize E gd = OK gd' ->
          gd' :: G |= Sfalse ->
          step 
            (State f pc E cs G s) [Estep 2 (Gassume gd)]
            (Inconsistent_with G gd')

      (** [Gassert] checks (with the solver) if its guard [gd],
          holds. If so, we advance the PC.
          
           *)
      | step_assert : forall f pc pc' cs E G s gd gd',
          pc = Gassert gd :: pc' ->
          symbolize E gd = OK gd' ->
          G |= gd' ->
          (* G' = bool_of_sexpr gd' :: G -> *)
          step 
            (State f pc  E cs G s) [Estep 1 (Gassert gd)]
            (State f pc' E cs G s)
            (* (State f pc' cs E G' s) *)
            (* I can see adding the guard to the path
               constraints making the model checker faster
               but also slower. I don't know enough about
               solver engineering to decide one way or the
               other. *)

      (** If the guard [gd], does not hold, the machine moves
          to an error state. see [step_assert].
          
           *)
      | step_assert_fail : forall f pc pc' cs E G s gd gd',
          pc = Gassert gd :: pc' ->
          symbolize E gd = OK gd' ->
          G |/= gd' ->
          step 
            (State f pc E cs G s) [Estep 2 (Gassert gd)]
            (Assrt_failure G [ gd']).

    (** Transitions for "regular" inter-procedural control flow.
        i.e. the Regular Call and return steps.
        
        *)
    Inductive RegCalls : state -> trace -> state -> Prop :=

      | step_call : forall cer pc cs E G s cee sargs x pc' cee_id args,
          pc = Gcall x cee_id args false :: pc' ->
          ge ! cee_id = Some cee ->
          OK sargs = E ## args ->
          RegCalls 
            (State cer pc E cs G s) [Estep 1 (Gcall x cee_id args false)]
            (Callstate cee sargs (Stackframe x cer pc' E cs) G s)

      | step_pass_control : forall f sargs cs G s E xx,
          E = init_sparams f.(params) sargs ->
          RegCalls 
            (Callstate f sargs cs G s) [Estep 3 xx]
            (State f f.(body) E cs G s)

      | step_return : forall f pc cs E G s srv e xx,
          pc = Greturn e :: xx ->
          OK srv = symbolize E e ->
          RegCalls 
            (State f pc E cs G s) [Estep 1 (Greturn e)]
            (Returnstate srv cs G s)

      | step_return_control : forall srv x cer rs E cs G s f E' xx,
          Some E' = PTree.set_only_stale x srv E ->
          RegCalls 
            (Returnstate srv (Stackframe x cer rs E cs) G s) [Estep 4 xx]
            (State f rs E cs G s).


    (** Transitions that abstract a function by using its contract instead.
        i.e. steps that perform Contract Replacement.
        
         *)
    Inductive ConRep : state -> trace -> state -> Prop :=

      | step_fn_contract : forall cer pc pc' E cs G s
                                  x cee_id args cee sargs
                                  E_req cee_requires E_ens
                                  cee_ensures s',
      
          pc = Gcall x cee_id args true :: pc' ->
          ge ! cee_id = Some cee ->

          (** Check the pre-conditions
          *)
          OK sargs = E ## args ->
          E_req = init_sparams cee.(params) sargs ->
          OK cee_requires = symbolize_list E_req cee.(requires) ->
          G |= cee_requires ->
          (* OK cee_requires = symbolize_requires E
                              cee.(params)
                              args
                              cee.(requires) -> *)

          (** assume the post-condition
          *)
          E_ens = build_ensure_env s cee.(params) sargs ->
          OK cee_ensures = symbolize_list E_ens cee.(ensures) ->
          s' = s + Pos.of_nat (List.length sargs) + 1 ->
          ConRep 
            (State cer pc   E                      cs                 G   s    ) [Estep 1 (Gcall x cee_id args true)]
            (State cer pc' (E ! x <- (Ssymbol s')) cs (cee_ensures ++ G) (s'+1))

      | step_fn_contract_fail : forall cer pc E cs G s cee_requires x
                                       cee_id args cee sargs E_req xx,
          pc = Gcall x cee_id args true :: xx ->
          ge ! cee_id = Some cee ->

          (** Check the pre-conditions
           *)
          OK sargs = E ## args ->
          E_req = init_sparams cee.(params) sargs ->
          OK cee_requires = symbolize_list E_req cee.(requires) ->
          G |/= cee_requires ->
          ConRep 
            (State cer pc E cs G s) [Estep 2 (Gcall x cee_id args true)]
            (Assrt_failure G (get_failed G cee_requires)).


      (* | check_requires : forall cer pc cs E G s cee sargs x pc' cee_id args xx,
           = true ->
          pc = Gcall x cee_id args xx :: pc' ->
          ge ! cee_id = Some cee ->
          OK cee_requires = symbolize_requires E params args cee.(requires) ->
          G |= cee_requires ->
          step 
            (State cer pc cs E G s)
            (Callstate cee sargs (Stackframe x cer pc' E cs) (cee.(requires) args ++ G) s). *)

      (* | check_ensures : forall f pc cs E G s srv e xx,
           = true ->
          pc = Greturn e :: xx ->
          OK srv = symbolize E e ->
          step 
            (State f pc cs E G s)
            (Returnstate srv cs G s) *)

    (** Combination of intra-procedural steps with regular calls.
    *)
    Inductive stepRC : state -> trace -> state -> Prop :=
      | RC_intraPCF : forall SI t SO,
          step SI t SO ->
          stepRC SI t SO
      | RC_interPCF : forall SI t SO,
          RegCalls SI t SO ->
          stepRC SI t SO.

    (** Combination of intra-procedural steps with contract replacement.
    *)
    Inductive stepCR : state -> trace -> state -> Prop :=
      | CR_intraPCF : forall SI t SO,
          step SI t SO ->
          stepCR SI t SO
      | CR_replacement : forall SI t SO,
          ConRep SI t SO ->
          stepCR SI t SO.


  End     RELSEM.


  (** ** Program runs / execution

        The follow are some definitions that allow us to
        talk about program runs and verifications concepts.

        %\chrc{still need to properly define "replacement"}%
  *)

  (** Initial and final states, used to define program runs.
    *)

  Inductive initial_state (p : program) : state -> Prop :=
    | initial_state_intro : forall main_id main,
        List.hd_error p = Some (main_id,main) ->
        initial_state p (Callstate main [] Stknil [] 1%positive).

  Inductive final_state : state -> Prop :=
    | fs_regular : forall xx1 xx2 xx3,
        final_state (Returnstate xx1 Stknil xx2 xx3)
    | fs_IW : forall xx1 xx2,
        final_state (Inconsistent_with xx1 xx2)
    | fs_AF : forall xx1 xx2,
        final_state (Assrt_failure xx1 xx2).

  (** Defines the transitive closure of step relations
  *)
  Local Definition Star :=
    @star genv state event.

  Definition not_AF S : Prop :=
    forall xx1 xx2, S <> Assrt_failure xx1 xx2.

  (** State [S], under transition system [stp],
      does not reach an assertion failure state.
  *)
  Definition no_failure_from stp S :=
    forall ge t FS xx1 xx2,
    Star stp ge S t FS ->
    final_state FS ->
    FS <> Assrt_failure xx1 xx2.

  (** A program is considered verified if it does
      not enter an assertion failure state.
  *)
  Definition verifiedP stp (p: program) :=
    forall SI,
    initial_state p SI ->
    no_failure_from stp SI.

  (* Definition no_failure_from_fn (S: state) :=
    forall ge t Send xx1 xx2,
    star ge S t Send ->
    end_of_fn Send ->
    Send <> Assrt_failure xx1 xx2.

  Parameter entry_point : function -> state -> Prop.

  Definition verifiedF (f: function) := forall Sentry,
    entry_point f Sentry ->
    no_failure_from_fn Sentry. *)





End    Semantics.



