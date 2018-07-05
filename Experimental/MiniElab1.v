(* ====================================================== *)
(* Extending MiniElab by allowing variables in signatures *)
(* using the nominal set of semantic objects              *)
(* ====================================================== *)
Require Import String.

Require Import Basics.
Require Import Syntax.
Require Import SemObjects.
Require Import CpdtTactics.
Require Import ElabCore.
Require Import NomEnv.
Require Import CustomTactics.
Require Import ProofIrrelevance.

Module FreshTSetEnv := NomN.Fresh NomN.PFin PermSemOb.
Module FreshTSet := NomN.Fresh NomN.PFin NomN.PFin.

Infix ":U:" := (TSetMod.union) (at level 40).
Infix "#" := FreshTSetEnv.fresh (at level 40) : env_scope.
Infix "#" := FreshTSet.fresh (at level 40) : set_scope.

Delimit Scope env_scope with E.
Delimit Scope set_scope with S.

(* ------------------------------------------------------ *)
(* Elaboration rules for modules types and specifications *)
(* ------------------------------------------------------ *)

Inductive Mty_melab : Env -> mty -> MTy -> Prop :=
| Bra_mty_melab : forall E spec S,
    Spec_melab E spec S -> Mty_melab E (Bra_mty spec) S
| Mtid_mty_melab : forall E mtid S,
    lookLongMtid mtid E = Some S -> Mty_melab E (Mtid_mty mtid) S
| Arr_mty_melab : forall E mty1 mty2 E' M,
    Mty_melab E mty1 (MSigma emptyTSet (NonParamMod E')) -> Mty_melab E mty2 (MSigma emptyTSet M) ->
    Mty_melab E (Arr_mty None mty1 mty2) (MSigma emptyTSet (Ftor emptyTSet E' (MSigma emptyTSet M)))
with Spec_melab : Env -> spec -> MTy -> Prop :=
| Type_spec_some_melab : forall E tid ty Ty,
    Ty_elab E ty Ty -> Spec_melab E (Type_spec tid (Some ty))
                                  (MSigma emptyTSet (NonParamMod (addEnvTid tid Ty emptyEnv)))
| Val_spec_melab : forall E vid ty Ty,
    Ty_elab E ty Ty -> Spec_melab E (Val_spec vid ty)
                                  (MSigma emptyTSet (NonParamMod (addEnvVid vid Ty emptyEnv)))
| Module_spec_nonparam_melab : forall E E' mid mty,
    Mty_melab E mty (MSigma emptyTSet (NonParamMod E')) ->
    Spec_melab E (Module_spec mid mty) (MSigma emptyTSet (NonParamMod (addEnvMid mid (NonParamMod E') emptyEnv)))
| Module_spec_param_melab : forall E E' M mid mty,
    Mty_melab E mty (MSigma emptyTSet (Ftor emptyTSet E' M)) ->
    Spec_melab E (Module_spec mid mty)
               (MSigma emptyTSet (NonParamMod (addEnvMid mid (Ftor emptyTSet E' M) emptyEnv)))
| Include_spec_melab : forall E mty M,
    Mty_melab E mty M -> Spec_melab E (Include_spec mty) M
| Seq_spec_elab : forall E s1 s2 E1 E2,
    Spec_melab E s1 (MSigma emptyTSet (NonParamMod E1)) ->
    Spec_melab (plusEnvEnv E E1) s2 (MSigma emptyTSet (NonParamMod E2)) ->
    Spec_melab E (Seq_spec s1 s2) (MSigma emptyTSet (NonParamMod(plusEnvEnv E1 E2)))
| Emp_spec_melab : forall E,
    Spec_melab E Emp_spec (MSigma emptyTSet (NonParamMod emptyEnv)).


Module Examples1.

  Import EnvMod.
  
  Parameter int : tid.
  Parameter t : tid.
  Parameter s : tid.
  
  (* ----------------------------------- *)
  (* {int->t1} |- type s=int : (){s->t1} *)
  (* ----------------------------------- *)
  
  
  Definition E0 : Env := plusEnvEnv emptyEnv (addEnvTid int (Tv_Ty 1) emptyEnv).

  Definition ex3 : spec := Type_spec s (Some (Longtid_ty (Tid_longtid int))).

  Set Printing Coercions.
  
  Lemma ex3lem: Spec_melab E0 ex3
                           (MSigma emptyTSet
                                   (NonParamMod (addEnvTid s (Tv_Ty 1) emptyEnv))).

  Proof.
    unfold ex3. repeat constructor. simpl.
    rewrite <- mapAddPlusEmpty. rewrite EnvMod.add_lookup.
    reflexivity.
  Qed.
End Examples1.

  (* ---------------------------------------------------------- *)
  (* Elaboration rules for modules expressions and declarations *)
  (* ---------------------------------------------------------- *)

Inductive Mexp_melab : Env -> mexp -> MTy -> Prop :=
  | Bra_mexp_melab : forall E mdec E',
      Mdec_melab E mdec (MSigma emptyTSet (NonParamMod E'))  ->
      Mexp_melab E (Bra_mexp mdec) (MSigma emptyTSet (NonParamMod E'))
  | Mid_mexp_melab : forall E mid M,
      lookMidE mid E = Some M ->
      Mexp_melab E (Mid_mexp mid) (MSigma emptyTSet M)
  | Prj_mexp_melab : forall E mexp mid E' M,
      Mexp_melab E mexp (MSigma emptyTSet (NonParamMod E')) ->
      lookMidE mid E' = Some M ->
      Mexp_melab E (Prj_mexp mexp mid) (MSigma emptyTSet M)
  | Funct_mexp_melab : forall E0 mid mty mexp E E',
      Mty_melab E0 mty (MSigma emptyTSet (NonParamMod E)) ->
      Mexp_melab (addEnvMid mid (NonParamMod E) E0) mexp (MSigma emptyTSet E') ->
      Mexp_melab E0 (Funct_mexp mid mty mexp)
                 (MSigma emptyTSet (Ftor emptyTSet E (MSigma emptyTSet E')))
  | App_mexp_melab : forall E0 longmid mexp E E' E'' T,
      lookLongMid longmid E0 = Some (Ftor emptyTSet E' (MSigma T (NonParamMod E''))) ->
      Mexp_melab E0 mexp (MSigma emptyTSet (NonParamMod E)) ->
      enriches E E' ->
      T # E ->
      Mexp_melab E0 (App_mexp longmid mexp) (MSigma T (NonParamMod E''))
  with Mdec_melab : Env -> mdec -> MTy -> Prop :=
  | Dec_mdec_melab : forall E dec E',
      Dec_elab E dec E' ->
      Mdec_melab E (Dec_mdec dec) (MSigma emptyTSet (NonParamMod E'))
  | Type_mdec_melab : forall E tid ty Ty,
      Ty_elab E ty Ty ->
      Mdec_melab E (Type_mdec tid ty) (MSigma emptyTSet (NonParamMod (addEnvTid tid Ty emptyEnv)))
  | Mod_mdec_melab : forall E0 mid mexp M T,
      Mexp_melab E0 mexp (MSigma T M) ->
      Mdec_melab E0 (Mod_mdec mid mexp) (MSigma T (NonParamMod (addEnvMid mid M emptyEnv)))
  (*
  | ModTyp_mdec_melab : forall E mtid mty S,
      Mty_melab E mty S ->
      Mdec_melab E (ModTyp_mdec mtid mty) emptyTSet (addEnvMtid mtid S emptyEnv)
  *)
  | Open_mdec_melab : forall E0 mexp E,
      Mexp_melab E0 mexp (MSigma emptyTSet (NonParamMod E)) ->
      Mdec_melab E0 (Open_mdec mexp) (MSigma emptyTSet (NonParamMod E))
  | Seq_mdec_melab : forall E mdec1 mdec2 E1 E2 T1 T2 T2' E2',
      Mdec_melab E mdec1 (MSigma T1 (NonParamMod E1)) ->
      (* we add an assumption that the two signatures are aplha-converitble  *)
      ae_mty (MSigma T2 (NonParamMod E2)) (MSigma T2' (NonParamMod E2')) ->
      Mdec_melab (plusEnvEnv E E1) mdec2 (MSigma T2 (NonParamMod E2)) ->
      (T1 # T2')%S ->
      (T1 # PermSemOb.fvs E)%S ->
      Mdec_melab E (Seq_mdec mdec1 mdec2) (MSigma (T1 :U: T2') (NonParamMod (plusEnvEnv E1 E2')))
  | Emp_mdec_melab : forall E,
      Mdec_melab E Emp_mdec (MSigma emptyTSet (NonParamMod emptyEnv)).

(* -------------------------------------------------- *)
(* An example of the module declaration, for which    *)
(* it is crucial to be able to apply alpha-conversion *)
(*----------------------------------------------------*)

Module FunctorAppTwice.

  Open Scope env_scope.
  Parameter m1 : tid.
  Parameter m2 : tid.
  Parameter Fn : tid.
  Parameter a : vid.
  Parameter b : vid.

  Parameter m1_Fn_neq : Fn <> m1.

  Import EnvMod.
  Import TSetMod.

  Definition Ø := empty.
  Definition Øe := emptyEnv.

  Notation "'[' k '|->' v ']ₜ'" := (addEnvTid k v Øe) (at level 100) : env_scope.
  Notation "'[' k '|->' v ']ₘ'" := (addEnvMid k v Øe) (at level 100) : env_scope.

  Definition s_ a := singleton a.

  Definition emptyVE {A}:= VecEnv.ve_empty (A:=A).
  
  Definition singleTEnv (k : tid) (v : Ty) : Env := [ k |-> v]ₜ.

  Definition singleMEnv (k : mid) (v : Mod) : Env := [ k |-> v]ₘ.

  Definition sig1 : MTy := MSigma (s_ 1) (NonParamMod ([a |-> Tv_Ty 1]ₜ)).
  
  Definition ftor : Mod := (Ftor Ø Øe sig1).
  
  Definition E0 := [Fn |-> ftor]ₘ.
  Definition ε := Bra_mexp Emp_mdec.

  Infix "@" := App_mexp (at level 80).
  Definition Fn_app : mexp := (Mid_longmid Fn) @ ε.
  Definition dec1 := Mod_mdec m1 Fn_app.
  Definition dec2 := Mod_mdec m2 Fn_app.
  Definition E1 :=  [m1 |-> (NonParamMod ([a |-> Tv_Ty 1]ₜ))]ₘ.
  Definition E2 :=  [m2 |-> (NonParamMod ([a |-> Tv_Ty 2]ₜ))]ₘ.
  Definition E2' := [m2 |-> (NonParamMod ([a |-> Tv_Ty 1]ₜ))]ₘ.

  Notation "'[_' E |- s ! '(' T ',' E1 ')' '_]'" :=
    (Mdec_melab E s (MSigma T (NonParamMod E1))) (at level 80).

  Infix ";;" := Seq_mdec (at level 40).

  Lemma enriches_empty : enriches emptyEnv emptyEnv.
  Proof.
  Admitted.

  Lemma look_plusEnvEnv_single k1 k2 v1 v2 :
    k1 <> k2 -> lookLongMid (Mid_longmid k1)
                            (plusEnvEnv ([k1 |-> v1]ₘ) ([k2 |-> v2]ₘ)) = Some v1.
  Proof.
  Admitted.

  Lemma action_singleton :
    forall r k v, (PermSemOb.action r ([k |-> v]ₘ)) =
                  singleMEnv k ((PermSemOb.action_mod r) v).
  Proof.
    intros.
    unfold singleMEnv.
  Admitted.

  Lemma action_mod_singleton :
    forall r k v,
      (PermSemOb.action_mod r (NonParamMod ([k |-> (NonParamMod ([a |-> v]ₜ))]ₘ))) =
      (NonParamMod ([k |-> (NonParamMod ([a |-> (PermTy.action r v)]ₜ))]ₘ)).
  Proof.
  Admitted.

  (* [dec1 ;; dec2] expands to [module m1 = Fn(ε) ;; module m2 = Fn(ε)] That is,
     it is a sequence of declarations with the bodies containing an
     application of the same functor [Fn] to the empty expression [ε]. *)
  Example ex1 : Fn <> m1 ->
                [_ E0 |- dec1 ;; dec2 ! ((s_ 1) :U: (s_ 2), plusEnvEnv E1 E2) _].
  Proof.
    intro Hneq.
    (* To be able to elaborate this sequence of declarations, we need to show
       that the variable 1 in E2 can be renamed to 2 giving alpha-equivalent term*)
    apply Seq_mdec_melab with (T2 := s_ 1) (E2:= E2').
    + constructor. apply App_mexp_melab with (E':=emptyEnv) (E:=emptyEnv).
      * compute. rewrite Key_compare_eq. f_equal.
      * constructor. constructor.
      * apply enriches_empty.
      * unfold FreshTSetEnv.fresh,Disjoint,not. intros. destruct H as [H1 H2]. inversion H2.
    + (* the transposition (1 2) witnesses that signatures are aplha-convertible *)
      apply ae_mty_c with (p:=NomN.swap 1 2).
      * intros. unfold E2' in *. inversion H.
      * unfold E2' in *. unfold E2. rewrite action_mod_singleton.
        constructor.
        constructor;auto.
        ** constructor. intros. rewrite VE.toOrdEnv_fromOrdEnv_inv in H,H0.
           compute in *. destruct (ID.compare mid m2);tryfalse.
           inversion H. inversion H0. constructor. constructor;auto.
           *** constructor. intros. simpl in *. inversion H4.
           *** constructor. intros. simpl in *. inversion H4.
        ** constructor. intros. inversion H.
      * compute. f_equal. apply proof_irrelevance.
    + constructor. apply App_mexp_melab with (E':=emptyEnv) (E:=emptyEnv).
      * unfold E0,E1,ftor,sig1. rewrite look_plusEnvEnv_single. reflexivity. apply Hneq.
      * constructor. constructor.
      * apply enriches_empty.
      * unfold FreshTSetEnv.fresh,Disjoint,not. intros. destruct H as [H1 H2]. inversion H2.
    + unfold FreshTSet.fresh,AtomN.V.Disjoint,not. intros;intuition.
      unfold NomN.PFin.supp in *.
      rewrite AtomN.V.OP.P.Dec.F.singleton_iff in *. tryfalse.
    + unfold E0.
      unfold FreshTSetEnv.fresh,AtomN.V.Disjoint,not. intros;intuition.
      unfold NomN.PFin.supp,PermSemOb.supp in *. compute in *.
      intros;intuition. inversion H1.
  Qed.
End FunctorAppTwice.
