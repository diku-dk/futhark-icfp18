(* ========================== *)
(* Elaboration rules          *)
(* ========================== *)

Require Import Basics.
Require Import Syntax.
Require Import SemObjects.
Require Import CpdtTactics.
Require Import ElabCore.
Require Import NomEnv.

Module FreshTSetEnv := NomN.Fresh NomN.PFin PermSemOb.
Module FreshTSet := NomN.Fresh NomN.PFin NomN.PFin.


Infix ":U:" := TSetMod.union (at level 40).
Infix "#" := FreshTSetEnv.fresh (at level 40) : env_scope.
Infix "#" := FreshTSet.fresh (at level 40) : set_scope.

Delimit Scope env_scope with E.
Delimit Scope set_scope with S.


(* ------------------------------------------------------ *)
(* Elaboration rules for modules types and specifications *)
(* ------------------------------------------------------ *)

(* Currently, we ignore the issues with variables bound in module types
   and functors and assume these sets of bound variables to be empty *)

Inductive Mty_melab : Env -> mty -> MTy -> Prop :=
| Bra_mty_melab : forall E spec S,
    Spec_melab E spec S -> Mty_melab E (Bra_mty spec) S
| Mtid_mty_melab : forall E mtid S,
    lookLongMtid mtid E = Some S -> Mty_melab E (Mtid_mty mtid) S
| Arr_mty_melab : forall E mty1 mty2 E' M,
    Mty_melab E mty1 (MSigma emptyTSet (NonParamMod E')) -> Mty_melab E mty2 (MSigma emptyTSet M) ->
    Mty_melab E (Arr_mty None mty1 mty2) (MSigma emptyTSet (Ftor emptyTSet E' (MSigma emptyTSet M)))
with Spec_melab : Env -> spec -> MTy -> Prop :=
| Type_spec_none_elab : forall (E:Env) (id:tid) (t:Tv),
    Spec_melab E (Type_spec id None) (MSigma (addTSet t emptyTSet) (NonParamMod (addEnvTid id (Tv_Ty t) emptyEnv)))
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
| Seq_spec_elab : forall E s1 s2 E1 E2 T1 T2,
    Spec_melab E s1 (MSigma T1 (NonParamMod E1)) ->
    Spec_melab (plusEnvEnv E E1) s2 (MSigma T2 (NonParamMod E2)) ->
    (T1 # T2)%S ->
    (T1 # PermSemOb.fvs E)%S ->
    Spec_melab E (Seq_spec s1 s2) (MSigma (T1 :U: T2) (NonParamMod (plusEnvEnv E1 E2)))
| Emp_spec_melab : forall E,
    Spec_melab E Emp_spec (MSigma emptyTSet (NonParamMod emptyEnv)).

Module Examples.
(* ---------------------------------------------*)
(* {} |- type t type s : ({t1,t2}){t->t1,s->t2} *)
(* ---------------------------------------------*)

  Import SemObjects.EnvMod.
  Import TSetMod.

  
  Parameter s : ID.t.
  Parameter t : ID.t.

  Definition ex1 : spec := Seq_spec (Type_spec t None) (Type_spec s None).

  Lemma singleton_add a : singleton a = add a empty.
  Proof.
    apply set_extensionality; intros; split; intros; auto with set.
  Qed.

  Lemma singleton_neq_disj a b : a <> b -> Disjoint (singleton a) (singleton b).
  Proof.
    rewrite TSetMod.Disjoint_spec. intros. unfold not.
    intros H1.
    destruct H1.
      assert (k=a). rewrite TSetMod.OP.P.Dec.F.singleton_iff in *.
      auto with set.
      assert (k=b).  unfold NomN.PFin.supp in *. rewrite TSetMod.OP.P.Dec.F.singleton_iff in *.
      auto with set. congruence.
  Qed.
  
  Lemma empty_disj X : Disjoint X empty.
  Proof.
    rewrite TSetMod.Disjoint_spec. intros. unfold not.
    intros. destruct H as [H1 H2]. cbv in H2. inversion H2.
  Qed.

  Lemma ex1elab: Spec_melab emptyEnv ex1
                          (MSigma ((singleton 2) :U: (singleton 1))
                                  (NonParamMod (addEnvTid s (Tv_Ty 1)
                                                          (addEnvTid t (Tv_Ty 2) emptyEnv)))).
  Proof.
    unfold ex1.
    rewrite map1.
    repeat rewrite singleton_add.
    repeat econstructor.
    - repeat rewrite <- singleton_add.
      apply singleton_neq_disj. auto.
    - rewrite <- singleton_add.
      apply empty_disj.
  Qed.

  (* --------------------------------------------*)
  (* {} |- type t type s=t : ({t1}){t->t1,s->t1} *)
  (* --------------------------------------------*)
  Definition ex2 : spec :=
    Seq_spec (Type_spec t None) (Type_spec s (Some (Longtid_ty (Tid_longtid t)))).

  Lemma ex2elab: Spec_melab emptyEnv ex2
                          (MSigma (addTSet 1 emptyTSet)
                                  (NonParamMod (addEnvTid s (Tv_Ty 1)
                                                          (addEnvTid t (Tv_Ty 1) emptyEnv)))).

  Proof.
    unfold ex2. rewrite set1. rewrite map1.
    repeat constructor; try (rewrite <- singleton_add; apply empty_disj). simpl.
    apply EnvMod.add_lookup.
  Qed.

End Examples.


Section Examples1.

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

Inductive Mexp_melab : Env -> mexp -> TSet -> Mod -> Prop :=
  | Bra_mexp_melab : forall E mdec E',
      Mdec_melab E mdec emptyTSet E'  ->
      Mexp_melab E (Bra_mexp mdec) emptyTSet (NonParamMod E')
  | Mid_mexp_melab : forall E mid M,
      lookMidE mid E = Some M ->
      Mexp_melab E (Mid_mexp mid) emptyTSet M
  | Prj_mexp_melab : forall E mexp mid E' M,
      Mexp_melab E mexp emptyTSet (NonParamMod E') ->
      lookMidE mid E' = Some M ->
      Mexp_melab E (Prj_mexp mexp mid) emptyTSet M
  | Funct_mexp_melab : forall E0 mid mty mexp E E',
      Mty_melab E0 mty (MSigma emptyTSet (NonParamMod E)) ->
      Mexp_melab (addEnvMid mid (NonParamMod E) E0) mexp emptyTSet E' ->
      Mexp_melab E0 (Funct_mexp mid mty mexp)
                 emptyTSet (Ftor emptyTSet E (MSigma emptyTSet E'))
  | App_mexp_melab : forall E0 longmid mexp E E' E'',
      lookLongMid longmid E0 = Some (Ftor emptyTSet E' (MSigma emptyTSet (NonParamMod E''))) ->
      Mexp_melab E0 mexp emptyTSet (NonParamMod E) ->
      enriches E E' ->
      Mexp_melab E0 (App_mexp longmid mexp) emptyTSet (NonParamMod E'')
  with Mdec_melab : Env -> mdec -> TSet -> Env -> Prop :=
  | Dec_mdec_melab : forall E dec E',
      Dec_elab E dec E' ->
      Mdec_melab E (Dec_mdec dec) emptyTSet E'
  | Type_mdec_melab : forall E tid ty Ty,
      Ty_elab E ty Ty ->
      Mdec_melab E (Type_mdec tid ty) emptyTSet (addEnvTid tid Ty emptyEnv)
  | Mod_mdec_melab : forall E0 mid mexp M,
      Mexp_melab E0 mexp emptyTSet M ->
      Mdec_melab E0 (Mod_mdec mid mexp) emptyTSet (addEnvMid mid M emptyEnv)
  | ModTyp_mdec_melab : forall E mtid mty S,
      Mty_melab E mty S ->
      Mdec_melab E (ModTyp_mdec mtid mty) emptyTSet (addEnvMtid mtid S emptyEnv)
  | Open_mdec_melab : forall E0 mexp E,
      Mexp_melab E0 mexp emptyTSet (NonParamMod E) ->
      Mdec_melab E0 (Open_mdec mexp) emptyTSet E
  | Seq_mdec_melab : forall E mdec1 mdec2 E1 E2 T1 T2,
      Mdec_melab E mdec1 T1 E1 ->
      Mdec_melab (plusEnvEnv E E1) mdec2 T2 E2 ->
      (T1 # T2)%S ->
      (T1 # PermSemOb.fvs E)%S ->
      Mdec_melab E (Seq_mdec mdec1 mdec2) (T1 :U: T2) (plusEnvEnv E1 E2)
  | Emp_mdec_melab : forall E,
      Mdec_melab E Emp_mdec emptyTSet emptyEnv.

Scheme melab_mexp_mut :=
    Induction for Mexp_melab Sort Prop
  with melab_mdec_mut := Induction for Mdec_melab Sort Prop.

Combined Scheme melab_mut from melab_mexp_mut, melab_mdec_mut.

Section Examples2.

  Parameter two : tid.
  Parameter X : tid.
  Parameter a : vid.
  Parameter b : vid.

  (* p1 = module X = { val a = two } val b = X.a *)

  Definition p1 : mdec :=
    Mod_mdec X (Bra_mexp (Dec_mdec (Val_dec a (Longvid_exp (Vid_longvid two))))).

  Definition p2 : mdec :=
    Dec_mdec (Val_dec b (Longvid_exp (Long_longvid X (Vid_longvid a)))).

  Definition p : mdec := Seq_mdec p1 p2.

  Definition E1 : Env :=
    plusEnvEnv E0 (addEnvVid two (Tv_Ty 1) emptyEnv).

  Definition E : Env := addEnvVid a (Tv_Ty 1) emptyEnv.

  Definition E' : Env :=
    addEnvVid b (Tv_Ty 1)
              (addEnvMid X (NonParamMod E) emptyEnv).

End Examples2.
