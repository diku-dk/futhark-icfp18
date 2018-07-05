(* =========================================================== *)
(* Static interpretation relation and the proof of termination *)
(* (the normalisation part of the Proposition 6.1)             *)
(* =========================================================== *)

Require Import String.
Require Import Vector.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Wf Coq.Program.Program Coq.Program.Tactics.
Require Import ProofIrrelevance FunctionalExtensionality.

Require Import Basics.
Require Import Syntax.
Require Import SemObjects.
Require Import Target.
Require Import IntObjects.
Require Import ElabCore.
Require Import MiniElab.
Require Import CpdtTactics.
Require Import CompCore.
Require Import CustomTactics.

Require Import NomEnv.

Import PermIEnvLabel.

Open Scope IEnv_scope.

(* -------------------------------------------------------------------- *)
(* Static interpretation rules for modules expressions and declarations *)
(* -------------------------------------------------------------------- *)

(* Some issues related to bound variables are left for further development *)
Inductive Mexp_int : IEnv -> mexp -> TSet -> IMod -> c -> Prop :=
| Bra_mexp_int : forall IE mdec N IE' c,
    Mdec_int IE mdec N IE' c ->
    Mexp_int IE (Bra_mexp mdec) N (INonParamMod IE') c
| Mid_mexp_int : forall IE mid IM,
    lookMidIE mid IE = Some IM ->
    Mexp_int IE (Mid_mexp mid) emptyTSet IM Emp_c
| Prj_mexp_int : forall IE mexp mid N c IE' IM,
    Mexp_int IE mexp N (INonParamMod IE') c ->
    lookMidIE mid IE' = Some IM ->
    Mexp_int IE (Prj_mexp mexp mid) N IM c
| Funct_mexp_int : forall IE0 mid mty mexp E0 M E,
    erasure_IEnv IE0 E0 ->
    Mty_melab E0 mty (MSigma emptyTSet (NonParamMod E)) ->
    Mexp_melab (addEnvMid mid (NonParamMod E) E0) mexp emptyTSet M ->
    Mexp_int IE0 (Funct_mexp mid mty mexp)
             emptyTSet (IFtor IE0 emptyTSet E (MSigma emptyTSet M) mid mexp) Emp_c
| App_mexp_int : forall IE0 longmid mexp mexp' IE IE' IE'' IE''' N N' c c' E' E'' mid,
    lookLongIMid longmid IE = Some (IFtor IE0 emptyTSet E' (MSigma emptyTSet (NonParamMod E'')) mid mexp') ->
    Mexp_int IE mexp N (INonParamMod IE') c ->
    filtering_IEnv IE' E' IE'' ->
    Mexp_int (addIEnvMid mid (INonParamMod IE'') IE0) mexp' N' IE''' c' ->
    Mexp_int IE (App_mexp longmid mexp) (unionTSet N N') IE''' (Seq_c c c')
with Mdec_int : IEnv -> mdec -> TSet -> IEnv -> c -> Prop :=
| Dec_mdec_int : forall IE dec N IE' c,
    Dec_comp IE dec N IE' c ->
    Mdec_int IE (Dec_mdec dec) N IE' c
| Type_mdec_int : forall IE tid ty Ty E,
    erasure_IEnv IE E ->
    Ty_elab E ty Ty ->
    Mdec_int IE (Type_mdec tid ty) emptyTSet (addIEnvTid tid Ty emptyIEnv) Emp_c
| Mod_mdec_int : forall IE mid mexp N IM c,
    Mexp_int IE mexp N IM c ->
    Mdec_int IE (Mod_mdec mid mexp) N (addIEnvMid mid IM emptyIEnv) c
| ModTyp_mdec_int : forall E IE mtid mty S,
    Mty_melab E mty S ->
    erasure_IEnv IE E ->
    Mdec_int IE (ModTyp_mdec mtid mty) emptyTSet (addIEnvTmid mtid S emptyIEnv) Emp_c
| Open_mdec_int : forall IE mexp N IE' c,
    Mexp_int IE mexp N (INonParamMod IE') c ->
    Mdec_int IE (Open_mdec mexp) N IE' c
| Seq_mdec_int : forall IE mdec1 mdec2 N1 N2 IE1 IE2 c1 c2,
    Mdec_int IE mdec1 N1 IE1 c1 ->
    Mdec_int (plusIEnvIEnv IE IE1) mdec2 N2 IE2 c2 ->
    (* (N1 # N2)%S -> *)
    (* (N1 # .fvs E)%S -> *)
    Mdec_int IE (Seq_mdec mdec1 mdec2) (unionTSet N1 N2) (plusIEnvIEnv IE1 IE2) (Seq_c c1 c2)
| IEmp_mdec_int : forall IE,
    Mdec_int IE Emp_mdec emptyTSet emptyIEnv Emp_c.

Scheme int_mexp_mut :=
  Induction for Mexp_int Sort Prop
  with int_mdec_mut := Induction for Mdec_int Sort Prop.

Combined Scheme int_mut from int_mexp_mut, int_mdec_mut.

Hint Resolve erasure_IEnv_tid_extend erasure_IEnv_tid_extend erasure_IEnv_empty.

Import EnvMod.

(* ----------------------------------------------------------- *)
(* Consistency relation between elaboration environments and   *)
(* interpretation environments.                                *)
(* ----------------------------------------------------------- *)

Definition consistent_IVEnv (VE:VEnv) (IVE:IVEnv) : Prop :=
   forall k t, (forall l, look k IVE = Some (l,t) -> look k VE = Some t) /\
               (look k VE = Some t -> exists l, look k IVE = Some (l,t)).

Notation Vec := Vector.t.
Import VectorNotations.
Module VE := EnvMod.VecEnv.

Local Coercion _to {A} := SemObjects.EnvMod.VecEnv._to (A:=A).
Local Coercion _from {A} := SemObjects.EnvMod.VecEnv._from (A:=A).

(** Consistency logical relation is defined by mutual recursion on
    the structure of the elaboration environments (semantic objects) *)
Fixpoint consistent_IEnv (E:Env) (IE:IEnv) : Prop :=
  match E, IE with
    EnvCtr TE VE ME MTE, IEnvCtr TE' IVE IME MTE' =>
    TE = TE' /\ consistent_IVEnv VE IVE /\ consistent_IMEnv ME IME /\ MTE = MTE'
  end
with consistent_IMEnv (ME:MEnv) (IME:IMEnv) : Prop :=
  match ME, IME with
    MEnvCtr me, IMEnvCtr ime =>
    dom (SemObjects.VE._to me) = dom (SemObjects.VE._to ime) /\
    match me,ime with
      (* NOTE : instead of forcing two vectors to be of the same length we
         just return False in case if vectors are not aligned *)
      VecEnv.mkVecEnv _  nn (exist _ ks _) vs,
      VecEnv.mkVecEnv _  nn' (exist _ ks' _) vs' =>
      (* We would like to use [VecEnv.Foralls.Forall2_fix consistent_IMod nn nn' vs vs']
         here, but unfortunately, this doesn't work in this situation.
         Probably, Coq doesn't unfold [Forall2_fix] here to see, that the
         argument is decreasing. Though, sometimes Coq does that, see
         definition of [ntsize] in Section 2.8 of CPDT *)
      (fix con_step {n n'} (l : Vec Mod n) (ll : Vec IMod n') : Prop :=
         match l,ll with
         | [],[] => True
         | m :: tl, im :: tl'  =>
           con_step tl tl' /\  consistent_IMod m im
         | _,_ => False
         end) nn nn' vs vs'
    end
  end
with consistent_IMod (M:Mod) (IM:IMod) : Prop :=
  match M with
    NonParamMod E =>
    match IM with
      INonParamMod IE => consistent_IEnv E IE
    | IFtor _ _ _ _ _ _ => False
    end
  | Ftor T0 E (MSigma T M) =>
    exists IE0 mid mexp,
    IM = IFtor IE0 T0 E (MSigma T M) mid mexp
    /\ forall IE, consistent_IEnv E IE ->
                  exists N IM c,
                    (Mexp_int (addIEnvMid mid (INonParamMod IE) IE0) mexp N IM c
                     /\ consistent_IMod M IM)
  end.

Import VecEnv.Foralls.


(* ----------------------- *)
(* Facts about consistency *)
(* ----------------------- *)

Lemma consistent_look_mid': forall mid IME ME M,
    consistent_IMEnv ME IME ->
    (lookMid mid ME = Some M) ->
    exists IM, lookIMid mid IME = Some IM /\ consistent_IMod M IM.
Proof.
  intros until M. intros Hcim Hmid. destruct ME, IME. simpl in *.
  destruct v0. destruct v.
  destruct keys,keys0. simpl in *.
  unfold dom,En.elements,En.Raw.elements in Hcim. simpl in *.
  generalize dependent x.  generalize dependent vals.
  generalize dependent v_size. generalize dependent v_size0.
  induction vals0; intros; dependent destruction x0.
  - crush. tryfalse.
  - destruct vals; dependent destruction x.
    + simpl in *. destruct Hcim. tryfalse.
    + destruct Hcim as [Hdom Tl]. destruct Tl as [Heq Hcm].
      unfold look,En.find in *. simpl in *.
      inversion Hdom. subst.
      remember (Key.compare mid h2) as mid_comp.
      destruct mid_comp.
      * tryfalse.
      * inversion Hmid. subst.
        exists h1;crush.
      * inversion v0. dependent destruction H2.
        inversion v. dependent destruction H2.
        apply IHvals0 with (x0:=x0); auto.
Qed.

Lemma consistent_look_mid: forall IE E M mid,
    consistent_IEnv E IE ->
    (lookMidE mid E = Some M) ->
    exists IM, lookMidIE mid IE = Some IM /\ consistent_IMod M IM.
Proof.
  intros.
  destruct E,IE. simpl in *.
  destruct H as [Heq Tl]. destruct Tl as [Hciv Tl]. destruct Tl as [Hcm Hmeq]. subst.
  eapply consistent_look_mid'; eauto.
Qed.

Lemma consistent_look_longvid: forall IE E t longvid,
    consistent_IEnv E IE ->
    (lookLongVid longvid E = Some t) ->
    exists l, lookLongIVid longvid IE = Some (l,t).
Proof.
  intros.
  generalize dependent IE. generalize dependent E.
  induction longvid.
  - intros. unfold consistent_IEnv in H. destruct E. destruct IE.
    destruct H as [eq H]. destruct H as [H2 x].
    clear x. unfold consistent_IVEnv in H2. subst.
    rename t1 into s.
    rename t0 into t.
    assert (H2':=H2 s t). destruct H2'. clear H.
    crush.
  - intros. simpl in *.
    destruct E, IE. simpl in *.
    rename t1 into s.
    remember (lookMid s m) as opt_mod. destruct opt_mod as [mod | ];tryfalse.
    destruct mod; tryfalse.
    destruct H as [Heqt tl]. destruct tl as [Hciv tl]. destruct tl as [Hcim Heqm]. subst.
    symmetry in Heqopt_mod.
    assert (H' : exists IM, lookIMid s i0 = Some IM /\ consistent_IMod (NonParamMod e) IM).
    intros. eapply consistent_look_mid'; eauto.
    destruct H' as [IM Hc]. destruct Hc as [Hmid Hcmod]. rewrite Hmid. destruct IM;tryfalse.
    simpl in Hcmod.
    eapply IHlongvid;eauto.
Qed.


Lemma consistent_look_longmid: forall IE E M longmid,
    consistent_IEnv E IE ->
    (lookLongMid longmid E = Some M) ->
    exists IM, lookLongIMid longmid IE = Some IM /\ consistent_IMod M IM.
Proof.
  intros.
  generalize dependent E. generalize dependent IE.
  induction longmid.
  - intros.
    destruct E. destruct IE. simpl in *.
    destruct H as [Heqt H]. destruct H as [H2 x].
    destruct x as [Hcim Heqm].
    eapply consistent_look_mid';eauto.
  - intros. simpl in *.
    destruct E. destruct IE. simpl in *.
    destruct H as [Heqt H]. destruct H as [H2 x].
    destruct x as [Hcim Heqm]. subst.
    destruct (lookMid t0 m) eqn:Hlook; tryfalse. destruct m0;tryfalse.
    assert (H' : exists IM, lookIMid t0 i0 = Some IM /\ consistent_IMod (NonParamMod e) IM).
    eapply consistent_look_mid'; eauto.
    destruct H' as [IM Hc]. destruct Hc as [Hmid Hcmod]. rewrite Hmid. destruct IM;tryfalse.
    eapply IHlongmid;eauto.
Qed.

Lemma consistent_IEnv_extend: forall IE E t l s,
  consistent_IEnv E IE -> consistent_IEnv (addEnvVid s t E) (addIEnvVid s (l,t) IE).
Proof.
  intros.
  destruct E,IE. crush.
  destruct v,i; simpl in *. unfold consistent_IVEnv in *.
  intros. split.
  + intros l0 H0. unfold look in *.
    rewrite FM.P.F.add_o in H0.
    destruct (FM.P.F.eq_dec s k).
    * inversion H0. subst.
      apply add_lookup.
    * destruct (H k t1) as [Hl Hr].
      rewrite FM.P.F.add_neq_o;auto. eapply Hl;eauto.
  + rewrite FM.P.F.add_o.
    destruct (FM.P.F.eq_dec s k).
    * exists l. subst. rewrite add_lookup in *. inversion H0.
      subst. reflexivity.
    * intros H'. unfold look in *. destruct (H k t1) as [Hl Hr].
       rewrite FM.P.F.add_neq_o;auto.
Qed.

Lemma consistent_IEnv_tid_extend: forall IE E t s,
  consistent_IEnv E IE -> consistent_IEnv (addEnvTid s t E) (addIEnvTid s t IE).
Proof.
  intros.
  destruct E,IE. crush.
Qed.

Lemma consistent_IEnv_mtid_extend: forall IE E t s,
  consistent_IEnv E IE -> consistent_IEnv (addEnvMtid s t E) (addIEnvTmid s t IE).
Proof.
  intros.
  destruct E,IE. crush.
Qed.


Set Printing Coercions.

(* NOTE : We prevent functions back and forth between environment the representations
   from unfolding and try just to use the fact that it is an isomorphism *)
Arguments SemObjects.VE._from A oe : simpl never.
Arguments SemObjects.VE._to A ve : simpl never.
Arguments SemObjects.VE.fromOrdEnv A oe : simpl never.
Arguments SemObjects.VE.toOrdEnv A ve : simpl never.

Lemma consistent_IEnv_mid_extend: forall IE E M IM s,
    consistent_IEnv E IE -> consistent_IMod M IM ->
    consistent_IEnv (addEnvMid s M E) (addIEnvMid s IM IE).
Proof.
  intros.
  destruct E,IE. destruct m,i0. simpl in *.
  destruct H as [Ht Htl]. destruct Htl as [Hc Htl].
  destruct Htl as [Ht' Htl'].
  rewrite <- (Forall2_fix_fold_unfold consistent_IMod) in *.
  rewrite <- (ForallEnv2_fold_unfold consistent_IMod) in *.
  (* NOTE : here we use an alternative variant of Lemma ForallEnv2_fold_unfold,
     because pattern-matching gets reduced. *)
  erewrite <- (ForallEnv2_fold_unfold' consistent_IMod);eauto.
  rewrite SemObjects.VE.Foralls.ForallEnv2_fix_EnvRel_iff in *;auto.
  rewrite SemObjects.VE.Foralls.ForallEnv2_fix_EnvRel_iff';eauto; try reflexivity.
  intuition;auto.
  repeat (rewrite VecEnv.toOrdEnv_fromOrdEnv_inv).
  unfold EnvRel.
  intuition;subst;simpl in *.
  + inversion Ht'. destruct (H1 k) as [L R].
    rewrite FM.P.F.add_in_iff in *. intuition;auto.
  + inversion Ht'. destruct (H1 k) as [L R].
    rewrite FM.P.F.add_in_iff in *. intuition;auto.
  + inversion Ht'.
    rename s into k'.
    rewrite FM.P.F.add_o in *.
    destruct (FM.P.F.eq_dec k' k).
    * assert (M = v2) by congruence. assert (IM = v') by congruence. subst. assumption.
    * apply (H3 k);auto.
Qed.

Lemma consistent_IEnv_empty: consistent_IEnv emptyEnv emptyIEnv.
Proof.
  constructor. constructor. split.
  - unfold consistent_IVEnv; crush;tryfalse.
  - crush. unfold emptyMTEnv. f_equal. unfold SemObjects.VE.ve_empty. compute. f_equal.
    f_equal. apply proof_irrelevance.
Qed.

Lemma consistent_IVEnv_plus e e' ie ie' :
  consistent_IVEnv e ie -> consistent_IVEnv e' ie'
  -> consistent_IVEnv (e ++ e') (ie ++ ie').
Proof.
  intros H1 H2.
  unfold consistent_IVEnv in *.
  split.
  + intros l Ht0.
    rewrite <- FM.P.F.find_mapsto_iff in *.
    rewrite FM.P.update_mapsto_iff in *.
    destruct Ht0.
    * destruct (H2 k t0). rewrite FM.P.F.find_mapsto_iff in *. left. eauto.
    * right. destruct H. split.
      ** destruct (H1 k t0). rewrite FM.P.F.find_mapsto_iff in *. eauto.
      ** unfold not. intro He'. apply H0.
         inversion He' as [v Hv].
         assert (Hv' : En.MapsTo k v e') by auto.
         rewrite FM.P.F.find_mapsto_iff in Hv'.
         destruct (H2 k v) as [L R].
         assert (Hex := R Hv'). destruct Hex as [l' Hlv].
         apply En.find_2 in Hlv. apply MapsTo_In in Hlv. assumption.
  + intros Ht0.
    rewrite <- FM.P.F.find_mapsto_iff in *.
    rewrite FM.P.update_mapsto_iff in *.
    destruct Ht0.
    * rewrite FM.P.F.find_mapsto_iff in *.
      destruct (H2 k t0) as [L R]. destruct (R H) as [l Hlt0].
      exists l.
      rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.update_mapsto_iff in *.
      left. auto.
    * destruct H as [He Hne'].
      rewrite FM.P.F.find_mapsto_iff in *.
      destruct (H1 k t0) as [L R]. destruct (R He) as [l Hlt0].
      exists l.
      rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.update_mapsto_iff in *.
      right. split.
      ** assumption.
      ** unfold not. intro He'. apply Hne'.
         inversion He' as [v Hv].
         assert (Hv' : En.MapsTo k v ie') by auto.
         rewrite FM.P.F.find_mapsto_iff in Hv'.
         destruct v as [l' t'].
         destruct (H2 k t') as [L' R'].
         assert (Ht' := L' _ Hv').
         rewrite <- FM.P.F.find_mapsto_iff in Ht'. apply MapsTo_In in Ht'.
         assumption.
Qed.

Lemma consistent_IEnv_plus: forall IE1 E1 IE2 E2,
    consistent_IEnv E1 IE1 -> consistent_IEnv E2 IE2 ->
    consistent_IEnv (plusEnvEnv E1 E2) (plusIEnvIEnv IE1 IE2).
Proof.
  intros.
  destruct E1,IE1,E2,IE2. destruct m,m0,m2,m3,i0,m1,i2,m4. simpl in *.
  destruct H0 as [Ht Htl]. destruct Htl as [Hc Htl].
  destruct H as [Ht' Htl']. destruct Htl' as [Hc' Htl'].
  split. congruence.
  split. apply consistent_IVEnv_plus; auto.
  (* We are switching to the "extensional" representation to be able to
     use properties of environments in abstract way, without
     looking on the concrete representation *)
  rewrite <- (Forall2_fix_fold_unfold consistent_IMod) in *.
  rewrite <- (ForallEnv2_fold_unfold consistent_IMod) in *.
  rewrite ForallEnv2_fix_EnvRel_iff in *.
  repeat (rewrite VecEnv.toOrdEnv_fromOrdEnv_inv).
  (* ------------------------------------------------------ *)
  unfold EnvRel in *.
  intuition; subst.
  + inversion H0. inversion H2. subst. clear H0. clear H2.
    rewrite FM.P.update_in_iff in *.
    destruct H1.
    * left. rewrite <- H3. auto.
    * right. rewrite <- H. auto.
  + inversion H0. inversion H2. subst. clear H0. clear H2.
    rewrite FM.P.update_in_iff in *.
    destruct H1.
    * left. rewrite H3. auto.
    * right. rewrite H. auto.
  + inversion H0. inversion H2. subst. clear H0. clear H2.
    apply En.find_2 in H1. apply En.find_2 in H6.
    rewrite FM.P.update_mapsto_iff in *.
    destruct H1,H6.
    * apply (H5 k); apply En.find_1; assumption.
    * destruct H1. apply (H5 k).
      ** apply En.find_1. assumption.
      ** destruct (H k) as [L R].
         assert (H' := L (MapsTo_In H0)). exfalso. auto.
    * destruct H0. apply (H4 k).
      ** apply En.find_1. assumption.
      ** destruct (H k) as [L R].
         assert (H' := R (MapsTo_In H1)). exfalso. auto.
    * destruct H0,H1; apply (H4 k); auto.
  + inversion H0. inversion H2. subst. clear H0. clear H2. reflexivity.
Qed.

Lemma consistent_ienv_imod_lem : forall ie e,
    consistent_IEnv e ie -> consistent_IMod (NonParamMod e) (INonParamMod ie).
Proof.
  crush.
Qed.

Lemma consistent_imod_ienv_lem : forall ie e,
    consistent_IMod (NonParamMod e) (INonParamMod ie) -> consistent_IEnv e ie.
Proof.
  crush.
Qed.

Lemma consistent_imod_uniform : forall x E,
  consistent_IMod (NonParamMod E) x  -> exists IE, x = INonParamMod IE.
Proof.
  intros. destruct x; exists i; crush.
Qed.

Lemma consistent_imod_uniform_ftor : forall T IM E MS,
  consistent_IMod (Ftor T E MS) IM  -> exists IE T' E' MS' mid mexp, IM = IFtor IE T' E' MS' mid mexp.
Proof.
  intros. destruct IM.
  - destruct MS. simpl in *. do 4 destruct H. tryfalse.
  - destruct MS. simpl in *. do 4 destruct H. inversion H; subst. repeat eexists; eauto.
Qed.

Lemma EnvRel_unmatched_size {A B} (ve : VecEnv.VecEnv B) (P : A -> B -> Prop) :
  ve <> empty -> ~ EnvRel P empty ve.
Proof.
  intro Hneq.
  remember (_to ve) as E.
  destruct ve. destruct keys. simpl in *.
  unfold not. intro.
  destruct vals.
  * apply Hneq. f_equal. dependent destruction x. f_equal. apply proof_irrelevance.
  * unfold EnvRel in *. destruct H. dependent destruction x.
    destruct (H h) as [L R].
    assert (Hin : In B h E). subst. unfold In,En.In. simpl. unfold to_list.
    unfold En.Raw.PX.In. eexists. econstructor. eauto.
    assert (Hfail := R Hin). inversion Hfail as [a Hfail']. unfold empty in *. simpl in *.
    inversion Hfail'.
Qed.

Lemma Forall_look_nested_Forall2 {n A B} (vs : Vec A n) (vs' : Vec B n)
      (P : A -> B -> Prop) :
  Forall (fun v => Forall (P v) vs') vs ->
  Forall2 P vs vs'.
Proof.
  intro H.
    generalize dependent vs'.
    dependent induction vs.
    * dependent destruction vs'; constructor.
    * intros vs' H. dependent destruction vs'.
      constructor.
      ** inversion H. dependent destruction H2. inversion H3.
         *** subst. auto.
      ** apply IHvs. inversion H. dependent destruction H2.
         inversion H3. dependent destruction H2.
         eapply Forall_nested_cons. eauto.
Qed.

Lemma consistent_to_erasure : forall E IE,
    consistent_IEnv E IE -> erasure_IEnv IE E.
Proof.
  (* We do not introduce last hypothesis, otherwise
     application of the mutual induction principle fails *)
  intros E IE.
  (* It's important to keep E abstracted *)
  generalize dependent E.
  induction IE using IEnv_mut with
      (P0 := fun ime => forall me', consistent_IMEnv (MEnvCtr me') ime
                        -> erasure_IMEnv ime (MEnvCtr me'))
      (P1 := fun im => forall m, consistent_IMod m im ->
                 erasure_IMod im m); intro E.
  + crush. destruct E as [te ve me mte]. simpl in H. intuition. subst.
    destruct me. constructor; auto.
  + intro Hc.
    assert (Hc' := Hc). simpl in *.
    destruct Hc as [Hdom Hfix].
    assert (HH : EnvRel (fun (im : IMod) (m : Mod)  =>
                            consistent_IMod m im -> erasure_IMod im m)
           (_to t0) (_to E)).
    apply (Forall_EnvRel (eq_sym Hdom)).
    apply H.
    (*TODO: move rewrites below to a custom tactic *)
    rewrite <- (Forall2_fix_fold_unfold consistent_IMod) in Hc'.
    rewrite <- (ForallEnv2_fold_unfold consistent_IMod) in Hc'.
    rewrite ForallEnv2_fix_EnvRel_iff in Hc'.
    destruct t0. destruct E. destruct keys,keys0.
    constructor. simpl in *.
    destruct HH as [Hin He].
    split;auto.
    intros. apply He with (k:=k); auto.
    destruct Hc' as [Hin' Hcon]. apply Hcon with (k:=k); auto.
  + intros Hc. destruct E.
    * constructor. simpl in Hc. apply IHIE;auto.
    * simpl in *. destruct m. destruct Hc. destruct H. destruct H. destruct H. tryfalse.
  + intros Hc. destruct E.
    * tryfalse.
    * simpl in Hc. destruct m1.
      destruct Hc. destruct H. destruct H. destruct H.
      inversion H. subst. constructor.
Qed.

Lemma consistent_imod_uniform_ftor2 : forall T T' IM E M,
    consistent_IMod (Ftor T E (MSigma T' M)) IM ->
    exists IE mid mexp, IM = IFtor IE T E (MSigma T' M) mid mexp /\
                        forall IE',
                          consistent_IEnv E IE' ->
                          exists N IM' c, Mexp_int (addIEnvMid mid (INonParamMod IE') IE) mexp N IM' c /\
                                         consistent_IMod M IM'.
Proof.
  intros. simpl in *. do 4 destruct H. eauto.
Qed.

(** The filtering function satisfies the filtering relation, provided that
    environments are consistent *)
Lemma filt_IVEnv_fun_spec ive' ve' ve :
    consistent_IVEnv ve' ive' -> env_ext ve' ve ->
    filt_IVEnv ive' ve (filt_fun ive' ve).
Proof.
  intros Hc Hex.
  constructor.
  + unfold env_ext. intros e p H.
    apply En.find_1. apply En.find_2 in H. unfold filt_fun,restrict in H.
    apply FM.P.filter_iff in H; intuition.
  + constructor.
    * intros l H. apply En.find_1. apply En.find_2 in H. unfold filt_fun,restrict in H.
      apply FM.P.filter_iff in H; intuition.
      unfold consistent_IVEnv in Hc. unfold env_ext in *.
      destruct (Hc k t0) as [L R]. apply En.find_1 in H0.
      assert (HH := L l H0). apply En.find_2. apply En.mem_2 in H1.
      destruct H1 as [t1 Ht1]. apply En.find_1 in Ht1.
      assert (HH' := Hex _ _ Ht1).
      assert (t0 = t1) by congruence.
      subst. auto.
    * intro H.
      unfold consistent_IVEnv in Hc. unfold env_ext in *.
      destruct (Hc k t0) as [L R].
      assert (HH := R (Hex _ _ H)).
      destruct HH as [l Hl]. exists l.
      apply En.find_1. unfold filt_fun,restrict.
      rewrite FM.P.filter_iff;intuition. apply En.mem_1.
      apply En.find_2 in H. eapply MapsTo_In;eauto.
Qed.

Lemma env_ext_filt_fun_eq {A : Type} (e' e : AEnv A) :
  env_ext e' e -> filt_fun e' e = e.
Proof.
  intro H.
  unfold filt_fun,restrict. apply env_extensionality_alt.
  intros k v.
  split.
  + intros. apply En.find_2 in H0.
    rewrite FM.P.filter_iff in H0; intuition.
    apply En.mem_2 in H2.
    destruct H2 as [v1 Hv1]. apply En.find_1 in Hv1.
    assert (HH' := H _ _ Hv1).
    apply En.find_1 in H1. unfold look in *.
    assert (v = v1) by congruence;subst;auto.
  + intros Hl. apply En.find_1. rewrite FM.P.filter_iff; intuition.
    apply En.find_2 in Hl. apply En.mem_1. eapply MapsTo_In;eauto.
Qed.

Lemma filt_fun_env_ext {A B : Type} (e' : AEnv A) (e : AEnv B) :
  env_ext e' (filt_fun e' e).
Proof.
  unfold env_ext.
  intros k v Hv. unfold filt_fun,restrict in *. intros. apply En.find_2 in Hv.
  rewrite FM.P.filter_iff in Hv; intuition.
Qed.

Lemma filt_TEnv_fun_spec ite' te' :
  env_ext ite' te' ->
  filt_ITEnv ite' te' (filt_fun ite' te').
Proof.
  intros H.
  constructor.
  + unfold env_ext in *.
    intros k e Hl. apply En.find_1. apply En.find_2 in Hl. unfold filt_fun,restrict in Hl.
    apply FM.P.filter_iff in Hl; intuition.
  + apply env_ext_filt_fun_eq; auto.
Qed.

Definition restrict_map {A B} (f : A -> B -> A) (e : AEnv A) (e' : AEnv B) :=
  En.map2 (fun oe oe' =>
             match oe,oe' with
             | Some v, None => None
             | None, Some v => None
             | Some v, Some v' => Some (f v v')
             | None,None => None
             end)
          e e'.

(* Filtering relation, defined in more "algorithmic" style *)
Inductive flt_Env_rel : IEnv -> Env -> IEnv -> Prop :=
  flt_Env_r :
    forall TE' TE IVE VE IME' ME IME MTE,
      flt_IMEnv_rel IME' ME IME ->
      flt_Env_rel (IEnvCtr TE' IVE IME' MTE)
                  (EnvCtr TE VE ME  emptyMTEnv)
                  (IEnvCtr (filt_fun TE' TE) (filt_fun IVE VE) IME emptyMTEnv)
   with
   flt_IMEnv_rel : IMEnv -> MEnv -> IMEnv -> Prop :=
     flt_IMEnv_r : forall (ime' : VE.VecEnv IMod) (me : VE.VecEnv Mod) ime,
       RestrictionRel flt_IMod_rel (_to ime') (_to me) (_to ime) ->
       flt_IMEnv_rel (IMEnvCtr ime')
                     (MEnvCtr me)
                     (IMEnvCtr ime)
   with
   flt_IMod_rel :  IMod -> Mod -> IMod -> Prop :=
   | flt_IMod_nmp_r : forall ie' ie e,
       flt_Env_rel ie' e ie ->
       flt_IMod_rel (INonParamMod ie') (NonParamMod e) (INonParamMod ie)
   | flt_IMod_ftor_r : forall IE0 T E' E G G' mid mexp,
       E' = E ->
       G' = G ->
       (* enriches E' E -> *)
       (* enrichesModType G' G -> *)
       flt_IMod_rel (IFtor IE0 T E G' mid mexp) (Ftor T E' G) (IFtor IE0 T E' G mid mexp).

Scheme flt_mut :=
  Induction for flt_Env_rel Sort Prop
  with
    Induction for flt_IMEnv_rel Sort Prop
  with
    Induction for flt_IMod_rel Sort Prop.

Lemma flt_consistent ie' ie e' e :
  enriches e' e ->
  consistent_IEnv e' ie' ->
  flt_Env_rel ie' e ie ->
  consistent_IEnv e ie.
Proof.
  generalize dependent e. generalize dependent e'. generalize dependent ie.
  induction ie' using IEnv_mut
    with (P0 := fun ime' => forall me' me ime,
                    enrichesM me' me ->
                    consistent_IMEnv me' ime' ->
                    flt_IMEnv_rel ime' me ime ->
                    consistent_IMEnv me ime)
         (P1 := fun im' => forall m' m im,
                 enrichesMod m' m ->
                 consistent_IMod m' im' ->
                 flt_IMod_rel im' m im ->
                 consistent_IMod m im).
  + intros ie e' e Hen Hc.
    inversion Hen as [ve' ve te' te me' me mte' mte Hvext Htext Henm H2 H3]. subst.
    simpl in *. intuition. subst.
    rename t0 into te'. rename i into ive'. rename i0 into ime'.
    destruct ie.
    inversion_clear H.
    unfold consistent_IVEnv in H2.
    intuition.
    ** symmetry. apply env_ext_filt_fun_eq;auto.
    ** unfold consistent_IVEnv in *. intros.
       destruct (H2 k t1) as [Ht Hl].
         split.
         *** intros l Ht0. apply En.find_2 in Ht0.
             apply FM.P.filter_iff in Ht0. destruct Ht0.
             apply En.find_1 in H.
             assert (HH := Ht _ H). unfold env_ext in *.
             apply En.mem_2 in H3. destruct H3 as [t2 Ht2].
             apply En.find_1 in Ht2.
             assert (Ht1' := Hvext _ _ Ht2). assert (t1 = t2) by congruence. subst. auto.
             intuition.
         *** intros Ht0. assert (HH := Hl (Hvext _ _ Ht0)). destruct HH as [l Hl'].
             exists l. apply En.find_1. unfold filt_fun,restrict. rewrite FM.P.filter_iff.
             split. apply En.find_2. assumption. apply En.mem_1. eapply MapsTo_In;eauto.
             intuition.
    ** eapply IHie';eauto.
  + intros me0' me0 ime0 Hen Hc Hflt.
    inversion Hen as [me' me Hdom He Heq0 Heq1]. subst.
    rename t0 into ime'. simpl in *.
    rewrite <- (Forall2_fix_fold_unfold consistent_IMod) in *.
    rewrite <- (ForallEnv2_fold_unfold consistent_IMod) in *.
    rewrite ForallEnv2_fix_EnvRel_iff in *.
    inversion_clear Hc as [Hd Hcim].
    destruct ime0. inversion_clear Hflt as [? ? ? Hr].
    split.
    ** rewrite dom_extensionality in Hd. unfold _to in Hdom.
       eapply RestrictionRel_dom_eq; eauto.
       eapply domain_eq_r;eauto.
    ** rewrite <- (ForallEnv2_fold_unfold consistent_IMod).
       rename v into ime.
       assert (Hfa : dom (_to me) = dom ime /\
                     ForallEnv2_fix consistent_IMod me ime).
       rewrite ForallEnv2_fix_EnvRel_iff.
       unfold EnvRel.
       split.
       *** intros k'. apply dom_extensionality.
           rewrite dom_extensionality in Hd. unfold _to in Hdom.
           eapply RestrictionRel_dom_eq; eauto.
           eapply domain_eq_r;eauto.
       *** intros k v v' Hv Hv'.
           assert (HH : exists v v'',
                      look k ime' = Some v'' /\ look k me = Some v /\ flt_IMod_rel v'' v v') by
               (apply (RestrictionRel_spec Hr Hv');auto).
           destruct HH as [v0 Htmp]. destruct Htmp as [v'' Htmp].
           destruct Htmp as [Hv'' Htmp]. destruct Htmp as [Hv0 Hflt].
           unfold _to in *.
           assert (v = v0) by congruence. subst.
           assert (Hin_me := MapsTo_In (En.find_2 Hv)).
           assert (Hin_me' := Hdom _ Hin_me).
           inversion Hin_me' as [m' Hm']. apply En.find_1 in Hm'.
           assert (H' := Forall_forall_vals H). simpl in *.
           eapply H';eauto.
       *** destruct Hfa. auto.
  + intros. destruct m;destruct m';  destruct im; inversion H1; inversion H; subst.
    simpl in *. eapply IHie'; eauto.
  + intros m' m'' im Hen Hc Hflt.
    destruct m';destruct m''; inversion_clear Hen; inversion Hflt; subst;tryfalse.
    simpl in *.  destruct m2. destruct Hc.
    do 3 destruct H. inversion_clear H.
    exists x,x0,x1.
    split;auto.
Qed.

Lemma flt_exists ie' e' e :
  enriches e' e ->
  consistent_IEnv e' ie' ->
  exists ie, flt_Env_rel ie' e ie.
Proof.
  generalize dependent e. generalize dependent e'.
  induction ie' using IEnv_mut
    with (P0 := fun ime' => forall me' me,
                    enrichesM me' me ->
                    consistent_IMEnv me' ime' ->
                    exists ime, flt_IMEnv_rel ime' me ime)
         (P1 := fun im' => forall m' m,
                 enrichesMod m' m ->
                 consistent_IMod m' im' ->
                 exists im, flt_IMod_rel im' m im).
  + intros e' e Hen Hc.
    inversion Hen as [ve' ve te' te me' me mte' mte Hvext Htext Henm H2 H3]. subst.
    simpl in *. intuition. subst.
    rename t0 into te'. rename i into ive'. rename i0 into ime'.
    destruct (IHie' _ _ Henm H0) as [ime Hime].
    exists (IEnvCtr (filt_fun te' te) (filt_fun ive' ve) ime emptyMTEnv).
    constructor;auto.
  + intros me0' me0 Hen Hc.
    inversion Hen as [me' me Hdom He Heq0 Heq1]. subst.
    rename t0 into ime'. simpl in *.
    rewrite <- (Forall2_fix_fold_unfold consistent_IMod) in *.
    rewrite <- (ForallEnv2_fold_unfold consistent_IMod) in *.
    rewrite ForallEnv2_fix_EnvRel_iff in *.
    inversion Hc as [Hd Hcim].

    assert (Hex : exists ime, RestrictionRel flt_IMod_rel (_to ime') (_to me) ime).
    assert (H' := Forall_forall_vals H). simpl in *.
    apply RestrictionRel_exists. intros v k Hv v' Hv'.
    assert (Hin_me := MapsTo_In (En.find_2 Hv)).
    assert (Hin_me' := Hdom _ Hin_me).
    inversion Hin_me' as [m' Hm']. apply En.find_1 in Hm'.
    eapply (H' k _ Hv' m');eauto.

    destruct Hex as [ime Hime]. exists (IMEnvCtr (_from ime)).
    constructor. rewrite VE.toOrdEnv_fromOrdEnv_inv. assumption.
  + intros. destruct m;destruct m'; inversion H; subst.
    * simpl in *. destruct (IHie' _ e H3 H0) as [ie Hie].
      exists (INonParamMod ie). constructor. assumption.
    * simpl in *. destruct m. do 4 destruct H0.
      inversion H0.
  + intros m' m'' Hen Hc.
    destruct m';destruct m''; inversion Hen; tryfalse. subst.
    simpl in *. destruct m2. destruct Hc.
    inversion Hen. subst.
    do 3 destruct H. inversion_clear H.
    exists (IFtor x t2 e1 (MSigma t1 m1) x0 x1).
    apply flt_IMod_ftor_r;auto.
Qed.

(* NOTE : That's how the function, implementing filtering could look like. *)
(* Of course, this implementation doesn't work, because Coq's restriction on fixpoint. *)
(* [Program] tactic doesn't help here, because measure cannot be used with the mutual definitions *)

(* Program Fixpoint flt_Env_fun (ie : IEnv) (e : Env) {measure env_measure}: IEnv := *)
(*   match ie,e with *)
(*     IEnvCtr TE' IVE IME MTE', EnvCtr TE VE ME MTE => *)
(*     IEnvCtr (filt_fun TE' TE) (filt_fun IVE VE) (flt_IMEnv_fun IME ME) MTE *)
(*   end *)
(* with *)
(* flt_IMEnv_fun (ime' : IMEnv) (me : MEnv) := *)
(*   match ime', me with *)
(*   | IMEnvCtr ve', MEnvCtr ve => *)
(*     IMEnvCtr (restrict_map flt_IMod_fun (_to ve') (_to ve)) *)
(*   end *)
(* with *)
(* flt_IMod_fun (im' : IMod) (m : Mod) : IMod := *)
(*   match im',m with *)
(*   | INonParamMod ie, NonParamMod e => INonParamMod (flt_Env_fun ie e) *)
(*   | IFtor IE0 T E G mid mexp, Ftor T' E' G' => IFtor IE0 T E G mid mexp *)
(*   | IFtor IE0 T E G mid mexp, NonParamMod e => im' *)
(*   | INonParamMod ie, Ftor T' E' G' => im' *)
(*   end. *)


Definition filt_IMEnv_fun (ime' : IMEnv) (me : MEnv) :=
  match ime', me with
  | IMEnvCtr ve', MEnvCtr ve => IMEnvCtr (restrict (_to ve') (_to ve))
  end.

Definition filt_IEnv (ie : IEnv) (e : Env) :=
  match ie,e with
    IEnvCtr TE' IVE IME MTE', EnvCtr TE VE ME MTE =>
    IEnvCtr (filt_fun TE' TE) (filt_fun IVE VE) (filt_IMEnv_fun IME ME) (MTE')
  end.

Lemma flt_Env_rel_to_filtering_IEnv ie' e' e ie :
  enriches e' e ->
  consistent_IEnv e' ie' ->
  flt_Env_rel ie' e ie -> filtering_IEnv ie' e ie.
Proof.
 revert ie. revert e. revert e'.
 induction ie' using IEnv_mut with
      (P0 := fun ime' => forall me ime me',
               enrichesM me' me ->
               consistent_IMEnv me' ime' ->
               flt_IMEnv_rel ime' me ime ->
               filtering_IMEnv ime' me ime)
      (P1 := fun im' => forall m im m',
               enrichesMod m' m ->
               consistent_IMod m' im' ->
               flt_IMod_rel im' m im ->
               filtering_IMod im' m im).
 + intros e' e ie He Hc Hflt. destruct e',ie,e; simpl in *; inversion He; intuition; subst.
   inversion_clear Hflt.
   constructor.
   * eapply filt_IVEnv_fun_spec;eauto.
   * eapply filt_TEnv_fun_spec;eauto.
   * eapply IHie';eauto.
 + intros me ime me' He Hc Hflt.
   destruct me',ime,me; inversion He; simpl in *. intuition; subst.
   inversion Hflt. subst.
   constructor.
   * eapply RestrictionRel_dom_subset;eauto.
   * symmetry. eapply RestrictionRel_dom_eq;eauto. eapply domain_eq_r; eauto.
   * intros k im' m im Him' Hm Him.
     rename t0 into ime'. rename v1 into me. rename v0 into ime. rename v into me'.
     assert (HH : exists m0 im0',
                look k ime' = Some im0' /\ look k me = Some m0 /\ flt_IMod_rel im0' m0 im) by
         (apply (RestrictionRel_spec H7 Him);auto).
     destruct HH as [v0 Htmp]. destruct Htmp as [v'' Htmp].
     destruct Htmp as [Hv'' Htmp]. destruct Htmp as [Hv0 Hflt'].
     unfold _to in *.
     assert (v'' = im') by congruence.
     assert (v0 = m) by congruence. subst.
     eapply Forall_forall_vals in H;eauto.
     assert (Hem' : exists m', look k me' = Some m') by
         (apply En.find_2 in Hm; apply MapsTo_In in Hm; destruct (H2 _ Hm) as [m' Hm'];
          apply En.find_1 in Hm'; eexists;eauto).
     destruct Hem' as [m' Hm'].
     eapply H;eauto.
     rewrite <- (Forall2_fix_fold_unfold consistent_IMod) in *.
     rewrite <- (ForallEnv2_fold_unfold consistent_IMod) in *.
     assert (Hfa : EnvRel consistent_IMod me' ime') by
         (rewrite <- ForallEnv2_fix_EnvRel_iff; intuition).
     inversion Hfa as [Hdom Hcm]. eauto.
 + intros m im m' He Hc Hflt.
   destruct m,im,m'; inversion_clear Hflt; inversion_clear He.
   constructor. eauto.
 + rename m into t.
   intros m im m' He Hc Hflt.
   destruct m,im,m'; inversion_clear Hflt; inversion_clear He.
   constructor; eauto.
Qed.

Lemma consistent_enrich_to_filtering: forall E IE' E',
    enriches E' E ->
    consistent_IEnv E' IE' ->
    exists IE, filtering_IEnv IE' E IE /\ consistent_IEnv E IE.
Proof.
  intros e ie' e' He Hc.
  assert (Hie_ex : exists ie, flt_Env_rel ie' e ie) by (eapply flt_exists;eauto).
  destruct Hie_ex as [ie Hie].
  exists ie. split.
  + eapply flt_Env_rel_to_filtering_IEnv;eauto.
  + eapply flt_consistent;eauto.
Qed.


(* -------------------------------------- *)
(* Main proposition (see Proposition 6.1) *)
(* -------------------------------------- *)

Hint Resolve consistent_IEnv_extend consistent_IEnv_empty.

Lemma comp_consistent_dec: forall dec E E' IE,
    Dec_elab E dec E' -> consistent_IEnv E IE ->
    exists N IE' c, Dec_comp IE dec N IE' c  /\ consistent_IEnv E' IE'.
Proof.
  crush.
  pose (AtomN.Atom_inf (PermIEnvLabel.supp IE)) as fresh_l.
  destruct fresh_l as [l Hfresh].
  exists (addTSet l emptyTSet).

  inversion H. subst.
  apply consistent_to_erasure in H0.
  apply comp_exp with (IE := IE) in H1.
  - destruct H1. remember (Val_c l x) as c.
    exists (addIEnvVid v (l,t0) emptyIEnv). exists c.
    split.
    + remember (Val_dec v e) as dec.
      rename v into vid. rename x into ex. rename e into exp. subst dec c.
      clear H H0 E. constructor;auto.
    + apply consistent_IEnv_extend. apply consistent_IEnv_empty.
  - crush.
Qed.

Lemma interp :
  (forall E mexp T M,
      Mexp_melab E mexp T M -> forall IE,
      consistent_IEnv E IE ->
      exists N IM c, Mexp_int IE mexp N IM c /\ consistent_IMod M IM) /\
  (forall E mdec T E',
      Mdec_melab E mdec T E' -> forall IE,
      consistent_IEnv E IE ->
      exists N IE' c, Mdec_int IE mdec N IE' c /\ consistent_IEnv E' IE').
Proof.
  apply melab_mut; intros; tryfalse.
  - assert (H1 := H IE H0). crush. exists x. exists (INonParamMod x0). exists x1. split.
    + constructor; eauto.
    + auto.
  - exists emptyTSet. apply consistent_look_mid with (M:=M) (mid:=mid) in H; auto.
    destruct H. destruct H. exists x. exists Emp_c. split.
    + constructor. eauto.
    + assumption.
  - assert (H1:=H IE H0). clear H. destruct H1 as [N H1]. destruct H1. destruct H. destruct H.
    exists N. rename x0 into c. assert (H2:=H1). apply consistent_imod_uniform in H1. destruct H1. subst.
    apply consistent_imod_ienv_lem in H2.
    apply consistent_look_mid with (M:=M) (mid:=mid) in H2;auto.
    destruct H2. destruct H1. exists x. exists c. split.
    + clear E m e H0 E' H2 M. rename x into IM.
      rename x0 into IE'. apply Prj_mexp_int with (IE':=IE'); auto.
    + auto.
  - exists emptyTSet. exists (IFtor IE emptyTSet E (MSigma emptyTSet E') mid mexp). exists Emp_c.
    split.
    + apply consistent_to_erasure in H0. clear H. apply Funct_mexp_int with (E0:=E0); auto.
    + crush. exists IE. exists mid. exists mexp. split.
      * reflexivity.
      * intros IE' H1.
        apply consistent_IEnv_mid_extend
          with (M:=NonParamMod E) (IM:=INonParamMod IE') (s:=mid) (IE:=IE) (E:=E0)
                in H1.
        rename H into IH.
        apply IH;auto. auto.
  - remember (Ftor emptyTSet E' (MSigma emptyTSet (NonParamMod E''))) as M.
    assert (H1:=H0).
    apply consistent_look_longmid with (M:=M) (longmid:=longmid) in H0;auto.
    destruct H0 as [IM H0]. destruct H0.
    assert (H':=H IE H1).
    destruct H' as [N1 H']. destruct H' as [IM1 H']. destruct H' as [c1 H'].
    + subst M. assert (H3:=H2). apply consistent_imod_uniform_ftor2 in H2.
      destruct H2 as [IE1 H2]. destruct H2 as [mid H2]. destruct H2 as [mexp1 H2]. destruct H2.
      destruct H'. assert (H6':=H6). apply consistent_imod_uniform in H6.
      destruct H6 as [IE' HeqIE']. subst.
      apply consistent_imod_ienv_lem in H6'.
      apply consistent_enrich_to_filtering with (IE':=IE') in e0; auto.
      destruct e0 as [IE'' H2]. destruct H2 as [Hflt H6].
      assert (H4' := H4 IE'' H6).
      destruct H4' as [N2 H4']. destruct H4' as [IM2 H4']. destruct H4' as [c2 H4']. destruct H4'.
      exists (unionTSet N1 N2). exists IM2. exists (Seq_c c1 c2). split.
      * apply App_mexp_int with (IE0:=IE1) (mexp' := mexp1) (IE' := IE')
                                (IE'' := IE'') (E'' := E'') (E':=E') (mid:=mid); auto.
      * auto.
  - assert (H1:=H). apply consistent_to_erasure in H. apply comp_consistent_dec with (IE:=IE) in d; auto.
    + destruct d as [N H0]. destruct H0 as [IE' H0]. destruct H0 as [c H0].
      destruct H0 as [L R]. exists N. exists IE'. exists c. split.
      * constructor. auto.
      * auto.
  - exists emptyTSet. exists (addIEnvTid tid Ty emptyIEnv). exists Emp_c. split.
    + econstructor; eauto. apply consistent_to_erasure. auto.
    + apply consistent_IEnv_tid_extend. apply consistent_IEnv_empty.
  - assert (H':=H IE H0). destruct H' as [N H']. destruct H' as [IM H']. destruct H' as [c H']. destruct H' as [L R].
    exists N. exists (addIEnvMid mid IM emptyIEnv). exists c. split.
    + constructor; auto.
    + apply consistent_IEnv_mid_extend; auto.
  - exists emptyTSet, (addIEnvTmid mtid S emptyIEnv), Emp_c.
    split.
    + assert (He : erasure_IEnv IE E ) by (apply consistent_to_erasure;auto).
      apply ModTyp_mdec_int with (E:=E);auto.
    + apply consistent_IEnv_mtid_extend. apply consistent_IEnv_empty.
  - assert (H':=H IE H0). destruct H' as [N H']. destruct H' as [IM H']. destruct H' as [c H']. destruct H' as [L R].
    exists N.
    assert (R2:=R). apply consistent_imod_uniform in R. destruct R. subst.
    exists x. exists c. split.
    + constructor; auto.
    + apply consistent_imod_ienv_lem; auto.
  - assert (H':=H IE H1). destruct H' as [N1 H']. destruct H' as [IE1 H']. destruct H' as [c1 H'].
    destruct H' as [INT1 ERA1]. apply consistent_IEnv_plus with (IE2:=IE1) (E2:=E1) in H1; auto.
    assert (H0':=H0 (plusIEnvIEnv IE IE1) H1).
    destruct H0' as [N2 H0']. destruct H0' as [IE2 H0']. destruct H0' as [c2 H0'].
    destruct H0' as [INT2 ERA2].
    exists (unionTSet N1 N2). exists (plusIEnvIEnv IE1 IE2). exists (Seq_c c1 c2). split.
    + constructor; auto.
    + apply consistent_IEnv_plus; auto.
  - exists emptyTSet. exists emptyIEnv. exists Emp_c. split.
    + constructor; auto.
    + auto.
Qed.
