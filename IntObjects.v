(* ====================== *)
(* Interpretation Objects *)
(* ====================== *)

Require Import String FSets FMaps Coq.Program.Equality.
Require Import Basics CustomTactics CpdtTactics.
Require Vector.
Require Import SemObjects.
Require Import Target.
Require Import Syntax.
Require Import EnvExt.

Import Vector.
Import VectorNotations.
Notation Vec := Vector.t.

Definition NSet := TSetMod.t.
Definition emptyNSet := TSetMod.empty.
Definition addNSet (t:Tv) (T:TSet) : TSet := TSetMod.add t T.
Definition unionNSet (T1 T2: TSet) : TSet := TSetMod.union T1 T2.

Import EnvMod.

Import SemObjects.EnvMod.VecEnv.

Definition IVEnv := EnvMod.t (label*Ty).

Inductive IEnv :=
| IEnvCtr : TEnv -> IVEnv -> IMEnv -> MTEnv -> IEnv
with IMEnv :=
| IMEnvCtr : (VecEnv.VecEnv IMod) -> IMEnv
with IMod :=
| INonParamMod : IEnv -> IMod
| IFtor : IEnv -> TSet -> Env -> MTy -> mid -> mexp -> IMod.

Import VecEnv.Foralls.

Lemma O_Sn_eq_false {n} : 0 = S n -> False.
Proof.
  intro H. inversion H.
Qed.

Definition IEnv_mut (P : IEnv -> Prop) (P0 : IMEnv -> Prop) (P1 : IMod -> Prop)
           (f : forall (t : TEnv) (i : IVEnv) (i0 : IMEnv),
                  P0 i0 -> forall m : MTEnv, P (IEnvCtr t i i0 m))
           (f0 : forall t :  VecEnv.VecEnv IMod,
                  Forall P1 (VecEnv.vals _ t) -> P0 (IMEnvCtr t))
           (f1 : forall i : IEnv, P i -> P1 (INonParamMod i))
           (f2 : forall i : IEnv,
               P i -> forall (t : TSet) (e : Env) (m : MTy) (s : mtid) (m0 : mexp),
                 P1 (IFtor i t e m s m0)) :=
fix F (i : IEnv) : P i :=
  match i as i0 return (P i0) with
  | IEnvCtr t i0 i1 m => f t i0 i1 (F0 i1) m
  end
with F0 (i : IMEnv) : P0 i :=
  match i as i0 return (P0 i0) with
  | IMEnvCtr t => let fix step {n} (ms : VecEnv.t IMod n) : Forall P1 ms :=
                       match ms with
                         | [] => Forall_nil P1
                         | y :: l =>
                           Forall_cons P1 y l (F1 y) (step l)
                       end
                   in f0 t (step (VecEnv.vals _ t))
  end
with F1 (i : IMod) : P1 i :=
  match i as i0 return (P1 i0) with
  | INonParamMod i0 => f1 i0 (F i0)
  | IFtor i0 t e m s m0 => f2 i0 (F i0) t e m s m0
  end
for F.

(* Induction principle with predicate for MEnv that also depends on keys
   TODO: I left it here, though we probably won't need it *)
Definition IEnv_mut' (P : IEnv -> Prop) (P0 : IMEnv -> Prop) (P1 : mid -> IMod -> Prop)
           (f : forall (t : TEnv) (i : IVEnv) (i0 : IMEnv),
                  P0 i0 -> forall m : MTEnv, P (IEnvCtr t i i0 m))
           (f0 : forall t :  VecEnv.VecEnv IMod,
               Forall2_fix P1 _ _ (proj1_sig (VecEnv.keys _ t)) (VecEnv.vals _ t) ->
               P0 (IMEnvCtr t))
           (f1 : forall (i : IEnv) (k : mid), P i -> P1 k (INonParamMod i))
           (f2 : forall (i : IEnv) (k : mid),
               P i -> forall (t : TSet) (e : Env) (m : MTy) (s : mtid) (m0 : mexp),
                 P1 k (IFtor i t e m s m0)) : forall i, P i.
refine (fix F (i : IEnv) : P i :=
  match i as i0 return (P i0) with
  | IEnvCtr t i0 i1 m => f t i0 i1 (F0 i1) m
  end
with F0 (i : IMEnv) : P0 i :=
  match i as i0 return (P0 i0) with
  | IMEnvCtr t =>
    let fix step {n m} (ks : VecEnv.t mid n) (vs : VecEnv.t IMod m) (p: n=m) {struct vs}
        : Forall2_fix P1 _ _ ks vs := _
    in f0 t (step (proj1_sig (VecEnv.keys _ t)) (VecEnv.vals _ t) eq_refl)
  end
with F1 (i : IMod) (k : mid) {struct i} : P1 k i :=
  match i as i0 return (P1 k i0) with
  | INonParamMod i0 => f1 i0 k (F i0)
  | IFtor i0 t e m s m0 => f2 i0 k (F i0) t e m s m0
  end
    for F).
destruct ks as [|k' n ks']; destruct vs as [| v' m vs'].
+ apply I.
+ apply (False_rect _ (O_Sn_eq_false p)).
+ apply (False_rect _ (O_Sn_eq_false (eq_sym p))).
+ simpl. apply eq_add_S in p. destruct p.
  apply (conj (step n n ks' vs' eq_refl) (F1 v' k')).
Defined.

Definition emptyIMEnv  : IMEnv  := IMEnvCtr empty.
Definition emptyIEnv   : IEnv   := IEnvCtr empty empty emptyIMEnv emptyMTEnv.

Definition lookIMid (k : mid) (ime : IMEnv) : option IMod :=
  match ime with
    | IMEnvCtr imenv => look k imenv
  end.

Fixpoint lookLongITid (longk : longtid) (ie : IEnv) : option Ty :=
  match ie with
  | IEnvCtr te _ ime _ =>
    match longk with
    | Tid_longtid k => look k te
    | Long_longtid m_id longk' =>
      match (lookIMid m_id ime) with
      | Some (INonParamMod e') => lookLongITid longk' e'
      | _ => None
      end
    end
  end.

Fixpoint lookLongIVid (longk : longvid) (ie : IEnv) : option (label*Ty) :=
  match ie with
  | IEnvCtr _ ive ime _ =>
    match longk with
    | Vid_longvid k => look k ive
    | Long_longvid m_id longk' =>
      match (lookIMid m_id ime) with
      | Some (INonParamMod e') => lookLongIVid longk' e'
      | _ => None
      end
    end
  end.

Fixpoint lookLongIMid (longk : longmid) (ie : IEnv) : option IMod :=
  match ie with
  | IEnvCtr _ _ ime _ =>
    match longk with
    | Mid_longmid k => lookIMid k ime
    | Long_longmid m_id longk' =>
      match (lookIMid m_id ime) with
      | Some (INonParamMod e') => lookLongIMid longk' e'
      | _ => None
      end
    end
  end.

Definition lookMidIE (k : mid) (e : IEnv) : option IMod :=
  match e with
    | IEnvCtr _ _ me _ => lookIMid k me
  end.

Definition addIMEnv (k : mid) (t : IMod) (ime : IMEnv) :=
  match ime with
    | IMEnvCtr imenv => IMEnvCtr (add _ k t imenv)
  end.

Definition plusIEnvIEnv (E1 E2:IEnv) : IEnv :=
  match E1, E2 with
  | IEnvCtr te1 ve1 (IMEnvCtr menv1) (MTEnvCtr mtenv1),
    IEnvCtr te2 ve2 (IMEnvCtr menv2) (MTEnvCtr mtenv2) =>
    IEnvCtr (te1 ++ te2) (ve1 ++ ve2)
            (IMEnvCtr (menv1 ++ menv2))
            (MTEnvCtr (mtenv1 ++ mtenv2))
  end.

Open Scope nat.

(* Interpretation object erasure *)

Definition erasure_IVEnv (ive : EnvMod.t (label*Ty)) (ve: EnvMod.t Ty) : Prop :=
  forall k t, (forall l, look k ive = Some (l,t) -> look k ve = Some t) /\
              (look k ve = Some t -> exists l, look k ive = Some (l,t)).

Inductive erasure_IEnv : IEnv -> Env -> Prop :=
| era_IEnv : forall te ive ve ime me mte,
    erasure_IVEnv ive ve ->
    erasure_IMEnv ime me ->
    erasure_IEnv (IEnvCtr te ive ime mte) (EnvCtr te ve me mte)
with erasure_IMEnv : IMEnv -> MEnv -> Prop :=
| era_IMEnv : forall ime me,
    EnvRel erasure_IMod (_to ime) (_to me) ->
    erasure_IMEnv (IMEnvCtr ime) (MEnvCtr me)
with erasure_IMod : IMod -> Mod -> Prop :=
| era_IMod_INonParamMod : forall ie e,
    erasure_IEnv ie e ->
    erasure_IMod (INonParamMod ie) (NonParamMod e)
| era_IMod_IFtor : forall ie ts env mt x e,
    erasure_IMod (IFtor ie ts env mt x e) (Ftor ts env mt).

Scheme era_mut :=
  Induction for erasure_IEnv Sort Prop
  with erasure_IMEnv_mut := Induction for erasure_IMEnv Sort Prop
  with erasure_IMod_mut := Induction for erasure_IMod Sort Prop.


(* Two "base" cases. We say that set of vars T is disjoint from te or ve if
   for all keys in these maps corresponding values (if they are type variables)
   are not in T *)

Inductive disjoint_ivenv (T : TSet) (ive : IVEnv) :=
| disj_ivenv : forall v_id t t' l,
                TSetMod.In t T -> look v_id ive = Some (l,Tv_Ty t') ->
                ~ (t = t' \/ t = l)  -> disjoint_ivenv T ive.

Inductive disjoint_ienv (T : TSet) : IEnv -> Prop :=
| disj_ienv : forall te ve me mte,
               disjoint_tenv T te -> disjoint_ivenv T ve -> disjoint_imenv T me -> disjoint_mte T mte
               -> disjoint_ienv T (IEnvCtr te ve me mte)
with
disjoint_imenv (T : TSet) : IMEnv -> Prop :=
| disj_ime : forall mid me mod, lookIMid mid me = Some mod -> disjoint_imod T mod -> disjoint_imenv T me
with
disjoint_imod (T : TSet) : IMod -> Prop :=
| disj_inon_param_mod : forall e, disjoint_ienv T e -> disjoint_imod T (INonParamMod e)
| disj_iftor : forall bound e mt x exp ie,
    disjoint_env (TSetMod.diff T bound) e ->
    disjoint_mty (TSetMod.diff T bound) mt ->
    disjoint_ienv T ie ->
    disjoint_imod T (IFtor ie bound e mt x exp).

(* Functionality *)

Definition addIEnvTid (k : tid) (t : Ty) (E:IEnv) :=
  match E with
    IEnvCtr te ve me mte => IEnvCtr (add _ k t te) ve me mte
  end.

Definition addIEnvVid (k : vid) (t : label*Ty) (E:IEnv) :=
  match E with
    IEnvCtr te ve me mte => IEnvCtr te (add _ k t ve) me mte
  end.

Definition addIEnvMid (k : mid) (M : IMod) (E:IEnv) :=
  match E with
    IEnvCtr te ve me mte => IEnvCtr te ve (addIMEnv k M me) mte
  end.

Definition addIEnvTmid (k : mid) (M : MTy) (E:IEnv) :=
  match E with
    IEnvCtr te ve me mte => IEnvCtr te ve me (addMTEnv k M mte)
  end.

(* ------------------------ *)
(* Facts about environments *)
(* ------------------------ *)

Set Printing Coercions.

Lemma ienv0: forall tid ty M,
    addIEnvTid tid ty M = plusIEnvIEnv M (addIEnvTid tid ty emptyIEnv).
Proof.
  intros. destruct M.
  unfold addIEnvTid, emptyIEnv, plusIEnvIEnv, emptyIMEnv, emptyMTEnv.
  destruct i0. destruct m. f_equal.
  + f_equal.
    apply VecEnv.toOrdEnv_injective.
    repeat rewrite VecEnv.toOrdEnv_fromOrdEnv_inv. rewrite mapEmptyPlus.
    reflexivity.
  + f_equal.
    rewrite VecEnv.to_empty.
    rewrite mapEmptyPlus.
    rewrite VecEnv.fromOrdEnv_toOrdEnv_inv. reflexivity.
Qed.

Lemma ienv1: forall E, plusIEnvIEnv E emptyIEnv = E.
Proof.
  intros. destruct E. destruct i0. destruct m.
  unfold plusIEnvIEnv. unfold emptyIEnv, emptyIMEnv. unfold emptyMTEnv.
  repeat rewrite VecEnv.to_empty.
  repeat rewrite VecEnv.toOrdEnv_fromOrdEnv_inv. repeat rewrite mapEmptyPlus.
  repeat rewrite VecEnv.fromOrdEnv_toOrdEnv_inv.
  reflexivity.
Qed.

(* ------------------- *)
(* Facts about erasure *)
(* ------------------- *)

Lemma erasure_look_mid: forall {IE E m k},
    erasure_IMEnv IE E ->
    (lookMid k E = Some m) ->
    exists im, lookIMid k IE = Some im /\ erasure_IMod im m.
Proof.
  intros ie e m k He Hm.
  destruct ie as [ve]. destruct e as [ve'].
  inversion He as [? ? Hrel H1 H2]. subst.
  inversion Hrel as [Hdom Hem].
  destruct (Hdom k) as [L R].
  simpl in *.
  assert (Hin : In _ k ve') by (apply En.find_2 in Hm; apply MapsTo_In in Hm; auto).
  destruct (R Hin) as [im Him].
  exists im. split;eauto.
Qed.

Lemma erasure_look_longvid : forall IE E t longvid,
    erasure_IEnv IE E ->
    (lookLongVid longvid E = Some t) ->
    exists l, lookLongIVid longvid IE = Some (l,t).
Proof.
  intros IE E t long_id He Heq_id.
  generalize dependent t.
  revert E IE He.
  induction long_id; intros.
  - rename t0 into k. rename t1 into t.
    simpl in *.
    inversion He. subst.
    unfold erasure_IVEnv in *.
    assert (H' := H k t).
    destruct H' as [H1 H2]. auto.
  - rename t0 into k. rename t1 into t.
    simpl in *. inversion He. subst.
    remember (lookMid k me) as om. destruct om;tryfalse.
    symmetry in Heqom.

    assert (Him_ex : exists im, lookIMid k ime = Some im /\ erasure_IMod im m)
      by apply (erasure_look_mid H0 Heqom).

    destruct Him_ex as [im Htmp]. destruct Htmp as [Him He_im].
    rewrite Him.
    destruct m; destruct im; tryfalse.
    * inversion_clear He_im.
      eapply IHlong_id;eauto.
    * (* one impossible case left *)
      inversion He_im.
Qed.

Lemma erasure_IEnv_extend: forall IE E t l s,
  erasure_IEnv IE E -> erasure_IEnv (addIEnvVid s (l,t) IE) (addEnvVid s t E).
Proof.
  intros ie e t0 l k He.
  inversion He. subst.
  constructor.
  + unfold erasure_IVEnv.
    intros k' t. split.
    * intros l0 Hl.
      rewrite FM.P.F.add_o in *.
      destruct (FM.P.F.eq_dec k k').
      ** inversion Hl. reflexivity.
      ** unfold erasure_IVEnv in *.
         destruct (H k' t) as [L R].
         eauto.
    * intros Ht.
      rewrite FM.P.F.add_o in *.
      destruct (FM.P.F.eq_dec k k').
      ** subst. inversion Ht. exists l. reflexivity.
      ** unfold erasure_IVEnv in *.
         destruct (H k' t) as [L R]. auto.
  + assumption.
Qed.

Lemma erasure_IEnv_tid_extend: forall IE E t s,
  erasure_IEnv IE E -> erasure_IEnv (addIEnvTid s t IE) (addEnvTid s t E).
Proof.
  intros ie e t k He.
  inversion He. subst.
  constructor;auto.
Qed.

Lemma erasure_IEnv_mid_extend: forall IE E M IM s,
  erasure_IEnv IE E -> erasure_IMod IM M -> erasure_IEnv (addIEnvMid s IM IE) (addEnvMid s M E).
Proof.
  intros ie e m im k He Hem.
  inversion He. subst.
  destruct me.
  constructor;auto.
  destruct ime. unfold addIMEnv. constructor.
  repeat (rewrite VE.toOrdEnv_fromOrdEnv_inv).
  inversion H0. subst.
  apply EnvRel_add; assumption.
Qed.

Lemma erasure_IEnv_empty: erasure_IEnv emptyIEnv emptyEnv.
Proof.
  unfold emptyIEnv, emptyEnv. repeat rewrite VecEnv.from_empty.
  constructor. constructor.
  + intros l H; inversion H.
  + intros H. inversion H.
  + unfold emptyIMEnv. constructor.
    rewrite VE.toOrdEnv_fromOrdEnv_inv.
    rewrite to_empty. split.
    * (* NOTE : domain extensionality makes this case trivial *)
      rewrite dom_extensionality. reflexivity.
    * intros. inversion H.
Qed.

Lemma erasure_IEnv_plus : forall IE1 E1 IE2 E2,
    erasure_IEnv IE1 E1 -> erasure_IEnv IE2 E2 ->
    erasure_IEnv (plusIEnvIEnv IE1 IE2) (plusEnvEnv E1 E2).
Proof.
  intros ie1 e1 ie2 e2 He1 He2.
  inversion He1 as [? ? ? ? ? ? Hev1 Hem1]. subst.
  inversion He2 as [ ? ? ? ? ? ? Hev2 Hem2]. subst.
  simpl. destruct ime,mte,ime0,mte0,me,me0.
  constructor.
  unfold erasure_IVEnv in *. intros k t.
  destruct (Hev1 k t) as [L R].
  destruct (Hev2 k t) as [L' R'].
  split.
  + intros l Hl.
    rewrite <- FM.P.F.find_mapsto_iff in *.
    rewrite FM.P.update_mapsto_iff in *.
    destruct Hl as [H1 | H2].
    * left. rewrite FM.P.F.find_mapsto_iff in *. eauto.
    * destruct H2. right. split.
      ** rewrite FM.P.F.find_mapsto_iff in *.
         eapply L;eauto.
      ** intro Hin. destruct Hin as [v' Hv']. destruct (Hev2 k v') as [L0 R0].
         apply En.find_1 in Hv'.
         destruct (R0 Hv') as [l' Hl']. apply En.find_2 in Hl'. apply MapsTo_In in Hl'.
         unfold In in *. tryfalse.
  + intros Ht.
    rewrite <- FM.P.F.find_mapsto_iff in *.
    rewrite FM.P.update_mapsto_iff in *.
    destruct Ht as [H1 | H2].
    * destruct (R' H1) as [l Hl].
      exists l.
      rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.update_mapsto_iff in *.
      left. assumption.
    * destruct H2 as  [Ht Hnin]. destruct (R Ht) as [l Hl].
      exists l.
      rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.update_mapsto_iff in *.
      right. split.
      ** assumption.
      ** intro Hin. destruct Hin as [v' Hv']. destruct v' as [l' t'].
         destruct (Hev2 k t') as [L0 R0].
         apply En.find_1 in Hv'.
         assert (H:=L0 l' Hv').  apply En.find_2 in H. apply MapsTo_In in H.
         unfold In in *. tryfalse.
  + inversion Hem1 as [? ? Hrel1 H2 H3]. subst.
    inversion Hem2 as [? ? Hrel2 H2 H3]. subst.
    inversion Hrel1 as [Hdom1 Hrmod1].
    inversion Hrel2 as [Hdom2 Hrmod2].
    constructor. repeat (rewrite VE.toOrdEnv_fromOrdEnv_inv).
    rewrite dom_extensionality in *.
    split.
    * rewrite dom_extensionality. apply dom_plus;eauto.
    * intros k im m Him Hm.
      rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.update_mapsto_iff in *.
      destruct Him as [H1 | H2]; destruct Hm as [H3 | H4].
      ** rewrite FM.P.F.find_mapsto_iff in *. eauto.
      ** destruct H4. rewrite FM.P.F.find_mapsto_iff in *.
         rewrite <- dom_extensionality in *.
         destruct (Hdom2 k) as [L R].
         assert (Hin : In _ k v1) by (apply En.find_2 in H1; apply MapsTo_In in H1; assumption).
         assert (Hin' := L Hin).
         tryfalse.
      ** destruct H2.
         rewrite <- dom_extensionality in *.
         destruct (Hdom2 k) as [L R].
         apply MapsTo_In in H3.
         assert (Hin' := R H3).
         tryfalse.
      ** destruct H2. destruct H4.
         rewrite FM.P.F.find_mapsto_iff in *.
         eauto.
Qed.


Lemma erasure_ienv_imod_lem : forall ie e,
    erasure_IEnv ie e -> erasure_IMod (INonParamMod ie) (NonParamMod e).
Proof.
  intros. constructor. eauto.
Qed.

Lemma erasure_imod_ienv_lem : forall ie e,
    erasure_IMod (INonParamMod ie) (NonParamMod e) -> erasure_IEnv ie e.
Proof.
  intros. inversion H. assumption.
Qed.

(* ---------------------- *)
(* filtering              *)
(* ---------------------- *)

Definition filt_IVEnv (ive:EnvMod.t (label*Ty)) (ve:EnvMod.t Ty) (ive':EnvMod.t (label*Ty)) : Prop :=
  env_ext ive ive' /\ erasure_IVEnv ive' ve.

Definition filt_ITEnv (ite:EnvMod.t Ty) (te:EnvMod.t Ty) (ite':EnvMod.t Ty) : Prop :=
  env_ext ite ite' /\ ite' = te.

Inductive filtering_IEnv : IEnv -> Env -> IEnv -> Prop :=
  filt_env :
    forall (ve:VEnv) (ite te ite':TEnv) (me:MEnv) (ive ive':IVEnv) (ime ime' : IMEnv) (mte : MTEnv),
                filt_IVEnv ive ve ive' ->
                filt_ITEnv ite te ite' ->
                filtering_IMEnv ime me ime' ->
                filtering_IEnv (IEnvCtr ite ive ime mte) (EnvCtr te ve me emptyMTEnv)
                               (IEnvCtr ite' ive' ime' emptyMTEnv)
with filtering_IMEnv : IMEnv -> MEnv -> IMEnv -> Prop :=
       filt_menv : forall (ime' : VE.VecEnv IMod) (me : VE.VecEnv Mod) (ime : VE.VecEnv IMod),
         dom_subset (_to ime) (_to ime') ->
         dom ime = dom me ->
         (forall mid im' m im,
             look mid ime' = Some im' ->
             look mid me = Some m ->
             look mid ime = Some im ->
             filtering_IMod im' m im) ->
         filtering_IMEnv (IMEnvCtr ime') (MEnvCtr me) (IMEnvCtr ime)
with filtering_IMod : IMod -> Mod -> IMod -> Prop :=
     | filt_mod_nonparam : forall ie e ie',
         filtering_IEnv ie e ie' ->
         filtering_IMod (INonParamMod ie) (NonParamMod e) (INonParamMod ie')
     | filt_mod_ftor : forall IE0 T E' E G G' mid mexp,
         (* NOTE : we simplify things a bit here, requiring 
            environments to be equal, and not in enrichment relation *)
         (* enriches E' E -> *)
         (* enrichesModType G' G -> *)
         E = E' ->
         G = G' ->
         filtering_IMod (IFtor IE0 T E G' mid mexp) (Ftor T E' G) (IFtor IE0 T E' G mid mexp).

Scheme filt_mut :=
  Induction for filtering_IEnv Sort Prop
  with filtering_IMEnv_mut := Induction for filtering_IMEnv Sort Prop
  with filtering_IMod_mut := Induction for filtering_IMod Sort Prop.


(** That's how filtering function could look like, but we will use "restrict"
    operation on environments instead (see below) *)
Definition filtering_fix_list (ive' : IVEnv) (ve' : VEnv) : list (En.key * (label*Ty)) :=
  match ve' with
  | @En.Build_slist _ vs0 _ =>
    (fix flt vs :=
       match vs with
       | List.nil => List.nil
       | List.cons (k,v) vs' =>
         match (look k ive') with
         | Some (l,v') => List.cons (k,(l,v')) (flt vs')
         | None => (flt vs')
         end
       end) vs0
  end.

(** Filtering operation is just a restriction of one environment
    with respect domain of another environment *)
Definition filt_fun {A B : Type} := restrict (A:=A) (B:=B).

(* --------------------- *)
(* Facts about filtering *)
(* --------------------- *)

Lemma filtering_to_erasure: forall ie e ie',
    filtering_IEnv ie' e ie -> erasure_IEnv ie e.
Proof.
  intros ie e ie' Hflt.
  induction Hflt using filt_mut
    with (P0 := fun ime' me ime (f : filtering_IMEnv ime' me ime)  =>
                  erasure_IMEnv ime me)
         (P1 := fun im' m im (f : filtering_IMod im' m im) =>
                  erasure_IMod im m).
  + inversion IHHflt. inversion f0. inversion f. subst. constructor;eauto.
  + constructor. unfold EnvRel.
    split.
    * apply dom_extensionality;auto.
    * intros k v v' Hv Hv'.
      assert (Hdom : dom_subset (_to me) (_to ime')). eapply domain_eq_l;eauto.
      assert (Hin : In _ k ime') by
          (rewrite <- FM.P.F.find_mapsto_iff in Hv'; apply MapsTo_In in Hv';
           apply Hdom; assumption).
      inversion Hin as [im0 Him0].
      assert (Him' : look k ime' = Some im0) by
          (rewrite <- FM.P.F.find_mapsto_iff; auto).
      eapply H;eauto.
  + constructor;auto.
  + constructor.
Qed.


Lemma filtering_enriches: forall ie e e' ie',
    filtering_IEnv ie' e ie -> erasure_IEnv ie' e' -> enriches e' e.
Proof.
  intros ie e e' ie' Hflt.
  revert e'.
  induction Hflt using filt_mut
    with (P0 := fun ime' me ime (f : filtering_IMEnv ime' me ime)  =>
                  forall me', erasure_IMEnv ime' me' -> enrichesM me' me)
         (P1 := fun im' m im (f : filtering_IMod im' m im) =>
                  forall m', erasure_IMod im' m' -> enrichesMod m' m).
  + intros e' He. destruct e'. inversion He as [ ? ? ? ? ? ? Hev Hem]. subst. constructor;eauto.
    * inversion f as [Hext Herasure]. inversion_clear f.
      unfold erasure_IVEnv in *. unfold env_ext in *. intros k t Ht.
      destruct (Hev k t). destruct (Herasure k t) as [H3 H4].
      destruct (H4 Ht). eauto.
    * inversion f as [Hext Herasure]. inversion f0. subst. assumption.
  + intros me' Hme'. destruct me'.
    inversion Hme' as [? ? H0 H1 H2]. subst.  destruct H0 as [Hdom Hev'].
    rewrite dom_extensionality in Hdom.
    constructor.
    * eapply domain_eq_r;eauto. eapply domain_eq_l;eauto.
    * intros k e0' e0 He0' He'.
      assert (Hdom' : dom_subset (_to me) (_to ime')) by (eapply domain_eq_l;eauto).
      assert (Hin : In _ k ime') by
          (rewrite <- FM.P.F.find_mapsto_iff in He'; apply MapsTo_In in He';
           apply Hdom'; assumption).
      inversion Hin as [im0 Him0].
      assert (Him' : look k ime' = Some im0) by
          (rewrite <- FM.P.F.find_mapsto_iff; auto).
      assert (Hin' : In _ k ime ) by
        (rewrite <- dom_extensionality in e; destruct (e k) as [L R];
         rewrite <- FM.P.F.find_mapsto_iff in He'; apply MapsTo_In in He'; apply R; apply He').
      inversion Hin' as [im1 Him1].
      assert (Him1' : look k ime = Some im1) by
          (rewrite <- FM.P.F.find_mapsto_iff; auto).
      eapply H;eauto.
  + intros m He. destruct m;inversion He. subst.
    constructor. eauto.
  + intros m' He. inversion He. subst.
    constructor; eauto.
Qed.

