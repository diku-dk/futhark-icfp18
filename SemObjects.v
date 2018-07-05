(*===================================== *)
(* Semantic objects                     *)
(*===================================== *)


Require Import String MSetFacts MSetProperties ProofIrrelevance Vector Coq.Program.Equality.
Require Import Basics CustomTactics CpdtTactics EnvExt SetExt PeanoNat.

(* Using a finite map implemened as a sorted list with no duplication *)
Module EnvMod := EnvExt.OrdEnv Basics.ID.

Import EnvMod.

(* Environments, represented as a pair of vectors
   This representation is used in mutual inductive definitions
   where we cannot use EnvExt because of syntactic strict positivity
   check *)

Module VE := EnvMod.VecEnv.

Notation AEnv := EnvMod.t.

(* Finite set of variables/identifiers using ordered list implementation
   with extensionality property *)

Module TSetMod := SetExt PeanoNat.Nat.
Notation Tv := TSetMod.elt.

Definition TSet := TSetMod.t.
Definition emptyTSet := TSetMod.empty.
Definition addTSet := TSetMod.add.
Definition unionTSet := TSetMod.union.

(* -------------- *)
(* Semantic types *)
(* -------------- *)

Inductive Ty :=
  | Tv_Ty : Tv -> Ty
  | Arr_Ty : Ty -> Ty -> Ty.

(* --------------------- *)
(* Semantic environments *)
(* --------------------- *)

Definition TEnv := AEnv Ty.
Definition VEnv := AEnv Ty.

(** Definition of environments. We use VE.VecEnv (environments as pair of vectors) instead of
    just type constructor from OrdEnv, because of Coq's strict positivity check.
    OrdEnv implementation is based on the standard library implementation of finite maps
    as sorted lists. *)
Inductive Env :=
     | EnvCtr : TEnv -> VEnv -> MEnv -> MTEnv -> Env
with MEnv :=
     | MEnvCtr : VE.VecEnv Mod -> MEnv
with MTEnv :=
     | MTEnvCtr : VE.VecEnv MTy -> MTEnv
with Mod :=
     | NonParamMod : Env -> Mod
     | Ftor : TSet -> Env -> MTy -> Mod
with MTy :=
     | MSigma : TSet -> Mod -> MTy.

(* Scheme is useful to get induction principle with mutual recursion.
   Later, we derive a stronger induction principle by adding
   assumptions about nested inductive types like environments. *)
Scheme Env_mut :=
  Induction for Env Sort Prop
  with MEnv_mut := Induction for MEnv Sort Prop
  with MTEnv_mut:= Induction for MTEnv Sort Prop
  with Mod_mut  := Induction for Mod Sort Prop
  with MTy_mut  := Induction for MTy Sort Prop.

Import VE.
Import Vector.
Import VectorNotations.
Open Scope vector_scope.


(* Coercion venv_to_list {A} (vs : VecEnv A) := Vector.to_list (vals _ vs). *)

Local Coercion to_vals := vals.

(* This is the induction principle we should use for proofs *)
Definition Env_mut' (P : Env -> Prop) (P0 : MEnv -> Prop) (P1 : MTEnv -> Prop)
  (P2 : Mod -> Prop) (P3 : MTy -> Prop)
  (f : forall (t : TEnv) (v : VEnv) (m : MEnv),
       P0 m -> forall m0 : MTEnv, P1 m0 -> P (EnvCtr t v m m0))
  (f0 : forall (t : VecEnv Mod),
      Forall P2 t -> P0 (MEnvCtr t))
  (f1 : forall (t : VecEnv MTy),
          Forall P3 t -> P1 (MTEnvCtr t))
  (f2 : forall e : Env, P e -> P2 (NonParamMod e))
  (f3 : forall (t : TSet) (e : Env),
        P e -> forall m : MTy, P3 m -> P2 (Ftor t e m))
  (f4 : forall (t : TSet) (m : Mod), P2 m -> P3 (MSigma t m)) :=
fix F (e : Env) : P e :=
  match e as e0 return (P e0) with
  | EnvCtr t v m m0 => f t v m (F0 m) m0 (F1 m0)
  end
with F0 (m : MEnv) : P0 m :=
  match m as m0 return (P0 m0) with
    | @MEnvCtr t => let fix step {n} (ms : Vec Mod n) : Forall P2 ms :=
                       match ms in Vec _ n' return @Forall _ P2 n' ms with
                         | [] => Forall_nil P2
                         | y :: l =>
                           @Forall_cons _ P2 _ y _ (F2 y) (step l)
                       end
                   in f0 t (step (vals _ t))
  end
with F1 (m : MTEnv) : P1 m :=
  match m as m0 return (P1 m0) with
  | @MTEnvCtr t => let fix step {n} (ms : Vec MTy n) : Forall P3 ms :=
                       match ms with
                         | [] => Forall_nil P3
                         | y :: l =>
                           @Forall_cons _ _ _ y l (F3 y) (step l)
                       end
                  in f1 t (step t)
  end
with F2 (m : Mod) : P2 m :=
  match m as m0 return (P2 m0) with
  | NonParamMod e => f2 e (F e)
  | Ftor t e m0 => f3 t e (F e) m0 (F3 m0)
  end
with F3 (m : MTy) : P3 m :=
  match m as m0 return (P3 m0) with
  | MSigma t m0 => f4 t m0 (F2 m0)
  end
for F.


Definition emptyMTEnv := MTEnvCtr VE.ve_empty.
Definition EmptyMEnv me := match me with MEnvCtr m => EnvMod.En.Empty (_to m) end.
Definition EmptyTyEnv := empty (A:=Ty).
Definition EmptyModEnv := empty (A:=Mod).

Open Scope type_scope.

(* Enrichment *)
Inductive enriches : Env -> Env -> Prop :=
  | enr_env : forall (ve' ve : VEnv) (te' te : TEnv) (me' me : MEnv) (mte' mte : MTEnv),
                env_ext ve' ve ->
                env_ext te' te ->
                enrichesM me' me ->
                enriches (EnvCtr te' ve' me' mte') (EnvCtr te ve me emptyMTEnv)
  with
    enrichesM : MEnv -> MEnv -> Prop :=
  | enr_menv : forall (me' me : VecEnv Mod),
      dom_subset (_to me) (_to me') ->
      (forall mid (e' e : Mod), look mid (_to me') = Some e' ->
                                look mid (_to me) = Some e ->
                                enrichesMod e' e) ->
      enrichesM (MEnvCtr me') (MEnvCtr me)
  with
    enrichesMod : Mod -> Mod -> Prop :=
      | enr_np_mod : forall e' e, enriches e' e -> enrichesMod (NonParamMod e') (NonParamMod e)
      | enr_ftor   : forall t e e' s s',
          (* we simplify the notion of enrichment here by just requiring [e] and [e'] to be equal,
             instead of being in enrichment relation. The same for [s] and [s'] *)
          e' = e ->
          s' = s ->
          enrichesMod (Ftor t e' s') (Ftor t e s).


Definition lookMid (k : ID.t) (me : MEnv) : option Mod :=
  match me with
    | MEnvCtr menv => look k (_to menv)
  end.

Definition lookMtid (k : ID.t) (mte : MTEnv) : option MTy :=
  match mte with
  | MTEnvCtr m => look k (_to m)
  end.

Fixpoint lookLongTid (longk : longtid) (e : Env) : option Ty :=
  match e  with
  | EnvCtr te _ me _ =>
    match longk with
    | Tid_longtid k => look k te
    | Long_longtid m_id longk' =>
      match (lookMid m_id me) with
      | Some (NonParamMod e') => lookLongTid longk' e'
      | _ => None
      end
    end
  end.

Fixpoint lookLongVid (longk : longvid) (e : Env) : option Ty :=
  match e with
  | EnvCtr _ ve me _ =>
    match longk with
    | Vid_longvid k => look k ve
    | Long_longvid m_id longk' =>
      match (lookMid m_id me) with
      | Some (NonParamMod e') => lookLongVid longk' e'
      | _ => None
      end
    end
  end.

Fixpoint lookLongMid (longk : longmid) (e : Env) : option Mod :=
  match e with
  | EnvCtr _ _ me _ =>
    match longk with
    | Mid_longmid k => lookMid k me
    | Long_longmid m_id longk' =>
      match (lookMid m_id me) with
      | Some (NonParamMod e') => lookLongMid longk' e'
      | _ => None
      end
    end
  end.

Definition lookMidE (k : mid) (e : Env) : option Mod :=
  match e with
    | EnvCtr _ _ me _ => lookMid k me
  end.

Definition lookLongMtid (k : mtid) (e : Env) : option MTy :=
  match e with
  | EnvCtr _ _ _ mte => lookMtid k mte
  end.

Open Scope env_scope.

Definition addMEnv (k : mid) (t : Mod) (me : MEnv) : MEnv :=
  match me with
  | MEnvCtr menv => MEnvCtr ((EnvMod.add _ k t (_to menv)))
  end.

Definition addMTEnv (k : vid) (mty : MTy) (mte : MTEnv) : MTEnv :=
  match mte with
  | MTEnvCtr m => MTEnvCtr (EnvMod.add _ k mty (_to m))
  end.

Definition plusEnvEnv (E1 E2:Env) : Env :=
  match E1, E2 with
  | EnvCtr te1 ve1 (MEnvCtr menv1) (MTEnvCtr mtenv1),
    EnvCtr te2 ve2 (MEnvCtr menv2) (MTEnvCtr mtenv2) =>
    EnvCtr (te1 ++ te2) (ve1 ++ ve2)
           (MEnvCtr ((_to menv1) ++ (_to menv2)))
           (MTEnvCtr ((_to mtenv1) ++ (_to mtenv2)))
  end.

(* Two "base" cases. We say that set of vars [T] is disjoint from [te] or [ve] if
   for all keys in these maps corresponding values (if they are type variables)
   are not in [T] *)

Inductive disjoint_tenv (T : TSet) (te : TEnv) :=
| disj_tenv_tv : forall t_id t,
                   look t_id te = Some (Tv_Ty t) -> ~ TSetMod.In t T
                   -> disjoint_tenv T te
| disj_tenv_arr : forall t_id ty ty',
                    look t_id te = Some (Arr_Ty ty ty')
                    -> disjoint_tenv T te
| disj_tenv_empty : EnvMod.En.Empty te -> disjoint_tenv T te.

Inductive disjoint_venv (T : TSet) (ve : VEnv) :=
| disj_venv_tv : forall v_id (t : Tv),
                   look v_id ve = Some (Tv_Ty t) ->  ~ TSetMod.In t T
                   -> disjoint_venv T ve
| disj_venv_arr : forall v_id ty ty',
                    look v_id ve = Some (Arr_Ty ty ty')
                    -> disjoint_venv T ve
| disj_venv_empty : EnvMod.En.Empty ve -> disjoint_venv T ve.

Inductive disjoint_env (T : TSet) : Env -> Prop :=
| disj_env : forall te ve me mte,
               disjoint_tenv T te -> disjoint_venv T ve -> disjoint_menv T me -> disjoint_mte T mte
               -> disjoint_env T (EnvCtr te ve me mte)
with
disjoint_menv (T : TSet) : MEnv -> Prop :=
| disj_me_empty : forall (me : VecEnv Mod),
    EnvMod.En.Empty (_to me) -> disjoint_menv T (MEnvCtr me)
| disj_me_in : forall mid me md,
    lookMid mid me = Some md -> disjoint_mod T md ->
    disjoint_menv T me
with
  disjoint_mte (T : TSet) : MTEnv -> Prop :=
  | disj_mte_empty : forall (mtenv : VecEnv MTy),
      EnvMod.En.Empty (_to mtenv) -> disjoint_mte T (MTEnvCtr mtenv)
  | disj_mte_in : forall mtid mt mtenv, lookMtid mtid mtenv = Some mt ->
                                        disjoint_mty T mt -> disjoint_mte T mtenv
with
(* in this case (and in case of functor) we remove bound variables from the set [T] *)
disjoint_mty (T : TSet) : MTy -> Prop :=
| disj_mty : forall bound md, disjoint_mod (TSetMod.diff T bound) md -> disjoint_mty T (MSigma bound md)
with
disjoint_mod (T : TSet) : Mod -> Prop :=
| disj_non_param_mod : forall e, disjoint_env T e -> disjoint_mod T (NonParamMod e)
| disj_ftor : forall bound e mt, disjoint_env (TSetMod.diff T bound) e
                                 -> disjoint_mty (TSetMod.diff T bound) mt
                                 -> disjoint_mod T (Ftor bound e mt).

Definition empty_tys := TSetMod.empty.

Module SetFacts := WFacts TSetMod.
Module SetProperties := OrdProperties TSetMod.

Import SetFacts SetProperties SetProperties.P.

(* Sanity check *)

Lemma disjoint_tenv_empty te : forall T, TSetMod.Empty T -> disjoint_tenv T te.
Proof.
  intros.
  destruct te as [l sl]. destruct l.
  + apply disj_tenv_empty. apply EnvMod.En.empty_1.
  + destruct p as [s ty]. destruct ty.
    (* Tv *)
    eapply disj_tenv_tv with (t_id:=s).
    unfold look,En.find. simpl.
    rewrite Key_compare_eq. reflexivity.
    auto.
    (* arr *)
    eapply disj_tenv_arr with (t_id:=s).
    unfold look, En.find. simpl.
    destruct (Key.compare s s) as [f |_ | f]; try (apply En.E.lt_not_eq in f; tryfalse).
    reflexivity.
Qed.

Lemma disjoint_venv_empty ve : forall T, TSetMod.Empty T -> disjoint_venv T ve.
Proof.
  Proof.
  intros.
  destruct ve as [l sl]. destruct l.
  + apply disj_venv_empty. apply EnvMod.En.empty_1.
  + destruct p as [s ty]. destruct ty.
    * (* Tv *)
      eapply disj_venv_tv with (v_id:=s).
      unfold look,En.find. simpl.
      rewrite Key_compare_eq. reflexivity.
      auto.
    * (* arr *)
      eapply disj_venv_arr with (v_id:=s).
      unfold look, En.find. simpl.
      destruct (Key.compare s s) as [f |_ | f]; try (apply En.E.lt_not_eq in f; tryfalse).
      reflexivity.
Qed.

Hint Resolve disjoint_tenv_empty disjoint_venv_empty.

Lemma disjoint_env_empty e :
  forall T, TSetMod.Empty T -> disjoint_env T e.
Proof.
  induction e using Env_mut'
  with (P0 := fun x => forall T, TSetMod.Empty T -> disjoint_menv T x)
       (P1 := fun x => forall T, TSetMod.Empty T -> disjoint_mte T x)
       (P2 := fun x => forall T, TSetMod.Empty T -> disjoint_mod T x)
       (P3 := fun x => forall T, TSetMod.Empty T -> disjoint_mty T x);
  intros.
  - constructor; auto.
  - destruct t as [n ks vs]. destruct ks as [ks' ks_sort].
    dependent destruction ks';dependent destruction vs.
    + simpl.
      apply disj_me_empty. simpl. unfold lift. apply En.empty_1.
    + simpl in H.   
      inversion_clear H.
      apply disj_me_in with (mid:=h) (md:=h0).
      * unfold lookMid. unfold look, En.find. simpl.
        rewrite Key_compare_eq. reflexivity.      
      * apply H1;auto.
  - destruct t as [n ks vs]. destruct ks as [ks' ks_sort].
    dependent destruction ks';dependent destruction vs.
    + apply disj_mte_empty. simpl. unfold lift. apply En.empty_1.
    + inversion_clear H. subst. apply disj_mte_in with (mtid:=h) (mt:=h0).
      * unfold lookMtid. simpl. unfold look, En.find. simpl.
        rewrite Key_compare_eq. reflexivity.
      * apply H1;auto.
  - constructor. apply IHe; auto.
  - assert (H1 : TSetMod.Empty (TSetMod.diff T t)).
    apply empty_diff_1. auto. unfold TSetMod.Empty in *.
    constructor; auto.
  - assert (H1 : TSetMod.Empty (TSetMod.diff T t)).
    apply empty_diff_1. auto. unfold TSetMod.Empty in *.
    constructor; auto.
Qed.

(* Functionality *)

Definition addEnvTid (k : tid) (t : Ty) (E:Env) :=
  match E with
    EnvCtr te ve me mte => EnvCtr (te[[k |-> t]]) ve me mte
  end.

Definition addEnvVid (k : vid) (t : Ty) (E:Env) :=
  match E with
    EnvCtr te ve me mte => EnvCtr te (ve[[ k |-> t]]) me mte
  end.

Definition addEnvMid (k : mid) (M : Mod) (E:Env) :=
  match E with
    EnvCtr te ve (MEnvCtr me) mte => EnvCtr te ve (MEnvCtr ((_to me)[[k |-> M]])) mte
  end.

Definition addEnvMtid (k : mtid) (v : MTy) (E:Env) :=
  match E with
    EnvCtr te ve me mte  => EnvCtr te ve me (addMTEnv k v mte)
  end.

Definition emptyEnv : Env := EnvCtr empty empty (MEnvCtr empty) (MTEnvCtr empty).

(* Facts *)

(* NOTE: We use hint database [set], which contains properties
   of sets and allows to solve some goals with [auto] *)
Lemma set1: forall t S, addTSet t S = unionTSet (addTSet t emptyTSet) S.
Proof.
  intros.
  apply TSetMod.set_extensionality with (X:=addTSet t S).
  intros x.
  split.
  + intros H; rewrite Dec.F.add_iff in *; destruct H;auto with set.
  + intros H. apply Dec.F.union_1 in H.
    destruct H; auto with set.
Qed.

(* An interesting thing is that [EnvMod.Raw.add k t e] is not equal to 
   [EnvMod.Raw.add k t (AEmptyEnv Ty) :+: e]
   because of the way how updates of existing keys are implemented *)
Lemma mapAddPlusEmpty: forall {A} (e : AEnv A) k t,
    e[[k |-> t]] = (e ++ (empty [[k |-> t]])).
Proof.
   crush.
Qed.

Lemma mapEmptyPlus: forall {A} (e : AEnv A),
    e ++ empty = e.
Proof.
  crush.
Qed.

Lemma mapEmptyPlus' : forall {A} (e e0: AEnv A),
    e0 = empty -> e ++ e0 = e.
Proof.
  intros. rewrite H.
  crush.
Qed.

Set Printing Coercions.

(* NOTE: properties of operations on semantic objects require
   to use [fromOrdEnv_toOrdEnv_inv] in proofs *)
Lemma map1: forall tid ty M, addEnvTid tid ty M = plusEnvEnv M (addEnvTid tid ty emptyEnv).
Proof.
  intros. destruct M. destruct m; destruct m0. simpl.
  f_equal.
  + rewrite mapEmptyPlus'.
    * rewrite fromOrdEnv_toOrdEnv_inv;reflexivity.
    * unfold empty, En.empty. f_equal. apply proof_irrelevance.
  + rewrite mapEmptyPlus'.
    rewrite fromOrdEnv_toOrdEnv_inv. reflexivity.
    unfold empty, En.empty. f_equal. apply proof_irrelevance.
Qed.

Lemma env1: forall E, plusEnvEnv E emptyEnv = E.
Proof.
  intros. destruct E. destruct m0. destruct m.
  unfold plusEnvEnv. unfold emptyEnv.
  repeat rewrite VecEnv.toOrdEnv_fromOrdEnv_inv.
  repeat rewrite mapEmptyPlus.
  repeat rewrite VecEnv.fromOrdEnv_toOrdEnv_inv.
  reflexivity.
Qed.
