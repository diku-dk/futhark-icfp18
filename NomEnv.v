(*============================================ *)
(*   Nominal sets of semantic objects and      *)
(*      interpretation objects                 *)
(*============================================ *)

Require Import SemObjects IntObjects Target Nom Vector EnvExt Basics CustomTactics.
Require Import Program.Equality.

(** We use set of variables TSetMod (elements are natural numbers) *)
Module AtomN <: Atom.
  Module V := TSetMod.
  (* We left this as an axiom, but one can show this property by taking x = max(X)+1 *)
  Axiom Atom_inf : forall (X : V.t), {x : V.elt | ~ V.In x X}.
End AtomN.

Module NomN := Nominal AtomN.

(* -------------------------------------- *)
(* Nominal set of types                   *)
(* -------------------------------------- *)
Module PermTy <: NomN.NominalSet.
  Import NomN.
  Module V := Atom.V.
  Definition X := Ty.

  Fixpoint action (r : Perm) (ty : Ty) :=
    match ty with
    | Tv_Ty v => Tv_Ty ((perm r) v)
    | Arr_Ty t1 t2 => Arr_Ty (action r t1) (action r t2)
    end.

  Notation "r @ x" := (action r x) (at level 80).

  Lemma action_id : forall (x : X), (id_perm @ x) = x.
  Proof.
    intros x.
    induction x;simpl;try congruence;auto.
  Qed.

  Lemma action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).
  Proof.
    intros x r r'.
    induction x.
    + simpl. f_equal.
    + simpl. congruence.
  Qed.

  Fixpoint supp (ty : Ty) : V.t :=
    match ty with
    | Tv_Ty v => V.singleton v
    | Arr_Ty t1 t2 => V.union (supp t1) (supp t2)
    end.

  Import V.

  Lemma supp_spec :
    forall  (r : Perm)  (x : X),
      (forall (a : V.elt), In a (supp x) -> (perm r) a = a) -> (r @ x) = x.
  Proof.
    intros r x H.
    induction x.
    + simpl in *. rewrite H;auto with set. apply V.singleton_spec. reflexivity.
    + simpl in *. f_equal.
      * apply IHx1. intros. apply H. apply union_spec. auto.
      * apply IHx2. intros. apply H. apply union_spec. auto.
  Qed.

  Definition fresh a x := ~ In a (supp x).

  (* NOTE : this property seems to be very uniform, look it up in papers on nominal sets *)
  Lemma supp_action : forall r t,
      PermTy.supp (PermTy.action r t) = PFin.action r (PermTy.supp t).
  Proof.
    intros r t.
    induction t.
    + simpl. rewrite PFin.action_singleton. reflexivity.
    + simpl. rewrite PFin.equivar_union. rewrite IHt1. rewrite IHt2. reflexivity.
  Qed.

End PermTy.

(* ------------------------------------------------- *)
(* Nominal set of "plain" environments - finite maps *)
(* with no mutual inductive structure                *)
(* ------------------------------------------------- *)
Module PermPlainEnv <: NomN.NominalSet.
  Import NomN.
  Module V := Atom.V.

  Import EnvMod.

  Definition X := EnvMod.t Ty.
  Definition singleEnv (k : tid) (t : Ty) : X := EnvMod.add _ k t EnvMod.empty.

  Definition action (r : Perm) (x : X) :=
    EnvMod.En.map (PermTy.action r) x.

  Notation "r @ x" := (action r x) (at level 80).

  Hint Resolve EnvMod.En.find_1 EnvMod.En.find_2
       EnvMod.En.map_1 : env.


  Lemma action_id : forall (x : X), (id_perm @ x) = x.
  Proof.
    intros x.
    apply EnvMod.env_extensionality_alt.
    intros. split.
    + intros H. apply EnvMod.En.find_2 in H. unfold action in *.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      destruct H as [a H']. destruct H'. subst. rewrite PermTy.action_id. auto with env.
    + intros H. unfold action in *.
      apply EnvMod.En.find_1.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      exists v. rewrite PermTy.action_id. split;auto.
  Qed.

  Lemma action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).
  Proof.
    intros x r r'.
    apply EnvMod.env_extensionality_alt. intros.
    split;unfold action in *.
    + intros H.
      apply EnvMod.En.find_1. apply EnvMod.En.find_2 in H.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *. destruct H as [a H']. destruct H'.
      subst. rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      destruct H0 as [b H0']. destruct H0'.
      subst.
      exists b. split.
      * apply PermTy.action_compose.
      * auto.
    + intros H.
      apply EnvMod.En.find_1. apply EnvMod.En.find_2 in H.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      destruct H as [a H']. destruct H'.
      rewrite <- PermTy.action_compose in *.
      exists (PermTy.action r' a).
      split;auto.
  Qed.

  Lemma action_singleton :
    forall r k v, (r @ (singleEnv k v)) = singleEnv k ((PermTy.action r) v).
  Proof.
    intros.
    apply env_extensionality_alt. intros k' v'.
    split; intros Hk'; compute in *;
      destruct (ID.compare k' k);tryfalse;auto.
  Qed.

  Definition supp (x : X) : V.t :=
    EnvMod.En.fold (fun k v v' => V.union (PermTy.supp v) v') x V.empty.

  Lemma in_env_in_supp (E : X) k e v :
    look k E = Some e -> V.In v (PermTy.supp e) -> V.In v (supp E).
  Proof.
    unfold supp.
    apply FM.P.fold_rec_weak with
        (P:= fun x y => look k x = Some e -> V.In v (PermTy.supp e) -> V.In v y).
    + intros m m' a H H1 H2 H3. intros. apply env_extensionality in H. subst. auto.
    + intros He Hv. tryfalse.
    + intros. rewrite V.union_spec in *.
      apply En.find_2 in H1. rewrite FM.P.F.add_mapsto_iff in *.
      destruct H1.
      * destruct H1. subst. auto.
      * destruct H1. right. apply H0; auto.
  Qed.

  Lemma supp_spec :
    forall  (r : Perm)  (x : X),
      (forall (a : V.elt), V.In a (supp x) -> (perm r) a = a) -> (r @ x) = x.
  Proof.
    intros r x Hs.
    unfold action in *.
    apply EnvMod.env_extensionality_alt. intros.
    split.
    + intros H. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *. destruct H as [a H']. destruct H'.
      subst. rewrite PermTy.supp_spec;intros;auto.
      apply Hs. eapply in_env_in_supp;eauto.
    + intros Hv. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff.
      exists v. split;auto. symmetry. apply PermTy.supp_spec.
      intros a Ha. apply Hs. eapply in_env_in_supp;eauto.
  Qed.

  Definition fresh a x := ~ V.In a (supp x).

  Definition all_fresh (vs : V.t) (x : X) := V.Disjoint vs (supp x).

  Lemma supp_action x r : supp (r @ x) = (PFin.action r) (supp x).
  Proof.
    unfold supp.
    apply FM.P.fold_rec_weak with
        (P:= fun x y =>
               En.fold (fun (_ : En.key) v v' =>
                          V.union (PermTy.supp v) v') (r @ x) V.empty =  PFin.action r y).
    + intros. apply env_extensionality in H. subst. assumption.
    + intros. reflexivity.
    + intros. unfold action. rewrite map_add;auto. rewrite FM.P.fold_add;intuition;auto.
      replace (map (PermTy.action r) m) with (r @ m) by reflexivity. rewrite H0.
      rewrite PFin.equivar_union. f_equal;intros. rewrite PermTy.supp_action. reflexivity.
      apply PermTy.supp_action.
      unfold FM.P.transpose_neqkey. intros.
      rewrite V.union_comm. rewrite V.union_assoc.
      replace (V.union a0 (PermTy.supp e0)) with
          (V.union (PermTy.supp e0) a0) by apply V.union_comm.
      reflexivity.
      apply En.map_2 in H1;auto.
  Qed.

  Lemma equivar_all_fresh : forall (vs :V.t) (x : X) (r : Perm),
      all_fresh vs x -> all_fresh (PFin.action r vs) (r @ x).
  Proof.
    intros vs x r H. unfold V.Disjoint, not in *. intros k H1.
    destruct r as [f Hf]. destruct Hf as [Hinj Hsupp].
    destruct H1 as [Hvs Hx]. rewrite supp_action in *.
    unfold PFin.action in *.
    rewrite V.set_map_iff in *. destruct Hvs as [k' Hvs']. destruct Hx.
    intuition;subst.
    (* NOTE : here we use the property that permutation is injective *)
    replace k' with x0 in * by (apply Hinj;auto).
    apply (H x0);auto.
  Qed.

  Hint Resolve map_spec En.map_1 En.map_2.

  Hint Unfold action.

  Lemma equivar_plus E E' r : (r @ (E ++ E')) = (r @ E) ++ (r @ E').
  Proof.
    apply env_extensionality_alt.
    intros. split;autounfold.
    + intros H. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff in H.
      destruct H as [a H']. destruct H' as [Heq Ha].
      rewrite FM.P.update_mapsto_iff in *.
      destruct Ha.
      * subst. left. apply En.map_1;auto.
      * destruct H. right. split.
        ** subst. apply En.map_1;auto.
        ** subst. unfold not. intros. apply H0. rewrite FM.P.F.map_in_iff in *;auto.
    + intros. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff in *.
      rewrite FM.P.update_mapsto_iff in *.
      destruct H.
      * rewrite FM.P.F.map_mapsto_iff in *.
        destruct H as [a H']. destruct H' as [Heq Ha].
        exists a. rewrite FM.P.update_mapsto_iff in *.
        intuition;auto.
      * destruct H. rewrite FM.P.F.map_mapsto_iff in *.
        destruct H as [a H']. destruct H' as [Heq Ha].
        exists a. rewrite FM.P.update_mapsto_iff in *.
        split;auto. right. rewrite FM.P.F.map_in_iff in *.
        intuition;auto.
  Qed.
End PermPlainEnv.


(* --------------------------------------- *)
(* Nominal set of semantic objects         *)
(* --------------------------------------- *)
Module PermSemOb <: NomN.NominalSet.
  Import NomN.
  Module V := Atom.V.

  Definition X := Env.

  Import VE.

  (* It is possible to define a permutation action on semantic objects as a function *)
  Fixpoint action (p : Perm) (E : X) :=
    match E with
    | EnvCtr te ve me mte => EnvCtr (PermPlainEnv.action p te)
                                    (PermPlainEnv.action p ve)
                                    (action_me p me) (action_mte p mte)
    end
  with action_me p me :=
         match me with
         | MEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           MEnvCtr {| v_size := nn;  keys := ks; vals := map (action_mod p) vs |}
         end
  with action_mte (p : Perm) mte:=
         match mte with
         | MTEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           MTEnvCtr {| v_size := nn;  keys := ks; vals := map (action_mty p) vs |}
         end
  with action_mod p (md : Mod) : Mod :=
         match md with
         | NonParamMod e => NonParamMod (action p e)
         | Ftor ts e mty => Ftor (PFin.action p ts) (action p e) (action_mty p mty)
         end
  with action_mty p (mty : MTy) : MTy :=
         match mty with
         | MSigma ts m => MSigma (PFin.action p ts) (action_mod p m)
         end.

  Notation "r @ x" := (action r x) (at level 80).

  Hint Resolve PermPlainEnv.action_id PFin.action_id.

  Lemma action_id : forall (x : X), (id_perm @ x) = x.
  Proof.
    intros x.
    induction x using Env_mut' with
        (P0 := fun me => (action_me id_perm me = me))
        (P1 := fun mte => (action_mte id_perm mte = mte))
        (P2 := fun m => (action_mod id_perm m = m))
        (P3 := fun mty => (action_mty id_perm mty = mty)); simpl;f_equal;auto.
    + destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl.
      f_equal;auto.
    + destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl.
      f_equal;auto.
  Qed.

  Lemma action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).
  Proof.
    Proof.
    intros x p p'.
    induction x using Env_mut' with
        (P0 := fun me => (action_me p (action_me p' me) = action_me (p ∘p p') me))
        (P1 := fun mte => (action_mte p (action_mte p' mte) = action_mte (p ∘p p') mte))
        (P2 := fun m => (action_mod p (action_mod p' m) = action_mod (p ∘p p') m))
        (P3 := fun mty => (action_mty p (action_mty p' mty) = action_mty (p ∘p p') mty)).
    - simpl. repeat rewrite PermPlainEnv.action_compose. rewrite IHx. rewrite IHx0. reflexivity.
    - destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl.
      f_equal;auto.
    - destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl.
      f_equal;auto.
    - simpl. congruence.
    - simpl. repeat rewrite PFin.action_compose. congruence.
    - simpl. repeat rewrite PFin.action_compose. congruence.
  Qed.

  Infix ":U:" := V.union (at level 40).

  (* This defintion works fine as well, although we call [fold_right]
     in the definition of [supp_mte] and [supp_mod], Coq is smart enough
     to figure out the decreasing argument *)
  Fixpoint supp E : V.t :=
    match E with
    | EnvCtr te ve me mte => (PermPlainEnv.supp te) :U:
                             (PermPlainEnv.supp ve) :U:
                             (supp_me me) :U:
                             (supp_mte mte)
    end
  with supp_me me :=
         match me with
         | MEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           fold_right (fun v v' => (supp_mod v) :U: v') vs V.empty
         end
  with supp_mte mte:=
         match mte with
         | MTEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           fold_right (fun v v' => (supp_mty v) :U: v') vs V.empty
         end
  with supp_mod (md : Mod) :=
         match md with
         | NonParamMod e => supp e
         | Ftor ts e mty => (PFin.supp ts) :U: (supp e) :U: (supp_mty mty)
         end
  with supp_mty (mty : MTy) :=
         match mty with
         | MSigma ts m => (PFin.supp ts) :U: (supp_mod m)
         end.

  Hint Resolve V.union_spec : set.

  Ltac solve_union_with H := apply H; repeat rewrite V.union_spec; auto with set.

  Lemma supp_spec :
    forall  (p : Perm)  (x : X),
      (forall (a : V.elt), V.In a (supp x) -> (perm p) a = a) -> (p @ x) = x.
  Proof.
    intros p.
    induction x using Env_mut' with
        (P0 := fun me =>
                 (forall (a : V.elt), V.In a (supp_me me) -> (perm p) a = a) ->
                 (action_me p me = me))
        (P1 := fun mte =>
                 (forall (a : V.elt), V.In a (supp_mte mte) -> (perm p) a = a) ->
                 (action_mte p mte = mte))
        (P2 := fun m =>
                 (forall (a : V.elt), V.In a (supp_mod m) -> (perm p) a = a) ->
                 (action_mod p m = m))
        (P3 := fun mty =>
                 (forall (a : V.elt), V.In a (supp_mty mty) -> (perm p) a = a) ->
                 (action_mty p mty = mty)).
    - intros. simpl in *. rewrite IHx; try (intros;solve_union_with H).
      rewrite IHx0; try (intros;solve_union_with H).
      repeat rewrite PermPlainEnv.supp_spec; try (intros; solve_union_with H). reflexivity.
    - intros H1. destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl in *. f_equal.
      apply H. intros; solve_union_with H1.
      apply IHvs. assumption. intros; solve_union_with H1.
    - intros H1. destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal. clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl in *. f_equal.
      apply H. intros. solve_union_with H1.
      apply IHvs. assumption. intros; solve_union_with H1.
    - intros. simpl in *. rewrite IHx;auto.
    - intros. simpl in *.
      rewrite IHx; try (intros; solve_union_with H).
      rewrite IHx0; try (intros; solve_union_with H).
      rewrite PFin.supp_spec;try (intros; solve_union_with H). reflexivity.
    - intros. simpl in *. rewrite PFin.supp_spec;try (intros; solve_union_with H).
      rewrite IHx; try (intros; solve_union_with H). reflexivity.
  Qed.

  Definition fresh x y := ~ V.In x (supp y).

  (* We also define a function that returns free variables in environment *)
  Fixpoint fvs E : V.t :=
    match E with
    | EnvCtr te ve me mte => (PermPlainEnv.supp te) :U:
                             (PermPlainEnv.supp ve) :U:
                             (fvs_me me) :U:
                             (fvs_mte mte)
    end
  with fvs_me me :=
         match me with
         | MEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           fold_right (fun v v' => (fvs_mod v) :U: v') vs V.empty
         end
  with fvs_mte mte:=
         match mte with
         | MTEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           fold_right (fun v v' => (fvs_mty v) :U: v') vs V.empty
         end
  with fvs_mod (md : Mod) :=
         match md with
         | NonParamMod e => fvs e
         | Ftor ts e mty => V.diff ((fvs e) :U: (fvs_mty mty)) ts
         end
  with fvs_mty (mty : MTy) :=
         match mty with
         | MSigma ts m => V.diff (fvs_mod m) ts
         end.
End PermSemOb.

Import EnvMod.
Import VE.
Import NomN.

Infix ":-:" := Atom.V.diff (at level 40).
Notation "r @ x" := (PFin.action r x) (at level 80) : set_scope.
Notation "r @ x" := (PermSemOb.action_mod r x) (at level 80) : env_scope.

Delimit Scope set_scope with S.
Delimit Scope env_scope with E.


(* -------------------------------------------------- *)
(* Alpha-equivalence of semantic objects in terms of  *)
(* permutations and freshness                         *)
(* -------------------------------------------------- *)
Inductive ae_env : Env -> Env -> Prop :=
| ae_env_c : forall (ve' ve : VEnv) (te' te : TEnv)
                    (me' me : MEnv) (mte' mte : MTEnv),
    ve' = ve ->
    te' = te ->
    ae_menv me' me ->
    ae_mte mte' mte ->
    ae_env (EnvCtr te' ve' me' mte') (EnvCtr te ve me mte)
  with
  ae_menv : MEnv -> MEnv -> Prop :=
  | ae_menv_c : forall (me' me : VE.VecEnv Mod),
      (forall mid (e' e : Mod),
          look mid (_to me') = Some e' ->
          look mid (_to me) = Some e ->
          ae_mod e' e) ->
      ae_menv (MEnvCtr me') (MEnvCtr me)
  with
  ae_mte : MTEnv -> MTEnv -> Prop :=
  | ae_mte_c : forall (mte' mte : VE.VecEnv MTy),
      (forall mtid (e' e : MTy),
          look mtid (_to mte') = Some e' ->
          look mtid (_to mte) = Some e ->
          ae_mty e' e) ->
      ae_mte (MTEnvCtr mte') (MTEnvCtr mte)
  with
  ae_mod : Mod -> Mod -> Prop :=
  | ae_mod_np : forall e' e,
      ae_env e' e -> ae_mod (NonParamMod e') (NonParamMod e)
  | ae_mod_ftor : forall t e e' mty mty',
      ae_env e e' ->
      ae_mty mty mty' ->
      ae_mod (Ftor t e' mty') (Ftor t e mty)
 with
 ae_mty : MTy -> MTy -> Prop :=
 | ae_mty_c : forall m m',
     forall (T T' : Atom.V.t) p,
       (forall a, Atom.V.In a ((PermSemOb.supp_mod m) :-: T)
                  -> (perm p) a = a) ->
    ae_mod (p @ m)%E m' ->
    T' = (p @ T)%S ->
    ae_mty (MSigma T' m') (MSigma T m).

Module PermIVEnv <: NomN.NominalSet.
  Import EnvMod.
  Import NomN.
  Import Atom.
  Import Coq.Program.Basics.

  Definition X := IVEnv.
  Definition singleEnv (k : tid) (t : label * Ty) : X := EnvMod.add _ k t EnvMod.empty.

  Definition action (r : Perm) (x : IVEnv) :=
    EnvMod.En.map (fun (v : label * Ty) => let (l,ty) := v in (l, (PermTy.action r) ty)) x.

  Notation "r @ x" := (action r x) (at level 80).

  Axiom action_id : forall (x : X), (id_perm @ x) = x.

  Axiom action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).

  Hint Resolve EnvMod.En.find_1 EnvMod.En.find_2
       EnvMod.En.map_1 : env.

  Definition supp (x : X) : V.t :=
    EnvMod.En.fold (fun k v v' => V.union ((PermTy.supp ∘ snd) v) v') x V.empty.
  Axiom supp_spec :
    forall  (r : Perm)  (x : X),
      (forall (a : V.elt), V.In a (supp x) -> (perm r) a = a) -> (r @ x) = x.

End PermIVEnv.

(* ---------------------------------------*)
(* Nominal set of interpretation objects  *)
(* (labels as atoms)                      *)
(* -------------------------------------- *)
Module PermIVEnvLabel <: NomN.NominalSet.
  Import EnvMod.
  Import NomN.
  Import Atom.
  Import Coq.Program.Basics.

  Definition X := IVEnv.

  Definition action (r : Perm) (x : IVEnv) : IVEnv :=
    EnvMod.En.map (fun (v : label * Ty) => let (l,ty) := v in ((perm r) l, ty)) x.

  Notation "r @ x" := (action r x) (at level 80).

  Lemma action_id : forall (x : X), (id_perm @ x) = x.
  Proof.
    intros x.
    apply EnvMod.env_extensionality_alt.
    intros. split.
    + intros H. apply EnvMod.En.find_2 in H. unfold action in *.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      destruct H as [a H']. destruct H',a. subst. simpl. auto with env.
    + intros H. unfold action in *.
      apply EnvMod.En.find_1.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      exists v. destruct v. simpl. split;auto.
  Qed.

  Lemma action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).
  Proof.
    intros x r r'.
    apply EnvMod.env_extensionality_alt. intros.
    split;unfold action in *.
    + intros H.
      apply EnvMod.En.find_1. apply EnvMod.En.find_2 in H.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *. destruct H as [a H']. destruct H'.
      subst. rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      destruct H0 as [b H0']. destruct H0'.
      subst.
      exists b. split.
      * destruct b. reflexivity.
      * destruct b. auto.
    + intros H.
      apply EnvMod.En.find_1. apply EnvMod.En.find_2 in H.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
      destruct H as [a H']. destruct H'.
      destruct a as [l ty]. simpl in *.
      exists ((perm r') l,ty).
      split.
      * auto.
      * rewrite EnvMod.FM.P.F.map_mapsto_iff in *.
        exists (l,ty). split;auto.
  Qed.


  Definition supp (x : X) : V.t :=
    EnvMod.En.fold (fun k v v' => V.union (V.singleton (fst v)) v') x V.empty.

  Lemma in_env_in_supp (E : X) k ty l :
    look k E = Some (l,ty) -> V.In l (supp E).
  Proof.
    unfold supp.
    apply FM.P.fold_rec_weak.
    + intros m m' a H H1 H2. apply env_extensionality in H. subst. auto.
    + intros He. tryfalse.
    + intros. rewrite V.union_spec in *.
      apply En.find_2 in H1. rewrite FM.P.F.add_mapsto_iff in *.
      destruct H1.
      * destruct H1. subst. simpl. auto with set.
      * destruct H1. right. apply H0; auto.
  Qed.

  Lemma supp_spec :
    forall  (r : Perm)  (x : X),
      (forall (a : V.elt), V.In a (supp x) -> (perm r) a = a) -> (r @ x) = x.
  Proof.
    intros r x Hs.
    unfold action in *.
    apply EnvMod.env_extensionality_alt. intros.
    split.
    + intros H. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite EnvMod.FM.P.F.map_mapsto_iff in *. destruct H as [a H']. destruct H'.
      subst. destruct a. rewrite Hs;auto.
      eapply in_env_in_supp;eauto.
    + intros Hv. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff.
      exists v. split;auto. destruct v. rewrite Hs. reflexivity. eapply in_env_in_supp;eauto.
  Qed.

End PermIVEnvLabel.

Module PermIEnvLabel <: NomN.NominalSet.
  Module V := AtomN.V.
  Import NomN.
  Import EnvMod.
  Import VE.

  Definition X : Type := IEnv.

  Fixpoint action (p :Perm) (ie : X) : X :=
    match ie with
    | IEnvCtr te ive ime mte => IEnvCtr te
                                        (PermIVEnvLabel.action p ive)
                                        (action_ime p ime)
                                        mte
    end
  with action_ime p ime :=
           match ime with
           | IMEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
             IMEnvCtr {| v_size := nn;  keys := ks; vals := (Vector.map (action_imod p) vs) |}
           end
  with action_imod p (md : IMod) : IMod :=
         match md with
         | INonParamMod e => INonParamMod (action p e)
         | IFtor ie ts e mty mid mexp =>
           IFtor (action p ie) ts e mty mid mexp
         end.


  Notation "r @ x" := (action r x) (at level 80).

  Lemma action_id : forall (x : X), (id_perm @ x) = x.
  Proof.
    induction x using IEnv_mut with
            (P0 := fun ime => (action_ime id_perm ime = ime))
            (P1 := fun m => (action_imod id_perm m = m)).
    - simpl. rewrite PermIVEnvLabel.action_id. rewrite IHx. reflexivity.
    - destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl.
      f_equal;auto.
    - simpl. congruence.
    - simpl. congruence.
  Qed.

  Lemma action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).
  Proof.
    intros x p p'.
    induction x using IEnv_mut with
            (P0 := fun ime => (action_ime p (action_ime p' ime) = action_ime (p ∘p p') ime))
            (P1 := fun m => (action_imod p (action_imod p' m) = action_imod (p ∘p p') m)).
    - simpl. rewrite PermIVEnvLabel.action_compose. rewrite IHx. reflexivity.
    - destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl.
      f_equal;auto.
    - simpl. congruence.
    - simpl. congruence.
  Qed.

  Infix ":U:" := V.union (at level 40).

  Fixpoint supp (ie : X) : V.t :=
    match ie with
    | IEnvCtr te ive ime mte => (PermIVEnvLabel.supp ive) :U: (supp_ime ime)
    end
  with supp_ime ime :=
         match ime with
         | IMEnvCtr {| v_size := nn;  keys := ks; vals := vs |} =>
           fold_right (fun v v' => (supp_imod v) :U: v') vs V.empty
         end
  with supp_imod (md : IMod) : V.t :=
         match md with
         | INonParamMod ie => supp ie
         | IFtor ie ts e mty mid mexp => supp ie
         end.

  Lemma supp_spec :
    forall  (p : Perm)  (x : X),
      (forall (a : V.elt), V.In a (supp x) -> (perm p) a = a) -> (p @ x) = x.
  Proof.
    intros p.
    induction x using IEnv_mut with
        (P0 := fun ime =>
                 (forall (a : V.elt), V.In a (supp_ime ime) -> (perm p) a = a) ->
                 (action_ime p ime = ime))
        (P1 := fun m =>
                 (forall (a : V.elt), V.In a (supp_imod m) -> (perm p) a = a) ->
                 (action_imod p m = m)).
    - intros. simpl in *. rewrite IHx. rewrite PermIVEnvLabel.supp_spec. reflexivity.
      intros. auto with set. auto with set.
    - intros H1. destruct t0 as [n ks vs]. simpl in *. f_equal. f_equal.
      clear ks.
      dependent induction vs; auto.
      dependent destruction H. simpl in *.
      f_equal.  apply H; auto with set. apply IHvs;auto. intros. auto with set.
    - intros. simpl. rewrite IHx;auto.
    - intros. simpl. rewrite IHx;auto.
  Qed.

  Notation "a # x" := (~ V.In a (supp x)) (at level 40) : IEnv_scope.

End PermIEnvLabel.