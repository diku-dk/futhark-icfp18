(* =========================================================== *)
(* Environments (finite maps) with extensionality.             *)
(* Uses the [FMapList] implementation from the Coq standard    *)
(* library exposed through a slightly different interface and  *)
(* extended with new methods and properties.                   *)
(* =========================================================== *)


Require Import OrderedType String FSets FMaps Sorting SetoidList ProofIrrelevance
        OrderedType Program.Equality FunctionalExtensionality.
Require Import Basics.
Require Vector.
Require Import CustomTactics.

Module Type FINMAP.
  Declare Module Key : UsualOrderedType.
  Parameter t     : Type -> Type.
  Parameter add   : forall {A:Type}, Key.t -> A -> t A -> t A.
  Parameter look  : forall {A:Type}, Key.t -> t A -> option A.
  Parameter empty : forall {A:Type}, t A.
  Parameter plus  : forall {A:Type}, t A -> t A -> t A.
  Parameter In    : forall {A:Type}, Key.t -> t A -> Prop.
  Parameter disj_envs : forall {A:Type} {B:Type}, t A -> t B -> Prop.
  Parameter map   : forall {A B :Type},  (A -> B) -> t A -> t B.
  Axiom map_spec  : forall {A B :Type} (k : Key.t) (v : A) (E : t A) (f : A -> B),
      look k E = Some v -> look k (map f E) = Some (f v).
  Parameter restrict : forall {A B :Type}, t A -> t B -> t A.
End FINMAP.

Module OrdEnv (X : UsualOrderedType) <: FINMAP.
  Module Key := X.
  Module En := FMapList.Make Key.

  Module FM := OrdProperties En.

  Definition t := En.t.

  (* ---------- *)
  (* Operations *)
  (* ---------- *)

  Definition add := En.add.
  Definition look {A : Type} := @En.find A.
  Definition empty {A} := En.empty A.
  Definition look_list {A : Type} := @En.Raw.find A.
  Definition plus {A : Type} := FM.P.update (elt:=A).
  Definition env_ext {A : Type} (X' X : t A) :=
    forall k e, look k X = Some e -> look k X' = Some e.
  Lemma env_ext_refl A (e : t A) : env_ext e e.
  Proof.
    unfold env_ext. auto.
  Qed.
  Lemma env_ext_empty A (e : t A) : env_ext e empty.
  Proof.
    unfold env_ext. intros k v H. inversion H.
  Qed.

  Definition In := En.In.

  Definition map {A B : Type}:= @En.map A B.

  Hint Resolve En.find_1 En.find_2.
  Lemma map_spec A B k v E (f : A -> B) :
    look k E = Some v -> look k (map f E) = Some (f v).
  Proof.
    intros.
    apply En.find_1. apply En.map_1. auto.
  Qed.

  (** Almost like [restrict] in the library, but our variant takes two environments,
      containing elements of different types *)
  Definition restrict {A B} (e : t A) (e' : t B) := FM.P.filter (fun k _ => En.mem k e') e.

  Definition ltk {A}:= En.Raw.PX.ltk (elt:=A).
  
  Lemma MapsTo_In {A} {E : t A} {k v} : En.MapsTo k v E -> In _ k E.
  Proof.
    intro H.
    unfold In,En.In,En.Raw.PX.In. eauto.
  Qed.

  Definition dom_subset {A B : Type} (e : t A) (e': t B) := forall k, En.In k e -> En.In k e'.

  Definition disj_envs {A B : Type} (e : t A) (e': t B) :=
    forall k, ~ (En.In k e /\ En.In k e').

  (* If env X extends X', then domain of X' is a subset of the domain of X*)
  Lemma env_ext_dom_subset {A : Type} (X X' : t A) : env_ext X X' -> dom_subset X' X.
  Proof.
    intros E.
    unfold dom_subset. intros k Hk.
    destruct Hk as [v HkvX'].
    assert (HkvX : En.MapsTo k v X). apply En.find_2. apply En.find_1 in HkvX'. apply (E _ _ HkvX').
    induction HkvX'.
    - destruct y as [k' v']. destruct H as [H1 H2]. simpl in *. subst.
      exists v'. auto.
    - auto.
  Qed.


  Notation "e ++ e'" := (plus e e') : env_scope.
  Notation "e '[[' k '|->' v ']]'" := (@add _ k v e) (at level 80) : env_scope.

  (* A sorted association list *)
  Definition sort_alist {A : Type} (l : list (En.key * A)) :=
    sort ltk l.

  (* A coercion from an evidence, that list `l` is sorted to the type `slist` *)
  Coercion lift_to_env {A : Type} {l : list (En.key*A)} (sl : sort_alist l) := En.Build_slist sl.
  Notation lift := lift_to_env.

  (* First components of key,value pair are equal *)
  Definition eq_key := @FM.O.eqk.
  (* Both components of key,value pair are equal *)
  Definition eq_keyval := @FM.O.eqke.
  (* First components are in `less than` relation  *)
  Definition lt_key {A} := @En.lt_key A.

  Definition key_eq (x y : En.key) := x = y.

  Lemma look_list_sorted A k (l : list (Key.t * A)) (sl : sort lt_key l) :
    look_list k l = look k (lift sl).
  Proof.
    reflexivity.
  Qed.

  Definition dom_subset_list {A : Type} (e e': list (Key.t * A)) :=
    forall k, InA (eq_key A) k e -> InA (eq_key A) k e'.

  Lemma eqlistA_refl A m (eql : A -> A -> Prop) :
    (forall x y, eql x y <-> x = y) ->  eqlistA eql m m.
  Proof.
    intros H.
    induction m.
    + constructor.
    + constructor. rewrite H. reflexivity. auto.
  Qed.

  Lemma equal_eqlistA :
    forall A (m m': list A) (eql : A -> A -> Prop),
      (forall x y, eql x y <-> x = y) ->
      eqlistA eql m m' <-> m = m'.
  Proof.
    intros until eql. intros Heqimpl.
    split.
    + intros H.
      induction H; auto.
      subst. assert (Heq : x = x'). rewrite <- Heqimpl. assumption.
      subst. reflexivity.
    + intro H. subst. apply eqlistA_refl. assumption.
  Qed.

  Lemma Key_compare_eq {x} : Key.compare x x = EQ eq_refl.
  Proof.
    assert (H:=FM.ME.elim_compare_eq (y:=x) eq_refl).
    destruct H as [q Heq].
    destruct q. assumption.
  Qed.

  Lemma tail_sorted {A} {r : A -> A -> Prop} {xs x} :
    sort r (x :: xs) -> sort r xs.
  Proof.
    intro H. inversion H. assumption.
  Qed.

  Open Scope env_scope.

  (* --------------------------- *)
  (* Environment extensionality  *)
  (* --------------------------- *)

  Lemma elements_extensionality A (E E' : En.t A) :
    (forall k, look k E = look k E') -> En.elements E = En.elements E'.
  Proof.
    intros.
    rewrite <- equal_eqlistA with (eql := eq_keyval A).
    + apply FM.elements_Equal_eqlistA. unfold En.Equal. apply H.
    + intros. split.
      * intro H0. inversion H0. destruct x,y; simpl in *; subst; auto.
      * intro H0. subst. compute. split;reflexivity.
  Qed.

  Lemma eq_elements_eq_envs_iff A (E E' : En.t A) : En.elements E = En.elements E' <-> E = E'.
  Proof.
    split.
    - intro H.
      destruct E as [e P]. destruct E' as [e' P'].
      generalize dependent e'.
      induction e; intros.
      + destruct e';simpl;tryfalse. f_equal. apply proof_irrelevance.
      + destruct e';simpl;tryfalse. simpl in *. inversion H. subst.
        f_equal. apply proof_irrelevance.
    - intros H. destruct E as [e p]. destruct E' as [e' p']. inversion H.
      subst. reflexivity.
  Qed.

  Lemma env_extensionality A (E E' : En.t A) :
    (forall k, look k E = look k E') <-> E = E'.
  Proof.
    split.
    - intro H. apply eq_elements_eq_envs_iff.
      apply elements_extensionality. assumption.
    - intros. congruence.
  Qed.

  (** An alternative definition of environment extensionality,
      which says that two environments should agree only on non-None values *)
  Lemma env_extensionality_alt A (E E' : En.t A) :
    (forall k v, look k E = Some v <-> look k E' = Some v) <-> E = E'.
  Proof.
    split.
    - intro H. apply env_extensionality.
      intro k. specialize H with (k := k).
      remember (look k E) as o. remember (look k E') as o'.
      destruct o'.
      * rewrite H. reflexivity.
      * destruct o.
        ** destruct (H a). destruct (H0 eq_refl). reflexivity.
        ** reflexivity.
    - intros.
      split.
      * intros. congruence.
      * congruence.
  Qed.


  (* ---------------------- *)
  (* Domain of a finite map *)
  (* ---------------------- *)

  Definition dom {A : Type} (E : En.t A) : list En.key :=
    List.map (fun p => match p with (k,_) => k end) (En.elements E).

  Lemma Empty_env_Empty_dom {A : Type} (E : En.t A) : En.Empty E -> dom E = List.nil.
  Proof.
    intros. unfold dom.
    assert (Hempty : En.elements E = List.nil). apply FM.P.elements_Empty; auto.
    rewrite Hempty. reflexivity.
  Qed.

  Lemma dom_sorted_elems A (E : En.t A) : sort lt_key (En.elements E) -> sort En.E.lt (dom E).
  Proof.
    intros Hs.
    destruct E as [Env Pr].
    induction Env.
    - rewrite Empty_env_Empty_dom; simpl; auto.
      apply FM.P.elements_Empty; auto.
    - simpl in *. unfold dom. simpl. destruct a.
      constructor.
      + inversion Pr. subst. eapply IHEnv. eauto. Unshelve. auto.
      + inversion Pr. subst. inversion H2.
        constructor.
        constructor; eauto.
  Qed.

  Hint Resolve En.elements_3.

  Lemma dom_sorted A (E : En.t A) : sort En.E.lt (dom E).
  Proof.
    apply dom_sorted_elems; auto.
  Qed.

  Lemma in_elems_in_dom_iff A (E : En.t A) k :
    (exists e, InA (En.eq_key_elt (elt:=A)) (k, e) (En.elements (elt:=A) E))
    <-> InA key_eq k (dom E).
  Proof.
    split; intro H.
    - destruct E as [Env Pr]. simpl in *.
      induction Env.
      + inversion H as [e H']. inversion H'.
      + unfold dom in *. simpl in *.
        inversion H as [e H']. inversion H'.
        * inversion H1. simpl in *. constructor. destruct a. unfold key_eq. auto.
        * apply InA_cons_tl. inversion Pr. subst.
          apply IHEnv; auto. inversion H'; subst; exists e; auto.
    - destruct E as [Env Pr]. simpl in *.
      induction Env.
      + inversion H.
      + inversion H. destruct a.
        * unfold dom in *. simpl in *.
          exists a. constructor. subst. destruct H1. reflexivity.
        * subst.
          inversion Pr as [| a' e' H' H'']. subst.
          assert (H2 := IHEnv H' H1). destruct H2 as [e Hin].
          exists e. apply InA_cons_tl; auto.
   Qed.

  Lemma in_env_in_dom_iff A (E : En.t A) k : En.In k E <-> InA key_eq k (dom E).
  Proof.
    split.
    - intro H.
      unfold En.In,En.Raw.PX.In in H. destruct H as [e H'].
      rewrite <- in_elems_in_dom_iff. exists e.
      apply En.elements_1. apply H'.
    - intro H.
      unfold En.In,En.Raw.PX.In, En.Raw.PX.MapsTo.
      rewrite -> in_elems_in_dom_iff. auto.
  Qed.

  Lemma in_env_equiv_dom A B (E : En.t A) (E' : En.t B) :
    (forall k, En.In k E <-> En.In k E') ->
    (forall k, InA key_eq k (dom E) <-> InA key_eq k (dom E')).
  Proof.
    intros. destruct (H k) as [L R].
    split.
    - intros Hin.
      assert (H' : En.In k E). rewrite in_env_in_dom_iff; auto.
      apply in_env_in_dom_iff. apply (L H').
    - intros Hin.
      assert (H' : En.In k E'). rewrite in_env_in_dom_iff; auto.
      apply in_env_in_dom_iff. apply (R H').
  Qed.

  Hint Resolve dom_sorted.

  Lemma dom_extensionality A B (E : En.t A) (E' : En.t B) :
    (forall k, En.In k E <-> En.In k E') <-> dom E = dom E'.
  Proof.
    split.
    - intros. eapply equal_eqlistA with key_eq. intros. split; intro; auto.
      eapply SortA_equivlistA_eqlistA; eauto with *.
      constructor; intros.
      + rewrite <- in_env_equiv_dom;eauto.
      + rewrite <- in_env_equiv_dom;eauto. symmetry;auto.
    - intros H k.
      split.
      + intros Hin.
        rewrite -> in_env_in_dom_iff. rewrite <- H.
        rewrite <- in_env_in_dom_iff. assumption.
      + intros Hin.
        rewrite -> in_env_in_dom_iff. rewrite -> H.
        rewrite <- in_env_in_dom_iff. assumption.
  Qed.

  Lemma dom_eq_look {A B} (k k' : Key.t) (v : A) (v' : B)
        (xs : list (Key.t * A)) (ys : list (Key.t * B))
        (sxs : sort lt_key ((k,v) :: xs)) (sys : sort lt_key ((k',v') :: ys)) :
    dom (lift sxs) = dom (lift sys) ->
    k = k' /\
    look k (lift sxs) = Some v /\
    look k' (lift sys) = Some v'.
  Proof.
    intro H.
    inversion H. subst.
    split; auto. split.
    + apply En.find_1. constructor. reflexivity.
    + apply En.find_1. constructor. reflexivity.
  Qed.

  (* NOTE: type of elements of all the environments could be distinct.
     So, we define next lemmas in most generic way with three type parameters *)
  Lemma domain_eq_l {A B C} (e : En.t A) (e' : En.t B) (e'' : En.t C) :
    dom e = dom e' -> dom_subset e e'' -> dom_subset e' e''.
  Proof.
    intros Heq Hdom.
    rewrite <- dom_extensionality in Heq.
    unfold dom_subset. intros k He'.
    destruct (Heq  k) as [L R].
    apply Hdom;auto.
  Qed.

  Lemma domain_eq_r {A B C} (e : En.t A) (e' : En.t B) (e'' : En.t C) :
    dom e' = dom e'' -> dom_subset e e' -> dom_subset e e''.
  Proof.
    intros Heq Hdom.
    rewrite <- dom_extensionality in Heq.
    unfold dom_subset. intros k He'.
    destruct (Heq  k) as [L R].
    apply L;auto.
  Qed.

  Lemma dom_add {A B} (e : En.t A) (e' : En.t B) (k : Key.t) (v : A) (v' : B) :
    dom e = dom e' -> dom (e[[k|->v]]) = dom (e'[[k|->v']]).
  Proof.
    intros Hdom.
    rewrite <- dom_extensionality in *.
    intros k'.
    destruct (Hdom k') as [L R].
    split; intros Hin; rewrite FM.P.F.add_in_iff in *; destruct Hin;auto.
  Qed.

  Lemma dom_plus {A B} (e1: En.t A) (e2 : En.t B) (e3 : En.t A) (e4 : En.t B) :
    dom e1 = dom e2 -> dom e3 = dom e4 -> dom (e1 ++ e3) = dom (e2 ++ e4).
  Proof.
    intros Hdom1 Hdom2.
    rewrite <- dom_extensionality in *.
    intros k'.
    destruct (Hdom1 k') as [L1 R1].
    destruct (Hdom2 k') as [L2 R2].
    split; intros Hin; rewrite FM.P.update_in_iff in *; destruct Hin;auto.
  Qed.
  
  (* ------------------------ *)
  (* Codomain of a finite map *)
  (* ------------------------ *)

  Definition codomain {A : Type} (oe : t A) : list A :=
    List.map (fun x => match x with (_,v) => v end) (En.elements oe).

  (* --------------------------------- *)
  (* Some properties of the operations *)
  (* --------------------------------- *)

  Hint Resolve En.map_1.
  
  Lemma map_add A B k v E (f : A -> B) :
    ~ In _ k E -> map f (add _ k v E) = add _ k (f v) (map f E).
  Proof.
    intros H.
    apply env_extensionality_alt.
    intros. split.
    + intros Hv0. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff in *. apply FM.P.F.add_mapsto_iff.
      destruct Hv0. destruct H0; subst.
      rewrite  FM.P.F.add_mapsto_iff in *. intuition;subst;auto.
    + intros Hv0. rewrite <- FM.P.F.find_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff in *. rewrite FM.P.F.add_mapsto_iff in *.
      rewrite FM.P.F.map_mapsto_iff in *.
      intuition;subst;auto. exists v. rewrite FM.P.F.add_mapsto_iff;intuition;auto.
      destruct H2 as [x Hx]. exists x. rewrite FM.P.F.add_mapsto_iff;intuition;auto.
  Qed.

  Lemma add_lookup : forall A k (v : A) E,
      look k (E[[k |-> v]]) = Some v.
  Proof.
    intros.
    apply FM.P.F.add_eq_o. reflexivity.
  Qed.

  (** NOTE: we need some properties reveling a bit of a structure 
     behind the environment representation. We are going to use that 
     in connection to pair-of-vectors representation of environments *)
  Lemma cons_add_env {A k} {v : A} {xs}
        (sxs : sort lt_key ((k,v) :: xs)) :
    lift sxs = add _ k v (lift (tail_sorted sxs)).
  Proof.
    apply env_extensionality_alt.
    intros k0 v0.
    split.
    + intros Hv0. simpl in *.
      destruct (X.compare k0 k) eqn:Hlt.
      * compute in Hv0. rewrite Hlt in Hv0.
        inversion Hv0.
      * destruct e. rewrite add_lookup.
        compute in *. rewrite Hlt in *.
        assumption.
      * compute in Hv0. rewrite Hlt in Hv0.
        clear Hlt. apply En.E.lt_not_eq in l.
        rewrite FM.P.F.add_neq_o; assumption.
    + intros Hv0.
      destruct (X.compare k0 k) eqn:Hlt.
      * rewrite FM.P.F.add_o in Hv0.
        destruct (Key.eq_dec k k0).
        ** destruct e. clear Hlt. apply En.E.lt_not_eq in l. tryfalse.
        ** apply En.find_2 in Hv0. apply MapsTo_In in Hv0.
           unfold In,En.In in Hv0. rewrite En.Raw.PX.In_alt in Hv0.
           destruct Hv0 as [v0' Hv0'].
           assert (l' := En.Raw.PX.Sort_In_cons_1 sxs Hv0').
           compute in l'.
           assert (Hk0 : X.lt k0 k0) by apply (X.lt_trans l l').
           apply FM.ME.lt_antirefl in Hk0. tryfalse.
      * destruct e. rewrite add_lookup in *.
        compute in *. rewrite Hlt in *.
        assumption.
      * compute. rewrite Hlt.
        clear Hlt. apply En.E.lt_not_eq in l.
        rewrite FM.P.F.add_neq_o in Hv0; assumption.
  Qed.

  Lemma cons_add_env_look {A k} {v : A} {xs}
        (sxs : sort lt_key ((k,v) :: xs)) :
    forall k0, look k0 (lift sxs) = look k0 (add _ k v (lift (tail_sorted sxs))).
  Proof.
    rewrite env_extensionality.
    apply cons_add_env.
  Qed.


  Lemma map_add_plus_empty_lookup: forall A E k (v : A),
      look k (E ++ (empty[[k |->v]])) = Some v.
  Proof.
    intros.
    (* NOTE: Instead of unfolding definitions here,
       we can just use properties of operations on environments *)
    apply En.find_1.
    rewrite FM.P.update_mapsto_iff.
    left. apply En.add_1. reflexivity.
  Qed.

  (* This property is easy to prove by just computing
     with concrete implementation *)
  Lemma plus_empty_r: forall {A} (e : En.t A),
    e ++ empty = e.
  Proof.
    reflexivity.
  Qed.


  (** A nice use case for environment extensionality:
      instead of proving this property by induction on
      underlying list structure (which is a bit messy
      in this case, because it involves two folds),
      we use specification of plus operation *)

  Lemma plus_empty_l: forall {A} (e : En.t A),
    empty ++ e = e.
  Proof.
    intros.
    apply env_extensionality.
    intros.
    remember (look k e) as v.
    destruct v.
    + apply En.find_1.
      rewrite FM.P.update_mapsto_iff.
      left. symmetry in Heqv. apply En.find_2.
      exact Heqv.
    + apply FM.P.F.not_find_in_iff.
      symmetry in Heqv.
      apply FM.P.F.not_find_in_iff in Heqv.
      unfold not in * . intro H.
      apply Heqv. apply FM.P.update_in_iff in H.
      destruct H.
      * inversion H. inversion H0.
      * auto.
  Qed.

  (* The same property as above, but we use an alternative formulation
     of environment extensionality *)
  Lemma plus_empty_l': forall {A} (e : En.t A),
    empty ++ e = e.
  Proof.
    intros.
    apply env_extensionality_alt.
    intros.
    split.
    + intro H. apply En.find_2 in H. rewrite FM.P.update_mapsto_iff in H.
      destruct H.
      * apply En.find_1. auto.
      * destruct H. inversion H.
    + intro H. apply En.find_2 in H.
      apply En.find_1. rewrite FM.P.update_mapsto_iff.
      left. assumption.
  Qed.

  Lemma empty_unfold A (p : sort lt_key (nil : list (En.key * A))) :
    empty = En.Build_slist p.
  Proof.
    unfold empty, En.empty. f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma OrdEnv_congr {A : Type} (l l': list (Key.t * A)) (sl : sort ltk l) (sl' : sort ltk l'):
    l = l' -> {| En.this := l; En.sorted := sl |} = {| En.this := l'; En.sorted := sl' |}.
  Proof.
    intro H. subst.
    replace sl with sl' by apply proof_irrelevance.
    reflexivity.
  Qed.

  (* ------------------------------------------ *)
  (* Extensional definition of two environments *)
  (* being related elementwise                  *)
  (* ------------------------------------------ *)
  Definition EnvRel {A B} (P : A -> B -> Prop) (E : En.t A) (E' : En.t B) : Prop :=
    (forall k, In _ k E <-> In _ k E') /\
    (forall k v v', look k E = Some v -> look k E' = Some v' -> P v v').

  Lemma EnvRel_add {A B} (P : A -> B -> Prop) (k : Key.t) (v : A) (v' : B) e e':
    EnvRel P e e' -> P v v' -> EnvRel P (e[[k|->v]]) (e'[[k|->v']]).
  Proof.
    intros Hrel Hp.
    inversion Hrel as [Hdom Hp'].    
    split.
    + rewrite dom_extensionality in *. apply dom_add;auto.
    + intros k0 v0 v0' Hv0 Hv0'.
      rewrite FM.P.F.add_o in *.
      destruct (En.E.eq_dec k k0).
      * assert (v = v0) by congruence. assert (v' = v0') by congruence.
        subst. assumption.
      * eapply Hp'; eauto.
  Qed.

  Lemma EnvRel_cons {A B} (P : A -> B -> Prop) (k : Key.t) (v : A) (v' : B)
            (xs : list (Key.t * A)) (ys : list (Key.t * B))
            (sxs : sort lt_key ((k,v) :: xs)) (sys : sort lt_key ((k,v') :: ys)) :
        EnvRel P (lift sxs) (lift sys) ->
        P v v'/\ EnvRel P (lift (tail_sorted sxs)) (lift (tail_sorted sys)).
      Proof.
        intros Hr.
        split.
        + inversion Hr as [Hdom Hp].
          apply Hp with (k0:=k);compute;rewrite Key_compare_eq;reflexivity.
        + inversion_clear Hr as [Hdom Hp].
          split.
          * rewrite dom_extensionality in *.
            inversion Hdom. assumption.
          * intros k' v0 v0' Hv0 Hv0'.
            (* NOTE : we are going to use the fact that if list [(x :: xs)] is ordered
               by a strict order [lt], then [x] doesn't occur in [xs] *)
            assert (Hnotin : ~ OrdEnv.In _ k (lift (tail_sorted sxs)))
              by (destruct xs; inversion sxs; eapply En.Raw.PX.Sort_Inf_NotIn;eauto).
            apply Hp with (k0:=k').
            ** rewrite cons_add_env.
               rewrite FM.P.F.add_o.
               destruct (Key.eq_dec k k').
               *** unfold Key.eq in e; subst. apply En.find_2 in Hv0. apply MapsTo_In in Hv0.
                   unfold OrdEnv.In in *. tryfalse.
               *** exact Hv0.
            ** unfold OrdEnv.In in *.
               rewrite cons_add_env.
               rewrite FM.P.F.add_o.
               destruct (Key.eq_dec k k').
               *** unfold Key.eq in e; subst. apply En.find_2 in Hv0 . apply MapsTo_In in Hv0 .
                   unfold OrdEnv.In in *. tryfalse.
               *** exact Hv0'.
      Qed.

  Inductive RestrictionRel {A B} (R : A -> B -> A -> Prop) : t A -> t B -> t A -> Prop :=
  | restr_of_empty    : forall e, RestrictionRel R empty e empty
  | restr_to_empty    : forall e', RestrictionRel R e' empty empty
  | restr_in  : forall e' e e'' k v v' v'',
      RestrictionRel R e' e e'' ->
      look k e' = Some v' ->
      R v' v v'' ->
      RestrictionRel R e' (add _ k v e) (add _ k v'' e'')
  | restr_not_in : forall e' e e'' k v,
      RestrictionRel R e' e e'' ->
      ~ In _ k e' ->
      RestrictionRel R e' (add _ k v e) e''.

  Lemma Empty_empty_eq {A} (e : En.t A) :
    En.Empty e -> e = empty.
  Proof.
    intro H.
    apply env_extensionality.
    intro. remember (look k e) as e'.
    destruct e'.
    * exfalso. apply (H k a). symmetry in Heqe'. apply En.find_2 in Heqe'. assumption.
    * reflexivity.
  Qed.

  Lemma Add_add_eq {A} (e e' : En.t A) k v :
    FM.P.Add k v e e' -> e' = (e[[ k |-> v ]]).
  Proof.
    intros H.
    apply env_extensionality.
    intro. remember (look k0 e') as e''.
    unfold FM.P.Add in H. rewrite <- H. assumption.
  Qed.

  Lemma env_ext_add {A} (e' e: En.t A) k v :
    ~ In _ k e -> env_ext e' e ->
    env_ext (e'[[k |-> v]]) e.
  Proof.
    intros Hnotin H.
    unfold env_ext in *.
    intros k0 v0 H0.
    assert (He' := H _ _ H0).
    apply En.find_2 in H0.
    apply MapsTo_In in H0.
    assert (Hneq : k <> k0). intro Heq. tryfalse.
    rewrite FM.P.F.add_neq_o; assumption.
  Qed.

  Lemma RestrictionRel_spec {A B} {e' e'': En.t A} {e : En.t B} {k v''}
    {R : A -> B -> A -> Prop} :
    RestrictionRel R e' e e'' -> look k e'' = Some v'' ->
    exists v v', look k e' = Some v' /\ look k e = Some v /\ R v' v v''.
  Proof.
    intros Hr Hl.
    generalize dependent k. generalize dependent v''.
    induction Hr; intros.
    + inversion Hl.
    + inversion Hl.
    + apply En.find_2 in Hl. rewrite FM.P.F.add_mapsto_iff in Hl.
      * destruct Hl as [Hl1 | Hl2].
        ** exists v,v'. intuition; subst.
           *** assumption.
           *** apply add_lookup.
           *** assumption.
        ** destruct Hl2 as [Hneq Hmaps]. apply En.find_1 in Hmaps.
           destruct (IHHr _ _ Hmaps) as [v0 Htmp]. destruct Htmp as [v0' Htmp].
           intuition. exists v0,v0'. split.
           *** assumption.
           *** split.
               rewrite FM.P.F.add_neq_o; assumption.
               assumption.
    + destruct (IHHr _ _ Hl) as [v0 Htmp].
      destruct Htmp as [v0' Htmp].
      destruct Htmp as [Hv0' Hv0].
      exists v0,v0'.
      split.
      * assumption.
      * assert (Hneq : k <> k0). intro Heq. apply En.find_2 in Hv0'. apply MapsTo_In in Hv0'. subst.
        tryfalse.
        rewrite FM.P.F.add_neq_o; assumption.
  Qed.

  Lemma RestrictionRel_dom_eq {A B} (e' e'': En.t A) (e : En.t B)
        (R : A -> B -> A -> Prop) :
    dom_subset e e' ->
    RestrictionRel R e' e e'' -> dom e = dom e''.
  Proof.
    intros Hdom H.
    apply dom_extensionality.
    intros k. split.
    + intros Hin.
      induction H.
      * apply (Hdom _ Hin).
      * inversion Hin as [v Hv]. inversion Hv.
      * rewrite FM.P.F.add_in_iff.
        destruct (Key.eq_dec k0 k);auto.
        right. apply IHRestrictionRel.
        ** unfold dom_subset. intros k' He.
           apply Hdom. rewrite FM.P.F.add_in_iff. right. auto.
        ** rewrite FM.P.F.add_in_iff in Hin. destruct Hin;tryfalse. assumption.
      * apply IHRestrictionRel;auto.
        ** unfold dom_subset. intros k' He'.
           assert (He_add : In _ k' (e [[k0 |-> v]])) by
               (rewrite FM.P.F.add_in_iff; destruct (Key.eq_dec k0 k); auto).
           assert (H' := Hdom _ He_add). assumption.
        ** assert (H' := Hdom _ Hin).
           apply FM.P.F.add_in_iff in Hin.
           unfold In in *. destruct Hin; tryfalse.
           assumption.
    + intros He''. inversion He'' as [v Hv].
      apply En.find_1 in Hv.
      assert (HH :=RestrictionRel_spec H Hv).
      destruct HH as [v0 Htmp]. destruct Htmp as [v' Htmp]. intuition.
      apply En.find_2 in H2. apply MapsTo_In in H2. assumption.
  Qed.


  (* TODO : reformulate proof in terms of RestrictionRel_spec *)
  Lemma RestrictionRel_restrict {A B} (e' e'': En.t A) (e : En.t B) k v:
    RestrictionRel (fun v' v v'' => v' = v'') e' e e'' -> look k e'' = Some v ->
    look k e' = Some v /\ In _ k e.
  Proof.
    intros Hr Hl.
    generalize dependent k. generalize dependent v.
    induction Hr; intros.
    + inversion Hl.
     + inversion Hl.
     + apply En.find_2 in Hl. rewrite FM.P.F.add_mapsto_iff in Hl.
       split.
       * destruct Hl as [Hl1 | Hl2].
         ** intuition. subst. assumption.
         ** destruct Hl2 as [Hneq Hmaps]. apply En.find_1 in Hmaps.
            destruct (IHHr _ _ Hmaps) as [Hv Hin]. assumption.
       * destruct Hl as [Hl1 | Hl2].
         ** intuition. subst. apply En.find_2 in H. apply MapsTo_In in H.
            apply FM.P.F.add_in_iff. auto.
         ** destruct Hl2 as [Hneq Hmaps]. apply En.find_1 in Hmaps.
            destruct (IHHr _ _ Hmaps) as [Hv Htmp]. destruct Htmp as [Hin Hex].
            apply MapsTo_In in Hex. apply FM.P.F.add_in_iff. auto.
     + destruct (IHHr _ _ Hl) as [Hv0 He].
       split.
       * assumption.
       * rewrite FM.P.F.add_in_iff; auto.
  Qed.

  Lemma RestrictionRel_restrict_env_ext {A B} (e' e'': En.t A) (e : En.t B) :
    RestrictionRel (fun v' v v'' => v' = v'') e' e e'' -> env_ext e' e''.
  Proof.
    unfold env_ext.
    intros H k v Hl.
    apply RestrictionRel_restrict with (k0:=k) (v0:=v) in H.
    intuition; auto. auto.
  Qed.

  Lemma RestrictionRel_dom_subset {A B} (e' e'': En.t A) (e : En.t B)
        (R : A -> B -> A -> Prop) :
    RestrictionRel R e' e e'' -> dom_subset e'' e'.
  Proof.
    intros H. unfold dom_subset. intros k Hin.
    inversion Hin as [v Hv].
    apply En.find_1 in Hv.
    assert (HH :=RestrictionRel_spec H Hv).
    destruct HH as [v0 Htmp]. destruct Htmp as [v' Htmp]. intuition.
    apply En.find_2 in H0. apply MapsTo_In in H0. assumption.
  Qed.

  Lemma RestrictionRel_restriction_exists {A B} (e': En.t A) (e : En.t B) :
    exists (e'' : En.t A), (RestrictionRel (fun _ _ _ => True) e' e e'').
  Proof.
    intros.
    generalize dependent e'.
    induction e using FM.P.map_induction; intros e'.
    * assert (e  = empty). apply Empty_empty_eq;auto. subst.
      exists empty. constructor.
    * apply Add_add_eq in H0. subst.
      destruct (IHe1 e') as [e'' He''].
      destruct (FM.P.F.In_dec e' x) as [Hin | Hnotin].
      rename e3 into v.
      inversion Hin as [v' Hv'].
      ** exists (e''[[x |-> v']]).
         eapply restr_in with (v'0:=v').
         apply He''. apply En.find_1;assumption. trivial.
      ** exists e''.  constructor;auto.
  Qed.

  Lemma RestrictionRel_exists {A B} (R : A -> B -> A -> Prop) (e': En.t A) (e : En.t B) :
    (forall v k, look k e = Some v ->
                 forall v', look k e' = Some v' -> exists v'', R v' v v'') ->
    exists (e'' : En.t A), (RestrictionRel R e' e e'').
  Proof.
    intros He.
    generalize dependent e'.
    induction e using FM.P.map_induction; intros e0.
    * assert (e = empty). apply Empty_empty_eq;auto. subst.
      exists empty. constructor.
    * apply Add_add_eq in H0. subst. intros.
      rename x into k. rename e3 into v.
      assert (Hv : look k (e1 [[k |-> v]]) = Some v) by apply add_lookup.
      assert (HH := He _ _ Hv).
      assert (HHH : forall (v : B) (k : En.key),
                 look k e1 = Some v ->
                 forall (v' : A), look k e0 = Some v' -> exists (v'' : A), R v' v v'').
      intros v0 k0 Hv0 v' Hv'.
      apply He with (k0:=k0).
      assert (Hneq : k <> k0). intro Heq. subst.
      apply En.find_2 in Hv0. apply MapsTo_In in Hv0. unfold In in Hv0. tryfalse.
      rewrite FM.P.F.add_neq_o; assumption. assumption.

      destruct (IHe1 _ HHH) as [e'' He''].
      destruct (FM.P.F.In_dec e0 k) as [Hin | Hnotin].
      ** inversion Hin as [v' Hv'].
         apply En.find_1 in Hv'.
         destruct (HH v' Hv') as [v'' Hv''].
         exists (e''[[k |-> v'']]).
         apply restr_in with (v'0:=v').
         apply He''. assumption. assumption.
      ** exists e''. constructor; auto.
  Qed.

  (* ------------------------------------------ *)
  (* Experimental: Lists sorted by construction *)
  (* ------------------------------------------ *)

  Inductive tbval (A : Type) :=
  | bot : tbval A
  | top : tbval A
  | tbval_lift : A -> tbval A.

  Definition tbval_lift' {A} := tbval_lift A.
  Definition _bot {A} := bot A.
  Definition _top {A} := top A.


  Notation "'tb[|' x '|]'" := (tbval_lift' x)(at level 20).

  Inductive R_tbval {A:Type} (R : A -> A -> Prop) : tbval A -> tbval A -> Prop :=
  | rtbval_top : forall a, R_tbval R (top A) (tb[|a|])
  | rtbval_bot : forall a, R_tbval R (tb[|a|]) (bot A)
  | rtb_val_lift : forall a b, R a b -> R_tbval R (tb[|a|]) (tb[|b|]).

  Inductive rlist {A : Type} (R : A -> A -> Prop) (l u : tbval A) :=
  | rl_nil : R_tbval R l u -> rlist R l u
  | rl_cons : forall (a : A) , rlist R (tb[|a|]) u -> R_tbval R l (tb[|a|]) -> rlist R l u.

  Inductive kvlist (K :Type) (V : Type) (R : K -> K -> Prop) (l : tbval K) :=
  | kvl_nil : kvlist K V R l
  | kvl_cons : forall (k : K),
      V -> kvlist K V R (tb[|k|]) -> R_tbval R l (tb[|k|])
      -> kvlist K V R l.

  Definition KVEnv (A : Type) := kvlist Key.t A Key.lt (bot Key.t).
  Definition OEnv (A : Type) := rlist (@lt_key A) (bot (Key.t * A)) (top (Key.t * A)).

  Definition Nat_olist := rlist (fun x y => x < y) _bot _top.

  Fixpoint rlist_to_list {A R l u} (oe : @rlist A R l u) : list A :=
    match oe with
    | rl_nil _ _ _ _ => List.nil
    | rl_cons _ _ _ a xs _ => a :: rlist_to_list xs
    end.

  Definition OEnv_to_list {A} (oe : OEnv A) := rlist_to_list oe.

  Fixpoint kvlist_to_list {K V R l} (kvl : kvlist K V R l) : list (K * V) :=
    match kvl with
    | kvl_nil _ _ _ _ => List.nil
    | kvl_cons _ _ _ _ k v xs _ => (k,v) :: kvlist_to_list xs
    end.

  Definition KVEnv_to_list {A} (e : KVEnv A) := kvlist_to_list e.

  (* ---------------------------- *)
  (* Pair-of-vectors environments *)
  (* ---------------------------- *)

  (* Environments, represented as a pair of a sorted vector of
     keys and a vector of values. This representation is isomorphic to slist *)

  Module VecEnv.

    Import Vector.
    Definition t := Vector.t.
    Notation Vec := Vector.t.
    Import VectorNotations.
    Open Scope vector_scope.


    Inductive VecHdRel {A : Type} (R : A -> A -> Prop) (a : A) : forall {n}, Vec A n -> Prop :=
      VHdRel_nil : VecHdRel R a []
    | VHdRel_cons : forall n (b : A) (l : Vec A n), R a b -> VecHdRel R a (b :: l).

    Inductive VecSorted {A : Type} (R : A -> A -> Prop) : forall {n}, Vec A n -> Prop :=
      VSorted_nil : VecSorted R []
    | VSorted_cons : forall {n} (a : A) (l : Vec A n),
        VecSorted R l -> VecHdRel R a l -> VecSorted R (a :: l).


    Notation vsort := VecSorted.
    Definition skeys n := {vs : Vec Key.t n | vsort Key.lt vs }.

    Record VecEnv (A : Type) :=
      mkVecEnv { v_size : nat;
                 keys   : skeys v_size;
                 vals   : Vec A v_size }.

    Definition ve_empty {A} : VecEnv A.
      refine (mkVecEnv _ 0 _ []). exists []. constructor.
    Defined.

    Lemma ve_empty_eq {A}: forall ks_sort,
        (ve_empty : VecEnv A) = mkVecEnv _ 0 (exist _ [] ks_sort) [].
    Proof.
      intros. unfold ve_empty. f_equal.
      f_equal. apply proof_irrelevance.
    Qed.

    (* Coercion to_vals := vals. *)
    Definition venv_to_list {A} (vs : VecEnv A) := Vector.to_list (vals _ vs).

    (* Inspired by https://github.com/mbrcknl/ylj15-coq-pattern-match/blob/master/vec.v *)

    Definition uncons {A: Type} {m: nat} (v: Vec A (S m)): A * Vec A m :=
        match v in Vec _ j return
              match j with
                | O   => unit
                | S i => A * Vec A i
              end
        with
          | []         => tt
          | x :: xt => (x, xt)
        end.

    Definition vzip {A B : Type} : forall {n}, Vec A n -> Vec B n -> Vec (A * B) n :=
      fix zip {n} vs := match vs in Vec _ m return Vec B m -> Vec (A * B) m with
      | [] => fun vs' => []
      | cons _ v n0 tl =>
        fun vs' =>
          (match vs' in Vec _ m' return
                 (S n0 = m' -> match m' with 0 => (unit : Type) | S _ => Vec _ _ end) with
           | [] => fun _ => tt
           | cons _ v' _ tl' =>
             fun H =>
               cons _ (v,v') _ (zip tl (transport (eq_add_S _ _ (eq_sym H)) tl'))
           end) eq_refl
                        end.

    Definition vzip' {n} {A B : Type} (vp : Vec A n * Vec B n) := prod_curry vzip vp.

    Lemma vzip_step' {n A B} (a : A) (b : B) (vs : Vec A n) (vs' : Vec B n) :
      vzip' (a :: vs, b :: vs') = (a,b) :: vzip vs vs'.
    Proof.
      reflexivity.
    Qed.

    Lemma vzip_vzip'_eq {n} {A B : Type} (p : Vec A n * Vec B n) :
      vzip' p = vzip (fst p) (snd p).
    Proof.
      unfold vzip'. destruct p. simpl. reflexivity.
    Qed.

    Definition vunzip {A B : Type} :
      forall {n}, (Vec (A * B)%type n) -> (Vec A n * Vec B n)%type :=
      fix unzip {n} vs := match vs with
      | [] => ([],[])
      | (a,b) :: tl => (a :: fst (unzip tl), b :: snd (unzip tl))
      end.

    Definition rel_fst {A B : Type} (R : A -> A -> Prop) (p p' : A * B) :=
      R (fst p) (fst p').
    
    Lemma vzip_sorted {n A R} (ks : Vec Key.t n) (vs : Vec A n) :
      vsort R ks -> vsort (rel_fst R) (vzip ks vs).
    Proof.
      intros H.
      induction H.
      + constructor.
      + dependent destruction vs.
        simpl. constructor. auto.
        dependent destruction l.
        - constructor.
        - dependent destruction vs. simpl.
          constructor. inversion H0. subst. auto.
    Qed.

    Lemma to_list_sorted {n A R} (vs : Vec A n) : vsort R vs -> sort R (to_list vs).
    Proof.
      intros H.
      dependent induction vs.
      + constructor.
      + dependent destruction H. simpl. constructor.
        - apply IHvs. assumption.
        - dependent destruction vs.
          * constructor.
          * simpl. constructor. dependent destruction H0. assumption.
    Qed.

    Definition toOrdEnv {A : Type} (ve : VecEnv A) : En.t A :=
     match ve with
     | mkVecEnv _ _ (exist _ ks sorted_ks) vs =>
       let skvs := vzip_sorted ks vs sorted_ks
       in En.Build_slist (to_list_sorted (vzip' (ks,vs)) skvs)
     end.

    Lemma toOrdEnv_fold_unfold {A : Type} n ks s_ks vs :
      toOrdEnv (mkVecEnv A n (@exist _ _ ks s_ks) vs) =
      lift_to_env (to_list_sorted (vzip ks vs) (vzip_sorted ks vs s_ks)).
    Proof. reflexivity. Qed.

    Lemma of_list_sorted {A R} (xs : list A) : sort R xs -> vsort R (of_list xs).
    Proof.
      intro H.
      induction H as [| a tl Htl IHs Hhdrel].
      + constructor.
      + simpl. constructor.
        * assumption.
        * destruct tl.
          ** constructor.
          ** simpl. inversion Hhdrel. constructor;auto.
    Qed.

    Lemma vunzip_sorted {n A B R} (kvs : Vec (A * B) n) :
      vsort (rel_fst R) kvs
      -> vsort R (fst (vunzip kvs)).
    Proof.
      intros H.
      dependent induction H.
      + constructor.
      + simpl in *. destruct a. remember (vunzip l) as un.
        destruct un. constructor.
        * eapply IHVecSorted.
        * dependent destruction l.
          ** simpl in *. inversion Hequn. constructor.
          ** simpl in *. destruct h. simpl in *. dependent destruction H0.
             remember (vunzip l) as un2.
             destruct un2. inversion Hequn.
             constructor. apply H0.
    Qed.

    Lemma vunzip_vzip_inv {n A B} (vs : Vec A n) (vs' : Vec B n) :
      vunzip (vzip vs vs') = (vs, vs').
    Proof.
      induction vs.
      + dependent destruction vs'. reflexivity.
      + dependent destruction vs'. simpl. rewrite IHvs.
        reflexivity.
    Qed.

    Lemma vunzip_vzip_inv' {n A B} (vp : Vec A n * Vec B n) :
      vunzip (vzip' vp) = vp.
    Proof.
      destruct vp.
      apply vunzip_vzip_inv.
    Qed.

    Lemma vzip_vunzip_inv {n A B} (kvs : Vec (A*B) n) :
      (fun p => vzip (fst p) (snd p)) (vunzip kvs) = kvs.
    Proof.
      induction kvs.
      + reflexivity.
      + simpl in *. destruct h. simpl. rewrite IHkvs.
        reflexivity.
    Qed.

    Lemma vzip_vunzip_inv' {n A B} (kvs : Vec (A*B) n) :
      vzip' (vunzip kvs) = kvs.
    Proof.
      induction kvs.
      + reflexivity.
      + simpl in *. destruct h. simpl. rewrite <- vzip_vzip'_eq.  rewrite IHkvs.
        reflexivity.
    Qed.

    Hint Resolve of_list_sorted to_list_sorted vzip_sorted vunzip_vzip_inv vzip_vunzip_inv.
    (* NOTE : It is crucial to have this definition transparent      *)
    (*        (it ends with Defined, instead of Qed)                 *)
    (* This way, we make the term witnessing the equality  available *)
    (* for reduction.                                                *)
    Definition to_list_length {n A} (vs : Vec A n) : n = length (to_list vs).
    Proof.
      induction vs.
      + reflexivity.
      + simpl. unfold to_list in IHvs. rewrite <- IHvs. reflexivity.
    Defined.

    Definition slist_to_list {A} (sl : En.t A) :=
      match sl with @En.Build_slist _ xs _ => xs end.

    Definition fromOrdEnv {A : Type} (oe : En.t A) : VecEnv A :=
      match oe with
           @En.Build_slist _ xs xs_sort =>
           let kvs := vunzip (of_list xs) in
           let vs := snd kvs in
           let skvs := vunzip_sorted (of_list xs) (of_list_sorted _ xs_sort)  in
           mkVecEnv A _ (exist _ (fst kvs) skvs) vs
      end.

    Arguments fromOrdEnv A oe : simpl never.

    Coercion to_key_list {n} (ks : skeys n) :=
      match ks with
        exist _ ks _ => ks
      end.

    Lemma transport_cons {n m A} (vs : Vec A n) (a : A) (p : n = m):
      transport (ap S p) (a :: vs) =
      a :: transport p vs.
    Proof.
      destruct p. reflexivity.
    Qed.

    (* Taken from the Vector module of Coq stdlib *)
    Lemma to_list_of_list_opp {A} (l: list A): to_list (of_list l) = l.
    Proof.
      induction l.
      - reflexivity.
      - unfold to_list; simpl. f_equal. apply IHl.
    Qed.

    Lemma of_list_to_list_inv {n A} (vs : Vec A n) :
      of_list (to_list vs) = transport (to_list_length vs) vs.
    Proof.
      induction vs.
      + reflexivity.
      + replace (of_list (to_list (h :: vs))) with (h :: of_list (to_list vs)) by reflexivity.
        replace (to_list_length (h :: vs)) with (ap S (to_list_length vs)) by reflexivity.
        rewrite transport_cons with (p:=to_list_length vs).
        rewrite <-IHvs. reflexivity.
    Qed.
    
    Lemma toOrdEnv_fromOrdEnv_inv {A : Type} (oe : En.t A) :
      (toOrdEnv (fromOrdEnv oe)) = oe.
    Proof.
      destruct oe.
      simpl.
      assert (H : this = to_list (vzip (fst (vunzip (of_list this)))
                                       (snd (vunzip (of_list this))))).
      rewrite <- vzip_vzip'_eq.
      rewrite vzip_vunzip_inv'. rewrite to_list_of_list_opp. reflexivity.

      apply OrdEnv_congr. auto.
    Qed.

    Definition VecEnv_congr {A} n n'
               (ks : Vec Key.t n) (ks_sort : vsort Key.lt ks)
               (ks' : Vec Key.t n') (ks_sort' : vsort Key.lt ks')
               (vs : Vec A n) (vs' : Vec A n') (p : n = n') :
      (transport p ks) = ks' ->
      (transport p vs) = vs' ->
      {| v_size := n;  keys := exist _ ks ks_sort;   vals := vs |} =
      {| v_size := n'; keys := exist _ ks' ks_sort'; vals := vs' |}.
    Proof.
      intros.
      destruct p.
      simpl in *. subst.
      replace ks_sort with ks_sort' by apply proof_irrelevance.
      reflexivity.
    Qed.

    Lemma to_list_injective {n A} {vs vs' : Vec A n} :
      to_list vs = to_list vs' -> vs = vs'.
    Proof.
      intros Heq.
      dependent induction vs.
      + dependent destruction vs';reflexivity.
      + dependent destruction vs'.
        inversion Heq.
        f_equal;auto.
    Qed.

    Lemma vzip_injective {n A B} {vs ws : Vec A n} {vs' ws' : Vec B n} :
      vzip vs vs' = vzip ws ws' -> vs = ws /\ vs' = ws'.
    Proof.
      intros Heq.
      dependent induction vs;
        dependent destruction ws; dependent destruction vs'; dependent destruction ws'.
      + auto.
      + simpl in *. dependent destruction Heq.
        assert (H := IHvs _ _ _ x).
        intuition;subst;auto.
     Qed.

    Lemma toOrdEnv_injective {A : Type} (ve ve' : VecEnv A) :
      toOrdEnv ve = toOrdEnv ve' -> ve = ve'.
    Proof.
      intro H.
      destruct ve,ve'. destruct keys0,keys1. simpl in *. inversion H.
      assert (Hsize := ap (length (A:=_)) H1).
      repeat rewrite <- to_list_length in Hsize.
      subst.
      assert (H2 := vzip_injective (to_list_injective H1)). destruct H2.
      apply VecEnv_congr with (p := eq_refl); auto.
    Qed.

    Open Scope program_scope.
    
    Lemma fromOrdEnv_toOrdEnv_inv {A : Type} (ve : VecEnv A) :
      (fromOrdEnv (toOrdEnv ve)) = ve.
    Proof.
      destruct ve as [n ks vs]. destruct ks as [ks' ks_sort].
      simpl. remember (to_list_length (vzip ks' vs)) as q.
      unfold fromOrdEnv. simpl.
      apply VecEnv_congr with (p:=eq_sym q).
      + rewrite <- @move_transport with
            (f:=fun n v => fst (@vunzip _ _ n v)).
        subst.
        rewrite of_list_to_list_inv in *.
        rewrite transp_concat.
        rewrite concat_inv_r.
        simpl. rewrite vunzip_vzip_inv.
        reflexivity.
      + rewrite <- @move_transport with
            (f:=fun n v => snd (@vunzip _ _ n v)).
        subst.
        rewrite of_list_to_list_inv in *.
        rewrite transp_concat.
        rewrite concat_inv_r.
        simpl. rewrite vunzip_vzip_inv.
        reflexivity.
    Qed.

    Coercion _to {A} := toOrdEnv (A:=A).
    Coercion _from {A} := fromOrdEnv (A:=A).


    Lemma to_empty {A : Type} : toOrdEnv (A:=A) ve_empty = empty.
    Proof.
      simpl. unfold empty, En.empty.
      compute. f_equal. apply proof_irrelevance.
    Qed.

    Lemma from_empty {A : Type} : fromOrdEnv (A:=A) empty = ve_empty.
    Proof.
      compute. f_equal. f_equal.
      apply proof_irrelevance.
    Qed.

    (*  -------------------------------------------------------------- *)
    (*  Different ways to quantify over the elements of a vector and   *)
    (*  values in a vector environment along with conversion between   *)
    (*  these definitions.                                             *)
    (* --------------------------------------------------------------- *)
    Module Foralls.
      Definition Forall_fix :=
        fix ff {A n} (P : A -> Prop) (vs : Vec A n) : Prop :=
          match vs with
          | [] => True
          | v :: tl  =>
            ff P tl /\  P v
          end.

      Lemma Forall_Forall_fix_iff A n (P : A -> Prop) (vs : Vec A n) :
        Forall_fix P vs <-> Forall P vs.
      Proof.
        split.
        + intro H.
          induction vs.
          * constructor.
          * destruct H. constructor; auto.
        + intro H.
          induction H.
          * simpl. trivial.
          * simpl. split; auto.
      Qed.

      Fixpoint Forall2_fix {A B} (P : A -> B -> Prop) (n n' : nat)
               (l : Vec A n) (ll : Vec B n') : Prop :=
        match l,ll with
        | [],[] => True
        | m :: tl, im :: tl'  =>
          Forall2_fix P _ _ tl tl'  /\  P m im
        | _,_ => False
        end.

      Lemma Forall2_Forall2_fix_iff A B n (P : A -> B -> Prop) (vs : Vec A n) (vs' : Vec B n) :
        Forall2_fix P _ _ vs vs' <-> Forall2 P vs vs'.
      Proof.
        split.
        + intros H.
          dependent induction vs;dependent destruction vs'.
          * constructor.
          * simpl in  H. destruct H.
            constructor.
            ** assumption.
            ** apply IHvs;auto.
        + intros H. dependent induction H;simpl;auto.
      Qed.

      Definition ForallEnv2_fix {A B} (P : A -> B -> Prop)
                 (ve : VecEnv.VecEnv A) (ve' : VecEnv.VecEnv B) :=
        match ve,ve' with
          VecEnv.mkVecEnv _  n (exist _ ks _) vs,
          VecEnv.mkVecEnv _  n' (exist _ ks' _) vs' => Forall2_fix P n n' vs vs'
        end.

      Lemma ForallEnv2_fix_EnvRel_iff A B
            (P : A -> B -> Prop) (ve : VecEnv A) (ve' : VecEnv B) :
        (dom ve = dom ve' /\ ForallEnv2_fix P ve ve') <-> EnvRel P ve ve'.
      Proof.
        split.
        + intro H0.
        destruct H0 as [Hdom Hf].
        unfold EnvRel.
        split.
        * apply dom_extensionality. assumption.
        * intros. destruct ve as [n ks vs]. destruct ve' as [n' ks' vs'].
          destruct ks,ks'. simpl in *.
          dependent induction vs.
          ** destruct vs'.
             *** dependent destruction x.
                 simpl in *. inversion H.
             *** tryfalse.
          ** dependent destruction vs';tryfalse.
             dependent destruction x. dependent destruction x0. simpl in *.
             (* Here, we are switching from [cons] operation on the underlying list representation
                to [add] operation of environment *)
             remember (to_list_sorted ((h, h0) :: vzip x vs)
                                      (vzip_sorted (h :: x) (h0 :: vs) v0)) as svs.
             rewrite cons_add_env_look with (sxs:=svs) in H.
             remember (to_list_sorted ((h1, h2) :: vzip x0 vs')
                                      (vzip_sorted (h1 :: x0) (h2 :: vs') v1)) as svs'.
             rewrite cons_add_env_look with (sxs:=svs') in H0.
             inversion Hdom. subst.
             destruct Hf.
             rewrite FM.P.F.add_o in *.
             destruct (Key.eq_dec h1 k).
             *** destruct e.
                 assert (Heq1 : h0 = v) by congruence.
                 assert (Heq2 : h2 = v') by congruence.
                 subst. auto.
             *** dependent destruction v0.
                 dependent destruction v1.
                 apply IHvs with (k:=k) (vs':=vs') (x:=x) (x0:=x0) (v0:=v0) (v1:=v1);auto.
        + intros.
          split.
          * destruct H. apply dom_extensionality; auto.
          * destruct ve,ve',keys0,keys1. simpl in *.
            dependent induction vals0.
            ** destruct H. apply dom_extensionality in H.
               destruct vals1.
               *** simpl;trivial.
               *** (* NOTE: here we use the information about vectors length
                      from the types of vectors to prove this case by
                      explosion on the hypothesis about equality of domains.
                      Without length information in vector types we would
                      have to add length constraint on components of
                      VecEnv to the statement of the lemma *)
                 dependent destruction x; dependent destruction x0.
                 tryfalse.
            ** intros; simpl in *.
               dependent destruction vals1; dependent destruction x; dependent destruction x0.
               (* NOTE : the same applies here: we use information encoded in dependent type
                  of vectors *)
               *** inversion H. apply dom_extensionality in H0. simpl in H0. tryfalse.
               *** assert (h = h1) by (inversion H; apply dom_extensionality in H0; inversion H0;
                                       reflexivity).
                   subst.
                   eapply EnvRel_cons in H.
                   destruct H as [Hp Hr].
                   dependent destruction v. dependent destruction v0.
                   split;auto.
                   eapply IHvals0 with (v:=v) (v0:=v0);eauto.
      Qed.

      Lemma ForallEnv2_fix_EnvRel_iff' A B
            (P : A -> B -> Prop) (ve : VecEnv A) (ve' : VecEnv B) (e : En.t A) (e' : En.t B) :
        e = _to ve -> e' = _to ve' ->
        (dom e = dom e' /\ ForallEnv2_fix P ve ve') <-> EnvRel P e e'.
      Proof.
        intros. subst. apply ForallEnv2_fix_EnvRel_iff.
      Qed.

      Lemma Forall2_fix_fold_unfold {A B} (P : A -> B -> Prop) :
        Forall2_fix P =
        (fix ff {n n'} (l : Vec A n) (ll : Vec B n') : Prop :=
           match l,ll with
           | [],[] => True
           | v :: tl, v' :: tl'  =>
             ff tl tl' /\ P v v'
           | _,_ => False
           end).
      Proof.
        extensionality n. extensionality n'. extensionality vs. extensionality vs'.
        generalize dependent vs'. generalize dependent n'.
        dependent induction vs.
        + dependent destruction vs'; reflexivity.
        + dependent destruction vs'.
          * reflexivity.
          * simpl. rewrite <- IHvs. reflexivity.
      Qed.

      Lemma ForallEnv2_fold_unfold {A B} (P : A -> B -> Prop) ve ve' :
        ForallEnv2_fix P ve ve'=
        match ve,ve' with
          VecEnv.mkVecEnv _  n (exist _ ks _) vs,
          VecEnv.mkVecEnv _  n' (exist _ ks' _) vs' => Forall2_fix P n n' vs vs'
        end.
      Proof.
        reflexivity.
      Qed.

      (* NOTE: sometimes, pattern matching in the definition of [ForallEnv2_fold_unfold]
         reduces to something of different shape and makes it impossible to apply original lemma.
         We replace pattern matching with propositional equalities that makes this lemma
         less restrictive for rewriting than [ForallEnv2_fold_unfold] *)
      Lemma ForallEnv2_fold_unfold' {A B} (P : A -> B -> Prop) ve ve' n n'
            ks ks' sks sks' vs vs':
        ve = VecEnv.mkVecEnv _  n (exist _ ks sks) vs ->
        ve' = VecEnv.mkVecEnv _  n' (exist _ ks' sks') vs' ->
        ForallEnv2_fix P ve ve'=  Forall2_fix P n n' vs vs'.
      Proof.
        intros. subst. reflexivity.
      Qed.


      Lemma Forall_nested_cons n A B (v' : B)
            (vs : Vec A n) (vs' : Vec B n) (P : A -> B -> Prop):
        Forall (fun v : A => Forall (P v) (v' :: vs')) vs ->
        Forall (fun v : A => Forall (P v) (vs')) vs.
      Proof.
        intros H.
        induction H.
        + constructor.
        + constructor. inversion H. dependent destruction H3. assumption.
          assumption.
      Qed.

      (* Lemma Forall2_nested_look n A B (v' : B) *)
      (*       (vs : Vec A n) (vs' : Vec B n) (P : A -> B -> Prop): *)
      (*       Forall2 (fun k v => forall v', look k ve' = Some v' -> P v v') -> *)
      (*       Forall2 (fun k v : A => Forall (P v) (vs')) vs. *)
      (* Proof. *)
      (*   intros H. *)
      (*   induction H. *)
      (*   + constructor. *)
      (*   + constructor. inversion H. dependent destruction H3. assumption. *)
      (*     assumption. *)
      (* Qed. *)

      Set Printing Coercions.

      Lemma Forall_EnvRel {A B} {ve : VecEnv.VecEnv A} {ve' : VecEnv.VecEnv B}
            {P : A -> B -> Prop} :
        dom ve = dom ve' ->
        Forall (fun v => forall v', P v v') (VecEnv.vals _ ve) ->
        EnvRel P ve ve'.
      Proof.
        destruct ve as [n ks vs]. destruct ve' as [n' ks' vs']. destruct ks,ks'. simpl.
        intro Hdom.
        intro H.
        unfold EnvRel. split. rewrite dom_extensionality. auto.
        generalize dependent vs'. generalize dependent x0.
        dependent induction vs.
        + intros; destruct x0; dependent destruction x.
          * simpl. tryfalse.
          * dependent destruction vs'. inversion Hdom.
        + intros. dependent destruction vs'.
          * dependent destruction x0; dependent destruction x. tryfalse.
          * dependent destruction x0; dependent destruction x. inversion Hdom. subst.
            simpl in *. dependent destruction H.
            remember (to_list_sorted ((h1, h0) :: vzip x vs)
                                     (vzip_sorted (h1 :: x) (h0 :: vs) v)) as svs.
            rewrite cons_add_env_look with (sxs:=svs) in H1.
            remember (to_list_sorted ((h1, h2) :: vzip x0 vs')
                                     (vzip_sorted (h1 :: x0) (h2 :: vs') v0)) as svs'.
            rewrite cons_add_env_look with (sxs:=svs') in H2.
            rewrite FM.P.F.add_o in *.
            destruct (Key.eq_dec h1 k).
            ** destruct e.
               assert (Heq1 : h0 = v1) by congruence.
               assert (Heq2 : h2 = v') by congruence.
               subst. apply H.
            ** dependent destruction v. dependent destruction v0.
               eapply IHvs with (k:=k) (vs':=vs') (x:=x) (x0:=x0) (v0:=v0) (v:=v); auto.
      Qed.

      Lemma Forall_forall_vals {A} {ve : VecEnv.VecEnv A} {P : A -> Prop} :
        Forall (fun v => P v) (vals _ ve) -> (forall k v, look k ve = Some v -> P v).
      Proof.
        intros Hve k v Hv.
        destruct ve as [n ks' vs]. destruct ks' as [ks ks_sort].
        dependent induction vs.
        + simpl in *.
          dependent destruction ks. tryfalse.
        + simpl in *. dependent destruction Hve.
          dependent destruction ks.
          assert (ks_sort':=ks_sort).
          dependent destruction ks_sort.
          rename h into k'. simpl in *.
          remember (to_list_sorted
                      ((k', h0) :: vzip ks vs)
                      (vzip_sorted (k' :: ks) (h0 :: vs)
                                   (VSorted_cons Key.lt k' ks ks_sort v))) as svs.
          rewrite cons_add_env_look with (sxs:=svs) in Hv.
          rewrite FM.P.F.add_o in *.
          destruct (Key.eq_dec k' k).
          * destruct e. inversion Hv. subst. assumption.
          * eapply IHvs with (ks:=ks) (k:=k) (ks_sort:=ks_sort);eauto.
      Qed.

    End Foralls.

  End VecEnv.


End OrdEnv.

Module EnvCoercionExpamples.
  Module NatDomEnv := (OrdEnv Nat_as_OT).
  Import NatDomEnv.
  Open Scope env_scope.

  (* Now, we can apply regular operations available for environments to sorted lists *)
  Import ListNotations.
  Definition l0 := [(0,0);(1,1)].
  Lemma sl_0 : sort_alist l0.
  Proof. repeat constructor. Qed.

  Definition plusL0 := sl_0 ++ sl_0.

  Definition addL0 := sl_0 [[2 |-> 2]].

End EnvCoercionExpamples.
