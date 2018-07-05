(*===================================== *)
(* Basic definitions for nominal sets.  *)
(*===================================== *)

Require Import MSets SetExt CustomTactics Eqdep_dec Bool
        FunctionalExtensionality ProofIrrelevance.


(* ----------------------------------- *)
(* Set of atoms                        *)
(* ----------------------------------- *)

(* We assume that there exists some countably infinite set of
  variables - atoms. It could be instantiated, for example with
  natural numbers. Then the existence of an element [x] in [Atom_inf]
  can be witnessed as [(max(X) + 1)] *)

Module Type Atom.
  Declare Module V : SetExtT.
  Axiom Atom_inf : forall (X : V.t), {x : V.elt | ~ V.In x X}.
End Atom.

Module Nominal (A : Atom).
  Module Atom := A.
  Import A.
  Module SetFacts := WFacts V.
  Module SetProperties := OrdProperties V.

  Open Scope program_scope.

  Definition is_inj  {A B : Type} (f : A -> B) : Prop :=
    forall (x y : A), f x = f y -> x = y.
  Definition is_surj {A B : Type} (f : A -> B) : Prop :=
    forall (y : B), exists (x : A), f x = y.

  Hint Unfold is_inj is_surj.

  Lemma inj_comp_inj {A B C: Type} (f : A -> B) (g : B -> C) :
    is_inj f -> is_inj g -> (is_inj (g ∘ f)).
  Proof.
    unfold is_inj. intros. auto.
  Qed.

  Lemma surj_comp_surj {A B C: Type} (f : A -> B) (g : B -> C) :
    is_surj f -> is_surj g -> (is_surj (g ∘ f)).
  Proof.
    autounfold. intros H H1 c.
    destruct (H1 c) as [b Hb].
    destruct (H b) as [a Ha].
    exists a; congruence.
  Qed.

  Lemma eq_leibniz_1 x y :  x = y -> V.E.eq x y.
  Proof.
    intros. subst.
    destruct (V.E.eq_equiv).
    apply Equivalence_Reflexive.
  Qed.

  Hint Resolve V.E.eq_leibniz eq_leibniz_1.

  Lemma eq_leibniz_iff x y : V.E.eq x y <-> x=y.
  Proof.
    split;auto.
  Qed.

  (* ----------------------------------- *)
  (* Definition of finitary permutations *)
  (* ----------------------------------- *)

  Definition is_biject {A B} (f : A -> B) :=
    (is_inj f) /\ (is_surj f).

  Definition has_fin_supp f := exists S, (forall t, ~ V.In t S -> f t = t).

  Record Perm :=
      { perm : V.elt -> V.elt;
        is_biject_perm :  is_biject perm;
        has_fin_supp_perm : has_fin_supp perm}.
  
  Lemma perm_eq (p1 p2 : Perm) : perm p1 = perm p2 -> p1 = p2.
  Proof.
    intros.
    destruct p1 as [f b f_s].
    destruct p2 as [f' b' f_s'].
    simpl in *. subst. destruct f_s. destruct f_s'. subst. f_equal.
    apply proof_irrelevance. apply proof_irrelevance.
  Qed.

  Definition id_perm : Perm.
      refine ({| perm:=id; is_biject_perm := _; has_fin_supp_perm := _ |}).
      + split. auto. refine (fun y => ex_intro _ y _);reflexivity.
      + exists V.empty;intros;auto.
  Defined.

  Definition perm_comp (r r' : Perm) : Perm.
    refine ({| perm:= (perm r) ∘ (perm r'); is_biject_perm := _; has_fin_supp_perm := _ |}).
    + split.
      * intros.
        destruct r as [f b f_s].
        destruct r' as [f' b' f_s'].
        destruct b,b'. unfold is_inj in *.
        simpl. apply inj_comp_inj; intuition; auto.
      * intros.
        destruct r as [f b f_s].
        destruct r' as [f' b' f_s'].
        destruct b,b'. unfold is_surj in *. 
        simpl. intros. apply surj_comp_surj;intuition; auto.
    + destruct r as [f b f_s].
      destruct r' as [f' b' f_s'].
      simpl. destruct f_s as [x Hx]. destruct f_s' as [x' Hx'].
      exists (V.union x x'). intros. unfold compose.
      rewrite Hx';auto with set.
  Defined.
  Notation "r ∘p r'" := (perm_comp r r') (at level 40).


  
  (* -------------- *)
  (* Swapping atoms *)
  (* -------------- *)

  (* Swapping two atoms is a simpliest permutation *)
  Definition swap_fn (a b c : V.elt) : V.elt :=
    if (V.E.eq_dec a c) then b
      else (if (V.E.eq_dec b c) then a
        else c).

  Hint Unfold swap_fn.

  Lemma is_inj_swap_fn a b : is_inj (swap_fn a b).
  Proof.
    autounfold. intros c1 c2 Heq.
    destruct (V.E.eq_dec a c1); destruct (V.E.eq_dec b c1);
      destruct (V.E.eq_dec a c2); destruct (V.E.eq_dec b c2);
        intros; repeat rewrite eq_leibniz_iff in *; congruence.
  Qed.

  Lemma is_surj_swap_fn a b : is_surj (swap_fn a b).
  Proof.
    intros c. autounfold.
    remember (if (V.E.eq_dec a c) then b
                              else (if (V.E.eq_dec b c) then a
                                    else c)) as c'.
    exists c'. subst.
    destruct (V.E.eq_dec a c); destruct (V.E.eq_dec b c);
      destruct (V.E.eq_dec b b);destruct (V.E.eq_dec a a);
      destruct (V.E.eq_dec a b);
        destruct (V.E.eq_dec a c); destruct (V.E.eq_dec b c);
      repeat rewrite eq_leibniz_iff in *;
      subst;tryfalse;auto.
  Qed.

  Lemma id_swap_fn a b c :
    ~ V.In c (V.union (V.singleton a) (V.singleton b)) -> swap_fn a b c = c.
  Proof.
    intros Hc. autounfold.
      destruct (V.E.eq_dec a c); destruct (V.E.eq_dec b c);auto with set;
        exfalso; auto with set.
  Qed.

  Lemma has_fin_supp_swap_fn a b : has_fin_supp (swap_fn a b).
  Proof.
    autounfold.
    exists (V.union (V.singleton a) (V.singleton b)).
    apply id_swap_fn.
  Qed.

  Lemma is_biject_swap_fn a b : is_biject (swap_fn a b).
  Proof.
    split.
    + apply is_inj_swap_fn.
    + apply is_surj_swap_fn.
  Qed.

  Definition swap (a b : V.elt) : Perm :=
    {| perm := swap_fn a b;
       is_biject_perm := is_biject_swap_fn _ _;
       has_fin_supp_perm  := has_fin_supp_swap_fn a b|}.

  Import ListNotations.

  Fixpoint zip {A B} (xs : list A) (ys : list B) : list (A * B) :=
    match xs, ys with
    | (x::xs'), (y::ys') => (x, y) :: zip xs' ys'
    | _, _ => []
    end.

  (* Swapping bunch of atoms as a composition of primitive swaps *)
  Definition swap_iter_fn (vs : list (V.elt * V.elt)) : V.elt -> V.elt :=
    fold_right (fun (e' : (V.elt * V.elt)) (f : V.elt -> V.elt) =>
                  let (e1,e2) := e' in f ∘ (swap_fn e1 e2)) id vs.

  Hint Resolve inj_comp_inj is_inj_swap_fn.

  Lemma swap_iter_fn_inj vs : is_inj (swap_iter_fn vs).
  Proof.
    induction vs;autounfold;intros x y H.
    + auto.
    + destruct a;simpl in *.
      assert (is_inj (swap_iter_fn vs ∘ swap_fn e e0));auto.
  Qed.

  Hint Resolve surj_comp_surj is_surj_swap_fn.

  Lemma swap_iter_fn_surj vs : is_surj (swap_iter_fn vs).
  Proof.
    induction vs;autounfold;intros x.
    + eexists. reflexivity.
    + destruct a;simpl in *.
      assert (is_surj (swap_iter_fn vs ∘ swap_fn e e0));auto.
  Qed.

  Lemma union_not_in A A' e : ~ V.In e (V.union A A') -> ~ V.In e A /\ ~ V.In e A'.
  Proof.
    intros H. auto with set.
  Qed.

  Import SetProperties.

  Hint Resolve P.Dec.F.singleton_1 P.Dec.F.singleton_2 V.E.eq_leibniz : set.

  Lemma is_biject_swap_iter vs vs' : is_biject (swap_iter_fn (zip vs vs')).
  Proof.
    split.
    + apply swap_iter_fn_inj.
    + apply swap_iter_fn_surj.
  Qed.
  
  Lemma has_fin_supp_swap_iter vs vs' :
    has_fin_supp (swap_iter_fn (zip vs vs')).
  Proof.
    exists (V.union (P.of_list vs) (P.of_list vs')). intros.
    generalize dependent vs'.
    induction vs;destruct vs';simpl;auto.
    simpl in *. unfold compose.
    intros H.
    
    (* This is required to apply IH *)
    assert (~ V.In t (V.union (P.of_list vs) (P.of_list vs'))).
    { apply union_not_in in H. destruct H; auto with set. }

    (* This is required to show that swap_n is the identity function outside of support *)
    assert (Ha : t <> a) by (apply union_not_in in H; destruct H; auto with set).
    assert (He : t <> e) by (apply union_not_in in H; destruct H; auto with set).

    assert (Ht : swap_fn a e t = t).
    { apply id_swap_fn. apply union_not_in in H.
      apply P.not_in_union;unfold not; intro Hin.
      * apply Ha; symmetry; auto with set.
      * apply He; symmetry; auto with set. }
    rewrite Ht. auto.
  Qed.

  Definition swap_iter (vs vs' : V.t) : Perm :=
    {| perm := swap_iter_fn (zip (V.elements vs) (V.elements vs'));
       is_biject_perm := is_biject_swap_iter _ _;
       has_fin_supp_perm := has_fin_supp_swap_iter _ _|}.

  Lemma swap_fn_involution a b : (swap_fn a b) ∘ (swap_fn a b) = id.
  Proof.
    apply functional_extensionality.
    intros x. unfold compose,swap_fn.
    destruct (P.FM.eq_dec a x),( P.FM.eq_dec b x),
    (P.FM.eq_dec a b),(P.FM.eq_dec b b),(P.FM.eq_dec a a),(P.FM.eq_dec b a);
      rewrite eq_leibniz_iff in *;
      tryfalse;auto;
    destruct (P.FM.eq_dec a x),( P.FM.eq_dec b x);rewrite eq_leibniz_iff in *;
      tryfalse;auto.
  Qed.
  
  Lemma swap_involution a b : (swap a b) ∘p (swap a b) = id_perm.
  Proof.
    apply perm_eq.
    unfold perm_comp, id_perm. simpl.
    rewrite swap_fn_involution. reflexivity.
  Qed.

  (* ---------------------------------------------- *)
  (* Freshness conditions and fresh name generators *)
  (* ---------------------------------------------- *)

  Definition fresh a A := ~ V.In a A.
  Definition all_fresh (x y : V.t) := forall k, ~(V.In k x /\ V.In k y).

  Infix "#" := fresh (at level 40) : a_scope.
  Infix "#" := all_fresh (at level 40) : as_scope.

  Open Scope as_scope.

  Delimit Scope a_scope with Atom.
  Import V.

  (* NOTE: it looks like a freshening function for the atom [a] from
     "Generalised Name Abstraction for Nominal Sets" by Ranald Clouston *)
  (** Type of a function with a property, that generated atom is fresh for the set [a] *)
  Definition FreshFn a := {f : V.t -> V.elt | forall x, ((f x) # a)%Atom }.

  (** Function that generates a fresh atom using [Atom_inf] property *)
  Definition fresh_fn : forall a : V.t, FreshFn a :=
    fun a =>  let H := Atom.Atom_inf a in
              exist (fun f : t -> elt => forall x : t, (f x # a)%Atom)
                    (fun _ : t => proj1_sig H)
                    (fun _ : t => proj2_sig H).

  (** Set of fresh atoms (wrt the set [a]) of cardinality [n] *)
  Definition AllFresh a n := { b : V.t | (b # a) /\ V.cardinal b = n }.

  (** Computational part of a function that generates set of fresh atoms *)
  Fixpoint get_freshs_internal (X : V.t) (n : nat) : V.t :=
    match n with
    | O => empty
    | S n' => let fatom := (proj1_sig (fresh_fn X)) X in
              add fatom (get_freshs_internal (add fatom X) n')
    end.

  Lemma get_freshs_internal_all_fresh : forall n a, (get_freshs_internal a n) # a.
  Proof.
    induction n;intros.
    + simpl. compute. intros. destruct H. rewrite <- SetProperties.P.Dec.F.empty_iff;eauto.
    + simpl. unfold all_fresh, not. intros.
      rewrite SetProperties.P.Dec.F.add_iff in *.
      intuition.
      * rewrite eq_leibniz_iff in *. subst. apply (proj2_sig (Atom.Atom_inf a));auto.
      * unfold all_fresh in *.
        assert (HH := IHn (add (proj1_sig (Atom.Atom_inf a)) a) k).
        apply HH. clear IHn HH. split;auto.
        rewrite SetProperties.P.Dec.F.add_iff in *. intuition;auto.
  Qed.

  Lemma get_freshs_cardinality : forall n a, V.cardinal (get_freshs_internal a n) = n.
  Proof.
    induction n;intros.
    + simpl. auto with set.
    + simpl. rewrite SetProperties.P.add_cardinal_2;auto.
      remember (proj1_sig (Atom.Atom_inf a)) as b.
      assert (H := get_freshs_internal_all_fresh n (add b a)).
      unfold not. intros. apply (H b). split;auto with set.
  Qed.

  (** Function that generates set of fresh atoms along with
      the proof of freshness *)
  Definition get_freshs (X : V.t) (n : nat) : AllFresh X n :=
    exist _ (get_freshs_internal X n)
            (conj (get_freshs_internal_all_fresh n X)
                  (get_freshs_cardinality n X)).

  Module Type NominalSet.
    Import V.

    Parameter X : Type.

    Parameter action : Perm -> X -> X.
    Notation "r @ x" := (action r x) (at level 80).

    Axiom action_id : forall (x : X), (id_perm @ x) = x.
    Axiom action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).

    Parameter supp : X -> V.t.
    Axiom supp_spec :
      forall  (r : Perm)  (x : X),
        (forall (a : elt), In a (supp x) -> (perm r) a = a) -> (r @ x) = x.

  End NominalSet.

  Module NomFacts (NS : NominalSet).
    Import NS.
    Import V.

    (* An alternative characterisation of support in terms of swap  *)
    Lemma supp_spec_swap :
      forall (a b : V.elt) (x : X),
        ~ In a (supp x) -> ~ In b (supp x) ->
        ((swap a b) @ x) = x.
    Proof.
      intros a b x Ha Hb.
      apply supp_spec.
      intros a' Ha'. simpl. autounfold.
      destruct (SetProperties.P.FM.eq_dec a a');
        destruct (SetProperties.P.FM.eq_dec b a');
        rewrite eq_leibniz_iff in *; congruence.
    Qed.
  End NomFacts.

  Module Fresh (nomX nomY : NominalSet).
    Definition fresh : nomX.X -> nomY.X -> Prop :=
      fun x y => Disjoint (nomX.supp x) (nomY.supp y).
  End Fresh.


  (* ------------------------------------------ *)
  (* Finite subsets of atoms form a nominal set *)
  (* ------------------------------------------ *)

  Module PFin <: NominalSet.
    Import V.
    Definition X := V.t.
    Definition action (r : Perm) (x : X) :=
      V.set_map (perm r) x.

    Notation "r @ x" := (action r x) (at level 80).

    Hint Resolve V.set_map_spec_1 V.set_map_spec V.set_map_iff : set.

    Lemma action_id : forall (x : X), (id_perm @ x) = x.
    Proof.
      intros x. unfold action.
      apply V.set_extensionality. intros x'.
      split.
      + intros Hx. rewrite V.set_map_iff in *. destruct Hx as [y H]. destruct H;subst;auto.
      + intros Hx. eauto with set.
    Qed.

    Lemma action_compose : forall (x : X) (r r' : Perm), (r @ (r' @ x)) = ((r ∘p r') @ x).
    Proof.
      intros x r r'. unfold action. apply V.set_extensionality. intros x'.
      split.
      + intros Hx. rewrite V.set_map_iff in *. destruct Hx.
        intuition;subst;auto. rewrite V.set_map_iff in *.
        destruct H1. intuition. subst.
        exists x1;split;auto.
      + intros Hx. rewrite V.set_map_iff in *. destruct Hx as [x1 H].
        destruct H.
        exists ((perm r') x1). subst; split;auto with set.
    Qed.

    Module Dec := DecidableEqDep BoolDec.

    Hint Resolve SetProperties.P.Dec.F.singleton_1 SetProperties.P.Dec.F.singleton_2 : set.

    Lemma action_singleton : forall r e, (r @ (singleton e)) = singleton ((perm r) e).
    Proof.
      intros.
      apply set_extensionality.
      intros. unfold action. split.
      + intros H. rewrite V.set_map_iff in *. destruct H;intuition;subst.
        rewrite SetProperties.P.Dec.F.singleton_iff in *.
        rewrite eq_leibniz_iff in *. subst. reflexivity.
      + intros H. rewrite V.set_map_iff in *.
        rewrite SetProperties.P.Dec.F.singleton_iff in *.
        rewrite eq_leibniz_iff in H. subst.
        exists e;auto with set.
    Qed.

    Definition supp (x : X) := x.

    Lemma supp_spec :
      forall  (r : Perm)  (x : X),
        (forall (a : V.elt), V.In a (supp x) -> (perm r) a = a) -> (r @ x) = x.
    Proof.
      intros. unfold action.
      apply set_extensionality. intro y. split.
      + intros H'. auto with set.
        rewrite set_map_iff in *. destruct H' as [y' Hy']. destruct Hy'.
        subst. rewrite H;auto.
      + intros H'. eapply set_map_spec_1;try symmetry;eauto.
    Qed.

    Definition fresh a x := ~ V.In a (supp x).

    Lemma equivar_union (x y : X) r : (r @ (V.union x y)) = V.union (r @ x) (r @ y).
    Proof.
      apply V.set_extensionality.
      intros z. split.
      + intros H. unfold action in *. rewrite union_spec in *. rewrite set_map_iff in *.
        destruct H. destruct H; subst.
        rewrite union_spec in *.
        destruct H0;auto with set.
        left. exists x0;auto.
      + intros H. unfold action in *. rewrite union_spec in *. rewrite set_map_iff in *.
        destruct H.
        * destruct H. exists x0; destruct H; split; auto with set.
        * rewrite set_map_iff in *. destruct H as [x0 Hx0]. destruct Hx0.
          exists x0;split;auto. rewrite union_spec in *. auto.
    Qed.

    Lemma equivar_inter (x y : X) r : (r @ (V.inter x y)) = V.inter (r @ x) (r @ y).
    Proof.
      apply V.set_extensionality.
      intros z. split.
      + intros H. unfold action in *.
        rewrite set_map_iff in *.
        destruct H. destruct H; subst.
        rewrite inter_spec in *.
        destruct H0;auto with set.
      + intros H. unfold action in *.
        rewrite inter_spec in *. rewrite set_map_iff in *.
        destruct H as [He' Hz]. destruct He' as [e' Htl].
        destruct Htl; subst.
        rewrite set_map_iff in *.
        destruct Hz as [e'' Htl]. destruct Htl.
        exists e''.
        assert (Heq : e' = e'') by (destruct r as [pm Hbiject Hsupp]; destruct Hbiject;auto).
        subst. auto with set.
    Qed.

    Definition all_fresh (x y : X):= Disjoint x (supp y).

    Lemma equivar_all_fresh (x y : X) r : V.Disjoint x y -> V.Disjoint (r @ x) (r @ y).
    Proof.
      intros. destruct r as [f Hf]. destruct Hf as [Hinj Hsupp].
      intros. rewrite Disjoint_spec in *. intros k.
      unfold action in *. simpl. intros H1. rewrite set_map_iff in *.
      destruct H1. destruct H0. destruct H0. subst.
      apply (H x0). split;auto.
      rewrite set_map_iff in *.
      destruct H1. destruct H0.
      (* NOTE : here we use the property that permutation is injective *)
      assert (x0 = x1) by (apply Hinj;auto).
      subst;auto.
    Qed.

    Lemma all_fresh_union X Y Z : all_fresh Z (union X Y) -> all_fresh Z X /\ all_fresh Z Y.
    Proof.
      intros H. unfold all_fresh in *.
      repeat rewrite Disjoint_spec in *; split;
        intros a H1; destruct H1; apply (H a); split; unfold supp; auto with set.
      Qed.

  End PFin.
End Nominal.
