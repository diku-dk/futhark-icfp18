(* =========================================================== *)
(* Finite sets with extensionality.                            *)
(* Uses the [MSetList] implementation from the Coq standard    *)
(* library exposed through a slightly different interface and  *)
(* extended with new methods and properties.                   *)
(* =========================================================== *)

Require Import MSetList MSets Structures.Orders Eqdep_dec.

Module BoolDec <: DecidableType.
    Definition U := bool.
    Definition eq_dec := Bool.bool_dec.
End BoolDec.

Module Type SetExtT.
  Include SWithLeibniz.
  Parameter Disjoint : t -> t -> Prop.
  Axiom Disjoint_spec : forall m m',  Disjoint m m' <-> forall k, ~ (In k m /\ In k m').
  Parameter set_extensionality :
    forall (X Y : t), (forall (x : elt), In x X <-> In x Y) -> X = Y.
  Parameter set_map : (elt -> elt) -> t -> t.
  Axiom set_map_spec : forall (f : elt -> elt) (X : t) (e : elt),
      In e X -> In (f e) (set_map f X).
  Axiom set_map_spec_1 : forall (f : elt -> elt) (X : t) (e e' : elt),
      In e X -> e' = f e -> In e' (set_map f X).
  Axiom set_map_iff : forall (f : elt -> elt) (X : t) e,
    In e (set_map f X) <-> exists e', e = f e' /\ In e' X.
  Axiom union_assoc :
    forall s s' s'' : t, (union (union s s') s'') = (union s (union s' s'')).
  Axiom union_comm : forall s s' : t, union s s' = union s' s.
End SetExtT.

Module SetExt (E : UsualOrderedType) <: SetExtT.
  Module SLeib <: MSetList.OrderedTypeWithLeibniz.
  Include E.
  Lemma eq_leibniz : forall x y, eq x y -> x = y.
  Proof.
    intros x y Heq. auto.
  Qed.
  End SLeib.
  Module S := MSetList.MakeWithLeibniz SLeib.

  Include S.

  Module OP := OrdProperties S.
  Import OP.

  Module Dec := DecidableEqDep BoolDec.

  Lemma set_extensionality (X Y : t):
    (forall  (x : elt), In x X <-> In x Y) -> X = Y.
  Proof.
    intros Hin.
    destruct X as [xs sxs]. destruct Y as [ys sys].
    assert (Heq : xs = ys) by
        (apply eq_leibniz_list;
         apply OP.sort_equivlistA_eqlistA; try rewrite Raw.isok_iff; auto).
    subst. f_equal.
    (* NOTE: We can solve this goal without assuming proof irrelevance, because
       for types with decidable equality UIP in provable *)
    apply Dec.UIP.
  Qed.

  Definition set_map (f : elt -> elt) (X : t) : t :=
    fold (fun x Y => add (f x) Y) X empty.

  Lemma set_map_spec (f : elt -> elt) (X : t) : forall (e : elt),
    In e X -> In (f e) (set_map f X).
  Proof.
    (* NOTE: it is very convenient to use special induction principle for fold here *)
    apply P.fold_rec with (P:=fun X Y => forall e, In e X -> In (f e) Y).
    + intros. exfalso. unfold S.Empty in *. apply (H e);auto.
    + intros. apply P.FM.add_iff. destruct (H1 e). intuition. subst. auto.
  Qed.

  Lemma set_map_spec_1 (f : elt -> elt) (X : t) : forall (e e' : elt),
    In e X -> e' = f e -> In e' (set_map f X).
  Proof.
    intros. subst. apply set_map_spec;auto.
  Qed.

  Lemma set_map_iff (f : elt -> elt) (X : t) : forall e,
    In e (set_map f X) <-> exists e', e = f e' /\ In e' X.
  Proof.
    intros e.
    split.
    + revert e. apply P.fold_rec with
          (P := fun x' Y => forall e, In e Y -> exists e', e = f e' /\ In e' X).
      intros s' H' e He.
      * inversion He.
      * intros x a Y Y' Hx Hx' Hadd IH e He. apply P.FM.add_iff in He. intuition.
        subst. exists x. unfold P.Add in *. destruct (Hadd x);intuition.
    + intros. destruct H. intuition. subst.
      apply set_map_spec;auto.
  Qed.

  Definition Disjoint (m m' : t) :=
    forall k, ~ (In k m /\ In k m').

  Lemma Disjoint_spec m m' : Disjoint m m' <-> forall k, ~ (In k m /\ In k m').
  Proof.
    split;auto.
  Qed.

  Lemma union_assoc :
    forall s s' s'' : S.t, (S.union (S.union s s') s'') = (S.union s (S.union s' s'')).
  Proof.
    intros. apply set_extensionality. apply P.union_assoc.
  Qed.

  Lemma union_comm : forall s s' : S.t, S.union s s' = S.union s' s.
  Proof.
    intros.
    apply set_extensionality. intros.
    split;intros; apply P.Dec.F.union_1 in H; intuition;auto with set.
  Qed.

End SetExt.
