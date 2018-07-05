Require Import String OrderedType OrderedTypeEx.

(* ----------- *)
(* Identifiers *)
(* ----------- *)

(* We assume some abstract type of identifiers,
   which has decidable equality and order *)

Parameter ident : Set.

Module ID <: UsualOrderedType.
  Definition t : Set := ident.
  Definition eq (v v' : t) : Prop := v = v'.
  Parameter lt : t -> t -> Prop.
  Definition eq_refl x := eq_refl (A:=t) x.
  Definition eq_sym := eq_sym (A:=t).
  Definition eq_trans := eq_trans (A:=t).
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Definition from_ident (s : ident ) : t := s.
End ID.

Local Coercion ID.from_ident : ident >-> ID.t.

Notation tid := ID.t.
Notation vid := ID.t.
Notation mid := ID.t.
Notation mtid := ID.t.

(* ---------------- *)
(* Long identifiers *)
(* ---------------- *)

Inductive longtid :=
| Tid_longtid : tid -> longtid
| Long_longtid : mid -> longtid -> longtid.

Inductive longvid :=
| Vid_longvid : vid -> longvid
| Long_longvid : mid -> longvid -> longvid.

Inductive longmid :=
| Mid_longmid : mid -> longmid
| Long_longmid : mid -> longmid -> longmid.

(* -------------------------------------------- *)
(* Useful properties and operations on equality *)
(* -------------------------------------------- *)

(** NOTE: these properties are required in proofs involving dependent types (e.g. vectors),
    since standard tactics like [rewrite] sometimes fail because of dependencies. *)

(** Transport along the equality.
    Transport sometimes is required to *state* theorems in presence of dependent types.
    Without it some statements would not even typecheck *)
Definition transport {A : Type} {a b : A} {P : A -> Type} : a = b -> P a -> P b
  := fun p H => eq_rect a P H b p.

(** Action on paths *)
Definition ap {A B : Type} (f : A -> B) {a a' : A}
           (p : a = a') : f a = f a'.
  induction p. reflexivity. Defined.

(** Action on paths dependent *)
Definition apd {A : Type}{B : A -> Type}(f : forall (a : A), B a)
           {a a' : A}(p : a = a') : transport p (f a) = f a'.
  destruct p. reflexivity. Defined.

(** Concatenation of paths *)
Definition path_concat {A : Type} {x y z : A} : x = y -> y = z -> x = z.
  intros p q. destruct p. apply q. Defined.


(** Lemma 2.3.9 in the HoTT book *)
Definition transp_concat {A : Type} {B : A -> Type} {x y z : A} {u : B x}
           (p : x = y) (q : y = z) :
  transport q (transport p u) = transport (path_concat p q) u.
  destruct p. reflexivity. Defined.

(* Lemma 2.3.10 in the HoTT book *)
Definition transp_naturality {A B : Type} {C : B -> Type} {x y : A} {f : A -> B}
           {u : C (f x)} (p : x = y) :
  transport (ap f p) u =  @transport _ _ _ (fun x => C (f x)) p u.
  destruct p. reflexivity. Defined.

(* Lemma 2.3.11 in the HoTT book *)
Definition move_transport {A : Type}{F G : A -> Type}(f : forall {a : A}, F a -> G a)
           {a a' : A} (u : F a) (p : a = a') : f (transport p u) = transport p (f u).
  destruct p. reflexivity. Defined.

Definition concat_inv_r {A : Type} {x y : A} (p : x = y) :
  path_concat p (eq_sym p) = eq_refl.
  destruct p. reflexivity. Defined.

Definition concat_inv_l {A : Type} {x y : A} (p : x = y) :
  path_concat (eq_sym p) p = eq_refl.
  destruct p. reflexivity. Defined.
