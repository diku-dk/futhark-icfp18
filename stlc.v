(* =============================================================== *)
(* Normalisation of the Call-by-Value Simply-Typed Lambda Calculus *)
(* =============================================================== *)

Require Import String.
Require Import Coq.Program.Equality.
Require Import CpdtTactics.

Definition string_eq (x y: string) : bool :=
  match string_dec x y with
    | left _  => true
    | right _ => false
  end.

Inductive Ty : Set :=
  | tInt : Ty
  | tArr : Ty -> Ty -> Ty.

Notation "A :-> B" := (tArr A B) (at level 70).

Inductive Nat : Set :=
  | Zero : Nat
  | Succ : Nat -> Nat.

Inductive Exp : Set :=
  | Int : Nat -> Exp
  | Var : string -> Exp
  | Lam : string -> Exp -> Exp
  | App : Exp -> Exp -> Exp.

Inductive Env {A:Set} : Set :=
  | empty : Env
  | cons  : Env -> string -> A -> Env.

Fixpoint lookEnv {T:Set} (E:Env) (x:string) : option T :=
  match E with
    | empty => None
    | cons E y A =>
      if string_eq y x then Some A else lookEnv E x
  end.


Definition TEnv : Set := Env (A:=Ty).

(* Definition lookTEnv (G:TEnv) (x:string) : option Ty := lookEnv G x. *)

Fixpoint lookTEnv (G:TEnv) (x:string) : option Ty :=
  match G with
    | empty => None
    | cons G y A => if string_eq y x then Some(A) else lookTEnv G x
  end.

Inductive Typing : TEnv -> Exp -> Ty -> Prop :=
  | tyInt : forall (G:TEnv) (n:Nat), Typing G (Int n) tInt
  | tyVar : forall (G:TEnv) (x:string) (A:Ty), lookTEnv G x = Some(A) -> Typing G (Var x) A
  | tyLam : forall (G:TEnv) (x:string) (b:Exp) (A B:Ty),
            Typing (cons G x A) b B
            -> Typing G (Lam x b) (A :-> B)
  | tyApp : forall (G:TEnv) (f a:Exp) (A B:Ty),
               Typing G f (A :-> B)
               -> Typing G a A
               -> Typing G (App f a) B.


Notation "[ G |- a @ A ]" := (Typing G a A).

Inductive Val : Set :=
  | vInt  : Nat -> Val
  | vClos : Env (A:=Val) -> string -> Exp -> Val.

Definition DEnv := Env (A:=Val).

Fixpoint lookDEnv (E:DEnv) (x:string) : option Val :=
  match E with
    | empty => None
    | cons E y A => if string_eq y x then Some A else lookDEnv E x
  end.

Inductive Eval : DEnv -> Exp -> Val -> Prop :=
  | eInt : forall (E:DEnv) (n:Nat), Eval E (Int n) (vInt n)
  | eVar : forall (E:DEnv) (x:string) (v:Val), lookDEnv E x = Some v -> Eval E (Var x) v
  | eLam : forall (E:DEnv) (x:string) (a:Exp), Eval E (Lam x a) (vClos E x a)
  | eApp : forall (E E0:DEnv) (f a e0:Exp) (v va:Val) (x: string),
             Eval E f (vClos E0 x e0)
               -> Eval E a va
               -> Eval (cons E0 x va) e0 v
               -> Eval E (App f a) v.

Notation "[ E |- a ==> v ]" := (Eval E a v).

Fixpoint Equiv (val:Val) (ty:Ty) : Prop :=
  match ty with
      tInt => exists n:Nat, val = (vInt n)
    | tArr A B => exists (x:string) (a:Exp) (E:DEnv),
                    (val = vClos E x a) /\
                    (forall v1:Val, Equiv v1 A ->
                                    exists v2:Val, [ cons E x v1 |- a ==> v2] /\ Equiv v2 B)
  end.

Notation "[ |= v @ t ]" := (Equiv v t).

Definition EquivEnv (E:DEnv) (G:TEnv) : Prop :=
  (forall (x:string) (val:Val),
    lookDEnv E x = Some val -> exists ty:Ty,lookTEnv G x = Some ty /\ Equiv val ty)
  /\
  (forall (x:string) (ty:Ty),
    lookTEnv G x = Some ty -> exists val:Val, lookDEnv E x = Some val /\ Equiv val ty).

Notation "[ |== E @ G ]" := (EquivEnv E G).

Lemma Look : forall (G:TEnv) (ty:Ty) (E:DEnv) (s: string),
    [ |== E @ G ] -> lookTEnv G s = Some ty
    -> exists v:Val, lookDEnv E s = Some v /\ [ |= v @ ty ].
Proof.
  intros. unfold EquivEnv in H. crush.
Qed.

Lemma EquivExtend : forall (G:TEnv) (E:DEnv) (s:string) (val:Val) (ty:Ty),
    [ |= val @ ty ] -> [ |== E @ G ] -> [ |== (cons E s val) @ (cons G s ty)].
Proof.
  intros G E s v ty Hty Heqv. constructor; intros s' v' E'; crush.
  - remember (string_eq s s') as b.
    destruct b.
    + inversion E'.  eexists. split. reflexivity. crush.
    + inversion Heqv as [H1 H2]. destruct (H1 s' v' E'). destruct H.
      eexists. split; crush.
  - remember (string_eq s s') as b.
    destruct b.
    + inversion E'. eexists. split. reflexivity. crush.
    + inversion Heqv as [H1 H2]. destruct (H2 s' v' E'). destruct H.
      eexists. split; crush.
Qed.

Lemma Normalisation : forall (exp:Exp) (G:TEnv) (ty:Ty) (E:DEnv),
    [ G |- exp @ ty ] -> [ |== E @ G ] ->
    exists val:Val, [ E |- exp ==> val ] /\ [ |= val @ ty ].
Proof.
  induction exp; crush.
  exists (vInt n). crush. clear H H0 ty G. apply eInt.
  inversion H. crush. exists n. crush.
  inversion H. crush. inversion H0. clear H1. specialize H2 with (x:=s)(ty:=ty).
  destruct (H2 H3). exists x. crush.
  constructor. crush.
  exists (vClos E s exp). split. constructor.
  inversion H. crush. exists s. exists exp. exists E. crush.
  specialize IHexp with (G:=cons G s A)(ty:=B)(E:=cons E s v1).
  destruct (IHexp H5).
  apply EquivExtend. crush. crush. exists x. crush.
  inversion H. crush.
  specialize IHexp1 with (G:=G)(ty:= A :-> ty) (E:=E).
  specialize IHexp2 with (G:=G)(ty:=A)(E:=E).
  destruct (IHexp1 H4 H0). clear IHexp1.
  destruct (IHexp2 H6 H0). clear IHexp2.
  destruct H1. destruct H2. crush.
  specialize H8 with (v1:=x0).
  destruct (H8 H5). exists x.
  split.  destruct H3. crush.
  apply eApp with (E0:=x3)(E:=E)(f:=exp1)(a:=exp2)(x:=x1)(va:=x0)(e0:=x2).
  crush. crush. crush. crush.
Qed.

Hint Constructors Typing Eval.

(** An alternative proof by induction on typing derivation *)
Lemma Normalisation_alt : forall (exp:Exp) (G:TEnv) (ty:Ty) (E:DEnv),
    [ G |- exp @ ty ] -> [ |== E @ G ] ->
    exists val:Val, [ E |- exp ==> val ] /\ [ |= val @ ty ].
Proof.
  intros until E. intros Ty Heqv.
  generalize dependent E.
  induction Ty; intros E Heqv.
  - exists (vInt n). crush. exists n. reflexivity.
  - inversion Heqv as [H1 H2]. destruct (H2 x A H) as [v H3]. destruct H3.
    exists v. crush.
  - exists (vClos E x b). crush.
    exists x. exists b. exists E. crush.
    specialize IHTy with (E:=cons E x v1). apply IHTy.
    apply EquivExtend; crush.
  - destruct (IHTy1 E Heqv) as [v H]. clear IHTy1.
    destruct (IHTy2 E Heqv) as [v' H']. clear IHTy2.
    destruct H. destruct H'. crush. destruct (H4 v' H2) as [v'' H''].
    destruct H''.
    exists v''; eauto.
Qed.
