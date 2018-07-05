(* ==================================================================== *)
(* Some examples showing that Coq's implementation of strict positivity *)
(* is a conservative approximation: it does not allow for some          *)
(* strictly positive definitions.                                       *)
(* ==================================================================== *)

Require Import EnvExt Sorting Vector Nat ZArith.
Require Import Basics.

(* ---------------------------- *)
(* A simple AST for expressions *)
(* ---------------------------- *)

Inductive OpName :=
| Neg : OpName
| Add : OpName.

(* This works *)
Inductive Exp :=
  | natNum : nat -> Exp
  | op : OpName -> list Exp -> Exp.

(* Type of lists-with-length implemented as a subset type *)
Definition VecST (A : Type) (n : nat) : Type := {xs : list A | length xs = n}.

Inductive Ops : nat -> Type:=
| NegZ : Ops 1
| AddZ : Ops 2.
(* But if we need list in the argument of the constructor to be of certain length
   (let's say we want to keep track of arity of the operations) : *)

(* Inductive ExpVecST := *)
(*   | natNumA : nat -> ExpVecST *)
(*   | opA : forall n, Ops n -> VecST ExpVecST n -> ExpVecST. *)

(* We get an error:  *)
(* Error: Non strictly positive occurrence of "ExpVecST" in *)
(*  "forall n : nat, VecST ExpVecST n -> ExpVecST". *)

Notation Vec := Vector.t.

(* But if we replace VectST works for vectors! *)
Inductive ExpVec :=
  | ZNumV : Z -> ExpVec
  | opV :  forall n, Ops n -> Vec ExpVec n -> ExpVec.

(* Now, we can define a total evaluation function *)
Program Definition eval_op {n} (f : Ops n) : Vec Z n -> Z :=
  match f with
  | NegZ => fun args => match n with
                        | O => _ (* impossible case *)
                        | 1 => (- hd (args))%Z
                        | S _ => _ (* impossible case *)
                        end
  | AddZ => fun args => match n with
                        | O => _ (* impossible case *)
                        | 1 => _ (* impossible case *)
                        | 2 => (hd args + hd (tl args))%Z
                        | S _ => _ (* impossible case *)
                        end
  end.

Fixpoint eval_ExpVec (e : ExpVec) : Z :=
  match e with
  | ZNumV n => n
  | opV n op_ args => eval_op op_ (map eval_ExpVec args)
  end.

(* -------------------------------------------- *)
(* Environments as lists of pair with a certain *)
(* "well-formedness" condition                  *)
(* -------------------------------------------- *)

(* We want the list in the argument of the constructor to be sorted: *)

Notation Key := nat.

Module M := EnvExt.OrdEnv Basics.ID.

(* Ordering for keys *)
Definition lt_key {A} (e e' : Key * A)  :=
  match e, e' with
    (k,v),(k',v') => k < k'
  end.

(* Sigma type representing list with a property being sorted according to lt_key  *)
Definition sort_list A := {xs : list (Key * A) | sort (@lt_key A) xs}.

(* The definition, which uses additional property 
   on an list argument, violates Coq's strict positivity constraint *)

(* Inductive ExpBad1 := *)
(*   ctrBad :  sort_list ExpBad1 -> ExpBad1. *)

(* Basically, all definitions, where we quantify over the list to
   to say something about the list, even without doing anything with
   the list elements, don't work.*)

(* Inductive ExpBad2 := *)
(* | c : (forall x : list (Key * ExpBad2), length x = 1) -> ExpBad2. *)


(* Now, the idea is to separate properties on keys (because we sort only by first component
   of the list) from the values *)

Definition skeys n := {keys | sort ID.lt keys & length keys = n}.

(* This definition is clearly isomorphic to the representation above,
   and it passes strict Coq's strict positivity check *)
Inductive Exp1 :=
| ctr1 : forall n, skeys n -> Vector.t Exp1 n -> Exp1.

(* We used this idea, though we replaced the list of keys with the vector *)
(* See OrdEnv.v *)
Inductive Exp2 :=
  ctr2 :  M.VecEnv.VecEnv Exp2 -> Exp2.
