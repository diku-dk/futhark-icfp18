(* ==================================== *)
(* Target Language Syntax and Semantics *)
(* ==================================== *)

Require Import String FMaps.
Require Import SemObjects.
Require Import CpdtTactics.
Notation label := nat.

(* Syntax *)

Inductive ex :=
| Lab_ex : label -> ex
| Lam_ex : label -> ex -> ex
| App_ex : ex -> ex -> ex.

Inductive c :=
| Val_c : label -> ex -> c
| Seq_c : c -> c -> c
| Emp_c : c.

(* Using finite map with no ordering *)
Module NEnvMod := FMapWeakList.Make Nat_as_DT.
Module FM := WProperties_fun Nat_as_DT NEnvMod.

(* Contexts *)
Definition Ctx := NEnvMod.t Ty.
Definition emptyCtx : Ctx := NEnvMod.empty Ty.
Definition plusCtx (X Y: Ctx) : Ctx := FM.update X Y.
Definition addCtx (l:label) (t:Ty) (ctx:Ctx) : Ctx := NEnvMod.add l t ctx.
Definition lookCtx (l:label) (ctx:Ctx) : option Ty := NEnvMod.find l ctx.

(* ----------------------------------- *)
(* Typing rules for target expressions *)
(* ----------------------------------- *)

Inductive Ex_elab : Ctx -> ex -> Ty -> Prop :=
| Lab_ex_elab : forall C l t,
    lookCtx l C = Some t -> Ex_elab C (Lab_ex l) t
| Lam_ex_elab : forall C l e t1 t,
    Ex_elab (addCtx l t1 C) e t -> Ex_elab C (Lam_ex l e) (Arr_Ty t1 t)
| App_ex_elab : forall C e1 e2 t1 t,
    Ex_elab C e1 (Arr_Ty t1 t) -> Ex_elab C e2 t1 -> Ex_elab C (App_ex e1 e2) t.

(* ------------------------------------ *)
(* Typing rules for target declarations *)
(* ------------------------------------ *)

Inductive C_elab : Ctx -> c -> Ctx -> Prop :=
| Val_c_elab : forall C l e t,
    Ex_elab C e t -> C_elab C (Val_c l e) (addCtx l t emptyCtx).


(* ----------------------------------- *)
(* Disjoint relation on code fragments *)
(* ----------------------------------- *)

Inductive disjoint_ex (N:TSet) : ex -> Prop :=
| Lab_ex_disj : forall l,
    ~ TSetMod.In l N ->
    disjoint_ex N (Lab_ex l)
| Lam_ex_disj : forall l e,
    ~ TSetMod.In l N
    -> disjoint_ex N e
    -> disjoint_ex N (Lam_ex l e)
| App_ex_disj : forall e1 e2,
    disjoint_ex N e1
    -> disjoint_ex N e2
    -> disjoint_ex N (App_ex e1 e2).

Inductive disjoint_c (N:TSet) : c -> Prop :=
| Val_c_disj : forall e l,
    ~ TSetMod.In l N ->
    disjoint_ex N e -> disjoint_c N (Val_c l e).