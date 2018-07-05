(* ============================== *)
(* Elaboration rules (core)       *)
(* ============================== *)

Require Import String.

Require Import Basics.
Require Import Syntax.
Require Import SemObjects.
Require Import CpdtTactics.
(* -------------------------------------- *)
(* Elaboration rules for core-level types *)
(* -------------------------------------- *)

Inductive Ty_elab : Env -> ty -> Ty -> Prop :=
| Longtid_ty_elab : forall (E:Env) (ltid:longtid) (t:Ty),
    lookLongTid ltid E = Some t -> Ty_elab E (Longtid_ty ltid) t
| Arr_ty_elab : forall (E:Env) (t1:ty) (t2:ty) (ty1:Ty) (ty2:Ty),
    Ty_elab E t1 ty1 -> Ty_elab E t2 ty2 -> Ty_elab E (Arr_ty t1 t2) (Arr_Ty ty1 ty2).


(* -------------------------------------------- *)
(* Elaboration rules for core-level expressions *)
(* -------------------------------------------- *)

Inductive Exp_elab : Env -> exp -> Ty -> Prop :=
| Longvid_exp_elab : forall (E:Env) (lvid:longvid) (t:Ty),
    lookLongVid lvid E = Some t -> Exp_elab E (Longvid_exp lvid) t
| Lam_exp_elab : forall (E:Env) (v:vid) (e:exp) (t1 t:Ty),
    Exp_elab (addEnvVid v t1 E) e t -> Exp_elab E (Lam_exp v e) (Arr_Ty t1 t)
| App_exp_elab : forall (E:Env) (e1 e2:exp) (t1 t:Ty),
    Exp_elab E e1 (Arr_Ty t1 t) -> Exp_elab E e2 t1 -> Exp_elab E (App_exp e1 e2) t
| Typ_exp_elab : forall (E:Env) (e:exp) (s:ty) (t:Ty),
    Exp_elab E e t -> Ty_elab E s t -> Exp_elab E (Typ_exp e s) t.


(* --------------------------------------------- *)
(* Elaboration rules for core-level declarations *)
(* --------------------------------------------- *)

Inductive Dec_elab : Env -> dec -> Env -> Prop :=
| Val_dec_elab : forall (E:Env) (v:vid) (e:exp) (t:Ty),
    Exp_elab E e t -> Dec_elab E (Val_dec v e) (addEnvVid v t emptyEnv).
