(* ============================== *)
(* Syntax for the source language *)
(* ============================== *)

Require Import String.
Require Import Basics.

(* ----------------- *)
(* The core language *)
(* ----------------- *)

Inductive ty :=
| Longtid_ty : longtid -> ty
| Arr_ty : ty -> ty -> ty.

Inductive exp :=
| Longvid_exp : longvid -> exp
| Lam_exp : vid -> exp -> exp
| App_exp : exp -> exp -> exp
| Typ_exp : exp -> ty -> exp.

Inductive dec :=
| Val_dec : vid -> exp -> dec.

(* ------------------------------- *)
(* Module types and specifications *)
(* ------------------------------- *)

Inductive mty :=
| Bra_mty : spec -> mty
| Mtid_mty : mtid -> mty
| Arr_mty : option mid -> mty -> mty -> mty
| With_mty : mty -> longtid -> ty -> mty
with spec :=
| Type_spec : tid -> option ty -> spec
| Val_spec : vid -> ty -> spec
| Module_spec : mid -> mty -> spec
| Include_spec : mty -> spec
| Seq_spec : spec -> spec -> spec
| Emp_spec : spec.

(* ----------------------------------- *)
(* Module expressions and declarations *)
(* ----------------------------------- *)

Inductive mexp :=
| Bra_mexp : mdec -> mexp
| Mid_mexp : mid -> mexp
| Prj_mexp : mexp -> mid -> mexp
| Funct_mexp : mid -> mty -> mexp -> mexp
| App_mexp : longmid -> mexp -> mexp
with mdec :=
| Dec_mdec : dec -> mdec
| Type_mdec : tid -> ty -> mdec
| Mod_mdec : mid -> mexp -> mdec
| ModTyp_mdec : mtid -> mty -> mdec
| Open_mdec : mexp -> mdec
| Seq_mdec : mdec -> mdec -> mdec
| Emp_mdec : mdec.
