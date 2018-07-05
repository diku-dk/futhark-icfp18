(* ======================================= *)
(* Compilation rules for the core language *)
(* ======================================= *)


Require Import String.

Require Import Basics.
Require Import Syntax.
Require Import SemObjects.
Require Import Target.
Require Import IntObjects.
Require Import ElabCore.
Require Import CpdtTactics.
Require Import NomEnv.

Import PermIEnvLabel.

Open Scope IEnv_scope.


(* -------------------------------------------- *)
(* Compilation rules for core-level expressions *)
(* -------------------------------------------- *)

Inductive Exp_comp : IEnv -> exp -> ex -> Ty -> Prop :=
| Longvid_exp_comp : forall IE longvid l t,
    lookLongIVid longvid IE = Some (l,t) ->
    Exp_comp IE (Longvid_exp longvid) (Lab_ex l) t
| Lam_exp_comp : forall IE vid exp ex t1 t l,
    Exp_comp (addIEnvVid vid (l,t1) IE) exp ex t ->
    Exp_comp IE (Lam_exp vid exp) (Lam_ex l ex) (Arr_Ty t1 t)
| App_exp_comp : forall IE exp1 exp2 ex1 ex2 t1 t,
    Exp_comp IE exp1 ex1 (Arr_Ty t1 t) ->
    Exp_comp IE exp2 ex2 t1 ->
    Exp_comp IE (App_exp exp1 exp2) (App_ex ex1 ex2) t
| Typ_exp_comp : forall IE exp ex ty t E,
    Exp_comp IE exp ex t ->
    erasure_IEnv IE E ->
    Ty_elab E ty t ->
    Exp_comp IE (Typ_exp exp ty) ex t.

(* --------------------------------------------- *)
(* Compilation rules for core-level declarations *)
(* --------------------------------------------- *)

Inductive Dec_comp : IEnv -> dec -> TSet -> IEnv -> c -> Prop :=
| Val_dec_comp : forall IE vid exp ex t l,
    Exp_comp IE exp ex t ->
    l # IE ->
    Dec_comp IE (Val_dec vid exp) (addTSet l emptyTSet) (addIEnvVid vid (l,t) emptyIEnv) (Val_c l ex).

Hint Constructors Exp_comp.
Hint Resolve erasure_look_longvid.

Lemma comp_exp: forall exp E t IE,
    Exp_elab E exp t -> erasure_IEnv IE E -> exists ex, Exp_comp IE exp ex t.
Proof.
  induction exp.
  + crush. inversion H. subst.
    apply erasure_look_longvid with (t:=t) (longvid:=l) in H0; eauto.
    destruct H0.
    exists (Lab_ex x). crush.

  + crush. inversion H. subst. rename t into s. rename t2 into t0.
    assert (H1 := IHexp (addEnvVid s t1 E)). clear IHexp.
    assert (H2 := H1 t0). clear H1.

    pose (AtomN.Atom_inf (PermIEnvLabel.supp IE)) as fresh_l.
    destruct fresh_l as [l Hfresh].
    assert (H3 := H2 (addIEnvVid s (l,t1) IE)). clear H2.
    apply erasure_IEnv_extend with (t:=t1) (l:=l) (s:=s) in H0.
    crush.
    exists (Lam_ex l x).
    constructor; eauto.
  + crush. inversion H. subst. assert (H1 := IHexp1 E (Arr_Ty t1 t) IE). clear IHexp1. crush.
    assert (H2 := IHexp2 E t1 IE). clear IHexp2. crush.
    exists (App_ex x x0). clear H H0 H4 H6 E. eauto.

  + crush. inversion H. subst. assert (H1 := IHexp E t0 IE). clear IHexp. crush. eauto.
Qed.

Hint Resolve erasure_IEnv_extend erasure_IEnv_empty.

Lemma comp_dec: forall dec E E' IE,
    Dec_elab E dec E' -> erasure_IEnv IE E ->
    exists N IE' c, Dec_comp IE dec N IE' c  /\ erasure_IEnv IE' E'.
Proof.
  crush.
  pose (AtomN.Atom_inf (PermIEnvLabel.supp IE)) as fresh_l.
  destruct fresh_l as [l Hfresh].
  exists (addTSet l emptyTSet).

  inversion H. subst.
  apply comp_exp with (IE := IE) in H1.

  destruct H1. remember (Val_c l x) as c.

  exists (addIEnvVid v (l,t) emptyIEnv).  exists c.

  split.

  remember (Val_dec v e) as dec.

  rename v into vid. rename x into ex. rename e into exp. subst dec c.

  clear H H0.
  constructor; assumption. apply erasure_IEnv_extend.
  apply erasure_IEnv_empty;assumption.
  assumption.
Qed.
