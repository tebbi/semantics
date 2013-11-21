Require Import Subst Size util lib.

Inductive type : Type :=
| TVar (x : var)
| Top
| Arr (A1 A2 : type)
| All (A1 : type) (A2 : bind type).

Definition ty_ctxt := list type.

Instance subst_type : Subst type. gen_Subst. Defined.
Instance substLemmas_type : SubstLemmas subst_type. 
gen_SubstLemmas. Defined.

Instance size_type : Size type. gen_Size. Defined.

Inductive ty_get : ty_ctxt -> var -> type -> Prop :=
| Get0 Delta A: ty_get (cons A Delta) 0 A.[ren(+1)]
| GetS Delta x A B : ty_get Delta x B -> ty_get (cons A Delta) (S x) B.[ren(+1)]
.

Definition inj {A B : Type} (f : A -> B) := forall x y, f x = f y -> x = y. 

Lemma ren_inj xi : inj xi -> inj (fun A => A.[ren xi]).
Proof.
  unfold inj. intros H A B H'.
  aind A; ssimpl in *.
  - destruct B; arew.
  - destruct B; arew.
  - destruct B; ssimpl in H'; inversion H'. f_equal; arew.
  - destruct B; ssimpl in H'; inversion H'. f_equal. arew. ssimpl in *.
    eapply IHA0;[idtac|eassumption]. intros. destruct x; destruct y; arew.
Qed.

Lemma ty_get_weakening Delta A x B : ty_get Delta x A <-> ty_get (Delta,,B) (S x) A.[ren(+1)].
Proof.
  split.
  - arew.
  - intros. inversion H; subst. apply ren_inj in H4; arew.
Qed.

Inductive wf_ty Delta : type -> Prop :=
| Wf_ty_TVar x B : ty_get Delta x B -> wf_ty Delta B -> wf_ty Delta (TVar x)
| Wf_ty_Top : wf_ty Delta Top
| Wf_ty_Arr A1 A2 : wf_ty Delta A1 -> wf_ty Delta A2 -> wf_ty Delta (Arr A1 A2)
| Wf_ty_All A1 A2 : wf_ty Delta A1 -> wf_ty (Delta,, A1) A2 -> wf_ty Delta (All A1 A2)
.
(*
Lemma wf_ty_weakening p Delta A B : p = (Delta, A) -> wf_ty Delta A -> wf_ty (Delta,,B) A.[ren(+1)].
Proof.
  
Qed.*)

Inductive sub (Delta : ty_ctxt) : type -> type -> Prop :=
| SA_Top A : wf_ty Delta A -> sub Delta A Top
| SA_Refl x : wf_ty Delta (TVar x) -> sub Delta (TVar x) (TVar x)
| SA_Trans x A B : ty_get Delta x A -> sub Delta A B -> sub Delta (Var x) B 
| SA_Arrow A1 A2 B1 B2 : sub Delta B1 A1 -> sub Delta A2 B2 -> sub Delta (Arr A1 A2) (Arr B1 B2)
| SA_All A1 A2 B1 B2 : sub Delta B1 A1 -> sub (cons B1 Delta) A2 B2 -> sub Delta (All A1 A2) (All B1 B2)
.

Require Import util lib Program.Equality.

Lemma wf_ren Delta1 Delta2 A xi zeta : wf_ty Delta1 A.[ren zeta] -> (forall x B, ty_get Delta1 (zeta x) B.[ren zeta] -> ty_get Delta2 (xi x) B.[ren xi]) -> wf_ty Delta2 A.[ren xi].
Proof.
  intros H. daind H. destruct A.
eapply IHwf_ty. eassumption.
  ssimpl. constructor. arew. apply IHwf_ty2. intros. destruct x; ssimpl in *. 
  - inversion H2; subst. ssimpl. pose proof (Get0 Delta2 A1.[ren xi]). ssimpl in H3. apply H3. 
  - inversion H2; subst. ssimpl in *. pose proof (GetS Delta2 (xi x) A1.[ren xi] B0.[ren xi]). ssimpl in H3. apply H3. arew.
Qed.

Lemma sub_wf Delta A B : sub Delta A B -> wf_ty Delta A /\ wf_ty Delta B.
Proof.
  intros H. 
  induction H; auto; arew.
  constructor. intuition. 
  autorevert A2. induction A2; intros; arew.
  - destruct x.
    + econstructor. constructor. eapply wf_ren. eassumption. intros. apply ty_get_weakening. assumption.
    + inversion H7; subst. econstructor. apply ty_get_weakening.  eapply ty_get_weakening. eassumption. eapply wf_ren. eapply wf_ren.

eassumption. intros. ssimpl. inversion H1; subst. econstructor.
  - 
  constructor.
  - arew. destruct v; arew. 
  - arew. eapply IHA2_1; arew.
Qed.


Lemma sub_refl Delta A : sub Delta A A.
Proof.
  revert Delta. induction A; eauto using sub.
Qed.

Ltac inv H := inversion H; subst; clear H.
Lemma sub_trans Delta A B C: sub Delta A B -> sub Delta B C -> sub Delta A C.
Proof.
  revert Delta A C. induction B.
  - intros. inv H. assumption.
    econstructor 3. eassumption.
Qed.
