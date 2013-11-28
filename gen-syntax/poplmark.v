Require Import Program.Equality ssreflect List.
Require Import Subst Size util lib Decidable Ctxts.

Inductive type : Type :=
| TVar (x : var)
| Top
| Arr (A1 A2 : type)
| All (A1 : type) (A2 : bind type).

Instance subst_type : Subst type. gen_Subst. Defined.
Instance substLemmas_type : SubstLemmas _ subst_type. 
gen_SubstLemmas. Defined.
Instance size_type : Size type. 
assert(Size var). exact(fun _ => 0).
gen_Size. Defined.

Lemma ren_size_inv A : forall xi, size A.[ren xi] = size A.
Proof.
  induction A; intros; sizesimpl; repeat(ssimpl; try autorew); try somega.
Qed.

Fixpoint wf_ty Delta A := match A with
  | TVar x => exists B, dep_get Delta x B
  | Top => True
  | Arr A B => wf_ty Delta A /\ wf_ty Delta B
  | All A B => wf_ty Delta A /\ wf_ty Delta,,A B
end.

Inductive sub (Delta : list type) : type -> type -> Prop :=
| SA_Top A : wf_ty Delta A -> sub Delta A Top
| SA_Refl x : wf_ty Delta (TVar x) -> sub Delta (TVar x) (TVar x)
| SA_Trans x A B : dep_get Delta x A -> sub Delta A B -> sub Delta (Var x) B 
| SA_Arrow A1 A2 B1 B2 : sub Delta B1 A1 -> sub Delta A2 B2 -> sub Delta (Arr A1 A2) (Arr B1 B2)
| SA_All A1 A2 B1 B2 : sub Delta B1 A1 -> wf_ty Delta B1 -> sub (Delta,,B1) A2 B2 -> sub Delta (All A1 A2) (All B1 B2)
.

Lemma wf_weak Delta1 Delta2 A xi : 
  wf_ty Delta1 A -> 
  (forall x B, dep_get Delta1  x B -> exists B', dep_get Delta2 (xi x) B') -> 
  wf_ty Delta2 A.[ren xi].
Proof.
  intros H. aind A. ssimpl.
  eapply IHA0. eassumption. intros.
  destruct x; ssimpl; arew; ssimpl. unfold lift. simpl. 
  edestruct H0; arew.
Qed.

Corollary wf_weak' Delta1 Delta2 A : 
  wf_ty Delta1 A -> 
  (length Delta1 <= length Delta2) -> 
  wf_ty Delta2 A.
Proof.
  intros. 
  cutrewrite(A = A.[ren id]);[idtac|now ssimpl]. 
  eapply wf_weak; eauto.
  intros.
  apply dep_get_defined.
  cut(id x < length Delta1). omega.
  apply dep_get_defined.
  eexists. eassumption.
Qed.

Lemma sub_refl Delta A : wf_ty Delta A -> sub Delta A A.
Proof.
  revert Delta. induction A; simpl; intuition; eauto using sub.
Qed.

Lemma sub_weak Delta1 Delta2 A1 A2 xi : sub Delta1 A1 A2 -> 
  (forall x B, dep_get Delta1 x B -> dep_get Delta2 (xi x) B.[ren xi]) -> 
  sub Delta2 A1.[ren xi] A2.[ren xi] .
Proof.
   intros H. aind H.
   - constructor. eapply wf_weak; now eauto.
   - econstructor; ssimpl.
     + now eauto.
     + eapply wf_weak; now eauto.
     + apply IHsub2. intros.
       destruct x; ssimpl; arew; ssimpl; rewrite (ren_uncomp _ _ (+1)); arew. 
Qed.

Lemma sub_wf {Delta A B} : sub Delta A B -> wf_ty Delta A /\ wf_ty Delta B.
Proof.
  intros H. aind H.
  eapply wf_weak'. eassumption.
  now simpl.
Qed.

Lemma sub_trans' n : 
  (forall Delta A B C, n = size B -> sub Delta A B -> sub Delta B C -> sub Delta A C) /\
  (forall Delta' Delta  B B' A C, n = size B -> sub Delta,,B,,,Delta' A C -> sub Delta B' B -> sub Delta,,B',,,Delta' A C)
.
Proof.
  induction n as [n IH] using (size_rec (fun x => x)).
  apply conj'.
  {
    intros Delta A B C ? H_AB H_BC. subst.
    revert C H_BC.
    induction H_AB; prepare.
    - now arew.
    - econstructor; now prepare.
    - inv H_BC. 
      + constructor. simpl. intuition. now eapply (sub_wf H_AB1). now eapply (sub_wf H_AB2).
      + constructor; eapply IH; eauto; somega.
    - inv H_BC.
      + constructor; constructor. 
        * eapply sub_wf; now eauto. 
        * eapply wf_weak'. now eapply (sub_wf H_AB2). now simpl.
      + rename B0 into C1. rename B3 into C2.
        constructor; eauto.
        * eapply IH; eauto; somega.
        * eapply IH; eauto; try somega.
          refine (proj2 (IH _ _) nil _ _ _ _ _ _ _ _); eauto; somega.
  }
  {
    intros H_trans Delta' Delta B B' A C ? H H_B'B. subst.
    revert B' H_B'B.
    depind H; prepare.
    - constructor.
      eapply wf_weak'. eassumption.
      repeat rewrite app_length. simpl. omega.
    - constructor. simpl.
      apply dep_get_defined. apply dep_get_defined in H.
      repeat rewrite -> app_length in *. simpl in *. omega.
    - decide (x = length Delta').
      + subst.
        econstructor. { apply dep_get_repl. }
        apply dep_get_steps' with (x := 0) in H.
        destruct H as [? [? H]]. inv H.
        eapply H_trans;[idtac | eapply sub_weak; try eassumption | idtac].
        * now rewrite ren_size_inv.
        * intros. change Delta,,B' with Delta,,,(nil,,B'). rewrite app_assoc.
          cutrewrite (S (length Delta') = length (nil,,B',,,Delta')); 
            first by apply dep_get_steps.
          rewrite app_length. simpl. omega.
        * ssimpl in IHsub.
          eapply IHsub; now eauto. 
      + econstructor; eauto.
        eapply dep_get_repl; now eauto.
    - constructor; now eauto.
    - constructor. 
      + now eauto. 
      + eapply wf_weak'. eassumption.
        repeat rewrite app_length. simpl. omega.
      + change Delta,,B',,,Delta',,B1 with Delta,,B',,,(Delta',,B1).
        eapply IHsub2; eauto. reflexivity.
  }
Qed.

Corollary sub_trans Delta A B C: sub Delta A B -> sub Delta B C -> sub Delta A C.
Proof.
  intros. eapply sub_trans'; eauto.
Qed.