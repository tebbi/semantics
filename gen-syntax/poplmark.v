Require Import Program.Equality ssreflect ssrfun List.
Require Import MMap Subst Size util lib Decidable Ctxts.

Inductive type : Type :=
| TyVar (x : var)
| Top
| Arr (A1 A2 : type)
| All (A1 : type) (A2 : bind type).

Instance subst_type : Subst type. gen_Subst. Defined.
Instance substLemmas_type : SubstLemmas _ subst_type. 
admit;gen_SubstLemmas. Qed.
Instance size_type : Size type. 
assert(Size var). exact(fun _ => 0).
gen_Size. Defined.

Lemma ren_size_inv A : forall xi, size A.[ren xi] = size A.
Proof.
  induction A; intros; sizesimpl; repeat(ssimpl; try autorew); try somega.
Qed.

Fixpoint wf_ty Delta A := match A with
  | TyVar x => exists B, dget Delta x B
  | Top => True
  | Arr A B => wf_ty Delta A /\ wf_ty Delta B
  | All A B => wf_ty Delta A /\ wf_ty Delta,,A B
end.

Reserved Notation "'SUB' Delta |- A <: B" (at level 68, A at level 99, no associativity).
Inductive sub (Delta : list type) : type -> type -> Prop :=
| SA_Top A : wf_ty Delta A -> SUB Delta |- A <: Top
| SA_Refl x : wf_ty Delta (Var x) -> SUB Delta |- Var x <: Var x
| SA_Trans x A B : dget Delta x A -> SUB Delta |- A <: B -> SUB Delta |- Var x <: B 
| SA_Arrow A1 A2 B1 B2 : SUB Delta |- B1 <: A1 -> SUB Delta |- A2 <: B2 -> SUB Delta |- Arr A1 A2 <: Arr B1 B2
| SA_All A1 A2 B1 B2 : SUB Delta |- B1 <: A1 -> wf_ty Delta B1 -> SUB Delta,,B1 |- A2 <: B2 -> SUB Delta |- All A1 A2 <: All B1 B2
where "'SUB' Delta |- A <: B" := (sub Delta A B).

Lemma wf_weak Delta1 Delta2 A xi : 
  wf_ty Delta1 A -> 
  (forall x B, dget Delta1  x B -> exists B', dget Delta2 (xi x) B') -> 
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
  apply dget_defined.
  cut(id x < length Delta1). omega.
  apply dget_defined.
  eexists. eassumption.
Qed.

Lemma sub_refl Delta A : wf_ty Delta A -> SUB Delta |- A <: A.
Proof.
  revert Delta. induction A; simpl; intuition; eauto using sub.
Qed.

Lemma sub_weak Delta1 Delta2 A1 A2 xi : SUB Delta1 |- A1 <: A2 -> 
  (forall x B, dget Delta1 x B -> dget Delta2 (xi x) B.[ren xi]) -> 
  SUB Delta2 |- A1.[ren xi] <: A2.[ren xi] .
Proof.
   intros H. aind H.
   - constructor. eapply wf_weak; now eauto.
   - econstructor; ssimpl.
     + now eauto.
     + eapply wf_weak; now eauto.
     + apply IHsub2. intros.
       destruct x; ssimpl; arew; ssimpl; rewrite (ren_uncomp _ _ (+1)); arew. 
Qed.

Lemma sub_wf {Delta A B} : SUB Delta |- A <: B -> wf_ty Delta A /\ wf_ty Delta B.
Proof.
  intros H. aind H.
  eapply wf_weak'. eassumption.
  now simpl.
Qed.

Lemma sub_trans' n : 
  (forall Delta A B C, n = size B ->
     SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C) /\
  (forall Delta' Delta B B' A C, n = size B ->
     SUB Delta,,B,,,Delta' |- A <: C ->
     SUB Delta |- B' <: B -> 
     SUB Delta,,B',,,Delta' |- A <: C).
Proof.
  induction n as [n IH] using (size_rec (fun x => x)).
  apply conj'.
  {
    intros Delta A B C ? H_AB H_BC. subst.
    revert C H_BC.
    induction H_AB; prepare.
    - now arew.
    - econstructor; now eauto.
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
      apply dget_defined. apply dget_defined in H.
      repeat rewrite -> app_length in *. simpl in *. omega.
    - decide (x = length Delta').
      + subst.
        econstructor. { apply dget_repl. }
        apply dget_steps' with (x := 0) in H.
        destruct H as [? [? H]]. inv H.
        eapply H_trans;[idtac | eapply sub_weak; try eassumption | idtac].
        * now rewrite ren_size_inv.
        * intros. change Delta,,B' with Delta,,,(nil,,B'). rewrite app_assoc.
          cutrewrite (S (length Delta') = length (nil,,B',,,Delta')); 
            first by apply dget_steps.
          rewrite app_length. simpl. omega.
        * ssimpl in IHsub.
          eapply IHsub; now eauto. 
      + econstructor; eauto.
        eapply dget_repl; now eauto.
    - constructor; now eauto.
    - constructor. 
      + now eauto. 
      + eapply wf_weak'. eassumption.
        repeat rewrite app_length. simpl. omega.
      + change Delta,,B',,,Delta',,B1 with Delta,,B',,,(Delta',,B1).
        eapply IHsub2; eauto. reflexivity.
  }
Qed.

Theorem sub_trans Delta A B C: 
  SUB Delta |- A <: B -> SUB Delta |- B <: C -> SUB Delta |- A <: C.
Proof.
  intros. eapply sub_trans'; eauto.
Qed.


Inductive term :=
| TeVar (x : var)
| Abs (A : type) (s : bind term)
| App (s t : term)
| TAbs (A : type) (s : bind term)
| TApp (s : term) (A : type)
.

Instance subst_term : Subst term. gen_Subst. Defined.
Instance substLemmas_term : SubstLemmas _ subst_term. 
gen_SubstLemmas. Defined.
Instance size_term : Size term. 
assert(Size var). exact(fun _ => 0).
gen_Size. Defined.

Instance mmap_term : MMap type term.
gen_MMap.
Defined.

Instance mmapLemmas_term : MMapLemmas mmap_term.
gen_MMapLemmas.
Defined.

Inductive value : term -> Prop :=
| Value_Abs A s : value(Abs A s)
| Value_TAbs A s : value(TAbs A s).

(*
Fixpoint wf_term Delta Gamma A := 
  match A with
    | TeVar x => exists B, get Gamma x B
    | Abs A s => wf_ty Delta A /\ wf_term Delta Gamma,,A s
    | App s t => wf_term Delta Gamma s /\ wf_term Delta Gamma t
    | TAbs A s => wf_ty Delta A -> wf_term Delta,,A Gamma s
    | TApp s A => wf_term Delta Gamma s /\ wf_ty Delta A
  end.
*)

Reserved Notation "'TY' Delta ; Gamma |- A : B" (at level 68, A at level 99, no associativity, format "'TY'  Delta ; Gamma  |-  A  :  B").
Inductive ty (Delta Gamma : list type) : term -> type -> Prop :=
| T_Var A x : 
    get Gamma x A   -> 
    TY Delta;Gamma |- Var x : A
| T_Abs A B s: 
    TY Delta;Gamma,,A |- s : B   ->   wf_ty Delta A   ->
    TY Delta;Gamma |- Abs A s : Arr A B
| T_App A B s t: 
    TY Delta;Gamma |- s : Arr A B   ->   TY Delta;Gamma |- t : A   -> 
    TY Delta;Gamma |- App s t : B
| T_TAbs A B s : 
    TY Delta,,A;Gamma |- s : B   ->   wf_ty Delta A   ->
    TY Delta;Gamma |- TAbs A s : All A B
| T_TApp A B A' s B' : 
    TY Delta;Gamma |- s : All A B   ->   SUB Delta |- A' <: A   -> B' = B.[A' .: Var] ->
    TY Delta;Gamma |- TApp s A' : B'
| T_Sub A B s : 
    TY Delta;Gamma |- s : A   ->   SUB Delta |- A <: B   ->
    TY Delta;Gamma |- s : B
where "'TY' Delta ; Gamma |- s : A" := (ty Delta Gamma s A).

Reserved Notation "'EV' s => t" (at level 68, s at level 80, no associativity, format "'EV'   s  =>  t").
Inductive eval : term -> term -> Prop :=
| E_AppAbs A s t : EV  App (Abs A s) t => s.[t .: Var]
| E_TAppTAbs A s B : EV  TApp (TAbs A s) B => s..[B .: Var]
| E_AppFun s s' t : 
    EV  s => s' -> 
    EV  App s t => App s' t
| E_AppArg s s' v: 
    EV  s => s' -> value v ->
    EV  App v s => App v s'
| E_TypeFun s s' A :
    EV  s => s' ->
    EV  TApp s A => TApp s' A
where "'EV' s => t" := (eval s t).


Lemma ty_weak Delta1 Delta2 Gamma1 Gamma2 s A xi zeta : 
  TY Delta1;Gamma1 |- s : A -> 
  (forall x B, dget Delta1 x B -> dget Delta2 (xi x) B.[ren xi]) -> 
  (forall x B, get Gamma1 x B -> get Gamma2 (zeta x) B.[ren xi]) -> 
  TY Delta2;Gamma2 |- s.[ren zeta]..[ren xi] : A.[ren xi] .
Proof.
   intros H. autorevert H; induction H; intros.
   - econstructor; now eauto.
   - ssimpl. econstructor.
     + apply IHty; eauto. intros [|]; arew.
     + eapply wf_weak; now eauto.
   - ssimpl. econstructor; arew.
   - ssimpl. econstructor.
     + apply IHty; eauto. intros [|]; arew.

ineconstructor.
 (econstructor; try now
   match goal with [H : _ |- _ ] => ssimpl; eapply H; now eauto end). ssimpl. eapply sub_weak; now intuition.
   
 ssimpl.   
   
ssimpl'. eapply IHty.
intuition. eauto. ; arew.
   - constructor. eapply wf_weak; now eauto.
   - econstructor; ssimpl.
     + now eauto.
     + eapply wf_weak; now eauto.
     + apply IHsub2. intros.
       destruct x; ssimpl; arew; ssimpl; rewrite (ren_uncomp _ _ (+1)); arew. 
Qed.