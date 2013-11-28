Require Import lib Omega util Subst List.

Section Subst.

Context {term : Type}.
Context {subst_funs : Subst term}.
Context {subst_lemmas : SubstLemmas _ subst_funs}.

Inductive dep_get {term : Type} {term_subst : Subst term} 
: list term -> var -> term -> Prop :=
| Get0 Delta A: dep_get Delta,,A 0 A.[ren(+1)]
| GetS Delta x A B : dep_get Delta x B -> dep_get Delta,,A (S x) B.[ren(+1)]
.

Lemma lift_inj A B n : A.[ren(+n)] = B.[ren(+n)] -> A = B.
Proof.
  intros H. 
  apply (f_equal (subst (ren (fun x => x - n)))) in H.
  ssimpl in H.
  cutrewrite ( ren ((+n) >>> ((fun x : var => x - n) : var -> var)) = Var) in H.
  now ssimpl in H.
  unfold lift.
  f_ext. intros x. simpl. f_equal. omega.
Qed.

Lemma dep_get_steps x Gamma Delta A : dep_get Gamma x A <-> dep_get (Gamma,,,Delta) (length Delta + x) A.[ren(+(length Delta))].
Proof.
  revert A x.
  induction Delta; intros.
  - split. 
    + now ssimpl.
    + intros H. simpl in H.
      unfold lift in *. 
      unfold ren in *.
      simpl in *.
      now rewrite subst_id in H.
  - simpl. cutrewrite (A.[ren (+S (length Delta))] = A.[ren(+length Delta)].[ren(+1)]). { split.
      + constructor. now apply IHDelta.
      + intros H. inv H. rewrite IHDelta. apply lift_inj in H4. rewrite H4 in H1. eassumption.
    }
                                                                                   rewrite subst_comp. f_equal. f_ext. intros x'. now ssimpl.
Qed.

Lemma dep_get_steps' x Gamma Delta A :  dep_get (Gamma,,,Delta) (x + length Delta) A ->
                               exists B, A = B.[ren(+(length Delta))] /\ dep_get Gamma x B.
Proof.
  revert A x.
  induction Delta; intros.
  - exists A.
    simpl in H.
    rewrite plus_0_r in H.
    intuition. 
  - simpl in *.
    rewrite NPeano.Nat.add_succ_r in *.
    inv H.
    edestruct IHDelta as [B' [? ?]]; eauto. exists B'. subst.
    ssimpl. intuition.
Qed.

Corollary dep_get_step Delta A x B : dep_get Delta x A <-> dep_get (Delta,,B) (S x) A.[ren(+1)].
Proof.
  apply dep_get_steps with (Delta := B :: nil).
Qed.

Lemma dep_get_repl Gamma A Delta : 
  (dep_get Gamma,,A,,,Delta (length Delta) A.[ren(+ S (length Delta))]) /\
  (forall x B A', x <> length Delta -> dep_get Gamma,,A,,,Delta x B -> dep_get Gamma,,A',,,Delta x B).
Proof.
  split.
  - pose proof (dep_get_steps 0 Gamma,,A Delta A.[ren(+1)]) as H.
    rewrite plus_0_r in H.
    cutrewrite (A.[ren (+1)].[ren (+length Delta)] =  A.[ren (+S (length Delta))]) in H. { apply H. constructor. }
    now ssimpl.
  - intros x. revert Gamma A Delta.
    induction x; intros Gamma A Delta H B A' H_get.
    + destruct Delta as [| C Delta]. { now intuition. }
      simpl in *.
      inv H_get. constructor. 
    + destruct Delta as [| C Delta]; simpl in *. 
      * inv H_get. now constructor.
      * inv H_get. constructor. eapply IHx; eauto.
Qed.

Lemma dep_get_defined Delta x : (exists B, dep_get Delta x B) <-> x < length Delta.
Proof.
  revert Delta.
  induction x; intros; split.
  - intros [? H]. inversion H. simpl. omega.
  - intro H. destruct Delta; first by inversion H. eexists. constructor.
  - intros [? H]. inversion H. simpl.
    assert(x < length Delta0).
    { apply IHx. eexists. eassumption. }
    omega.
  - intro H. destruct Delta; first by inversion H. 
    destruct (IHx Delta) as [_ IHx']. 
    edestruct IHx'; first by simpl in H; omega.
    eexists. constructor. eassumption.
Qed.

End Subst.