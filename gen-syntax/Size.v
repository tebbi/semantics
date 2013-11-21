Require Import lib.
(*
Delimit Scope pnat_scope with pnat.
Open Scope pnat_scope.

Unset Elimination Schemes.
Inductive pnat : Prop := O' | S' (pred : pnat).
Lemma pnat_ind : forall P : pnat -> Prop,
       P O' -> (forall n, P n -> P (S' n)) -> forall n, P n.
fix pnat_ind' 4.
intros. destruct n.
- apply H.
- apply H0. apply pnat_ind'; assumption.
Qed.
Set Elimination Schemes.

Fixpoint pplus n m := 
  match n with
    | O' => m
    | S' n' => S'(pplus n' m)
  end.

Infix "+'" := pplus (at level 50, left associativity) : pnat_scope.

Lemma pplus_assoc n1 n2 n3 : n1 +' (n2 +' n3) = n1 +' n2 +' n3.
Proof.
  revert n2 n3.
  induction n1; simpl; intuition. now f_equal.
Qed.


Lemma pplus_zero_l n : O' +' n = n. 
Proof. reflexivity. Qed.

Lemma pplus_zero_r n : n +' O' = n. 
Proof.
  induction n; simpl; now autorew.
Qed.

Lemma pplus_succ_l n m : S' n +' m  = S'(n +' m). 
Proof. reflexivity. Qed.

Lemma pplus_succ_r n m : n +' S' m  = S'(n +' m). 
Proof.
  induction n; simpl; now autorew.
Qed.

Hint Rewrite pplus_assoc pplus_zero_l pplus_zero_r pplus_succ_l pplus_succ_r : pplus.

Lemma pplus_comm n m : n +' m = m +' n.
Proof.
  revert m.
  induction n; intros; simpl; autorewrite with pplus; now autorew.
Qed.

Definition pleq n m := exists n', m = n +' n'.
Infix "<='" := pleq(at level 70, no associativity) : pnat_scope.

Lemma pleq_S n m : n <=' m -> S' n <=' S' m.
Proof.
  intros. destruct H. eexists. simpl. f_equal. eassumption.
Qed.

Lemma pleq_S_r n m : n <=' m -> n <=' S' m.
Proof.
  intros. destruct H. exists (S' x). autorewrite with pplus. f_equal. eassumption.
Qed.

Lemma pleq_zero n : O' <=' n.
Proof.
  eexists. reflexivity.
Qed.

Lemma pleq_plus n1 n2 m : n1 <=' n2 -> n1 +' m <=' n2 +' m.
Proof.
  intros H. destruct H as [x H]. exists x. 
  rewrite H.
  repeat rewrite <- pplus_assoc.
  now rewrite (@pplus_comm m x).
Qed.


Lemma pleq_plus_r n m : n <=' m +' n.
Proof.
  eexists.
  now rewrite pplus_comm.
Qed.
*)

Class Size (A : Type) := size : A -> nat.

Ltac gen_Size :=
hnf; match goal with [ |- ?A -> nat] =>
fix size' 1; intros s;
assert(size_inst : Size A);[exact size' | idtac];
destruct s eqn:E;
let term := type of s in
match goal with 
    [E : s = ?s' |- _] =>
    let rec map s := 
        (match s with 
             ?s1 ?s2 => 
             let size_s1 := map s1 in
             let s2_T := type of s2 in
             let size_s2 := match s2_T with 
                         | A => constr:(size' s2)
                         | _ => constr:(size s2)
                       end in
             constr:(size_s1 + size_s2)
           | _ => constr:(O) end) in 
    let t' := map s' in
    let t'' := eval simpl plus in t' in
    exact (S t'')
end
end.

Require Import Omega.

Lemma size_rec {A : Type} {size_A : Size A} f (x : A) : forall P : A -> Type, (forall x, (forall y, f y < f x -> P y) -> P x) -> P x.
Proof.
  intros P IS. cut (forall n x, f x <= n -> P x). { eauto. } 
  intros n. induction n; intros; apply IS; intros. 
  - omega.
  - apply IHn. omega.
Defined.


Tactic Notation "sinduction" ident(H) "using" constr(f) :=
autorevert H; induction H using (size_rec f); destruct H.

Tactic Notation "sinduction" ident(H) := sinduction H using size.

Ltac somega := repeat(unfold size in *; simpl in *); omega.

Instance def_size (A : Type) : Size A | 100 := (fun x => O).

Instance size_list (A : Type) (size_A : Size A) : Size (list A). gen_Size. Show Proof. Defined.

Instance size_nat : Size nat. gen_Size. Show Proof. Defined.

Inductive foo := Foo1 | Foo2 (_ : list foo) (_ : nat).

Instance size_foo : Size foo. gen_Size. Set Printing Implicit. Show Proof. Defined.

(*
Ltac elim_term :=
let rec elim2 x t := 
    match t with
      | ?t1 +' x => repeat rewrite pplus_assoc
      | ?t1 +' ?t2 =>
        refine(eq_ind_r (fun p : pnat => _ <=' _ +' p) _ (pplus_comm _ _));
        refine(eq_ind_r (fun p : pnat => _ <=' p) _ (pplus_assoc _ _ _));
        elim2 x t1
      | x => idtac
    end
in let elim1 x t := 
    match t with 
      | ?t1 +' x => idtac
      | ?t1 +' ?t2 => 
        refine(eq_ind_r (fun p : pnat => _ <=' p) _ (pplus_comm _ _));
          elim2 x t1
      | _ => idtac
    end 
in
  match goal with 
    | [ |- ?s +' ?x <=' ?t ] => elim1 x t; apply pleq_plus
    | [ |- ?x <=' ?t ] => elim1 x t; apply pleq_plus_r
  end.

Ltac solve_pleq :=
  intros;
  repeat match goal with [H : ?x <=' ?y |- _] => destruct H end;
  autorew;
  autorewrite with pplus;
  repeat apply pleq_S;
  repeat apply pleq_S_r;
  try apply pleq_zero;
  repeat elim_term.
*)
(*
Inductive ord : Prop :=
C (A : Type) : (A -> ord) -> ord.
*)