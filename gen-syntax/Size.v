Require Import lib.

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

Lemma size_rec {A : Type} f (x : A) : forall P : A -> Type, (forall x, (forall y, f y < f x -> P y) -> P x) -> P x.
Proof.
  intros P IS. cut (forall n x, f x <= n -> P x). { eauto. } 
  intros n. induction n; intros; apply IS; intros. 
  - omega.
  - apply IHn. omega.
Defined.


Tactic Notation "sinduction" ident(H) "using" open_constr(f) :=
let T := typeof H in
autorevert H; induction H using (@size_rec _ f);
match goal with [H : T |- _] => destruct H end.

Ltac sind H := 
let IH := fresh "IH" in
let x := fresh "x" in
induction H as [x IH] using (@size_rec _ size); try rename x into H.

Instance def_size (A : Type) : Size A | 100 := (fun x => O).

Instance size_list (A : Type) (size_A : Size A) : Size (list A). gen_Size. Show Proof. Defined.

Instance size_nat : Size nat := id.

Inductive foo := Foo1 | Foo2 (_ : list foo) (_ : nat).

Instance size_foo : Size foo. gen_Size. Set Printing Implicit. Show Proof. Defined.

Ltac sizesimpl := repeat(unfold size in *; unfold def_size in *; simpl in *).

Tactic Notation "somega" := sizesimpl; omega.

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