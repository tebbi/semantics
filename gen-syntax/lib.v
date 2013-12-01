Definition bind {X : Type} (T : X) := T.
Definition var := nat.

Ltac autorew := repeat match goal with [H : _ |- _] => rewrite H end.

Ltac typeof s := let T := type of s in T.
Notation nosimpl t := (let tt := tt in t).

Require Import FunctionalExtensionality.
Ltac f_ext := apply functional_extensionality.

Definition id {A} (x : A) := x.
Arguments id {A} x /.
Hint Unfold id.

Ltac autorevert x := 
  try (match goal with
    | [y : ?Y |- ?claim] =>
      try(match x with y => idtac end; fail 1);
        match goal with [z : _ |- _] => 
          match claim with appcontext[z] => 
            first[
                match Y with appcontext[z] => revert y; autorevert x end 
              | match y with z => revert y; autorevert x end]  
          end
        end 
       end).

Tactic Notation "in_all" tactic(T) :=
  repeat match goal with [H : _ |- _] =>
                  first[T H; try revert H | revert H]
  end; intros.

Lemma conj' (A B : Prop) : A -> (A -> B) -> A /\ B. 
Proof. tauto. Qed.
