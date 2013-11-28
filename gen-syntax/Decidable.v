Definition dec (X : Prop) : Type := {X} + {~ X}.
Class Dec (X : Prop) : Type := decide : dec X.
Arguments decide X {_}.

Ltac gen_Dec := unfold Dec; unfold dec; decide equality.

Instance decide_eq_nat (x y : nat) : Dec (x = y). gen_Dec. Defined.

Tactic Notation "decide" constr(p) := destruct (decide p).