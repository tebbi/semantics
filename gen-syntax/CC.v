Require Import Subst.

Inductive term : Type :=
| Universe : nat -> term
| Lam : term -> bind term -> term
| CCVar : var -> term
| Prod : term -> bind term -> term
| App : term -> term -> term
.

Instance subst_term : Subst term. gen_Subst. Defined.
Instance substLemmas_term : SubstLemmas subst_term. gen_SubstLemmas. Defined.

