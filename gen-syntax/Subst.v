Require Import lib Size Omega List ssreflect ssrfun util MMap.

Delimit Scope subst_scope with subst.
Open Scope subst_scope.

Definition scons {X : Type} s sigma x : X := match x with S x' => sigma x' | _ => s end.
Infix ".:" := scons (at level 60, right associativity) : subst_scope.

Definition lift (x y : var) : var := plus x y.

Arguments lift !x !y.

Notation "( + x )" := (lift x) (format "( + x )").

Definition upr xi := 0 .: (fun x => (+1) (xi x)).

Class Subst (term : Type) := {
  Var : var -> term;
  rename : (var -> var) -> term -> term;
  subst : (var -> term) -> term -> term
}.

Definition rcomp (xi zeta : var -> var) := zeta \o xi. 
Arguments rcomp xi zeta x /.

Notation "xi >>> zeta" := (rcomp xi zeta) (at level 55, left associativity) : subst_scope.
Notation "sigma >> tau" := (subst tau \o sigma) (at level 55, left associativity) : subst_scope.
(*Notation "sigma >>' tau" := (mmap(subst tau) \o sigma) (at level 55, left associativity) : subst_scope.*)
Notation "s .[ sigma ]" := (subst sigma s) (at level 2, sigma at level 200, left associativity, format "s .[ sigma ]" ) : subst_scope.
(*Notation "s ..[ sigma ]" := (mmap (subst sigma) s) (at level 2, sigma at level 200, left associativity, format "s ..[ sigma ]" ) : subst_scope.*)
Notation " l ,, x" := (cons x l) (at level 4, left associativity, format "l ,, x") : subst_scope.
Notation " l1 ,,, l2" := (l2 ++ l1) (at level 4, left associativity, format "l1 ,,, l2") : subst_scope.


Notation beta s := (s .: Var) (only parsing).

Definition ren {term : Type}{subst_funs : Subst term} xi (x : var) := Var (xi x).
Arguments ren {_ _} xi x/.
Notation up sigma := ((Var 0) .: sigma >> ren(+1)).


Class SubstLemmas (term : Type) (subst_funs : Subst term) := {
  rename_subst xi : rename xi = subst (ren xi);
  subst_id s : subst Var s = s;
  id_subst x sigma : subst sigma (Var x) = sigma x;
  subst_comp s sigma tau : subst tau (subst sigma s) = subst (sigma >> tau) s
}.


Section Subst.

Context {term : Type}.
Context {subst_funs : Subst term}.
Context {subst_lemmas : SubstLemmas _ subst_funs}.

Ltac ssimpl := 
  msimpl; 
  repeat match goal with 
             [|- context[?s]] => 
             first[
                 progress change s with rename
               | progress change s with subst
               | progress change s with Var
               | progress match s with ?s1 _ => change s1 with Var end] 
         end;
  try rewrite rename_subst;
  try rewrite subst_id;
  try rewrite id_subst;
  try rewrite subst_comp.

Lemma to_lift x : Var(S x) = (Var x).[ren(+1)].
Proof.
now ssimpl.
Qed.

Lemma Var_comp_l (sigma : var -> term) : Var >> sigma = sigma.
Proof.
  f_ext. intros. now ssimpl.
Qed.

Lemma Var_comp_r (sigma : var -> term) : sigma >> Var = sigma.
Proof.
  f_ext. intros. now ssimpl.
Qed.

Lemma zero_scons s sigma : (Var 0).[s .: sigma] = s.
Proof.
  now ssimpl.
Qed.

Lemma comp_assoc (sigma1 sigma2 sigma3 : var -> term) : (sigma1 >> sigma2) >> sigma3 = sigma1 >> sigma2 >> sigma3.
Proof.
  f_ext. intros. now ssimpl.
Qed.

Lemma comp_dist (sigma tau : var -> term) s : (s .: sigma) >> tau = s.[tau] .: sigma >> tau.
Proof.
  f_ext. intros x. now destruct x.
Qed.

Lemma scons_lift (x : var) : x .: lift (S x) = lift x.
Proof.
  unfold var in *.
  f_ext; intro y; destruct y; unfold lift; simpl; omega.
Qed.

Lemma lift_scons_comp s sigma : ren(+1) >> (s .: sigma) = sigma.
Proof.
  f_ext. intros. destruct x; now ssimpl.
Qed.

Lemma scons_Var_ren x xi : Var x .: ren xi = ren (x .: xi).
Proof.
  f_ext. intros y. now destruct y.
Qed.

Lemma lift_comp n m: (+n) >>> (+m) = (+(n+m)).
Proof.
  unfold lift. f_ext. intro. simpl. unfold var in *. omega.
Qed.

Lemma ren_comp xi zeta : ren xi >> ren zeta = ren (xi >>> zeta).
Proof.
  f_ext. intro. now ssimpl.
Qed.

Lemma fold_ren (xi zeta : var -> var) : (fun x => Var (xi (zeta x))) = ren (fun x => xi (zeta x)). reflexivity. Qed.

Lemma subst_comp' sigma tau : subst sigma \o subst tau = subst (tau >> sigma).
Proof.
  f_ext. intro. now ssimpl.
Qed.

Lemma ren_uncomp A xi zeta : A.[ren (xi >>> zeta)] = A.[ren xi].[ren zeta].
Proof.
  ssimpl. now rewrite ren_comp.
Qed.

(*
Fixpoint interp_ctxt Gamma A :=
  match Gamma with 
    | nil => A
    | Gamma,, B => A.[interp_ctxt Gamma B .: (fun x => interp_ctxt Gamma (Var x))]
  end.
*)
End Subst.

Hint Rewrite 
     @rename_subst @subst_id @id_subst @subst_comp @to_lift @Var_comp_l @Var_comp_r 
     @zero_scons @comp_assoc @comp_dist @scons_lift @lift_scons_comp @scons_Var_ren @lift_comp @ren_comp @fold_ren @subst_comp'
NPeano.Nat.add_1_r : subst.


Arguments rename {_ _}  xi s : simpl never.
Arguments subst {_ _} sigma s : simpl never.

Notation "'up' sigma" := ((Var 0) .: sigma >> ren(+1)) (at level 1) : subst_scope.

Ltac ssimpl' :=
  try unfold rename;
  try unfold subst;
  simpl; 
  repeat match goal with 
             [|- context[?s]] =>
             let T := typeof s in
             match T with
               | (var -> _) -> ?term -> ?term =>
                 let inst := fresh "inst" in
                 (* assert(inst : Subst term);[
                     now eauto with typeclass_instances | *)
                     first[
                         progress cutrewrite (s = subst);[idtac|reflexivity] | 
                         progress cutrewrite (s = rename);[idtac|reflexivity] ]
               | (var -> ?term) =>
                 (*assert(Subst term);[
                     now eauto with typeclass_instances | *)
                         progress cutrewrite (s = Var);[idtac|reflexivity]
             end
         end
.

Ltac ssimpl'H H :=
  try unfold rename in H;
  try unfold subst in H;
  simpl in H; 
  repeat (
      let T := typeof H in
      match T with context[?s] =>                           
        first[
            progress change s with Var in H
          | progress change s with rename in H
          | progress change s with subst in H
          ] 
      end 
    ).


Ltac ssimpl := 
  repeat(
     msimpl;
     ssimpl';
     try(autorewrite with subst; [idtac | now eauto with typeclass_instances ..])
    ); trivial.

Ltac ssimplH H := 
  repeat(
     msimplH H;
     ssimpl'H H;
      autorewrite with subst in H; [idtac | now eauto with typeclass_instances ..]
    ); trivial.

Tactic Notation "ssimpl" "in" ident(H) := ssimplH H.

Tactic Notation "ssimpl" "in" "*" := (in_all ssimplH); ssimpl.

Ltac gen_rename := 
fix rename 2; intros xi s;
destruct s eqn:E;
let term := typeof s in
match goal with 
    [E : s = ?s' |- _] =>
    let rec map s := 
        (match s with 
             ?s1 ?s2 => 
             let s1' := map s1 in
             let s2_T := typeof s2 in
             let s2' := match s2_T with 
                         | term => constr:(rename xi s2) 
                         | bind term => constr:(rename (upr xi) s2)
                         | var => constr:(xi s2)
                         | _ => s2 
                       end in
             constr:(s1' s2')
           | _ => s end) in 
    let t' := map s' in 
    exact t'
end.

Ltac has_var s := 
  match s with 
    | ?s1 ?s2 => 
      match has_var s1 with 
        | Some ?x => constr:(Some x)
        | _ => 
          match typeof s2 with 
            | var => constr:(Some s2) 
            | _ => None
          end 
      end
    | _ => None
  end.


Notation "'_up_' ( rename , Var , sigma )" := 
  ((Var 0) .: (rename (+1) \o sigma)) (only parsing).

Ltac gen_subst Var rename :=
fix subst 2; intros sigma s;
destruct s eqn:E;
let term := typeof s in
match goal with 
    [E : s = ?s' |- _] =>
    let rec map s := 
        (match s with 
             ?s1 ?s2 => 
             let s1' := map s1 in
             let s2_T := typeof s2 in
             let s2' := match s2_T with 
                         | term => constr:(subst sigma s2) 
                         | bind term => constr:(subst (_up_(rename, Var, sigma)) s2)
                         | var => constr:(sigma s2)
                         | _ => s2 
                       end in
             constr:(s1' s2')
           | _ => s end) in 
    match has_var s' with 
        | Some ?v => exact (sigma v)
        | _ => let t' := map s' in try exact t'
    end
end.

Ltac app_var := match goal with [ |- var] => assumption end.

Ltac gen_Subst := 
match goal with [|- Subst ?term] => 
assert (Var : var -> term); [intro; solve[constructor 1; [app_var] | constructor 2; [app_var] | constructor 3; [app_var] | constructor 4; [app_var] | constructor 5; [app_var] | constructor 6; [app_var] | constructor 7; [app_var] | constructor 8; [app_var] | constructor 9; [app_var] | constructor 10; [app_var] | constructor 11; [app_var] | constructor 12; [app_var] | constructor 13; [app_var] | constructor 14; [app_var] | constructor 15; [app_var] | constructor 16; [app_var] | constructor 17; [app_var] | constructor 18; [app_var] | constructor 19; [app_var] | constructor 20] | idtac];
assert (rename : (var -> var) -> term -> term ); [gen_rename | ..];
assert (subst : (var -> term) -> term -> term); [gen_subst Var rename | ..];
refine (Build_Subst _ Var rename subst)
end.

Ltac gen_SubstLemmas :=
repeat match goal with [H : _ |- _] => clear H end;
match goal with [ |- @SubstLemmas ?term ?subst_funs] =>
let rename := constr:(@rename term subst_funs) in
let subst := constr:(@subst term subst_funs) in
let Var := constr:(@Var term subst_funs) in
assert(rename_subst : forall xi : var -> var, rename xi = subst (ren xi));[
let xi := fresh "xi" in intros xi; 
f_ext; 
let s := fresh "s" in intros s; 
revert xi; induction s; 
intros; ssimpl'; f_equal; eauto;
autorew; ssimpl; f_equal; f_ext; 
let x := fresh "x" in intros x; now destruct x
| idtac];

assert(subst_id : forall s : term, subst Var s = s);[
let s := fresh "s" in intros s; induction s; 
ssimpl'; f_equal; eauto;
match goal with [H : _ |- _ ] => rewrite <- H end; 
f_equal; solve[ f_ext; intros [|]; reflexivity | assumption] 
| idtac];

assert(id_subst : forall (x : var) (sigma : var -> term), subst sigma (Var x) = sigma x);
[intros; reflexivity | idtac];
assert(rename_subst_comp : forall s sigma xi, (rename xi s).[sigma] = s.[ren xi >> sigma]);[
let s := fresh "s" in intros s; induction s; 
intros; ssimpl'; f_equal; eauto; ssimpl'; 
autorew; f_equal; f_ext; intros [|]; reflexivity
| idtac];

assert(rename_comp : forall xi1 xi2 x, rename xi1 (rename xi2 x) = rename (fun x => xi1(xi2 x)) x);[
intros; rewrite rename_subst; 
rewrite rename_subst_comp; now rewrite rename_subst
| idtac];

assert(up_rename_comm: forall sigma xi, up (sigma >> (ren xi)) = up sigma >> (ren (upr xi)));[
intros; f_ext; intros [|]; ssimpl'; trivial; 
intros; repeat rewrite <- rename_subst; now repeat rewrite rename_comp
| idtac];

assert(subst_rename_comp : forall s sigma xi, rename xi s.[sigma] = s.[sigma >> (ren xi)]);[
let s := fresh "s" in intros s; induction s; unfold funcomp in *;
solve[ 
match goal with [x : var |- _ ] => destruct x; ssimpl'; intros; now rewrite rename_subst end |
intros; ssimpl'; unfold funcomp; f_equal; now autorew]
| idtac];

assert(subst_up_S : forall sigma s, rename S s.[sigma] = (rename S s).[up sigma]);[
intros;
rewrite subst_rename_comp; rewrite rename_subst_comp;
f_equal; f_ext; intros; ssimpl'; now rewrite rename_subst
| idtac];

assert(subst_comp : forall (s : term) (sigma tau : var -> term),
                 subst tau (subst sigma s) =
                 subst (fun x : var => subst tau (sigma x)) s );[
intros s; induction s; intros; ssimpl'; f_equal; autorew; f_equal; trivial;
f_ext; intros [|]; intros; ssimpl'; autorew; trivial; repeat rewrite <- rename_subst; now autorew
| idtac];

constructor; assumption
end.
(*
Inductive term : Type :=
| Universe : nat -> term
| Lam : term -> bind term -> term
| CCVar : var -> term
| Prod : term -> bind term -> term
| App : term -> term -> term
.

Instance SubstTerm : Subst term.
gen_Subst. Defined.

Instance SubstLemmasTerm : SubstLemmas term SubstTerm.
gen_SubstLemmas. Defined.

Lemma beta_subst (s t : term) sigma : 
  s.[t .: Var].[sigma] = s.[Var 0 .: sigma >> lift].[t.[sigma] .: Var]. now ssimpl. Qed.
*)
