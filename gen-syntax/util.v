Require Import lib.

Ltac typeof A := let x := (type of A) in constr : x.

(* a variant of subst that prefers older variables *)
Ltac subst' := 
  try match goal with 
      [x : _ |- _] => subst x; subst'
  end.

Require Import Omega.

Require Import ssreflect ssrfun eqtype ssrbool ssrnat seq.
Require Import Add_tactics.AddTactics.
Require Import Coq.Program.Tactics.

Ltac done :=
  trivial; hnf; intros; solve
   [ do 10![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

Definition nth_option {A} (s : seq A) n := nth None (map some s) n.

Lemma equal_f {A B : Type} {f g : A -> B} : f = g -> forall x, f x = g x.
Proof. move=> H. rewrite H //. Qed.


Lemma funcomp_assoc (A B C D: Type) (f : A -> B) g (h : C -> D) : (f \o g) \o h = f \o (g \o h).
Proof. done. Qed.


Lemma eq_falseE b : b = false <-> ~~ b.
Proof. case b; firstorder. Qed.
Lemma andE b1 b2 : b1 && b2 <-> b1 /\ b2.
Proof. split; try apply /andP. move /andP. apply. Qed.
Lemma orE b1 b2 : b1 || b2 <-> b1 \/ b2.
Proof. split. apply /orP. move /orP. apply. Qed.
Lemma eq_trueE b : b = true <-> b. 
Proof. done. Qed.
Lemma eq_opE (T : eqType) (s t : T) : s == t <-> s = t.
Proof. split; move/eqP => H //.  Qed.
Lemma neg_eq_opE (T : eqType) (s t : T) : s != t <-> ~ s = t.
Proof. split; move/eqP => H //. Qed.
Lemma leibniz_refl T (s : T) : s = s <-> True. 
Proof. intuition. Qed.
Lemma is_trueE1 : true <-> True.
Proof. by intuition. Qed.
Lemma is_trueE2 : false <-> False.
Proof. by intuition. Qed.

Lemma leqE m n: (m <= n) <-> (m <= n)%coq_nat.
Proof.  by split => /leP A. Qed.

Lemma mulnE' : muln = mult. 
Proof. done. Qed.

Lemma negbE b : ~~ b <-> ~ b.
Proof. case b; by intuition. Qed.

Ltac elim_bool := 
  try rewrite -> eq_falseE in *;
  try rewrite -> eq_trueE in *;
  repeat first [
           rewrite -> negbE in * |
           rewrite -> orE in * |
           rewrite -> andE in * |
           rewrite -> eq_opE in *].

Ltac norm := elim_bool;
try rewrite -> addn0 in *;
try rewrite -> add0n in *;
try rewrite <- addSnnS in *.

Tactic Notation "ren" ident(H) ":" open_constr(T) := 
match goal with [G : T |- _] =>
  let T' := typeof G in unify T T'; rename G into H end.

Tactic Notation "renc" ident(H) ":" open_constr(T) := 
  match goal with [G : appcontext C [T] |- _] =>
                  let TG := typeof G in
                  let CT := context C [T] in
                  unify TG CT;
                  rename G into H 
  end.

Tactic Notation "rev" int_or_var(n) := do n match goal with [H  : _ |- _] => revert H end.

Tactic Notation "swap" ident(A) ident(B) := let C := fresh "tmp" in rename A into C, B into A; rename C into B.

Tactic Notation "nointr" tactic(t) := 
  let m := fresh "marker" in 
  pose (m := tt);
  t; revert_until m; clear m.

Tactic Notation "tmpintr" tactic(t) := nointr (intros; t).


Require Import FunctionalExtensionality.
Tactic Notation "f_ext" := tmpintr(apply functional_extensionality).

Tactic Notation "not" tactic(T) := try(T; fail 1).
Tactic Notation "test" tactic(T) := not(not T).
Tactic Notation "t" tactic(T) := try T.

(*
Ltac autorevert x := 
  try (match goal with
    | [y : _ |- _] =>
      try(match x with y => idtac end; fail 1);
      try(clear y; fail 1);
    (repeat (match goal with [H : appcontext[y] |- _] => (try(match x with H => idtac end; fail 1)); revert H end));
    try revert y; autorevert x
  end).
*)

Ltac autodestr :=
  match goal with
    | [ |- context[match ?s with _ => _ end]] => (destruct s) => *   
    | [ H : context[match ?s with _ => _ end] |- _] => (destruct s) => *
  end.

Ltac app_head s := match s with ?s1 ?s2 => app_head s1 | _ => s end.

Ltac is_constructor_eq s := 
  match s with 
    | ?s1 = ?s2 => 
      let s1' := app_head s1 in
      let s2' := app_head s2 in
      is_constructor s1'; is_constructor s2' 
    | _ => fail "no equation" 
  end.

Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Ltac is_trivial s := try (assert s; [clear_all; (done || fail 1) | fail]).

Inductive tag_type := Used | InvEq | Added.
(*
Inductive tag (type : tag_type) (T : Type) (A : T) := Tag (B : T) (_ : A = B).
*)

Inductive tag (type : tag_type) (T : Type) := Tag (A : T).
Inductive tag' (type : tag_type) (T : Type) (A : T) := Tag'.

Lemma untag type T: tag type T -> T. intuition. Qed.

Ltac use H := let T := typeof H in try match goal with [_ : tag Used T |- _] => fail 2 end; apply (Tag Used) in H.

Ltac use' H := try match goal with [_ : tag' Used _ H |- _] => fail 2 end; pose proof (@Tag' Used _ H).


Ltac add H := 
  let T := typeof H in 
  match goal with 
    | [_ : T |- _] => fail 1
    | [_ : tag' Added _ T |- _] => fail 1 
    | _ => idtac 
  end; 
  pose proof (@Tag' Added _ T);
  pose proof H.


Ltac is_tag s := match s with
                  | tag _ _ _ => idtac
                  | tag' _ _ _ => idtac
                end.

Ltac simplall :=
  simpl;
  let T H := let s := typeof H in try(is_tag s; fail 1); (simpl in H) in
  in_all T.

Ltac clean := 
  (let T H := let s := typeof H in try(is_tag s; fail 1); is_trivial s; clear H in
  in_all T); clear_dups.

Ltac autoinv :=
  match goal with [H : ?s = ?t |- _] => is_constructor_eq (s = t); progress inversion H; try subst end.

Ltac autoceq := 
  match goal with
    | [ |- context[match ?s with _ => _ end]] => (case_eq s)
    | [ H : context[?s'] |- _] => 
      match s' with (match ?s with _ => _ end) =>
        try (is_tag ltac:(typeof H); fail 1);
        try match goal with [_ : tag InvEq H |- _] => fail 2 end;
        match s with _ _ => case_eq s | _ => destruct s end
      end
  end;
    repeat (first[let H := fresh "I" in intro H; rewrite -> H in *; apply (Tag InvEq) in H  | intro]).

Ltac clean_user :=
  (let T H := let s := typeof H in (is_tag s; destruct H as [H]) in
  in_all T);
  clean.

Ltac autoinst :=
  intuition; simpl in *;
  repeat 
  match goal with [H : _ |- _] => 
    hnf in H; 
    let s := typeof H in
    match s with forall _ : ?T, _ =>               
      match goal with [x : T |- _] => first[add (H x) | add( H _ x) | add(H _ _ x)] end
    end
  end.


Ltac somega :=
  unfold maxn in *;
  unfold minn in *;
  (repeat match goal with
    | [ |- context[if ?n < ?m then _ else _]] => let I := fresh "I" in (case_eq (n < m)) => I; try rewrite -> I in * 
| [ H : context[if ?n < ?m then _ else _] |- _] => let I := fresh "I" in (case_eq (n < m)) => I; try rewrite -> I in *
  end);
  elim_bool;
  try rewrite <- plusE in *;
  try rewrite <- minusE in *;
  try rewrite -> mulnE' in *;
  try rewrite -> leqE in *;
  omega.


Ltac prepare := 
  repeat (repeat intro;
  eauto; try congruence; (try by constructor);
  try match goal with
        | |- ?claim => 
          first[
              progress simplall |
              progress subst |
              progress autoinv; idtac ">>> autoinv <<<" |
              f_ext; idtac ">>> f_ext" claim "<<<" | 
              first[is_constructor_eq claim; progress f_equal];idtac ">>> f_equal" claim "<<<"
            ]
      end); 
  clean;
  try (do 40 (match goal with H : _ |- _ => clear H end); fail 1).

Ltac autorew :=
  repeat match goal with [H : _ |- _] => first[rewrite -> H in * | rewrite -> (untag H) in *]; use H; let s := typeof H in idtac ">>> rewrite" H ":" s "<<<" end.

Ltac arew :=
  prepare;
  autorew;
  try match goal with 
        | H : ?s |- _ => 
          try(is_tag s; fail 1);
            use' s;
            progress( 
                (cut True; [ 
                   first[inversion H; subst]; try done
                 | ]); [(intros _ || done) | done ..]; clean
              );
            idtac ">>> inversion<<<"; try idtac ">>>" H ":" s "<<<"
      end;
  first[
  match goal with
    | |- ?claim => 
          first[
              split; idtac ">>> split <<<" 
            | f_ext; idtac ">>> f_ext" claim "<<<" 
            | autoceq; idtac ">>> autodestr <<<" 
            |  first[is_constructor_eq claim; (progress f_equal || exfalso)];idtac ">>> f_equal" claim "<<<" 
            | (*idtac ">>> trying prepare <<<"; 
              try match reverse goal with H : ?T |- _ => idtac ">>>" H ":" T "<<<"; fail end;*) 
              progress prepare; idtac ">>>prepare<<<"
            | somega; idtac ">>>somega<<<"
            ]; arew
        | H : ?s |- ?claim => 
          first[apply H | try(has_evar claim; fail 1); eapply H];
            use H;
            idtac ">>> apply" H s "<<<"; arew; fail 1
        
        | |- ?claim => first[(*progress autoinst; idtac ">>> autoinst <<<"; arew | *)split; idtac ">>> esplit <<<"; arew | econstructor; idtac ">>> constructor <<<"; by arew]
      end | intuition; clean_user].

Require Import Program.Equality.

Tactic Notation "aind" := 
   prepare; try match goal with 
    | x : _ |- _ => idtac ">>> induction on" x "<<<"; autorevert x; induction x; idtac ">>> subgoal of induction on" x "<<<"; intros => //=; intuition; prepare; progress arew
  end; arew.

Tactic Notation "daind" ident(x) := 
   prepare; autorevert x; depind x; idtac ">>> subgoal of induction on" x "<<<"; intros => //=; try autodestr; simpl in *; prepare; arew.


Tactic Notation "faind" ident(x) := 
   prepare; autorevert x; induction x; intros => //=; prepare.


Tactic Notation "aind" ident(x) := 
   faind x; arew.

Ltac oaind := 
   prepare; try match goal with 
    | x : _ |- _ => idtac ">>> induction on" x "<<<"; autorevert x; induction x; intros => //=; arew
  end; arew.

Ltac inv H := inversion H; subst; 
              try match goal with [H1 : ?s = _, H2 : ?s = _ |- _] => rewrite H1 in H2; inv H2 end.

Lemma nth_cat1 {A n} {l1 l2 : seq A} {x}: n < size l1 -> nth x (l1 ++ l2) n = nth x l1 n.
Proof.
  revert n.
  induction l1 as [|a l IH]; first done.
  destruct n => *; first done. apply IH. simpl in *. somega.
Qed.


Lemma nth_cat2 {A n} {l1 l2 : seq A} {x}: n >= size l1 -> nth x (l1 ++ l2) n = nth x l2 (n - size l1).
Proof.
  revert n.
  induction l1 as [|a l IH] => *; simpl in *. 
  - f_equal. somega. 
  - ren n : nat. destruct n; simpl; repeat autodestr; try done => *. 
    apply IH. somega.
Qed.

Definition ocat {T : Type} (a b : option T) := if a is None then b else a.


Lemma nat_sind (P : nat -> Prop): (forall n, (forall m, m < n -> P m) -> P n)
  -> forall n, P n.
Proof.
  move => H n.
  elim: n {-2}n (leqnn n). 
  - move => *; apply H. by intuition somega.
  - move => n IH n' H'.  rewrite leq_eqVlt in H'. norm. case H'; intuition subst; intuition.
Qed.

Lemma drop_drop T (l : seq T) : forall n m, drop n (drop m l) = drop (m+n) l.
Proof.
  elim l; first done.
  move => x xs IH n m /=.
  case_eq(n); case_eq(m) => * //=.
Qed.

(*
Ltac newdone := move => *; try done; simpl in *; norm; intuition; somega.
Ltac done := newdone.

Ltac crush := newdone.
*)


