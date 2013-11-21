Require Import lib Size.

Class MMap (A B: Type) := mmap : (A -> A) -> B -> B.

Class MMapLemmas `(mmap : MMap) := {
  mmap_id : mmap id = id;
  mmap_comp x f g: mmap f (mmap g x) = mmap (fun y => f(g y)) x
}.

Ltac gen_MMap :=
hnf; match goal with [ |- (?A -> ?A) -> ?B -> ?B] =>
 intros f; fix mmap' 1; intros s;
destruct s eqn:E;
let term := type of s in
match goal with 
    [E : s = ?s' |- _] =>
    let rec map s := 
        (match s with 
             ?s1 ?s2 => 
             let s1' := map s1 in
             let s2_T := type of s2 in
             let s2' := match s2_T with 
                         | A => constr:(f s2) 
                         | B => constr:(mmap' s2)
                         | context[B] => constr:(mmap mmap' s2)
                         | context[A] => constr:(mmap f s2)
                         | _ => s2  
                       end in
             constr:(s1' s2')
           | _ => s end) in 
    let t' := map s' in 
    exact t'
end
end.

Ltac gen_MMapLemmas :=
constructor;[
f_ext; induction 0; simpl; now autorew |
let x := fresh "x" in intros x; induction x; intros; simpl; now autorew].

Ltac msimpl := 
  unfold mmap;
  simpl; 
  repeat
match goal with [|- context[?s]] => 
           match s with 
             | ?s1 _ _ => match s1 with @mmap _ _ _ => fail 1 | _ => progress change s1 with (@mmap _ _ s1) end
             | ?s1 _ => match s1 with @mmap _ _ _ => fail 1 | _ => progress change s1 with (@mmap _ _ s1) end
           end 
         end.

Instance mmap_refl (A : Type) : MMap A A := id.
Instance mmap_lemmas_refl (A : Type) : MMapLemmas (mmap_refl A).
constructor; intuition. Qed.

Instance mmap_trans (A B C : Type) (mmap1 : MMap A B) (mmap2 : MMap B C) : MMap A C := (fun f => mmap (mmap f)).
Arguments mmap_trans _ _ _ _ _ _ _ /.
Instance mmap_lemmas_trans
(A B C : Type) (mmap1 : MMap A B) (mmap2 : MMap B C)
(l1 : MMapLemmas mmap1) (l2 : MMapLemmas mmap2) : MMapLemmas (mmap_trans A B C mmap1 mmap2).
destruct l1. destruct l2. constructor; cbv; unfold id in *; intros; autorew.
- now trivial.
- f_equal. f_ext. intros. now autorew.
Qed.

Instance mmap_list (A : Type) : MMap A (list A).
gen_MMap. Defined.

Instance mmap_lemmas_list (A : Type) : MMapLemmas (mmap_list A).
gen_MMapLemmas. Defined.

Inductive foo :=
  Foo (_ : list (list foo)).

Instance size_foo : Size foo. gen_Size. Defined.

Instance mmap_foo : MMap nat foo.
gen_MMap. Defined.
Instance mmap_lemmas_foo : MMapLemmas (mmap_foo).
constructor. 
- f_ext. intros x. msimpl. sinduction x.
  msimpl. f_equal. induction l.
  + reflexivity.
  + repeat msimpl. f_equal. induction a; 
 repeat(msimpl; autorew; intuition (try somega)).
 apply IHl. intros. apply H. somega.
- intros x. sinduction x. intros.
  
Defined.


