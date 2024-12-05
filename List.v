Require Import PeanoNat.

Inductive list {A : Type} | :=
	| nil : list
	| cons : A -> list -> list.
Arguments list _ : clear implicits.

Undelimit Scope list_scope.
Declare Scope list2_scope.
Delimit Scope list2_scope with list.
Bind Scope list2_scope with list.
Open Scope list2_scope.

Infix "::" := cons (at level 60, right associativity) : list2_scope.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list2_scope.
Notation "[ x ]" := (cons x nil) : list2_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list2_scope.
End ListNotations.

Import ListNotations.

Fixpoint length {A} (l : list A) := match l with
	| nil => O
	| cons _ l => S (length l)
end.

Fixpoint app {A} (l m : list A) := match l with
	| nil => m
	| cons a l1 => cons a (app l1 m)
end.

Infix "++" := app (right associativity, at level 60) : list2_scope.

Section Lists.
Context {A : Type}.

Implicit Types (l : list A) (d x : A).

Definition hd d l := match l with
	| [] => d
	| hd :: _ => hd
end.
Definition hd_error l := match l with
	| [] => None
	| hd :: _ => Some hd
end.
Definition tl l := match l with
	| [] => nil
	| _ :: tl => tl
end.

Fixpoint last d l := match l with
	| [] => d
	| hd :: tl => last hd tl
end.

Fixpoint In x l := match l with
	| [] => False
	| hd :: tl => x = hd \/ In x tl
end.

Fixpoint map {B} (f : A -> B) l := match l with
	| [] => []
	| hd :: tl => f hd :: map f tl
end.

Fixpoint rev_append l m := match l with
	| [] => m
	| hd :: tl => rev_append tl (hd :: m)
end.
Definition rev l := rev_append l [].

Fixpoint seq s (l : nat) := match l with O => [] | S l => s :: seq (S s) l end.

Fixpoint nth_error l n := match n, l with
	| O, hd :: _ => Some hd
	| S n, _ :: l => nth_error l n
	| O, [] | S _, [] => None
end.
Fixpoint nth l n d := match n, l with
	| O, hd :: _ => hd
	| S n, _ :: l => nth l n d
	| O, [] | S _, [] => d
end.
Definition nth_default l n d := match nth_error l n with
	| Some v => v
	| None => d
end.

Theorem nil_cons : forall x l, nil <> cons x l.
Proof using.
	discriminate.
Qed.

Theorem destruct_list l : { x & { tl | l = cons x tl } } + { l = [] }.
Proof using.
	destruct l as [|hd tl]; [right; exact eq_refl|left; exists hd, tl; exact eq_refl].
Qed.

Theorem hd_error_tl_repr : forall l x r, hd_error l = Some x /\ tl l = r <-> l = x :: r.
Proof using.
	intros [|hd tl] x r; [easy|cbn; split].
	- now intros [[= ->] ->].
	- now intros [= -> ->].
Qed.

Lemma hd_error_some_nil : forall l x, hd_error l = Some x -> l <> nil.
Proof using.
	intros [|hd tl] x; discriminate.
Qed.

Theorem length_zero_iff_nil : forall l, length l = 0 <-> l = [].
Proof using.
	intros [|? ?]; easy.
Qed.

Lemma tl_app_l : forall l1 l2, l1 <> [] -> tl (l1 ++ l2) = tl l1 ++ l2.
Proof using.
	intros [|? l1] l2 H; [contradiction (H eq_refl)|exact eq_refl].
Qed.

Lemma app_nil_r : forall l, l ++ [] = l.
Proof using.
	intros l; induction l as [|h l IH]; [exact eq_refl|exact (f_equal (cons h) IH)].
Qed.

Lemma rev_append_l : forall l1 l2 l3, rev_append (l1 ++ l2) l3 = rev_append l2 (rev_append l1 l3).
Proof using.
	intros l1; induction l1 as [|h1 l1 IH]; intros l2 l3.
	1: exact eq_refl.
	cbn; exact (IH _ _).
Qed.
Lemma rev_append_r : forall l1 l2 l3, rev_append l1 (l2 ++ l3) = (rev_append l1 l2) ++ l3.
Proof using.
	intros l1; induction l1 as [|h1 l1 IH]; intros l2 l3.
	1: exact eq_refl.
	cbn; exact (IH (_ :: _) _).
Qed.

Lemma rev_app_distr : forall l1 l2, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof using.
	intros l1 l2; unfold rev; rewrite rev_append_l, <-rev_append_r; exact eq_refl.
Qed.

Lemma rev_cons : forall l x, rev (x :: l) = rev l ++ [x].
Proof using.
	intros l x; unfold rev; cbn; exact (rev_append_r _ [] _).
Qed.
Lemma rev_unit : forall l x, rev (l ++ [x]) = x :: rev l.
Proof using.
	intros l x; exact (rev_app_distr _ _).
Qed.

Lemma rev_involutive : forall l, rev (rev l) = l.
Proof using.
	intros l; induction l as [|h l IH]; [exact eq_refl|rewrite rev_cons, (rev_unit _ _); exact (f_equal _ IH)].
Qed.

Lemma rev_inj : forall l1 l2, rev l1 = rev l2 -> l1 = l2.
Proof using.
	intros l1 l2 H; rewrite <-(rev_involutive l1), <-(rev_involutive l2); exact (f_equal _ H).
Qed.

Lemma rev_append_rev : forall l1 l2, rev_append l1 l2 = rev l1 ++ l2.
Proof using.
	intros l1 l2; unfold rev; exact (rev_append_r _ [] _).
Qed.

Lemma in_app : forall x l1 l2, In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof using.
	intros x l1 l2; split; induction l1 as [|h l1 IH]; intros H.
	- right; exact H.
	- destruct H as [H|H]; [left; left; exact H|specialize (IH H) as [IH|IH]; [left; right; exact IH|right; exact IH]].
	- destruct H as [[]|H]; exact H.
	- destruct H as [[H|H]|H]; [left; exact H|right; exact (IH (or_introl H))|right; exact (IH (or_intror H))].
Qed.

Lemma in_iff : forall x l, In x l <-> exists l1 l2, l = l1 ++ x :: l2.
Proof using.
	intros x l; split.
	- induction l as [|h l IH].
	  1: intros [].
	  intros [eq|xinl]; [exists [], l; exact (f_equal (fun v => v :: _) (eq_sym eq))|].
	  specialize (IH xinl) as (l1 & l2 & eq); exists (h :: l1), l2; exact (f_equal _ eq).
	- intros [l1 [l2 ->]]; induction l1 as [|h l1 IH]; [left; exact eq_refl|right; exact IH].
Qed.

Lemma length_app : forall l1 l2, length (l1 ++ l2) = length l1 + length l2.
Proof using.
	intros l1 l2; induction l1 as [|h l1 IH]; [exact eq_refl|cbn; rewrite IH; exact eq_refl].
Qed.

Lemma app_assoc : forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof using.
	intros l1 l2 l3; induction l1 as [|hd l1 IH]; [exact eq_refl|cbn; exact (f_equal _ IH)].
Qed.

Lemma seq_r : forall s l : nat, seq s (S l) = seq s l ++ [s + l]%nat.
Proof using.
	intros s l; generalize dependent s; induction l as [|l IH]; intros s.
	1: exact (f_equal (fun w => [w]) (eq_sym (PeanoNat.Nat.add_0_r _))).
	rewrite (eq_refl : seq _ (S (S _)) = _ :: seq _ (S _)), IH; exact (f_equal (fun w => _ :: _ ++ [w]) (plus_n_Sm _ _)).
Qed.

Lemma map_app : forall {B} (f : A -> B) l1 l2, map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof using.
	intros B f l1 l2; induction l1 as [|hd l1 IH]; [exact eq_refl|cbn; rewrite IH; exact eq_refl].
Qed.

Lemma nth_default_eq : forall l n d, nth_default l n d = nth l n d.
Proof using.
	intros l; induction l as [|hd l IH]; (intros [|n] d; [exact eq_refl|]); [exact eq_refl|exact (IH _ _)].
Qed.

Lemma length_rev_append : forall l1 l2, length (rev_append l1 l2) = length l1 + length l2.
Proof using.
	intros l1; induction l1 as [|hd l1 IH]; intros l2; [exact eq_refl|cbn; rewrite plus_n_Sm; exact (IH (_ :: _))].
Qed.
Lemma length_rev : forall l, length (rev l) = length l.
Proof using.
	intros l; rewrite <-(Nat.add_0_r (length l)); exact (length_rev_append _ _).
Qed.
Lemma length_map : forall {B} (f : A -> B) l, length (map f l) = length l.
Proof using.
	intros B f l; induction l as [|hd l IH]; [exact eq_refl|exact (f_equal S IH)].
Qed.

Lemma length_seq : forall (s l : nat), length (seq s l) = l.
Proof using.
	intros s l; generalize dependent s; induction l as [|l IH]; intros s; [exact eq_refl|exact (f_equal S (IH _))].
Qed.

Lemma map_ext : forall {B} (f1 f2 : A -> B) l, (forall x, f1 x = f2 x) -> map f1 l = map f2 l.
Proof using.
	intros B f1 f2 l Hf; induction l as [|hd l IH]; [exact eq_refl|exact (f_equal2 _ (Hf _) IH)].
Qed.

End Lists.

Lemma map_map : forall {A B C} (f1 : A -> B) (f2 : B -> C) l, map f2 (map f1 l) = map (fun x => f2 (f1 x)) l.
Proof using.
	intros A B C f1 f2 l; induction l as [|hd l IH]; [exact eq_refl|exact (f_equal _ IH)].
Qed.
