Module Type SetReqs.
Parameter val : Type.
Parameter val_dec : forall v1 v2 : val, { v1 = v2 } + { v1 <> v2 }.
End SetReqs.

Require Import List. Import ListNotations.
Require Import Relations.

Module Type FiniteSet.
Parameter val : Type.
Parameter t : Type.

Parameter equiv : t -> t -> Prop.
#[export] Declare Instance He : Equiv equiv.
Parameter In : val -> t -> Prop.

Parameter In_dec : forall v s, { In v s } + { ~ In v s }.
Parameter In_equiv : forall s1 s2, equiv s1 s2 <-> forall v, In v s1 <-> In v s2.

Parameter empty : t.
Parameter add : t -> val -> t.
Parameter union : t -> t -> t.

Parameter In_empty : forall v, ~ In v empty.
Parameter In_add : forall s v t, In t (add s v) <-> t = v \/ In t s.
Parameter In_union : forall s1 s2 v, In v (union s1 s2) <-> In v s1 \/ In v s2.
End FiniteSet.

Module Make (R : SetReqs) : FiniteSet
	with Definition val := R.val.
Definition val := R.val.
Definition t := list val.

Definition equiv (s1 s2 : t) := forall v, In v s1 <-> In v s2.

#[refine,export] Instance He : Equiv equiv := {}.
Proof using.
	1: intros x v; split; exact (fun H => H).
	1: intros x y H v; split; [exact (proj2 (H v))|exact (proj1 (H v))].
	intros x y z H1 H2 v; split; intros H; [exact (proj1 (H2 _) (proj1 (H1 _) H))|exact (proj2 (H1 _) (proj2 (H2 _) H))].
Qed.

Definition In v (s : t) := In v s.

Lemma In_dec : forall v s, { In v s } + { ~ In v s }.
Proof using.
	intros v s; induction s as [|hd tl IH]; cbn.
	1: right; intros [].
	destruct (R.val_dec v hd) as [veqhd|vnehd]; [left; left; exact veqhd|].
	destruct IH as [IH|IH]; [left; right; exact IH|right; intros [f|f]; [contradiction (vnehd f)|contradiction (IH f)]].
Qed.

Lemma In_equiv : forall s1 s2, equiv s1 s2 <-> forall v, In v s1 <-> In v s2.
Proof using.
	intros s1 s2; split; exact (fun H => H).
Qed.

Definition empty : t := [].
Definition add (s : t) v := v :: s.
Definition union (s1 s2 : t) := s1 ++ s2.

Lemma In_empty : forall v, ~ In v empty.
Proof using.
	intros ? [].
Qed.

Lemma In_add : forall s v t, In t (add s v) <-> t = v \/ In t s.
Proof using.
	intros s v t; split; exact (fun H => H).
Qed.

Lemma In_union : forall s1 s2 v, In v (union s1 s2) <-> In v s1 \/ In v s2.
Proof using.
	intros s1 s2 v; exact (in_app _  _ _).
Qed.
End Make.
