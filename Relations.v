From Coq Require Export Relations.
Require Import List. Import ListNotations.

Arguments inclusion {A} _ _.
Arguments same_relation {A} _ _.
Arguments transp {A} R _ _.
Arguments clos_trans {A} R _ _.
Arguments clos_refl_trans {A} R _ _.
Arguments clos_refl_trans_1n {A} R _ _.
Arguments clos_refl_trans_n1 {A} R _ _.
Arguments clos_refl_sym_trans {A} R _ _.
Notation "R ^+" := (clos_trans R) (at level 8, R constr, left associativity, format "R ^+").
Notation "R ^*" := (clos_refl_trans R) (at level 8, R constr, left associativity, format "R ^*").
Notation "R ^t" := (transp R) (at level 8, R constr, left associativity, format "R ^t").
Arguments r_step {A} {R} {_ _} _.
Arguments r_refl {A} {R} {_}.
Arguments t_step {A} {R} {_ _} _.
Arguments t_trans {A} {R} {_ _ _} _ _.
Arguments rt_step {A} {R} {_ _} _.
Arguments rt_refl {A} {R} {_}.
Arguments rt_trans {A} {R} {_ _ _} _ _.
Arguments rst_step {A} {R} {_ _} _.
Arguments rst_refl {A} {R} {_}.
Arguments rst_sym {A} {R} {_ _} _.
Arguments rst_trans {A} {R} {_ _ _} _ _.
Arguments clos_rt_clos_rst {A} {R} {_ _} _.

Definition compose {A B C} R T (x : A) (z : C) := exists y : B, R x y /\ T y z.

Notation "R \o T" := (compose R T) (at level 10, R constr, T constr, left associativity, format "R  \o  T").

Lemma clos_refl_trans_transp_permute : forall {A} {R : relation A} x y, R^*^t x y <-> R^t^* x y.
Proof using.
	intros A R x y; unfold transp; split;
	  (intros H; induction H as [x y H|x|x y z H1 IH1 H2 IH2]; [exact (rt_step H)|exact rt_refl|exact (rt_trans IH2 IH1)]).
Qed.

Fixpoint rt_iff {A} (R : relation A) x y l := match l with
	| [] => x = y
	| hd :: tl => R x hd /\ rt_iff R hd y tl
end.

Lemma rt_iff_last : forall {A} {R : relation A} {x y} {l},
	rt_iff R x y l -> last x l = y.
Proof using.
	intros A R x y l; generalize dependent x; induction l as [|hd2 l IH]; intros x H.
	1: exact H.
	exact (IH _ (proj2 H)).
Qed.
Lemma rt_iff_app : forall {A} {R : relation A} {x y z} {l1 l2},
	last x l1 = y /\ rt_iff R x z (l1 ++ l2) <-> rt_iff R x y l1 /\ rt_iff R y z l2.
Proof using.
	intros A R x y z l1 l2; split.
	- intros [<- H]; generalize dependent x; induction l1 as [|hd l1 IH]; intros x H.
	  1: split; [exact eq_refl|exact H].
	  apply and_assoc; split; [exact (proj1 H)|simpl in *; exact (IH _ (proj2 H))].
	- intros [H1 H2]; split; [exact (rt_iff_last H1)|];
	    generalize dependent x; induction l1 as [|hd l1 IH]; intros x H1.
	  1: rewrite H1; exact H2.
	  split; [exact (proj1 H1)|exact (IH _ (proj2 H1))].
Qed.

Lemma clos_refl_trans_iff : forall {A} {R : relation A} x y, R^* x y <-> exists l, rt_iff R x y l.
Proof using.
	intros A R x y; split.
	- intros H; induction H as [x y HR|x|x y z H1 [l1 IH1] H2 [l2 IH2]].
	  1: exists [y]; split; [exact HR|exact eq_refl].
	  1: exists []; exact eq_refl.
	  exists (l1 ++ l2); refine (proj2 (proj2 rt_iff_app (conj IH1 IH2))).
	- intros [l Hl]; generalize dependent x; induction l as [|hd tl IH]; intros x Hl.
	  1: rewrite Hl; exact rt_refl.
	  destruct Hl as [HR Hl]; exact (rt_trans (rt_step HR) (IH _ Hl)).
Qed.

Lemma clos_refl_trans_ext : forall {A} {R1 R2 : relation A}, inclusion R1 R2 -> inclusion (R1^*) (R2^*).
Proof using.
	intros A R1 R2 HR x y; rewrite !clos_refl_trans_iff; intros [l Hl].
	exists l; generalize dependent x; induction l as [|z l IH]; intros x Hl.
	1: exact Hl.
	split; destruct Hl as [Hw Hl]; [exact (HR _ _ Hw)|exact (IH _ Hl)].
Qed.

Fixpoint rst_iff {A} (R : relation A) x y l := match l with
	| [] => x = y
	| hd :: tl => (R x hd \/ R hd x) /\ rst_iff R hd y tl
end.

Lemma rst_iff_last : forall {A} {R : relation A} {x y} {l},
	rst_iff R x y l -> last x l = y.
Proof using.
	intros A R x y l; generalize dependent x; induction l as [|hd2 l IH]; intros x H.
	1: exact H.
	exact (IH _ (proj2 H)).
Qed.
Lemma rst_iff_app : forall {A} {R : relation A} {x y z} {l1 l2},
	last x l1 = y /\ rst_iff R x z (l1 ++ l2) <-> rst_iff R x y l1 /\ rst_iff R y z l2.
Proof using.
	intros A R x y z l1 l2; split.
	- intros [<- H]; generalize dependent x; induction l1 as [|hd l1 IH]; intros x H.
	  1: split; [exact eq_refl|exact H].
	  apply and_assoc; split; [exact (proj1 H)|simpl in *; exact (IH _ (proj2 H))].
	- intros [H1 H2]; split; [exact (rst_iff_last H1)|];
	    generalize dependent x; induction l1 as [|hd l1 IH]; intros x H1.
	  1: rewrite H1; exact H2.
	  split; [exact (proj1 H1)|exact (IH _ (proj2 H1))].
Qed.

Lemma clos_refl_sym_trans_iff : forall {A} {R : relation A} x y, clos_refl_sym_trans R x y <-> exists l, rst_iff R x y l.
Proof using.
	intros A R x y; split.
	- intros H; induction H as [x y HR|x|x y H [l IH]|x y z H1 [l1 IH1] H2 [l2 IH2]].
	  1: exists [y]; split; [left; exact HR|exact eq_refl].
	  1: exists []; exact eq_refl.
	  2: exists (l1 ++ l2); refine (proj2 (proj2 rst_iff_app (conj IH1 IH2))).
	  exists (tl (rev l ++ [x])); clear - IH; generalize dependent x; generalize dependent y; induction l as [|y l IH]; intros x z H.
	  1: exact (eq_sym H).
	  cbn in H; destruct H as [HR H]; rewrite rev_cons, (tl_app_l (rev l ++ [y]) _ ltac:(destruct (rev l); discriminate)).
	  refine (proj2 (proj2 rst_iff_app (conj (IH _ _ H) _))).
	  exact (conj (match HR with or_introl H => or_intror H | or_intror H => or_introl H end) eq_refl).
	- intros [l Hl]; generalize dependent x; induction l as [|hd tl IH]; intros x Hl.
	  1: rewrite Hl; exact rst_refl.
	  destruct Hl as [[HR|HR] Hl].
	  1: exact (rst_trans (rst_step HR) (IH _ Hl)).
	  exact (rst_trans (rst_sym (rst_step HR)) (IH _ Hl)).
Qed.

Lemma clos_refl_sym_trans_ext : forall {A} {R1 R2 : relation A}, inclusion R1 R2 -> inclusion (clos_refl_sym_trans R1) (clos_refl_sym_trans R2).
Proof using.
	intros A R1 R2 HR x y; rewrite !clos_refl_sym_trans_iff; intros [l Hl].
	exists l; generalize dependent x; induction l as [|z l IH]; intros x Hl.
	1: exact Hl.
	split; destruct Hl as [Hw Hl]; [destruct Hw as [Hw|Hw]; [left|right]; exact (HR _ _ Hw)|exact (IH _ Hl)].
Qed.

Lemma clos_refl_trans_l_ind : forall {A} {R : relation A} (P : _ -> _ -> Prop),
	(forall x, P x x) ->
	(forall x y z, R x y -> R^* y z -> P y z -> P x z) ->
	forall x y, R^* x y -> P x y.
Proof using.
	intros A R P Hr IH x y H; apply clos_rt_rt1n in H.
	induction H as [x|x y z H1 H2 IH2].
	1: exact (Hr _).
	exact (IH _ _ _ H1 (clos_rt1n_rt _ _ _ _ H2) IH2).
Qed.
Lemma clos_refl_trans_r_ind : forall {A} {R : relation A} (P : _ -> _ -> Prop),
	(forall x, P x x) ->
	(forall x y z, R^* x y -> P x y -> R y z -> P x z) ->
	forall x y, R^* x y -> P x y.
Proof using.
	intros A R P Hr IH x y H.
	assert (tmp := fun IH => @clos_refl_trans_l_ind _ R^t P^t Hr IH y x).
	rewrite <-clos_refl_trans_transp_permute in tmp; refine (tmp _ H); clear tmp.
	clear - IH; intros x y z H1 H2 IH2;
	  rewrite <-clos_refl_trans_transp_permute in H2; exact (IH _ _ _ H2 IH2 H1).
Qed.

Lemma clos_t_compose_swap : forall {A B} {f : A -> B} {R : relation B} x y, (fun x y => R (f x) (f y))^+ x y -> R^+ (f x) (f y).
Proof using.
	intros A B f R x y H; induction H as [x y H|x y z H1 IH1 H2 IH2].
	- exact (t_step H).
	- exact (t_trans IH1 IH2).
Qed.
Lemma clos_t_swap_compose : forall {A B} {f : A -> B} {R : relation B}, (forall y, exists x, y = f x) ->
	forall x y, R^+ (f x) (f y) -> (fun x y => R (f x) (f y))^+ x y.
Proof using.
	intros A B f R Hf x y H; remember (f x) as x' eqn:eqx; remember (f y) as y' eqn:eqy;
	  generalize dependent y; generalize dependent x; induction H as [x' y' H|x' y' z' H1 IH1 H2 IH2]; intros x -> y ->.
	- exact (t_step H).
	- specialize (Hf y') as [z ->]; exact (t_trans (IH1 _ eq_refl _ eq_refl) (IH2 _ eq_refl _ eq_refl)).
Qed.
Lemma clos_rt_compose_swap : forall {A B} {f : A -> B} {R : relation B} x y, (fun x y => R (f x) (f y))^* x y -> R^* (f x) (f y).
Proof using.
	intros A B f R x y H; induction H as [x y H|x|x y z H1 IH1 H2 IH2].
	- exact (rt_step H).
	- exact rt_refl.
	- exact (rt_trans IH1 IH2).
Qed.
Lemma clos_rt_swap_compose : forall {A B} {f : A -> B} {R : relation B}, (forall y, exists x, y = f x) ->
	forall x y, R^* (f x) (f y) -> f x = f y \/ (fun x y => R (f x) (f y))^* x y.
Proof using.
	intros A B f R Hf x y H; remember (f x) as x' eqn:eqx; remember (f y) as y' eqn:eqy;
	  generalize dependent y; generalize dependent x; induction H as [x' y' H|x'|x' z' y' H1 IH1 H2 IH2]; intros x -> y eqy.
	1,3: subst y'.
	- right; exact (rt_step H).
	- specialize (Hf z') as [z ->].
	  destruct (IH1 _ eq_refl _ eq_refl) as [IH1'|IH1'].
	  1: rewrite <-IH1' in IH2; exact (IH2 _ eq_refl _ eq_refl).
	  specialize (IH2 _ eq_refl _ eq_refl) as [IH2|IH2].
	  1: rewrite IH2 in IH1; exact (IH1 _ eq_refl _ eq_refl).
	  right; exact (rt_trans IH1' IH2).
	- left; exact eq_refl.
Qed.
Lemma clos_rt_swap_compose_inj : forall {A B} {f : A -> B} {R : relation B},
	(forall y, exists x, y = f x) -> (forall x y, f x = f y -> x = y) ->
	forall x y, R^* (f x) (f y) -> (fun x y => R (f x) (f y))^* x y.
Proof using.
	intros A B f R surj inj x y H; remember (f x) as x' eqn:eqx; remember (f y) as y' eqn:eqy;
	  generalize dependent y; generalize dependent x; induction H as [x' y' H|x'|x' z' y' H1 IH1 H2 IH2]; intros x -> y eqy.
	1,3: subst y'.
	- exact (rt_step H).
	- specialize (surj z') as [z ->]; exact (rt_trans (IH1 _ eq_refl _ eq_refl) (IH2 _ eq_refl _ eq_refl)).
	- rewrite (inj _ _ eqy); exact rt_refl.
Qed.

Lemma clos_rt_iff_eq_clos_t : forall {A} {R : relation A} {x y}, R^* x y <-> x = y \/ R^+ x y.
Proof using.
	intros A R x y; split.
	- intros H; induction H as [x y H|x|x y z _ [->|IH1] _ [<-|IH2]].
	  1: right; exact (t_step H).
	  1: left; exact eq_refl.
	  1: left; exact eq_refl.
	  1: right; exact IH2.
	  1: right; exact IH1.
	  1: right; exact (t_trans IH1 IH2).
	- intros [<-|H]; [exact rt_refl|].
	  induction H as [x y H|x y z _ IH1 _ IH2]; [exact (rt_step H)|exact (rt_trans IH1 IH2)].
Qed.

Lemma trans_clos_rt : forall {A} {R : relation A} [P : A -> Prop], (forall x y, P x -> R x y -> P y) -> forall {x}, P x -> forall {y}, R^* x y -> P y.
Proof using.
	intros A R P HP x Px y Rsxy.
	induction Rsxy as [x y Rxy|x|x y z _ IH1 _ IH2].
	- exact (HP _ _ Px Rxy).
	- exact Px.
	- exact (IH2 (IH1 Px)).
Qed.


(*** Typeclasses ***)

Class Equiv {A : Type} {equiv : relation A} := {
	equiv_refl : forall {x}, equiv x x;
	equiv_sym : forall {x y}, equiv x y -> equiv y x;
	equiv_trans : forall {x y z}, equiv x y -> equiv y z -> equiv x z;
}.
Arguments Equiv {_} _.
Class Respects {A : Type} {equiv : relation A} {He : Equiv equiv} {R : relation A} := {
	R_equiv : forall {x x' y y'}, equiv x x' -> equiv y y' -> R x y <-> R x' y';
}.
Arguments Respects {_} _ {_} _.

#[export] Instance eq_equiv (A : Type) : Equiv (@eq A) := {
	equiv_refl := @eq_refl _;
	equiv_sym := @eq_sym _;
	equiv_trans := @eq_trans _;
}.
#[export] Instance respects_eq {A : Type} R : Respects (@eq A) R := {
	R_equiv := ltac:(intros x x' y y' <- <-; split; exact (fun H => H));
}.

#[export] Instance iff_equiv : Equiv iff := {
	equiv_refl := iff_refl;
	equiv_sym := iff_sym;
	equiv_trans := iff_trans;
}.
#[export] Instance set_iff_equiv (A : Type) : Equiv (fun X Y : A -> Prop => forall x, X x <-> Y x) := {
	equiv_refl := fun X x => iff_refl _;
	equiv_sym := fun X Y HXY x => iff_sym (HXY _);
	equiv_trans := fun X Y Z HXY HYZ x => iff_trans (HXY _) (HYZ _);
}.

Section Respects.

Context {A : Type} {equiv : relation A} {He : Equiv equiv} {R : relation A} {Hr : Respects equiv R}.

Lemma Rplus_equiv : forall {x x' y y'}, equiv x x' -> equiv y y' -> R^+ x y <-> R^+ x' y'.
Proof using A He Hr R equiv.
	refine ((fun H x x' y y' Hx Hy => conj (H x x' y y' Hx Hy) (H _ _ _ _ (equiv_sym Hx) (equiv_sym Hy))) _).
	intros x x' y y' Hx Hy H; apply clos_trans_t1n in H; apply clos_t1n_trans.
	destruct H as [y Rxy|y z Rxy H]; [exact (t1n_step _ _ _ _ (proj1 (R_equiv Hx Hy) Rxy))|].
	refine (Relation_Operators.t1n_trans _ _ _ _ _ (proj1 (R_equiv Hx equiv_refl) Rxy) _).
	apply clos_t1n_trans, clos_trans_tn1 in H; apply clos_trans_t1n, clos_tn1_trans.
	destruct H as [z Ryz|z w Rzw H]; [exact (tn1_step _ _ _ _ (proj1 (R_equiv equiv_refl Hy) Ryz))|].
	exact (Relation_Operators.tn1_trans _ _ _ _ _ (proj1 (R_equiv equiv_refl Hy) Rzw) H).
Qed.
Lemma Rstar_equiv : forall {x x' y y'}, equiv x x' -> equiv y y' -> (R^* x y \/ equiv x y) <-> (R^* x' y' \/ equiv x' y').
Proof using A He Hr R equiv.
	refine ((fun H x x' y y' Hx Hy => conj (H x x' y y' Hx Hy) (H _ _ _ _ (equiv_sym Hx) (equiv_sym Hy))) _).
	intros x x' y y' Hx Hy [H|H]; [apply clos_rt_rt1n in H|right; exact (equiv_trans (equiv_trans (equiv_sym Hx) H) Hy)].
	destruct H as [|y z Rxy H]; [right; exact (equiv_trans (equiv_sym Hx) Hy)|left].
	apply clos_rt1n_rt, clos_rt_rtn1 in H.
	destruct H as [|z w Rzw H]; [exact (rt_step (proj1 (R_equiv Hx Hy) Rxy))|].
	exact (rt_trans (rt_step (proj1 (R_equiv Hx equiv_refl) Rxy)) (rt_trans (clos_rtn1_rt _ _ _ _ H) (rt_step (proj1 (R_equiv equiv_refl Hy) Rzw)))).
Qed.

End Respects.
