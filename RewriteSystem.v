Require Assoc. Require Import Relations.
Require Import List. Import ListNotations.

Section Content.

Context {A : Type}.

Context (equiv : relation A) {He : Equiv equiv}.

Context (R : relation A) {Hr : Respects equiv R}.

Definition normal_form x : Prop := forall y, ~ R x y.
Definition is_normal_form x y : Prop := R^* x y /\ normal_form y.
Definition normalizable x : Prop := exists y, is_normal_form x y.
Definition strong_normalizable x : Prop := Acc R^t x.

Lemma strong_normalizable_trans : forall x, strong_normalizable x -> forall y, R x y -> strong_normalizable y.
Proof using.
	intros x Hx y Rxy; exact (Acc_inv Hx Rxy).
Qed.

Definition unique_normal_form_for x := forall y1 y2, is_normal_form x y1 -> is_normal_form x y2 -> equiv y1 y2.
Definition unique_normal_form := forall x, unique_normal_form_for x.

Definition strong_confluence := forall x y1 y2,
	R x y1 -> R x y2 -> exists w, (R y1 w \/ equiv y1 w) /\ (R y2 w \/ equiv y2 w).
Definition confluence := forall x y1 y2,
	R^* x y1 -> R^* x y2 -> exists w, (R^+ y1 w \/ equiv y1 w) /\ (R^+ y2 w \/ equiv y2 w).
Definition local_confluence := forall x y1 y2,
	R x y1 -> R x y2 -> exists w, (R^+ y1 w \/ equiv y1 w) /\ (R^+ y2 w \/ equiv y2 w).

Lemma confluence_is_unf : confluence -> unique_normal_form.
Proof using A He Hr R equiv.
	intros H x y1 y2 H1 H2; specialize (H x y1 y2 (proj1 H1) (proj1 H2)) as [w [[Hw1|Hw1] Hw2]].
	1: destruct (clos_trans_t1n _ _ _ _ Hw1); contradiction (proj2 H1 _ H).
	destruct Hw2 as [Hw2|Hw2].
	1: destruct (clos_trans_t1n _ _ _ _ Hw2); contradiction (proj2 H2 _ H).
	exact (equiv_trans Hw1 (equiv_sym Hw2)).
Qed.

Definition church_rosser := same_relation (union _ equiv (clos_refl_sym_trans R)) (union _ equiv (compose (R^*) (R^*^t))).

Lemma confluence_iff_church_rosser : confluence <-> church_rosser.
Proof using A He Hr R equiv.
	unfold confluence, church_rosser, same_relation, inclusion, union, compose, transp; split.
	- intros H; split; (intros x y [H'|H']; [left; exact H'|]).
	  1: induction H' as [x y HR|x|x y HR [IH|[z [H1 H2]]]|x y z H1 [IH1|[c1 [H11 H12]]] H2 [IH2|[c2 [H21 H22]]]].
	  + right; exists y; split; [exact (rt_step HR)|exact rt_refl].
	  + right; exists x; split; exact rt_refl.
	  + left; exact (equiv_sym IH).
	  + right; exists z; split; assumption.
	  + left; exact (equiv_trans IH1 IH2).
	  + destruct (proj2 (Rstar_equiv IH1 equiv_refl) (or_introl H21)) as [Rsxc2|eqxc2].
	    1: right; exists c2; split; [exact Rsxc2|exact H22].
	    destruct (proj2 (Rstar_equiv equiv_refl eqxc2) (or_introl H22)) as [Rszx|eqzx].
	    1: right; exists x; split; [exact rt_refl|exact Rszx].
	    left; exact (equiv_sym eqzx).
	  + destruct (proj1 (Rstar_equiv IH2 equiv_refl) (or_introl H12)) as [Rszc1|eqzc1].
	    1: right; exists c1; split; [exact H11|exact Rszc1].
	    destruct (proj2 (Rstar_equiv equiv_refl eqzc1) (or_introl H11)) as [Rsxz|eqxz].
	    1: right; exists z; split; [exact Rsxz|exact rt_refl].
	    left; exact eqxz.
	  + specialize (H _ _ _ H12 H21) as [w [[Hw1|Hw1] [Hw2|Hw2]]].
	    1: right; exists w; split; [assert (tmp := clos_rt_t _ _ _ _ _ H11 Hw1)|assert (tmp := clos_rt_t _ _ _ _ _ H22 Hw2)].
	    3: right; exists c2; split; [assert (tmp := clos_rt_t _ _ _ _ _ H11 (proj2 (Rplus_equiv equiv_refl Hw2) Hw1))|exact H22].
	    4: right; exists c1; split; [exact H11|assert (tmp := clos_rt_t _ _ _ _ _ H22 (proj2 (Rplus_equiv equiv_refl Hw1) Hw2))].
	    1,2,3,4: clear - tmp; induction tmp as [x y H|x y z _ IH1 _ IH2]; [exact (rt_step H)|exact (rt_trans IH1 IH2)].
	    destruct (proj1 (Rstar_equiv equiv_refl Hw1) (or_introl H11)) as [H11'|H11'].
	    1: destruct (proj1 (Rstar_equiv equiv_refl Hw2) (or_introl H22)) as [H22'|H22'].
	    1: right; exists w; split; [exact H11'|exact H22'].
	    1: destruct (proj2 (Rstar_equiv equiv_refl H22') (or_introl H11')) as [H11''|H11''].
	    1: right; exists z; split; [exact H11''|exact rt_refl].
	    1: left; exact H11''.
	    destruct (proj1 (Rstar_equiv equiv_refl (equiv_trans Hw2 (equiv_sym H11'))) (or_introl H22)) as [H22'|H22'].
	    1: right; exists x; split; [exact rt_refl|exact H22'].
	    left; exact (equiv_sym H22').
	  + destruct H' as [w [H11 H12]].
	    right; exact (rst_trans (clos_rt_clos_rst H11) (rst_sym (clos_rt_clos_rst H12))).
	- intros [H1 _] x y1 y2 Hy1 Hy2.
	  specialize (H1 _ _ (or_intror (rst_trans (rst_sym (clos_rt_clos_rst Hy1)) (clos_rt_clos_rst Hy2)))) as [H|[w [H11 H12]]].
	  1: exists y2; split; right; [exact H|exact equiv_refl].
	  exists w; split; [rename H11 into tmp|rename H12 into tmp].
	  1,2: clear - Hr tmp; induction tmp as [x y H|x|x y z _ [IH1|IH1] _ [IH2|IH2]]; [left; exact (t_step H)|right; exact equiv_refl| | | |].
	  1,5: left; exact (t_trans IH1 IH2).
	  1,4: left; exact (proj1 (Rplus_equiv equiv_refl IH2) IH1).
	  1,3: left; exact (proj2 (Rplus_equiv IH1 equiv_refl) IH2).
	  1,2: right; exact (equiv_trans IH1 IH2).
Qed.

Lemma confluence_is_local : confluence -> local_confluence.
Proof using A He Hr R equiv.
	intros H x y1 y2 H1 H2; exact (H _ _ _ (rt_step H1) (rt_step H2)).
Qed.

Lemma strong_confluence_is_confluence : strong_confluence -> confluence.
Proof using A He Hr R equiv.
	unfold strong_confluence; intros H x y1 y2 H1 H2.
	apply clos_rt_rt1n in H1, H2.
	generalize dependent y1; induction H2 as [x|x y2 z2 Rxy2 H2 IH2]; intros y1 H1.
	1: exists y1; split; [right; exact equiv_refl|].
	1: apply clos_rt1n_rt, clos_rt_iff_eq_clos_t in H1; destruct H1 as [<-|H1].
	1: right; exact equiv_refl.
	1: left; exact H1.
	assert (tmp : exists w, (R^+ y1 w \/ equiv y1 w) /\ (R^+ y2 w \/ equiv y2 w)).
	- clear H2 IH2 z2.
	  generalize dependent y2; induction H1 as [x|x y1 z1 Rxy1 H1 IH1]; intros y2 Rxy2.
	  1: exists y2; split; [left; exact (t_step Rxy2)|right; exact equiv_refl].
	  specialize (H _ _ _ Rxy1 Rxy2) as [w1 [[Hw1|Hw1] [Hw2|Hw2]]].
	  1,2: specialize (IH1 _ Hw1) as [w2 [Hw21 Hw22]].
	  1: exists w2; split; [exact Hw21|left; destruct Hw22 as [H|H]; [exact (t_trans (t_step Hw2) H)|exact (t_step (proj1 (R_equiv equiv_refl H) Hw2))]].
	  1: exists w2; split;
	       [exact Hw21|destruct Hw22 as [H|H]; [left; exact (proj2 (Rplus_equiv Hw2 equiv_refl) H)|right; exact (equiv_trans Hw2 H)]].
	  1,2: exists z1; split; [right; exact equiv_refl|].
	  1: assert (tmp := t_step (proj2 (R_equiv equiv_refl Hw1) Hw2)); clear - tmp H1; left.
	  1: induction H1 as [y1|y1 z1 w Ry1w _ IH]; [exact tmp|exact (IH (t_trans tmp (t_step Ry1w)))].
	  destruct (proj1 (Rstar_equiv (equiv_trans Hw1 (equiv_sym Hw2)) equiv_refl) (or_introl (clos_rt1n_rt _ _ _ _ H1)))
	    as [H|H]; [|right; exact H].
	  apply clos_rt_iff_eq_clos_t in H; destruct H as [<-|H]; [right; exact equiv_refl|left; exact H].
	- destruct tmp as [w [Hw1 [Hw2|Hw2]]].
	  2: exists z2; split; [|right; exact equiv_refl].
	  2: destruct Hw1 as [Hw1|Hw1]; [left; assert (tmp := proj2 (Rplus_equiv equiv_refl Hw2) Hw1); clear - tmp H2|].
	  2: induction H2 as [y2|y2 z2 w2 Ry2z2 _ IH]; [exact tmp|exact (IH (t_trans tmp (t_step Ry2z2)))].
	  2: apply clos_rt1n_rt in H2; destruct (proj1 (Rstar_equiv (equiv_trans Hw2 (equiv_sym Hw1)) equiv_refl) (or_introl H2)) as [tmp|tmp].
	  2: apply clos_rt_iff_eq_clos_t in tmp; destruct tmp as [<-|tmp]; [right; exact equiv_refl|left; exact tmp].
	  2: right; exact tmp.
	  specialize (IH2 _ (clos_rt_rt1n _ _ _ _ (proj2 clos_rt_iff_eq_clos_t (or_intror Hw2)))) as [w2 [Hw21 Hw22]]; exists w2.
	  split; [|exact Hw22].
	  destruct Hw1 as [Hw1|Hw1]; destruct Hw21 as [Hw21|Hw21].
	  1: left; exact (t_trans Hw1 Hw21).
	  1: left; exact (proj1 (Rplus_equiv equiv_refl Hw21) Hw1).
	  1: left; exact (proj2 (Rplus_equiv Hw1 equiv_refl) Hw21).
	  1: right; exact (equiv_trans Hw1 Hw21).
Qed.

Lemma newman : local_confluence -> (forall x, strong_normalizable x) -> confluence.
Proof using A He Hr R equiv.
	unfold local_confluence, confluence.
	intros lc sn x z1 z2 H1 H2.
	generalize dependent z2; generalize dependent z1;
	  induction (sn x) as [x H IH]; intros z1 H1 z2 H2.
	apply clos_rt_iff_eq_clos_t in H1; destruct H1 as [<-|H1].
	1: exists z2; split; [|right; exact equiv_refl].
	1: apply clos_rt_iff_eq_clos_t in H2; destruct H2 as [<-|H2]; [right; exact equiv_refl|left; exact H2].
	apply clos_rt_iff_eq_clos_t in H2; destruct H2 as [<-|H2].
	1: exists z1; split; [right; exact equiv_refl|left; exact H1].
	assert (tmp : exists y1, R x y1 /\ R^* y1 z1).
	{ clear - H1; induction H1 as [x y H|x y z H1 IH1 H2 IH2]; [exists y; split; [exact H|exact rt_refl]|].
	  destruct IH1 as [y1 [Rxy1 IH1]]; exists y1; split; [exact Rxy1|clear - IH1 H2].
	  induction H2 as [y z H|y z w _ H1 _ IH2]; [exact (rt_trans IH1 (rt_step H))|exact (IH2 (H1 IH1))]. }
	clear H1; destruct tmp as [y1 [Rxy1 H1]].
	assert (tmp : exists y2, R x y2 /\ R^* y2 z2).
	{ clear - H2; induction H2 as [x y H|x y z H1 IH1 H2 IH2]; [exists y; split; [exact H|exact rt_refl]|].
	  destruct IH1 as [y2 [Rxy2 IH1]]; exists y2; split; [exact Rxy2|clear - IH1 H2].
	  induction H2 as [y z H|y z w _ H2 _ IH2]; [exact (rt_trans IH1 (rt_step H))|exact (IH2 (H2 IH1))]. }
	clear H2; destruct tmp as [y2 [Rxy2 H2]].
	specialize (lc _ _ _ Rxy1 Rxy2) as [w1 [[Hw11|Hw11] [Hw12|Hw12]]].
	2: exact (IH _ Rxy1 _ H1 _ (rt_trans (proj2 clos_rt_iff_eq_clos_t (or_intror (proj2 (Rplus_equiv equiv_refl Hw12) Hw11))) H2)).
	2: exact (IH _ Rxy2 _ (rt_trans (proj2 clos_rt_iff_eq_clos_t (or_intror (proj2 (Rplus_equiv equiv_refl Hw11) Hw12))) H1) _ H2).
	2: destruct (proj1 (Rstar_equiv (equiv_trans Hw11 (equiv_sym Hw12)) equiv_refl) (or_introl H1)) as [Rsy2z1|eqy2z1].
	2: exact (IH _ Rxy2 _ Rsy2z1 _ H2).
	2: exists z2; split; [|right; exact equiv_refl].
	2: destruct (proj1 (Rstar_equiv eqy2z1 equiv_refl) (or_introl H2)) as [Rsz1z2|eqz1z2].
	2: apply clos_rt_iff_eq_clos_t in Rsz1z2; destruct Rsz1z2 as [<-|Rpz1z2]; [right; exact equiv_refl|left; exact Rpz1z2].
	2: right; exact eqz1z2.
	destruct (IH _ Rxy1 _ H1 _ (proj2 clos_rt_iff_eq_clos_t (or_intror Hw11))) as [w2 [Hw21 Hw22]].
	assert (tmp : R^* y2 w2)
	  by (rewrite clos_rt_iff_eq_clos_t; right; destruct Hw22 as [H'|H'];
	        [exact (t_trans Hw12 H')|exact (proj1 (Rplus_equiv equiv_refl H') Hw12)]).
	destruct (IH _ Rxy2 _ tmp _ H2) as [w3 [Hw31 Hw32]]; clear tmp.
	exists w3; split; [clear - Hr Hw21 Hw31|exact Hw32].
	destruct Hw21 as [H1|H1]; destruct Hw31 as [H2|H2]; [left|left|left|right].
	1: exact (t_trans H1 H2).
	1: exact (proj1 (Rplus_equiv equiv_refl H2) H1).
	1: exact (proj2 (Rplus_equiv H1 equiv_refl) H2).
	1: exact (equiv_trans H1 H2).
Qed.

Lemma strong_normalizable_is_normalizable : (forall x, normal_form x \/ exists y, R x y) -> forall x, strong_normalizable x -> normalizable x.
Proof using A He Hr R equiv.
	intros HR x Hx; induction Hx as [x H IH].
	destruct (HR x) as [Hx|[y Rxy]]; [exists x; split; [exact rt_refl|exact Hx]|].
	specialize (IH _ Rxy) as [z [Rsyz Hz]]; exists z; split; [exact (rt_trans (rt_step Rxy) Rsyz)|exact Hz].
Qed.

End Content.

Lemma confluence_incl : forall {A : Type} {equiv} {He : Equiv equiv} {R T : relation A} {Hr : Respects equiv R} {Ht : Respects equiv T},
	inclusion R T -> inclusion T R^* -> confluence equiv T -> confluence equiv R.
Proof using.
	intros A equiv He R T Hr Ht RiT TiRs HT x y1 y2 Rsxy1 Rsxy2.
	apply (clos_refl_trans_ext RiT) in Rsxy1, Rsxy2.
	specialize (HT _ _ _ Rsxy1 Rsxy2) as [w [Hw1 Hw2]]; exists w; split; [destruct Hw1 as [Hw|Hw]|destruct Hw2 as [Hw|Hw]].
	2,4: right; assumption.
	1,2: assert (tmp := clos_rt_idempotent _ _ _ _ (clos_refl_trans_ext TiRs _ _ (proj2 clos_rt_iff_eq_clos_t (or_intror Hw)))).
	1,2: apply clos_rt_iff_eq_clos_t in tmp; destruct tmp as [->|tmp]; [right; exact equiv_refl|left; exact tmp].
Qed.
