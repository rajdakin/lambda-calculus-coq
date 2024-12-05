Require Import List. Import ListNotations.
Require Import Relations.
Require Coq.Program.Wf.

Class Dcpo {t : Type} (equiv : relation t) := {
	dcpo_equiv := equiv;
	dcpo_He :: Equiv equiv;
	dcpo_le : relation t;
	dcpo_le_refl : forall {x y}, equiv x y -> dcpo_le x y;
	dcpo_le_antisym : forall {x y}, dcpo_le x y -> dcpo_le y x -> equiv x y;
	dcpo_le_trans : forall {x y z}, dcpo_le x y -> dcpo_le y z -> dcpo_le x z;
	dcpo_is_ub (C : t -> Prop) x := forall y, C y -> dcpo_le y x;
	dcpo_is_lub (C : t -> Prop) x := dcpo_is_ub C x /\ forall y, dcpo_is_ub C y -> dcpo_le x y;
	dcpo_le_complete : forall {C : t -> Prop} x, C x ->
		(forall x y, C x -> C y -> exists k, C k /\ dcpo_le x k /\ dcpo_le y k) ->
		exists x, dcpo_is_lub C x;
}.

#[refine,export] Instance SetDcpo {t : Type} : Dcpo (t:=t -> Prop) (fun X Y => forall x, X x <-> Y x) := {
	dcpo_le := fun X Y => forall x, X x -> Y x;
}.
Proof using.
	1: intros X Y XeqY x Xx; exact (proj1 (XeqY _) Xx).
	1: intros X Y XiY YiX x; split; [exact (XiY _)|exact (YiX _)].
	1: intros X Y Z XiY YiZ x Xx; exact (YiZ _ (XiY _ Xx)).
	intros C _ _.
	exists (fun n => exists A, C A /\ A n); split.
	1: intros A CA x Ax; exists A; split; assumption.
	intros B HB x [A [CA Ax]]; exact (HB _ CA _ Ax).
Defined.
Arguments SetDcpo _ : clear implicits.
Definition lub_set {t : Type} (C : (t -> Prop) -> Prop) : t -> Prop := fun x => exists A, C A /\ A x.
Lemma lub_set_is_lub : forall {t} C, dcpo_is_lub C (@lub_set t C).
Proof using.
	intros t C; split.
	1: intros A CA x Ax; exists A; split; [exact CA|exact Ax].
	intros A HA x [B [CB Bx]]; exact (HA _ CB _ Bx).
Qed.

Lemma dcpo_lub_unique : forall {t} {equiv} {He : Dcpo equiv} (C : t -> Prop) x1 x2, dcpo_is_lub C x1 -> dcpo_is_lub C x2 -> equiv x1 x2.
Proof using.
	intros t equiv He C x1 x2 [H11 H12] [H21 H22].
	exact (dcpo_le_antisym (H12 _ H21) (H22 _ H11)).
Qed.

Lemma dcpo_ub_ext : forall {t} {equiv} {He : Dcpo equiv} {C1 C2 : t -> Prop}, (forall x, C2 x -> exists y, dcpo_le x y /\ C1 y) ->
	forall {x}, dcpo_is_ub C1 x -> dcpo_is_ub C2 x.
Proof using.
	intros t equiv He C1 C2 HC x Hx y Cy; apply HC in Cy; destruct Cy as [z [ylez Cz]]; exact (dcpo_le_trans ylez (Hx _ Cz)).
Qed.
Lemma dcpo_lub_ext : forall {t} {equiv} {He : Dcpo equiv} {C1 C2 : t -> Prop},
	(forall x, (exists y, dcpo_le x y /\ C1 y) <-> exists y, dcpo_le x y /\ C2 y) ->
	forall {x}, dcpo_is_lub C1 x -> dcpo_is_lub C2 x.
Proof using.
	intros t equiv He C1 C2 HC x [Hx1 Hx2]; split.
	- refine (dcpo_ub_ext (fun x Hx => proj2 (HC _) (ex_intro _ _ (conj (dcpo_le_refl equiv_refl) Hx))) Hx1).
	- intros y Hy; exact (Hx2 _ (dcpo_ub_ext (fun x Hx => proj1 (HC _) (ex_intro _ _ (conj (dcpo_le_refl equiv_refl) Hx))) Hy)).
Qed.
Lemma dcpo_ub_lub : forall {t} {equiv} {He : Dcpo equiv} {C : t -> Prop} {x}, dcpo_is_ub C x -> dcpo_is_ub (fun y => C y \/ dcpo_is_lub C y) x.
Proof using.
	intros t equiv He C x Hx y [Cy|Cy]; [exact (Hx _ Cy)|refine (proj2 Cy _ Hx)].
Qed.
Lemma dcpo_lub_lub : forall {t} {equiv} {He : Dcpo equiv} {C : t -> Prop} {x}, dcpo_is_lub C x -> dcpo_is_lub (fun y => C y \/ dcpo_is_lub C y) x.
Proof using.
	intros t equiv He C x Hx; split.
	- exact (dcpo_ub_lub (proj1 Hx)).
	- intros y Hy; exact (proj2 Hx _ (dcpo_ub_ext (fun z Cz => ex_intro _ _ (conj (dcpo_le_refl equiv_refl) (or_introl Cz))) Hy)).
Qed.

Lemma dcpo_ub_ext_r : forall {t} {equiv} {He : Dcpo equiv} {C : t -> Prop} {x1 x2}, dcpo_is_ub C x1 -> dcpo_equiv x1 x2 -> dcpo_is_ub C x2.
Proof using.
	intros t equiv He C x1 x2 Hx1 x1eqx2 y Cy; exact (dcpo_le_trans (Hx1 _ Cy) (dcpo_le_refl x1eqx2)).
Qed.
Lemma dcpo_lub_ext_r : forall {t} {equiv} {He : Dcpo equiv} {C : t -> Prop} {x1 x2}, dcpo_is_lub C x1 -> dcpo_equiv x1 x2 -> dcpo_is_lub C x2.
Proof using.
	intros t equiv He C x1 x2 Hx1 x1eqx2; split.
	- exact (dcpo_ub_ext_r (proj1 Hx1) x1eqx2).
	- intros y Hy; exact (dcpo_le_trans (dcpo_le_refl (equiv_sym x1eqx2)) (proj2 Hx1 _ Hy)).
Qed.

Definition well_defined {t1 t2} {eq1 : relation t1} {eq2 : relation t2} {H1 : Dcpo eq1} {H2 : Dcpo eq2} (f : t1 -> t2) :=
	forall x y, eq1 x y -> eq2 (f x) (f y).
Definition scott_continuity {t1 t2} {eq1 : relation t1} {eq2 : relation t2} {H1 : Dcpo eq1} {H2 : Dcpo eq2} (f : t1 -> t2) :=
	(forall x y, dcpo_le x y -> dcpo_le (f x) (f y)) /\
	(forall C x, C x -> (forall x y, C x -> C y -> exists z, C z /\ dcpo_le x z /\ dcpo_le y z) ->
		forall L, dcpo_is_lub C L -> dcpo_is_lub (fun x => exists y, C y /\ dcpo_equiv x (f y)) (f L)).

Lemma scott_continuity_is_wd : forall {t1 t2 eq1 eq2 Hd1 Hd2} f, @scott_continuity t1 t2 eq1 eq2 Hd1 Hd2 f -> well_defined f.
Proof using.
	intros t1 t2 eq1 eq2 Hd1 Hd2 f [Hf _] x y xeqy;
	  exact (dcpo_le_antisym (Hf _ _ (dcpo_le_refl xeqy)) (Hf _ _ (dcpo_le_refl (equiv_sym xeqy)))).
Qed.

Definition lub_fun {t1 t2} {eq1} {eq2} {H1 : Dcpo eq1} {H2 : Dcpo eq2} (lub_t2 : (t2 -> Prop) -> t2)
		(C : {f : t1 -> t2 | scott_continuity f} -> Prop) (x : t1) : t2 :=
	lub_t2 (fun fx => exists f, C f /\ dcpo_equiv fx (proj1_sig f x)).
Lemma lub_fun_wd : forall {t1 t2 eq1 eq2 H1 H2} lub_t2, (forall C, dcpo_is_lub C (lub_t2 C)) ->
	forall C, scott_continuity (@lub_fun t1 t2 eq1 eq2 H1 H2 lub_t2 C).
Proof using.
	intros t1 t2 eq1 eq2 Hd1 Hd2 lub_t2 lub_wd C; unfold lub_fun; split.
	- intros x y xley; refine (proj2 (lub_wd _) _ _); intros fx [[f Hf] [Cf fxeqfx]].
	  cbn in fxeqfx; refine (dcpo_le_trans (dcpo_le_refl fxeqfx) _); clear fx fxeqfx.
	  exact (dcpo_le_trans (proj1 Hf _ _ xley) (proj1 (lub_wd _) _ (ex_intro _ _ (conj Cf equiv_refl)))).
	- intros D x Dx HD L HL.
	  refine (dcpo_lub_ext_r (lub_wd _) (dcpo_le_antisym _ _)).
	  + clear x Dx; refine (proj2 (lub_wd _) _ _); intros y [x [Dx yeq]].
	    refine (dcpo_le_trans (dcpo_le_refl yeq) _); clear y yeq.
	    refine (proj2 (lub_wd _) _ _); intros y [f [Cf yeq]]; refine (dcpo_le_trans (dcpo_le_refl yeq) _); clear y yeq.
	    refine (dcpo_le_trans _ (proj1 (lub_wd _) _ (ex_intro _ _ (conj Cf equiv_refl)))).
	    exact (proj1 (proj2_sig f) _ _ (proj1 HL _ Dx)).
	  + refine (proj2 (lub_wd _) _ _); intros y [f [Cf yeq]]; refine (dcpo_le_trans (dcpo_le_refl yeq) _); clear y yeq.
	    refine (proj2 (proj2 (proj2_sig f) _ _ Dx HD _ HL) _ _); clear x Dx; intros y [x [Dx yeq]].
	    refine (dcpo_le_trans (dcpo_le_refl yeq) _); clear y yeq.
	    refine (dcpo_le_trans _ (proj1 (lub_wd _) _ (ex_intro _ _ (conj Dx equiv_refl)))).
	    exact (proj1 (lub_wd _) _ (ex_intro _ _ (conj Cf equiv_refl))).
Qed.

#[refine] Instance FunDcpo {t1 t2 : Type} {eq1 : relation t1} {eq2 : relation t2} {H1 : Dcpo eq1} {H2 : Dcpo eq2}
	(get_lub : (t2 -> Prop) -> t2) (get_lub_wd : forall C, dcpo_is_lub C (get_lub C))
	: Dcpo (fun f1 f2 : {f : t1 -> t2 | scott_continuity f} => forall x, dcpo_equiv (proj1_sig f1 x) (proj1_sig f2 x)) := {}.
Proof using.
	1: constructor.
	1: intros [f Hf] x; exact equiv_refl.
	1: intros [f Hf] [g Hg] H x; exact (equiv_sym (H x)).
	1: intros [f Hf] [g Hg] [h Hh] Hi1 Hi2 x; exact (equiv_trans (Hi1 x) (Hi2 x)).
	1: intros f g; exact (forall x, dcpo_le (proj1_sig f x) (proj1_sig g x)).
	1: intros [f Hf] [g Hg] feqg x; exact (dcpo_le_refl (feqg _)).
	1: intros [f Hf] [g Hg] fig gif x; exact (dcpo_le_antisym (fig _) (gif _)).
	1: intros [f Hf] [g Hg] [h Hh] fig gih x; exact (dcpo_le_trans (fig _) (gih _)).
	intros C [f Hf] Cf HC.
	unshelve refine (ex_intro _ (exist _ _ (lub_fun_wd get_lub get_lub_wd C)) _).
	cbn; split; intros [g Hg]; cbn.
	1: intros Cg x; refine (proj1 (get_lub_wd _) _ (ex_intro _ _ (conj Cg equiv_refl))).
	intros H x; refine (proj2 (get_lub_wd _) _ _); intros y [[h Hh] [Ch yeqhx]]; cbn in yeqhx.
	exact (dcpo_le_trans (dcpo_le_refl yeqhx) (H _ Ch _)).
Defined.
Lemma lub_fun_is_lub : forall {t1 t2 eq1 eq2 H1 H2} lub_t2 lub_t2_wd (C : sig _ -> Prop),
	dcpo_is_lub (Dcpo:=@FunDcpo t1 t2 eq1 eq2 H1 H2 lub_t2 lub_t2_wd) C (exist _ _ (lub_fun_wd lub_t2 lub_t2_wd C)).
Proof using.
	intros t1 t2 eq1 eq2 Hd1 Hd2 lub_t2 lub_wd C; unfold lub_fun; split.
	- intros [f Hf] Cf; cbn; intros x.
	  exact (proj1 (lub_wd _) _ (ex_intro _ _ (conj Cf equiv_refl))).
	- intros [f Hf] HC x; cbn in HC |- *.
	  refine (proj2 (lub_wd _) _ _); intros gx [[g Hg] [Cg gxeqgx]]; cbn in gxeqgx.
	  exact (dcpo_le_trans (dcpo_le_refl gxeqgx) (HC _ Cg _)).
Qed.

#[export] Instance SetFunDcpo {t1 t2 : Type} {eq1 : relation t1} {H1 : Dcpo eq1} : Dcpo _ := FunDcpo (H1:=H1) (@lub_set t2) lub_set_is_lub.

Require Import PeanoNat. Import Nat.
Import Logic.
Open Scope nat.

Section P_omega.

Fixpoint sum_firstn n := match n with O => O | S n => S n + sum_firstn n end.
Fixpoint inv_sum_firstn_aux n acc := match n - acc with O => acc | S n => inv_sum_firstn_aux n (S acc) end.
Definition inv_sum_firstn n := inv_sum_firstn_aux n O.

Lemma sum_firstn_ge_n : forall n, n <= sum_firstn n.
Proof using.
	intros [|n].
	1: exact (le_n _).
	exact (le_add_r (S n) _).
Qed.
Lemma sum_firstn_incr : forall m n, m <= n -> sum_firstn m <= sum_firstn n.
Proof using.
	intros m n H; induction H as [|n H IH].
	1: exact (le_n _).
	exact (Nat.le_trans _ _ _ IH (le_S _ _ (le_add_l _ _))).
Qed.
Lemma inv_sum_firstn_aux_def : forall n acc, inv_sum_firstn_aux n acc = match n - acc with O => acc | S n => inv_sum_firstn_aux n (S acc) end.
Proof using.
	intros [|n] acc; exact eq_refl.
Qed.
Lemma inv_sum_firstn_aux_wd_l : forall r n acc, acc <= n -> r <= n -> inv_sum_firstn_aux (sum_firstn n + r - sum_firstn acc) acc = n.
Proof using.
	intros r n acc Ha Hr.
	assert (tmp : exists k, n = k + acc)
	  by (clear r Hr; induction Ha as [|n Ha [k ->]]; [exists O; exact eq_refl|exists (S k); exact eq_refl]).
	clear Ha; destruct tmp as [k ->]; rename acc into n, k into m.
	generalize dependent n; induction m as [|m IHm]; intros n Hr.
	1: cbn; rewrite add_comm, add_sub; rewrite inv_sum_firstn_aux_def, (proj2 (sub_0_le _ n) Hr); exact eq_refl.
	rewrite plus_Sn_m, plus_n_Sm in Hr.
	rewrite plus_Sn_m at 2; rewrite plus_n_Sm, <-(IHm (S n) Hr); clear IHm Hr.
	rewrite inv_sum_firstn_aux_def at 1.
	rewrite <-sub_add_distr, (add_comm (sum_firstn n) n),
	        (eq_refl : sum_firstn (S m + n) + _ - (n + sum_firstn n) = (S (sum_firstn (S m + n) + r)) - sum_firstn (S n)).
	rewrite plus_Sn_m, (plus_n_Sm m n), (sub_succ_l _ _ (Nat.le_trans _ _ _ (sum_firstn_incr _ _ (le_add_l _ _)) (le_add_r _ _))).
	exact eq_refl.
Qed.
Corollary inv_sum_firstn_wd_l : forall r n, r <= n -> inv_sum_firstn (sum_firstn n + r) = n.
Proof using.
	intros r n Hr; assert (tmp := inv_sum_firstn_aux_wd_l r n O (le_0_n _) Hr); cbn in tmp; rewrite sub_0_r in tmp; exact tmp.
Qed.
Lemma inv_sum_firstn_aux_eq : forall n acc, inv_sum_firstn_aux n acc = inv_sum_firstn (n + sum_firstn acc).
Proof using.
	intros n acc; generalize dependent n; induction acc as [|m IHm]; intros n; cbn.
	1: rewrite add_0_r; exact eq_refl.
	specialize (IHm (n + S m)); rewrite inv_sum_firstn_aux_def, <-add_assoc, plus_Sn_m in IHm; rewrite <-IHm; clear IHm.
	rewrite <-plus_n_Sm, (add_sub (S n) _ : S (n + m) - m = S n); exact eq_refl.
Qed.
Lemma inv_sum_firstn_wd_r : forall n, sum_firstn (inv_sum_firstn n) <= n < sum_firstn (S (inv_sum_firstn n)).
Proof using.
	intros n.
	assert (tmp : exists k r, r <= k /\ n = sum_firstn k + r).
	{ induction n as [|n (k & r & IH & ->)].
	  1: exists O, O; split; [exact (le_n _)|exact eq_refl].
	  inversion IH as [IH'|k' IH' eq]; subst.
	  1: exists (S k), O; split; [exact (le_0_n _)|rewrite add_0_r, add_comm; exact eq_refl].
	  exists (S k'), (S r); split; [exact (le_n_S _ _ IH')|exact (plus_n_Sm _ _)]. }
	destruct tmp as (k & r & rlek & ->).
	rewrite (inv_sum_firstn_wd_l _ _ rlek); split; [exact (le_add_r _ _)|rewrite add_comm; exact (le_n_S _ _ (add_le_mono _ _ _ _ rlek (le_n _)))].
Qed.

Definition code_pair m n := sum_firstn (m + n) + m.
Definition code_pi1 n := n - sum_firstn (inv_sum_firstn n).
Definition code_pi2 n := inv_sum_firstn n - code_pi1 n.

Lemma code_pi1_pair : forall m n, code_pi1 (code_pair m n) = m.
Proof using.
	intros m n; unfold code_pi1, code_pair.
	rewrite (inv_sum_firstn_wd_l _ _ (le_add_r _ _)), add_comm; exact (add_sub _ _).
Qed.
Lemma code_pi2_pair : forall m n, code_pi2 (code_pair m n) = n.
Proof using.
	intros m n; unfold code_pi2; rewrite code_pi1_pair; unfold code_pair.
	rewrite (inv_sum_firstn_wd_l _ _ (le_add_r _ _)), add_comm; exact (add_sub _ _).
Qed.
Lemma code_pair_pi : forall n, code_pair (code_pi1 n) (code_pi2 n) = n.
Proof using.
	intros n; unfold code_pi2, code_pi1, code_pair.
	assert (tmp : exists k r, r <= k /\ n = sum_firstn k + r).
	{ specialize (inv_sum_firstn_wd_r n) as [len nlt].
	  exists (inv_sum_firstn n), (n - sum_firstn (inv_sum_firstn n)); split.
	  2: rewrite add_comm, <-(add_sub_swap _ _ _ len); exact (eq_sym (add_sub _ _)).
	  cbn in nlt; apply le_S_n in nlt.
	  exact (proj2 (le_sub_le_add_r _ _ _) nlt). }
	destruct tmp as (k & r & rlek & ->).
	rewrite (inv_sum_firstn_wd_l _ _ rlek), !(add_comm _ r), add_sub, add_comm; do 2 f_equal.
	rewrite add_comm, <-(add_sub_swap _ _ _ rlek); exact (add_sub _ _).
Qed.

Fixpoint remove_all (s : list nat) (n : nat) : list nat.
Proof using.
	destruct s as [|hd s].
	1: exact [].
	destruct (eq_dec hd n) as [|].
	1: exact (remove_all s n).
	exact (hd :: remove_all s n).
Defined.
Lemma in_remove_all : forall s n k, In k (remove_all s n) <-> n <> k /\ In k s.
Proof using.
	intros s n k; split; induction s as [|hd s IH]; intros H.
	1: contradiction H.
	1: cbn in *; destruct (eq_dec hd n) as [|ne]; [split; [exact (proj1 (IH H))|right; exact (proj2 (IH H))]|].
	1: destruct H as [->|H]; split; [symmetry; exact ne|left; exact eq_refl|exact (proj1 (IH H))|right; exact (proj2 (IH H))].
	1: contradiction (proj2 H).
	cbn in *; destruct H as [H1 [->|H2]]; destruct (eq_dec hd n) as [hdeqn|hdnen].
	1: contradiction (H1 (eq_sym hdeqn)).
	1: left; exact eq_refl.
	1: exact (IH (conj H1 H2)).
	right; exact (IH (conj H1 H2)).
Qed.

Lemma length_remove_all : forall s n, length (remove_all s n) <= length s.
Proof using.
	intros s n; induction s as [|hd s IH]; [exact (le_n _)|cbn; destruct (eq_dec hd n); [apply le_S|apply le_n_S]]; exact IH.
Qed.

#[program] Fixpoint dedup s {measure (length s)} := match s with [] => [] | hd :: tl => hd :: dedup (remove_all tl hd) end.
Next Obligation.
	cbn; apply le_n_S; exact (length_remove_all _ _).
Defined.
Next Obligation.
	unfold Wf.MR; intros s.
	remember (length s) as n eqn:eq; assert (Hn : length s <= n) by (subst n; exact (le_n _)); clear eq; generalize dependent s.
	induction n as [|n IH]; intros s Hs; refine (Acc_intro _ _); intros t Ht.
	1: inversion Hs; rewrite H0 in Ht; inversion Ht.
	assert (tmp := Nat.le_trans _ _ _ Ht Hs); apply le_S_n in tmp; specialize (IH _ tmp); exact IH.
Defined.
Lemma dedup_def : forall s, dedup s = match s with [] => [] | hd :: tl => hd :: dedup (remove_all tl hd) end.
Proof using.
	intros [|hd s]; [exact eq_refl|cbn; f_equal].
	unfold dedup, Wf.Fix_sub.
	match goal with |- Wf.Fix_F_sub _ _ _ _ _ ?H1 = Wf.Fix_F_sub _ _ _ _ _ ?H2 =>
	  remember H1 as H01 eqn:eq01; remember H2 as H02 eqn:eq02; clear eq01 eq02 end.
	unfold Wf.MR in H02.
	remember (remove_all s hd) as s' eqn:eqs'; clear hd s eqs'; rename s' into s.
	assert (H := H01).
	generalize dependent H02; generalize dependent H01; induction H as [s H IH]; intros [H01] [H02]; cbn.
	destruct s as [|hd s]; [exact eq_refl|f_equal; exact (IH _ (le_n_S _ _ (length_remove_all _ _)) _ _)].
Qed.
Opaque dedup.

Fixpoint code_finite_set_aux (s : list nat) : nat.
Proof using.
	destruct s as [|hd s].
	1: exact O.
	exact (pow 2 hd + code_finite_set_aux s).
Defined.
Definition code_finite_set s := code_finite_set_aux (dedup s).

Fixpoint incr_list_by s n := match s with
	| [] => [n]
	| hd :: tl => if hd =? n then incr_list_by tl (S n) else n :: hd :: tl
end.
Fixpoint decode_finite_set_aux n s := match n with
	| O => s
	| S n => decode_finite_set_aux n (incr_list_by s O)
end.
Definition decode_finite_set n := decode_finite_set_aux n [].

Lemma in_dedup : forall n s, In n (dedup s) <-> In n s.
Proof using.
	intros k s.
	remember (length s) as n eqn:eq; assert (Hn : length s <= n) by (subst; exact (le_n _)); clear eq.
	generalize dependent s; induction n as [|n IH]; intros s Hn.
	1: destruct s; [split; intros []|inversion Hn].
	destruct s as [|hd s]; [split; intros []|rewrite dedup_def; cbn in Hn; apply le_S_n in Hn; cbn].
	rewrite (IH _ (Nat.le_trans _ _ _ (length_remove_all _ _) Hn)), in_remove_all; split.
	1: intros [H|[_ H]]; [left; exact H|right; exact H].
	intros [H|H]; [left; exact H|].
	destruct (eq_dec hd k) as [->|hdnek]; [left; exact eq_refl|right; split; [exact hdnek|exact H]].
Qed.
Fixpoint dedup_prop (s : list nat) := match s with
	| [] => True
	| hd :: tl => ~ In hd tl /\ dedup_prop tl
end.
Lemma dedup_prop_wd : forall s, dedup_prop (dedup s).
Proof using.
	intros s.
	remember (length s) as n eqn:eq; assert (Hn : length s <= n) by (subst; exact (le_n _)); clear eq.
	generalize dependent s; induction n as [|n IH]; intros s Hn.
	1: destruct s; [exact I|inversion Hn].
	destruct s as [|hd s]; [exact I|rewrite dedup_def; cbn in Hn; apply le_S_n in Hn].
	split; [rewrite in_dedup, in_remove_all; intros [f _]; exact (f eq_refl)|refine (IH _ (Nat.le_trans _ _ _ (length_remove_all _ _) Hn))].
Qed.

Lemma remove_all_comm : forall s n1 n2, remove_all (remove_all s n1) n2 = remove_all (remove_all s n2) n1.
Proof using.
	intros s n1 n2; induction s as [|hd s IH]; [exact eq_refl|cbn].
	remember (eq_dec hd n1) as tmp eqn:eqhdn1; destruct tmp as [->|hdnen1]; cbn.
	1: destruct (eq_dec n1 n2) as [<-|n1nen2]; [exact eq_refl|cbn; rewrite <-eqhdn1; exact IH].
	destruct (eq_dec hd n2) as [->|hdnen2]; [exact IH|cbn; rewrite <-eqhdn1; exact (f_equal _ IH)].
Qed.
Lemma remove_all_idem : forall s n, remove_all (remove_all s n) n = remove_all s n.
Proof using.
	intros s n; induction s as [|hd s IH]; [exact eq_refl|cbn].
	remember (eq_dec hd n) as tmp eqn:eqhdn; destruct tmp as [->|hdnen]; [exact IH|cbn; rewrite <-eqhdn; exact (f_equal _ IH)].
Qed.
Lemma dedup_remove_all_comm : forall s n, dedup (remove_all s n) = remove_all (dedup s) n.
Proof using.
	intros s k.
	remember (length s) as n eqn:eq; assert (Hn : length s <= n) by (subst; exact (le_n _)); clear eq.
	generalize dependent s; induction n as [|n IH]; intros s Hn.
	1: destruct s; [exact eq_refl|inversion Hn].
	destruct s as [|hd s]; [exact eq_refl|rewrite (dedup_def (hd :: s)); cbn].
	cbn in Hn; apply le_S_n in Hn.
	destruct (eq_dec hd k) as [->|hdnen].
	2: rewrite dedup_def, remove_all_comm; exact (f_equal _ (IH _ (Nat.le_trans _ _ _ (length_remove_all _ _) Hn))).
	rewrite (IH _ Hn); exact (eq_sym (remove_all_idem _ _)).
Qed.

Lemma remove_all_not_in : forall s n, ~ In n s -> remove_all s n = s.
Proof using.
	intros s n H; induction s as [|hd s IH]; [exact eq_refl|cbn].
	destruct (eq_dec hd n) as [eq|hdnen]; [contradiction (H (or_introl (eq_sym eq)))|exact (f_equal _ (IH (fun H' => H (or_intror H'))))].
Qed.

Lemma code_finite_set_aux_in : forall s n, dedup_prop s -> In n s -> code_finite_set_aux s = 2^n + code_finite_set_aux (remove_all s n).
Proof using.
	intros s n Hs H.
	induction s as [|hd s IH]; [contradiction H|cbn in *].
	destruct (eq_dec hd n) as [->|hdnen]; [exact (f_equal (fun a => _ + code_finite_set_aux a) (eq_sym (remove_all_not_in _ _ (proj1 Hs))))|].
	destruct H as [<-|H]; [contradiction (hdnen eq_refl)|].
	cbn; rewrite add_assoc, (add_comm _ (2 ^ _)), <-add_assoc; exact (f_equal _ (IH (proj2 Hs) H)).
Qed.
Lemma code_finite_set_in : forall s n, In n s -> code_finite_set s = 2^n + code_finite_set (remove_all s n).
Proof using.
	intros s n H; unfold code_finite_set; rewrite dedup_remove_all_comm;
	  exact (code_finite_set_aux_in _ _ (dedup_prop_wd _) (proj2 (in_dedup _ _) H)).
Qed.
Lemma code_finite_set_eq : forall s, code_finite_set s = match s with [] => O | hd :: tl => 2^hd + code_finite_set (remove_all tl hd) end.
Proof using.
	intros [|hd tl]; [exact eq_refl|unfold code_finite_set; rewrite dedup_def at 1; exact eq_refl].
Qed.
Lemma code_finite_set_ext : forall s1 s2, (forall n, In n s1 <-> In n s2) -> code_finite_set s1 = code_finite_set s2.
Proof using.
	intros s1; remember (length s1) as n eqn:eq; assert (Hn : length s1 <= n) by (subst; exact (le_n _)); clear eq; generalize dependent s1.
	induction n as [|n IHn]; intros [|hd s1] Hn s2 Hs.
	1,3: destruct s2 as [|]; [exact eq_refl|contradiction (proj2 (Hs _) (or_introl eq_refl))].
	1: inversion Hn.
	cbn in *; apply le_S_n in Hn.
	rewrite code_finite_set_eq, (code_finite_set_in _ _ (proj1 (Hs _) (or_introl eq_refl))); f_equal.
	refine (IHn _ (Nat.le_trans _ _ _ (length_remove_all _ _) Hn) _ _).
	intros k; rewrite !in_remove_all; split; intros [hdnek H]; (split; [exact hdnek|]).
	1: exact (proj1 (Hs _) (or_intror H)).
	specialize (proj2 (Hs _) H) as [keqhd|H2]; [contradiction (hdnek (eq_sym keqhd))|exact H2].
Qed.

Fixpoint sorted_strict s := match s with
	| [] => True
	| hd1 :: tl1 => match tl1 with [] => True | hd2 :: _ => hd1 < hd2 /\ sorted_strict tl1 end
end.

Lemma sorted_strict_incr : forall s n, match s with [] => True | hd :: _ => n <= hd end -> sorted_strict s -> sorted_strict (incr_list_by s n).
Proof using.
	intros s; induction s as [|hd1 s IH]; intros n Hn Hs; [exact I|cbn].
	inversion Hn as [neqhd1|hd1' H eq]; subst.
	2: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))); split; [exact (le_n_S _ _ H)|exact Hs].
	rewrite eqb_refl; destruct s as [|hd2 s]; [exact I|refine (IH _ (proj1 Hs) (proj2 Hs))].
Qed.

Lemma sorted_strict_iff :
	forall s, sorted_strict s <->
	match s with [] => True | hd :: tl => match tl with [] => True | hd2 :: _ => hd < hd2 end /\ sorted_strict tl end.
Proof using.
	intros [|hd1 [|hd2 s]]; split.
	1,2,4: intros _; exact I.
	1: intros _; split; exact I.
	1: intros [H1 H2]; split; [exact H1|exact H2].
	intros H; exact H.
Qed.

Fixpoint insert n s := match s with
	| [] => [n]
	| hd :: tl => if hd <? n then hd :: insert n tl else n :: s
end.
Lemma in_insert : forall n s k, In k (insert n s) <-> In k (n :: s).
Proof using.
	intros n s k; split; induction s as [|hd tl IH].
	1,3: intros H; exact H.
	- unfold insert; fold insert; destruct (hd <? n) as [|]; [intros [<-|H]|intros H; exact H].
	  1: right; left; exact eq_refl.
	  specialize (IH H) as [IH|IH]; [left; exact IH|right; right; exact IH].
	- unfold insert; fold insert; intros [keqn|[<-|kin]].
	  1: destruct (hd <? n); [right; exact (IH (or_introl keqn))|left; exact keqn].
	  1: destruct (k <? n); [|right]; left; exact eq_refl.
	  destruct (hd <? n); [right; exact (IH (or_intror kin))|right; right; exact kin].
Qed.
Lemma sorted_strict_insert : forall n s, ~ In n s -> sorted_strict s -> sorted_strict (insert n s).
Proof using.
	intros n s nnis Hs; induction s as [|hd tl IH]; [exact I|unfold insert; fold insert].
	remember (hd <? n) as tmp eqn:hdlen; destruct tmp as [|]; swap 1 2.
	1: rewrite sorted_strict_iff; split;
	     [apply eq_sym, ltb_ge in hdlen; inversion hdlen; [contradiction (nnis (or_introl H))|exact (le_n_S _ _ H)]|exact Hs].
	rewrite sorted_strict_iff; split; [|refine (IH (fun H => nnis (or_intror H)) (proj2 (proj1 (sorted_strict_iff _) Hs)))].
	destruct tl as [|hd2 tl]; unfold insert; fold insert.
	1: exact (proj1 (ltb_lt _ _) (eq_sym hdlen)).
	destruct (hd2 <? n); [exact (proj1 Hs)|exact (proj1 (ltb_lt _ _) (eq_sym hdlen))].
Qed.

Lemma decode_finite_set_aux_add : forall n1 n2 acc,
	decode_finite_set_aux (n1 + n2) acc = decode_finite_set_aux n2 (decode_finite_set_aux n1 acc).
Proof using.
	intros n1 n2; induction n1 as [|n1 IH1]; intros acc.
	1: exact eq_refl.
	exact (IH1 _).
Qed.
Lemma decode_finite_set_aux_add_pow2 : forall n acc,
	sorted_strict acc ->
	(~ In n acc /\ decode_finite_set_aux (2 ^ n) acc = insert n acc) \/
	(In n acc /\ decode_finite_set_aux (2 ^ n) acc = decode_finite_set_aux (2 ^ (S n)) (remove_all acc n)).
Proof using.
	assert (tmp : forall n s, sorted_strict s ->
	          exists s1 s2, (forall v, In v s1 -> v < n) /\ (forall v, In v s2 -> n <= v) /\ sorted_strict s2 /\ s = s1 ++ s2).
	{ intros n s Hs.
	  induction s as [|hd s IH].
	  1: exists [], []; split; [|split; [|split; [exact I|exact eq_refl]]]; intros ? [].
	  specialize (IH (proj2 (proj1 (sorted_strict_iff _) Hs))) as (s1 & s2 & H1 & H2 & H3 & ->).
	  remember (hd <? n) as tmp eqn:hdltn; destruct tmp.
	  1: exists (hd :: s1), s2; repeat split; [intros v [<-|Hv];
	       [exact (proj1 (ltb_lt _ _) (eq_sym hdltn))|exact (H1 _ Hv)]|exact H2|exact H3].
	  destruct s1 as [|hd1 s1];
	    [|contradiction (proj1 (ltb_nlt _ _) (eq_sym hdltn) (lt_trans _ _ _ (proj1 Hs) (H1 _ (or_introl eq_refl))))].
	  exists [], (hd :: s2); repeat split;
	    [intros ? []|intros v [<-|Hv]; [exact (proj1 (ltb_ge _ _) (eq_sym hdltn))|exact (H2 _ Hv)]|exact Hs]. }
	assert (tmp2 : forall n s1 s2, (forall v, In v s1 -> v < n) -> (forall v, In v s2 -> n <= v) -> sorted_strict (s1 ++ s2) -> sorted_strict s2 ->
	          decode_finite_set_aux (2 ^ n) (s1 ++ s2) = s1 ++ incr_list_by s2 n); [clear tmp|].
	{ intros n; induction n as [|n IHn]; intros s1 s2 H1 H2 H3 H4.
	  1: destruct s1; [exact eq_refl|specialize (H1 _ (or_introl eq_refl)); inversion H1].
	  cbn; rewrite add_0_r, decode_finite_set_aux_add.
	  assert (tmp : (forall v, In v s1 -> v < n) \/ exists s1', s1 = s1' ++ [n] /\ forall v, In v s1' -> v < n).
	  { clear - H1 H3; induction s1 as [|hd s1 IH]; [left; intros ? []|].
	    specialize (IH (fun _ Hv => H1 _ (or_intror Hv)) (proj2 (proj1 (sorted_strict_iff _) H3))) as [IH|[s1' [-> IH]]].
	    2: right; exists (hd :: s1'); split; [exact eq_refl|intros v [<-|Hv]; [|exact (IH _ Hv)]].
	    2: destruct s1'; [exact (proj1 H3)|exact (lt_trans _ _ _ (proj1 H3) (IH _ (or_introl eq_refl)))].
	    destruct (eq_dec hd n) as [<-|hdnen].
	    1: right; exists []; split; [destruct s1 as [|hd2 ?]; [exact eq_refl|]|intros ? []].
	    1: contradiction (lt_neq _ _ (lt_trans _ _ _ (proj1 H3) (IH _ (or_introl eq_refl))) eq_refl).
	    left; intros v [<-|Hv]; [specialize (H1 _ (or_introl eq_refl)); inversion H1; subst|exact (IH _ Hv)].
	    1: contradiction (hdnen eq_refl).
	    exact H0. }
	  destruct tmp as [H1'|[s1' [-> H1']]]; clear H1; rename H1' into H1; [|rename s1' into s1].
	  1: assert (H2' := fun v Hv => le_S_n _ _ (le_S _ _ (H2 v Hv))); rename H2' into H2, H2 into H2'.
	  2: assert (H2' := fun v (Hv : In v (_ :: _)) => match Hv with
	                      | or_introl Hv => eq_ind _ (fun a => n <= a) (le_n _) _ (eq_sym Hv)
	                      | or_intror Hv => le_S_n _ _ (le_S _ _ (H2 v Hv)) end); clear H2; rename H2' into H2.
	  2: rewrite app_assoc in H3 |- *; cbn.
	  2: assert (H4' := list_ind _ (fun s1 => sorted_strict (s1 ++ n :: s2) -> sorted_strict (n :: s2))
	                      (fun H => H) (fun hd s1 IH H => IH (proj2 (proj1 (sorted_strict_iff _) H))) _ H3);
	       clear H4; rename H4' into H4.
	  1,2: rewrite (IHn _ _ H1 H2 H3 H4).
	  1,2: refine (eq_ind _ _ (IHn _ _ H1 _ _ (sorted_strict_incr _ _ _ H4)) _ _).
	  7: exact (le_n _).
	  1: clear - H2 H4; destruct s2 as [|hd s]; [intros ? [->|[]]; exact (le_n _)|cbn; intros v Hv].
	  1: destruct (hd =? n); [specialize (H2 _ (or_introl eq_refl)); clear - H2 H4 Hv|destruct Hv as [->|Hv]; [exact (le_n _)|exact (H2 _ Hv)]].
	  1: generalize dependent n; generalize dependent hd; induction s as [|hd2 s IH];
	       intros hd H4 n H2 Hv; [destruct Hv as [->|[]]; exact (le_S _ _ (le_n _))|].
	  1: cbn in Hv; destruct (hd2 =? S n); [exact (lt_le_incl _ _ (IH _ (proj2 H4) _ (le_lt_trans _ _ _ H2 (proj1 H4)) Hv))|].
	  1: destruct Hv as [->|[->|Hv]]; [exact (le_S _ _ (le_n _))|exact (lt_le_incl _ _ (le_lt_trans _ _ _ H2 (proj1 H4)))|].
	  1: clear - H4 H2 Hv; assert (Hn := Nat.le_trans _ _ _ H2 (lt_le_incl _ _ (proj1 H4))); clear H2.
	  1: assert (Hs := proj2 H4 : sorted_strict (_ :: _)); clear hd H4; generalize dependent hd2; induction s as [|hd2 s IH]; intros hd Hn Hs.
	  1: contradiction Hv.
	  1: destruct Hv as [<-|Hv]; [|exact (IH Hv _ (lt_le_incl _ _ (le_lt_trans _ _ _ Hn (proj1 Hs))) (proj2 Hs))].
	  1: exact (lt_le_incl _ _ (le_lt_trans _ _ _ Hn (proj1 Hs))).
	  2: destruct s2 as [|hd s2]; [exact I|exact (H2 _ (or_introl eq_refl))].
	  2: f_equal; assert (tmp : incr_list_by s2 n = n :: s2)
	       by (destruct s2 as [|hd s]; [|cbn; rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (H2' _ (or_introl eq_refl))))]; exact eq_refl).
	  2: rewrite tmp; clear tmp; cbn; rewrite eqb_refl; exact eq_refl.
	  2: cbn in H2 |- *; rewrite eqb_refl; clear - H4.
	  2: generalize dependent n; induction s2 as [|hd s IH]; intros n Hn v Hv; [destruct Hv as [->|[]]; exact (le_S _ _ (le_n _))|].
	  2: cbn in Hv; destruct (hd =? S n); [|destruct Hv as [->|Hv]; [exact (le_S _ _ (le_n _))|]].
	  2: refine (lt_le_incl _ _ (IH _ _ _ Hv)); apply sorted_strict_iff; split; [|exact (proj2 (proj1 (sorted_strict_iff (_ :: _)) (proj2 Hn)))].
	  2: destruct s as [|hd2 s]; [exact I|exact (le_lt_trans _ _ _ (proj1 Hn) (proj1 (proj2 Hn)))].
	  2: destruct Hv as [->|Hv]; [exact (lt_le_incl _ _ (proj1 Hn))|clear IH].
	  2: generalize dependent hd; induction s as [|hd2 s IH]; intros hd Hn; [contradiction Hv|destruct Hv as [<-|Hv];
	       [exact (lt_le_incl _ _ (lt_trans _ _ _ (proj1 Hn) (proj1 (proj2 Hn))))|]].
	  2: exact (IH Hv _ (conj (lt_trans _ _ _ (proj1 Hn) (proj1 (proj2 Hn))) (proj2 (proj2 Hn)))).
	  2: cbn; rewrite eqb_refl.
	  1,2: induction s1 as [|hd s1 IH]; [|apply sorted_strict_iff; split;
	         [destruct s1; [|exact (proj1 H3)]|exact (IH (proj2 (proj1 (sorted_strict_iff _) H3)) (fun v Hv => H1 _ (or_intror Hv)))]].
	  1: exact (sorted_strict_incr s2 _ ltac:(destruct s2; [exact I|exact (H2 _ (or_introl eq_refl))]) H4).
	  2: exact (sorted_strict_incr s2 _ ltac:(destruct s2; [exact I|exact (proj1 H4)]) (proj2 (proj1 (sorted_strict_iff _) H4))).
	  1,2: cbn; specialize (H1 _ (or_introl eq_refl)).
	  1: destruct s2; [|cbn; rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (H2' _ (or_introl eq_refl))))]; exact H1.
	  1: clear IHn IH H1 H2 H4; simpl app in H3; assert (H1 := proj1 H3); apply sorted_strict_iff, proj2 in H3.
	  1: generalize dependent n; induction s2 as [|hd2 s IH]; intros n Hs Hn;
	       [exact (le_S _ _ Hn)|specialize (IH _ (proj2 Hs) (lt_trans _ _ _ Hn (proj1 Hs))); cbn; apply sorted_strict_iff in Hs; destruct Hs as [H1 H2]].
	  1: inversion H1; subst; [rewrite eqb_refl; exact IH|rewrite (eqb_sym (S _) (S _) : _ = (n =? m)), (proj2 (eqb_neq _ _) (lt_neq _ _ H))].
	  1: exact (le_S _ _ Hn).
	  rewrite app_assoc; f_equal; cbn; rewrite eqb_refl.
	  clear IHn s1 H3 H1 H2; remember (S n) as m eqn:eqm; assert (Hm : n < m) by (subst; exact (le_n _)); clear eqm.
	  generalize dependent n; generalize dependent m; induction s2 as [|hd s IH]; intros m n H Hm;
	    [unfold incr_list_by; rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ Hm)); exact eq_refl|cbn; destruct (hd =? m)].
	  2: cbn; rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ Hm)); exact eq_refl.
	  refine (IH _ _ (proj2 (sorted_strict_iff (_ :: _)) (conj _ (proj2 (proj1 (sorted_strict_iff (_ :: _)) (proj2 H))))) (le_S _ _ Hm)).
	  destruct s; [exact I|exact (lt_trans _ _ _ (proj1 H) (proj1 (proj2 H)))]. }
	intros n s Hs.
	specialize (tmp n s Hs) as (s1 & s2 & H1 & H2 & H3 & ->).
	rewrite (tmp2 _ _ _ H1 H2 Hs H3).
	assert (tmp : ~ In n s2 \/ exists s2', s2 = n :: s2').
	1: destruct s2 as [|hd s2]; [left; intros []|destruct (eq_dec n hd) as [<-|nnehd]; [right; exists s2; exact eq_refl|left]].
	1: intros [neqhd|nins2]; [contradiction (nnehd neqhd)|contradict nins2; clear - H2 H3].
	1: generalize dependent hd; induction s2 as [|hd2 s2 IH]; intros hd H1 H2; [intros []|intros [<-|H]].
	1: exact (lt_neq _ _ (le_lt_trans _ _ _ (H1 _ (or_introl eq_refl)) (proj1 H2)) eq_refl).
	1: exact (IH _ (fun v Hv => H1 _ (or_intror Hv)) (proj2 H2) H).
	destruct tmp as [nnis2|[s2' ->]]; [left; split|right; split; [apply in_app; right; left; exact eq_refl|]].
	1: intros f; apply in_app in f; destruct f as [f|f]; [exact (lt_neq _ _ (H1 _ f) eq_refl)|exact (nnis2 f)].
	1: assert (tmp : incr_list_by s2 n = insert n s2); [|rewrite tmp; clear tmp].
	1: induction s2 as [|hd s2 IH]; [exact eq_refl|unfold insert; fold insert; unfold incr_list_by; fold incr_list_by].
	1: rewrite (proj2 (ltb_ge _ _) (H2 _ (or_introl eq_refl))), (proj2 (eqb_neq _ _) (fun f => nnis2 (or_introl (eq_sym f)))); exact eq_refl.
	1: clear - H1; induction s1 as [|hd s1 IH]; [exact eq_refl|simpl app; unfold insert; fold insert].
	1: rewrite (proj2 (ltb_lt _ _) (H1 _ (or_introl eq_refl))); exact (f_equal _ (IH (fun v Hv => H1 _ (or_intror Hv)))).
	cbn; rewrite eqb_refl.
	refine (eq_ind _ _ (eq_sym (tmp2 (S n) s1 s2' (fun v Hv => le_S _ _ (H1 _ Hv)) _ _ (proj2 (proj1 (sorted_strict_iff _) H3)))) _ _).
	1: intros v Hv; specialize (H2 _ (or_intror Hv)); clear - Hv H3; induction s2' as [|hd s IH]; [contradiction Hv|].
	1: destruct Hv as [<-|Hv]; [exact (proj1 H3)|].
	1: refine (IH (proj2 (sorted_strict_iff (n :: s)) (conj _ (proj2 (proj1 (sorted_strict_iff (hd :: s)) (proj2 H3))))) Hv).
	1: destruct s; [exact I|exact (lt_trans _ _ _ (proj1 H3) (proj1 (proj2 H3)))].
	1: clear - Hs; induction s1 as [|hd s1 IH]; [exact (proj2 (proj1 (sorted_strict_iff _) Hs))|apply sorted_strict_iff; cbn].
	1: split; [destruct s1; [|exact (proj1 Hs)]|exact (IH (proj2 (proj1 (sorted_strict_iff _) Hs)))].
	1: destruct s2'; [exact I|exact (lt_trans _ _ _ (proj1 Hs) (proj1 (proj2 Hs)))].
	cbn; f_equal.
	induction s1 as [|hd s1 IH]; cbn.
	2: destruct (eq_dec hd n) as [->|hdnen]; [contradiction (lt_neq _ _ (H1 _ (or_introl eq_refl)) eq_refl)|].
	2: exact (f_equal _ (IH (proj2 (proj1 (sorted_strict_iff _) Hs)) (fun v Hv => H1 _ (or_intror Hv)))).
	destruct (eq_dec n n) as [_|nnen]; [clear Hs H1 tmp2|contradiction (nnen eq_refl)].
	induction s2' as [|hd s IH]; [exact eq_refl|cbn; destruct (eq_dec hd n) as [->|_]; [contradiction (lt_neq _ _ (proj1 H3) eq_refl)|]].
	refine (f_equal _ (IH _ (fun v Hv => match Hv with or_introl h => H2 _ (or_introl h) | or_intror h => H2 _ (or_intror (or_intror h)) end))).
	apply sorted_strict_iff; split; [|exact (proj2 (proj1 (sorted_strict_iff (_ :: _)) (proj2 H3)))].
	destruct s as [|hd2 ?]; [exact I|exact (lt_trans _ _ _ (proj1 H3) (proj1 (proj2 H3)))].
Qed.

Lemma code_decode_finite_set : forall n s, sorted_strict s -> code_finite_set (decode_finite_set_aux n s) = n + code_finite_set s.
Proof using.
	intros n; unfold decode_finite_set; induction n as [|n IHn]; intros s Hs.
	1: exact eq_refl.
	cbn; rewrite (IHn _ (sorted_strict_incr s O ltac:(destruct s; [exact I|exact (le_0_n _)]) Hs));
	  rewrite plus_n_Sm; f_equal; clear IHn.
	assert (tmp : match s with [] => True | hd :: tl => O <= hd end) by (destruct s; [exact I|exact (le_0_n _)]).
	rewrite (eq_refl : S (code_finite_set s) = 2 ^ O + code_finite_set s).
	remember O as o eqn:eqo; rewrite eqo at 2.
	clear eqo; generalize dependent o; induction s as [|hd s IH]; intros o Ho.
	1: cbn; rewrite code_finite_set_eq; cbn; rewrite code_finite_set_eq; exact eq_refl.
	cbn; inversion Ho as [oeqhd|hd' H eq]; subst.
	1: destruct s as [|hd2 s]; rewrite eqb_refl.
	1: cbn; rewrite !(code_finite_set_eq [_]); cbn; rewrite code_finite_set_eq; exact (add_0_r _).
	1: rewrite (code_finite_set_eq (hd :: _)), add_assoc, (IH (proj2 Hs) _ (proj1 Hs)); cbn;
	     refine (f_equal2 (fun a b => (2^hd + a) + code_finite_set b) (add_0_r _) _).
	1: destruct (eq_dec hd2 hd) as [->|_]; [contradiction (lt_neq _ _ (proj1 Hs) eq_refl)|refine (f_equal _ (eq_sym (remove_all_not_in _ _ _)))].
	1: clear IH Ho n; generalize dependent hd2; induction s as [|hd3 s IH]; intros hd2 H; [intros []|intros [<-|H0]].
	1: destruct H as (H1 & H2 & _); refine (lt_neq _ _ (lt_trans _ _ _ H1 H2) eq_refl).
	1: refine (IH _ (conj (lt_trans _ _ _ (proj1 H) (proj1 (proj2 H))) (proj2 (proj2 H))) H0).
	rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))); rewrite code_finite_set_eq;
	  refine (f_equal (fun a => _ + code_finite_set a) (remove_all_not_in _ _ _)).
	intros [->|H0]; [exact (lt_neq _ _ H eq_refl)|contradict H0].
	clear IH Ho n.
	apply le_n_S in H; remember (S hd') as hd eqn:eq; clear hd' eq.
	generalize dependent hd; induction s as [|hd2 s IH]; intros hd H olehd; [intros []|intros [<-|H0]].
	1: exact (lt_neq _ _ (lt_trans _ _ _ olehd (proj1 H)) eq_refl).
	exact (IH _ (proj2 H) (lt_trans _ _ _ olehd (proj1 H)) H0).
Qed.
Lemma decode_code_finite_set : forall s n, In n s <-> In n (decode_finite_set (code_finite_set s)).
Proof using.
	unfold code_finite_set, decode_finite_set.
	intros s n; rewrite <-(in_dedup n s).
	assert (Hs := dedup_prop_wd s); remember (dedup s) as s' eqn:eqs; clear s eqs; rename s' into s.
	remember (@nil nat) as acc eqn:eqacc;
	  assert (Hsa : forall n, In n s -> ~ In n acc) by (subst acc; intros ? _ []);
	  assert (Ha : sorted_strict acc) by (subst acc; exact I);
	  rewrite <-(f_equal (fun a => In _ (a ++ _)) eqacc : In n (acc ++ s) = In n s), in_app;
	  clear eqacc.
	generalize dependent acc; induction s as [|hd s IH]; intros acc; split; intros H.
	- destruct H as [H|[]]; exact H.
	- left; exact H.
	- cbn; rewrite decode_finite_set_aux_add; specialize (decode_finite_set_aux_add_pow2 hd _ Ha) as [[_ tmp]|[tmp _]].
	  2: contradiction (Hsa _ (or_introl eq_refl) tmp).
	  rewrite tmp; clear tmp; refine (proj1 (IH (proj2 Hs) _ _ (sorted_strict_insert _ _ (Hsa _ (or_introl eq_refl)) Ha)) _).
	  1: intros k Hk; rewrite in_insert; intros [<-|Hk2]; [exact (proj1 Hs Hk)|exact (Hsa _ (or_intror Hk) Hk2)].
	  rewrite in_insert; destruct H as [H|[H|H]]; [left; right; exact H|left; left; exact H|right; exact H].
	- cbn in H; rewrite decode_finite_set_aux_add in H; specialize (decode_finite_set_aux_add_pow2 hd _ Ha) as [[_ tmp]|[tmp _]].
	  2: contradiction (Hsa _ (or_introl eq_refl) tmp).
	  rewrite tmp in H; clear tmp.
	  refine (match proj2 (IH (proj2 Hs) _ _ (sorted_strict_insert _ _ (Hsa _ (or_introl eq_refl)) Ha)) H with
	          | or_introl IH => match proj1 (in_insert _ _ _) IH with
	                            | or_introl IH => or_intror (or_introl IH) | or_intror IH => or_introl IH end
	          | or_intror IH => or_intror (or_intror IH) end).
	  intros k Hk; rewrite in_insert; intros [<-|Hk2]; [exact (proj1 Hs Hk)|exact (Hsa _ (or_intror Hk) Hk2)].
Qed.
Lemma decode_finite_set_sorted : forall n, sorted_strict (decode_finite_set n).
Proof using.
	intros n; unfold decode_finite_set; pose (acc := @nil nat); assert (Ha := I : sorted_strict acc); fold acc.
	generalize dependent acc; induction n as [|n IHn]; intros acc Ha.
	1: exact Ha.
	refine (IHn _ (sorted_strict_incr _ _ _ Ha)); destruct acc; [exact I|exact (le_0_n _)].
Qed.

Lemma equiv_lub : forall (A : nat -> Prop), dcpo_equiv A (lub_set (fun B => dcpo_le B A /\ exists l, forall x, B x <-> In x l)).
Proof using.
	intros A x; split.
	- intros Ax; exists (fun y => y = x); split; [split; [intros y ->; exact Ax|exists [x]]|exact eq_refl].
	  intros y; split; [intros H; left; exact H|intros [H|[]]; exact H].
	- intros [B [[HB [l Hl]] Bx]]; exact (HB _ Bx).
Qed.

Lemma continuity_iff : forall f : (nat -> Prop) -> (nat -> Prop),
	scott_continuity f <->
	forall A, dcpo_equiv (f A) (lub_set (fun x => exists B, (dcpo_le B A /\ (exists l, forall x, B x <-> In x l)) /\ forall n, x n <-> f B n)).
Proof using.
	intros f; split.
	- intros Hfsc A.
	  refine (equiv_trans (scott_continuity_is_wd _ Hfsc _ _ (equiv_lub A)) (dcpo_lub_unique _ _ _ _ (lub_set_is_lub _))).
	  refine (dcpo_lub_ext _ (proj2 Hfsc _ (fun _ => False) _ _ _ (lub_set_is_lub _))).
	  1: intros B; exact (iff_refl _).
	  1: split; [intros ? []|exists []; intros ?; exact (iff_refl False)].
	  intros B C [BleA [lB HB]] [CleA [lC HC]]; exists (fun x => B x \/ C x); split;
	    [split; [intros x [Bx|Cx]; [exact  (BleA _ Bx)|exact (CleA _ Cx)]
	            |exists (lB ++ lC); intros x; rewrite in_app, HB, HC; exact (iff_refl _)]
	    |split; intros x Hx; [left|right]; exact Hx].
	- intros Hf; refine ((fun fincr => conj fincr _) _); swap 1 2.
	  + intros A B AleB n fAn; refine (proj2 (Hf _ _) _); unfold lub_set.
	    specialize (proj1 (Hf A n) fAn) as [A0 [[A1 [[A1le [l Hl]] A0eq]] A0n]].
	    exact (ex_intro _ _ (conj (ex_intro _ _ (conj (conj (dcpo_le_trans A1le AleB) (ex_intro _ _ Hl)) A0eq)) A0n)).
	  + intros C x Cx HC L HL.
	    refine (dcpo_lub_ext_r _ (equiv_sym (Hf _))); split.
	    * intros A [B [CB Aeq]]; refine (dcpo_le_trans (dcpo_le_refl Aeq) _); clear A Aeq.
	      refine (dcpo_le_trans (dcpo_le_refl (Hf _)) _); refine (proj2 (lub_set_is_lub _) _ (dcpo_ub_ext _ (proj1 (lub_set_is_lub _)))).
	      intros A0 [A [[Ale Afin] Aeq]];
	        exact (ex_intro _ _ (conj (dcpo_le_refl equiv_refl) (ex_intro _ _ (conj (conj (dcpo_le_trans Ale (proj1 HL _ CB)) Afin) Aeq)))).
	    * intros A HA; refine (proj2 (lub_set_is_lub _) _ _).
	      intros B0 [B [[Ble Bfin] B0eq]].
	      assert (tmp : exists D, C D /\ dcpo_le B D).
	      { destruct Bfin as [l Hl]; clear B0 B0eq A HA.
	        unfold dcpo_le, SetDcpo in Ble.
	        assert (Leq := dcpo_lub_unique _ _ _ HL (lub_set_is_lub _)); lazy beta delta [lub_set] in Leq.
	        assert (Ble' := fun n ninl => proj1 (Leq _) (Ble n (proj2 (Hl _) ninl))).
	        refine (match _ with ex_intro _ D (conj CD Dle) =>
	                  ex_intro _ D (conj CD (fun n Hn => Dle n (proj1 (Hl _) Hn))) end).
	        clear L HL Ble Leq B Hl f Hf fincr.
	        induction l as [|n l IH]; [refine (ex_intro _ _ (conj Cx _))|].
	        1: intros ? [].
	        specialize (IH (fun n Hn => Ble' _ (or_intror Hn))) as [B [CB Ble]].
	        specialize (Ble' _ (or_introl eq_refl)) as [D [CD Dn]].
	        specialize (HC _ _ CB CD) as [E [CE [BleE DleE]]]; refine (ex_intro _ _ (conj CE _)).
	        intros k [->|kin]; [exact (DleE _ Dn)|exact (BleE _ (Ble _ kin))]. }
	      clear Ble; destruct tmp as [D [CD Ble]].
	      refine (dcpo_le_trans (dcpo_le_refl B0eq) _); clear B0 B0eq.
	      exact (dcpo_le_trans (fincr _ _ Ble) (HA _ (ex_intro _ _ (conj CD equiv_refl)))).
Qed.

Definition i0 : ((nat -> Prop) -> (nat -> Prop)) -> (nat -> Prop) :=
	fun f mn => f (fun y => In y (decode_finite_set (code_pi1 mn))) (code_pi2 mn).
Definition r0 : (nat -> Prop) -> ((nat -> Prop) -> (nat -> Prop)) :=
	fun e x n => exists y, dcpo_le y x /\ (exists l, (forall m, y m <-> In m l) /\ e (code_pair (code_finite_set l) n)).

Lemma r_continuity : forall A, scott_continuity (r0 A).
Proof using.
	unfold scott_continuity, dcpo_equiv, r0, dcpo_le, lub_set, SetDcpo.
	intros n; split.
	- intros A B AleB x [y [H1 H2]]; exists y; split; [exact (fun z Hz => AleB _ (H1 _ Hz))|exact H2].
	- intros C A CA HC L HL; split.
	  + intros B0 [B [CB B0eq]]; refine (dcpo_le_trans (dcpo_le_refl B0eq) _); clear B0 B0eq; cbn.
	    intros k [D [Dle [l [Deql nlk]]]].
	    exact (ex_intro _ _ (conj (fun k Dk => proj1 HL _ CB _ (Dle _ Dk)) (ex_intro _ _ (conj Deql nlk)))).
	  + intros B HB k [D [Dle [l [Deql nlk]]]].
	    assert (tmp : exists E, C E /\ dcpo_le D E).
	    { clear B HB k nlk.
	      refine (match _ with ex_intro _ E (conj CE Ele) =>
	                ex_intro _ E (conj CE (fun n Hn => Ele n (proj1 (Deql _) Hn))) end).
	      assert (Leq := dcpo_lub_unique _ _ _ HL (lub_set_is_lub _)); lazy beta delta [lub_set] in Leq.
	      assert (Dle' := fun n ninl => proj1 (Leq _) (Dle n (proj2 (Deql _) ninl))).
	      clear L HL D Dle Deql Leq.
	      induction l as [|k l IH]; [refine (ex_intro _ _ (conj CA _))|].
	      1: intros ? [].
	      specialize (IH (fun n Hn => Dle' _ (or_intror Hn))) as [B [CB Ble]].
	      specialize (Dle' _ (or_introl eq_refl)) as [D [CD Dk]].
	      specialize (HC _ _ CB CD) as [E [CE [BleE DleE]]]; refine (ex_intro _ _ (conj CE _)).
	      intros m [->|kin]; [exact (DleE _ Dk)|exact (BleE _ (Ble _ kin))]. }
	    clear A CA Dle; destruct tmp as [A [CA Dle]].
	    refine (HB _ (ex_intro _ _ (conj CA (fun _ => iff_refl _))) _ _).
	    exact (ex_intro _ _ (conj Dle (ex_intro _ _ (conj Deql nlk)))).
Qed.

Definition i : {f : (nat -> Prop) -> nat -> Prop | scott_continuity f} -> nat -> Prop := fun f => i0 (proj1_sig f).
Definition r A := exist _ _ (r_continuity A).

Lemma r_gbl_continuity : scott_continuity r.
Proof using.
	unfold r, r0; split.
	- intros f g fleg n k; cbn; intros [h [hlen [l [hfinite Hf]]]].
	  exists h; split; [exact hlen|exists l; split; [exact hfinite|exact (fleg _ Hf)]].
	- intros C A CA HC L HL; split.
	  + intros [f Hf] [B [CB feq]]; refine (dcpo_le_trans (dcpo_le_refl feq) _); clear f Hf feq; cbn.
	    intros D n [E [Ele [l [Hl Bln]]]].
	    exact (ex_intro _ _ (conj Ele (ex_intro _ _ (conj Hl (proj1 HL _ CB _ Bln))))).
	  + intros [f Hf] Hub; cbn; intros B n [D [Dle [l [Hl Lln]]]].
	    specialize (proj1 (dcpo_lub_unique _ _ _ HL (lub_set_is_lub _) _) Lln) as [E [CE Eln]].
	    refine (Hub _ (ex_intro _ _ (conj CE equiv_refl)) _ _ _); cbn.
	    exact (ex_intro _ _ (conj Dle (ex_intro _ _ (conj Hl Eln)))).
Qed.
Lemma i_gbl_continuity : scott_continuity i.
Proof using.
	unfold i, i0; split.
	- intros [f Hf] [g Hg]; cbn; intros fleg n; exact (fleg _ _).
	- intros C [f Hf] Cf HC L HL; cbn in HC; split.
	  + intros A [g [Cg Aeq]] n An; apply Aeq, (proj1 HL _ Cg) in An; exact An.
	  + intros A HA n Hn.
	  apply (dcpo_lub_unique _ _ _ HL (lub_fun_is_lub _ _ _)) in Hn; destruct Hn as [B [[g [Cg Beq]] Bn]].
	  exact (HA _ (ex_intro _ _ (conj Cg equiv_refl)) _ (proj1 (Beq _) Bn)).
Qed.

Lemma r_i_id : forall (f : (nat -> Prop) -> nat -> Prop) (Hf : scott_continuity f) n k, f n k <-> proj1_sig (r (i (exist _ f Hf))) n k.
Proof using.
	intros f Hc0 n x; assert (Hc := Hc0); unfold r, r0, i, i0; split.
	- intros fnx.
	  rewrite (continuity_iff _) in Hc; unfold equiv, lub_set in Hc.
	  apply Hc in fnx; destruct fnx as [A [[B [[HB [l Hl]] AeqfB]] Ax]].
	  exists B; split; [exact HB|exists l; split; [exact Hl|rewrite code_pi2_pair, code_pi1_pair]].
	  exact (proj1 (scott_continuity_is_wd _ Hc0 _ _ (fun x => iff_trans (Hl _) (decode_code_finite_set _ x)) _) (proj1 (AeqfB _) Ax)).
	- intros [y [ylen [l [Hl Hfx]]]].
	  refine (proj1 Hc _ _ ylen _ _).
	  rewrite code_pi2_pair, code_pi1_pair in Hfx.
	  exact (proj2 (scott_continuity_is_wd _ Hc0 _ _ (fun x => iff_trans (Hl _) (decode_code_finite_set _ x)) _) Hfx).
Qed.

Lemma scott_continuity_appl2 :
	forall {t1 t2 t3 eq1 eq2 eq3} {Hd1 : Dcpo eq1} {Hd2 : Dcpo eq2} {Hd3 : Dcpo eq3}
	       (f1 : t1 -> t2 -> t3) (f2 : t1 -> t2),
	(forall y, scott_continuity (fun v => f1 v y)) -> (forall x, scott_continuity (f1 x)) -> scott_continuity f2 ->
	scott_continuity (fun x => f1 x (f2 x)).
Proof using.
	intros t1 t2 t3 eq1 eq2 eq3 Hd1 Hd2 Hd3 f1 f2 Hf11 Hf12 Hf2; split.
	- intros x1 x2 x1lex2; refine (dcpo_le_trans (proj1 (Hf11 _) _ _ x1lex2) (proj1 (Hf12 _) _ _ (proj1 Hf2 _ _ x1lex2))).
	- intros C x Cx HC L HL; split.
	  + intros z [x' [Cx' zeq]]; refine (dcpo_le_trans (dcpo_le_refl zeq) _).
	    exact (dcpo_le_trans (proj1 (Hf11 _) _ _ (proj1 HL _ Cx')) (proj1 (Hf12 _) _ _ (proj1 Hf2 _ _ (proj1 HL _ Cx')))).
	  + intros z Hz.
	  refine (proj2 (proj2 (Hf11 (f2 L)) _ _ Cx HC _ HL) _ _).
	  intros z' [x' [Cx' z'eq]]; refine (dcpo_le_trans (dcpo_le_refl z'eq) _); clear z' z'eq.
	  assert (Hf2L := proj2 Hf2 _ _ Cx HC _ HL).
	  refine (proj2 (proj2 (Hf12 x') _ _ (ex_intro _ _ (conj Cx equiv_refl)) _ _ Hf2L) _ _).
	  1: intros y1 y2 [x1 [Cx1 y1eq]] [x2 [Cx2 y2eq]].
	  1: specialize (HC _ _ Cx1 Cx2) as [x3 [Cx3 [H1 H2]]].
	  1: refine (ex_intro _ _ (conj (ex_intro _ _ (conj Cx3 equiv_refl))
	       (conj (dcpo_le_trans (dcpo_le_refl y1eq) (proj1 Hf2 _ _ H1)) (dcpo_le_trans (dcpo_le_refl y2eq) (proj1 Hf2 _ _ H2))))).
	  intros z' [y [[x'' [Cx'' yeq]] z'eq]]; refine (dcpo_le_trans (dcpo_le_refl z'eq) _); clear z' z'eq.
	  specialize (HC _ _ Cx' Cx'') as [x1 [Cx1 [H1 H2]]].
	  refine (dcpo_le_trans _ (Hz _ (ex_intro _ _ (conj Cx1 equiv_refl)))).
	  refine (dcpo_le_trans (proj1 (Hf11 _) _ _ H1) (proj1 (Hf12 _) _ _ (dcpo_le_trans (dcpo_le_refl yeq) (proj1 Hf2 _ _ H2)))).
Qed.

Lemma scott_continuity_id : forall {t} {eq : relation t} {Hd : Dcpo eq}, scott_continuity (fun x : t => x).
Proof using.
	intros t eq Hd; split.
	1: exact (fun _ _ H => H).
	intros C x Cx HC L HL; refine (dcpo_lub_ext _ HL).
	intros y; split; [intros [z [yle Cz]]; refine (ex_intro _ _ (conj yle (ex_intro _ _ (conj Cz equiv_refl))))|].
	intros [z [yle [w [Cw zeq]]]]; refine (ex_intro _ _ (conj (dcpo_le_trans yle (dcpo_le_refl zeq)) Cw)).
Qed.

Lemma scott_continuity_const : forall [t1] {t2} {eq1 : relation t1} {eq2 : relation t2} {Hd1 : Dcpo eq1} {Hd2 : Dcpo eq2} (y : t2),
	scott_continuity (fun x : t1 => y).
Proof using.
	intros t1 t2 eq1 eq2 Hd1 Hd2 y; split.
	1: intros _ _ _; exact (dcpo_le_refl equiv_refl).
	intros C x Cx HC L HL; split.
	1: intros z [_ [_ zeq]]; exact (dcpo_le_refl zeq).
	intros z Hz; refine (Hz _ (ex_intro _ _ (conj Cx equiv_refl))).
Qed.

Lemma scott_continuity_comp : forall {t1 t2 t3 eq1 eq2 eq3} {Hd1 : Dcpo eq1} {Hd2 : Dcpo eq2} {Hd3 : Dcpo eq3} {f1 : t1 -> t2} {f2 : t2 -> t3},
	scott_continuity (H1:=Hd1) (H2:=Hd2) f1 -> scott_continuity (H2:=Hd3) f2 -> scott_continuity (fun x => f2 (f1 x)).
Proof using.
	intros t1 t2 t3 eq1 eq2 eq3 Hd1 Hd2 Hd3 f1 f2 Hf1 Hf2;
	  exact (scott_continuity_appl2 (fun _ => f2) _ (fun y => scott_continuity_const (f2 y)) (fun _ => Hf2) Hf1).
Qed.

Lemma scott_continuity_appl : forall {t1 t2 eq1 eq2} {Hd1 : Dcpo eq1} {Hd2 : Dcpo eq2} get_lub (get_lub_wd : forall C, dcpo_is_lub C (get_lub C)) (v : t1),
	scott_continuity (H1:=FunDcpo _ get_lub_wd) (fun f : sig (fun f : t1 -> t2 => scott_continuity f) => proj1_sig f v).
Proof using.
	intros t1 t2 eq1 eq2 Hd1 Hd2 get Hget v; split.
	- intros [f Hf] [g Hg] fleg; exact (fleg v).
	- intros C x Cx HC L HL; split.
	  + intros hv [[h Hh] [Ch hveq]]; exact (dcpo_le_trans (dcpo_le_refl hveq) (proj1 HL _ Ch v)).
	  + intros y Hy; cbn.
	    refine (dcpo_le_trans (dcpo_le_refl (dcpo_lub_unique _ _ _ HL (lub_fun_is_lub _ Hget C) v)) _); cbn.
	    exact (proj2 (Hget _) _ Hy).
Qed.

Lemma scott_continuity_fun_iff :
	forall {t1 t2 t3 eq1} {eq2 : relation t2} {eq3 : relation t3} {Hd1 : Dcpo eq1} {Hd2 : Dcpo eq2} {Hd3 : Dcpo eq3}
	       get_lub (get_lub_wd : forall C, dcpo_is_lub C (get_lub C)) (F : t1 -> { f : t2 -> t3 | scott_continuity f }),
	scott_continuity (H2:=FunDcpo _ get_lub_wd) F <-> forall y, scott_continuity (fun x => proj1_sig (F x) y).
Proof using.
	intros t1 t2 t3 eq1 eq2 eq3 Hd1 Hd2 Hd3 get Hget F; split; [intros [H1 H2]|intros H0]; split.
	- intros x1 x2 x1lex2; exact (H1 _ _ x1lex2 _).
	- intros C x Cx HC L HL.
	  refine (dcpo_lub_ext_r _ (dcpo_lub_unique _ _ _ (lub_fun_is_lub _ _ _) (H2 _ _ Cx HC _ HL) y)); unfold proj1_sig, lub_fun.
	  refine (dcpo_lub_ext _ (Hget _)).
	  intros z; split.
	  2: intros [z' [zle [x' [Cx' z'eq]]]]; refine (ex_intro _ _ (conj zle (ex_intro _ _ (conj (ex_intro _ _ (conj Cx' equiv_refl)) z'eq)))).
	  2: exact (dcpo_He (Dcpo:=FunDcpo _ Hget)).
	  intros [z' [zle [g [[x' [Cx' geq]] z'eq]]]].
	  exact (ex_intro _ _ (conj zle (ex_intro _ _ (conj Cx' (equiv_trans z'eq (geq _)))))).
	- intros x1 x2 x1lex2 y; exact (proj1 (H0 _) _ _ x1lex2).
	- intros C x Cx HC L HL; split.
	  + intros f [x' [Cx' feq]] y; refine (proj1 (proj2 (H0 y) _ _ Cx HC _ HL) _ (ex_intro _ _ (conj Cx' (feq _)))).
	  + intros f Hf y; refine (proj2 (proj2 (H0 y) _ _ Cx HC _ HL) _ _).
	    intros z [x' [Cx' zeq]]; refine (dcpo_le_trans (dcpo_le_refl zeq) (Hf _ (ex_intro _ _ (conj Cx' equiv_refl)) _)).
	    exact (dcpo_He (Dcpo:=FunDcpo _ Hget)).
Qed.

Lemma scott_continuity_fun_ext :
	forall {t1 t2 eq1 eq2} {Hd1 : Dcpo eq1} {Hd2 : Dcpo eq2} {f1 f2 : t1 -> t2},
	       (forall x, dcpo_equiv (Dcpo:=Hd2) (f1 x) (f2 x)) ->
	scott_continuity f1 -> scott_continuity f2.
Proof using.
	intros t1 t2 eq1 eq2 Hd1 Hd2 f1 f2 Hf; split.
	- intros x y xley; refine (dcpo_le_trans (dcpo_le_trans (dcpo_le_refl (equiv_sym (Hf _))) (proj1 H _ _ xley)) (dcpo_le_refl (Hf _))).
	- intros C x Cx HC L HL.
	  refine (dcpo_lub_ext_r (dcpo_lub_ext _ (proj2 H _ _ Cx HC _ HL)) (Hf _)).
	  clear x Cx; intros y; split; intros [z [yle [x [Cx zeq]]]]; refine (ex_intro _ _ (conj yle (ex_intro _ _ (conj Cx (equiv_trans zeq _))))).
	  1: exact (Hf _).
	  exact (equiv_sym (Hf _)).
Qed.

End P_omega.
