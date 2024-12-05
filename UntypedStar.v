Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Relations.
Require Import Untyped.

Open Scope nat.

Declare Custom Entry lsterms.
Declare Custom Entry bsterms.

Module UntypedLambdaStar (UntypedL : UntypedLambdaT).
Module Export Vars := UntypedL.Vars.

Inductive lsterm : Type :=
	| LVar : V -> lsterm
	| LApp : lsterm -> lsterm -> lsterm
	| LAbs : V -> lsterm -> lsterm
	| LStar : V -> lsterm -> lsterm -> lsterm.

Coercion LVar : V >-> lsterm.
Coercion LApp : lsterm >-> Funclass.
Notation "{{  l  }}" := l (l custom lsterms).

Notation "{ v }" := v (in custom lsterms at level 0, v constr).
Notation "( v )" := v (in custom lsterms at level 0, v custom lsterms at level 2).
Notation "^ x , M" := (LAbs x M) (in custom lsterms at level 2, x constr, M custom lsterms, format "^ x ,  M").
Notation "M N" := (LApp M N) (in custom lsterms at level 1, M custom lsterms, N custom lsterms, left associativity).
Notation "(^ * x , M ) N" := (LStar x M N) (in custom lsterms at level 1, x constr, M custom lsterms, N custom lsterms, format "(^ * x ,  M )  N").

Inductive bsterm : Type :=
	| BVar : V -> bsterm
	| BBound : nat -> bsterm
	| BApp : bsterm -> bsterm -> bsterm
	| BAbs : bsterm -> bsterm
	| BStar : bsterm -> bsterm -> bsterm.

Coercion BApp : bsterm >-> Funclass.
Notation "<{  b  }>" := b (b custom bsterms).

Notation "{ v }" := v (in custom bsterms at level 0, v constr).
Notation "( v )" := v (in custom bsterms at level 0, v custom bsterms at level 2).
Notation "< n >" := (BBound n) (in custom bsterms at level 0, n constr at level 1, format "< n >").
Notation "^ M" := (BAbs M) (in custom bsterms at level 2, M custom bsterms, format "^ M").
Notation "M N" := (BApp M N) (in custom bsterms at level 1, M custom bsterms, N custom bsterms, left associativity).
Notation "(^ * M ) N" := (BStar M N) (in custom bsterms at level 1, M custom bsterms, N custom bsterms, format "(^ * M )  N").

Fixpoint berase u := match u with
	| BVar x => UntypedL.BVar x
	| BBound n => UntypedL.BBound n
	| BApp u v => UntypedL.BApp (berase u) (berase v)
	| BAbs u => UntypedL.BAbs (berase u)
	| BStar u v => UntypedL.BApp (UntypedL.BAbs (berase u)) (berase v)
end.
Fixpoint lerase u := match u with
	| LVar x => UntypedL.LVar x
	| LApp u v => UntypedL.LApp (lerase u) (lerase v)
	| LAbs x u => UntypedL.LAbs x (lerase u)
	| LStar x u v => UntypedL.LApp (UntypedL.LAbs x (lerase u)) (lerase v)
end.

Fixpoint of_bterm u := match u with
	| UntypedL.BVar x => BVar x
	| UntypedL.BBound n => BBound n
	| UntypedL.BApp u v => BApp (of_bterm u) (of_bterm v)
	| UntypedL.BAbs u => BAbs (of_bterm u)
end.
Fixpoint of_lterm u := match u with
	| UntypedL.LVar x => LVar x
	| UntypedL.LApp u v => LApp (of_lterm u) (of_lterm v)
	| UntypedL.LAbs x u => LAbs x (of_lterm u)
end.

Lemma berase_of_bterm : forall u, berase (of_bterm u) = u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH].
	1,2: exact eq_refl.
	1: exact (f_equal2 _ IHu IHv).
	exact (f_equal _ IH).
Qed.
Lemma lerase_of_lterm : forall u, lerase (of_lterm u) = u.
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH].
	1: exact eq_refl.
	1: exact (f_equal2 _ IHu IHv).
	exact (f_equal (fun a => UntypedL.LAbs _ a) IH).
Qed.

Fixpoint bruijn_of_var x l n := match l with
	| [] => BVar x
	| hd :: tl => if dec_V hd x then BBound n else bruijn_of_var x tl (S n)
end.
Fixpoint bruijn_of u l := match u with
	| LVar x => bruijn_of_var x l O
	| LApp u v => BApp (bruijn_of u l) (bruijn_of v l)
	| LAbs x u => BAbs (bruijn_of u (x :: l))
	| LStar x u v => BStar (bruijn_of u (x :: l)) (bruijn_of v l)
end.
Fixpoint of_bruijn u n := match u with
	| BVar x => LVar x
	| BBound i => LVar (Nat.sub n (S i))
	| BApp u v => LApp (of_bruijn u n) (of_bruijn v n)
	| BAbs u => LAbs n (of_bruijn u (S n))
	| BStar u v => LApp (LAbs n (of_bruijn u (S n))) (of_bruijn v n)
end.

Lemma erase_bruijn_of : forall u l, berase (bruijn_of u l) = UntypedL.bruijn_of (lerase u) l.
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH|x u IHu v IHv]; intros l.
	- cbn; generalize 0; induction l as [|hd tl IH]; intros n.
	  1: exact eq_refl.
	  cbn; destruct (dec_V hd x) as [hdeqx|hdnex]; [exact eq_refl|exact (IH _)].
	- cbn; exact (f_equal2 _ (IHu _) (IHv _)).
	- cbn; exact (f_equal _ (IH _)).
	- cbn; exact (f_equal2 (fun a b => UntypedL.BApp (UntypedL.BAbs a) b) (IHu _) (IHv _)).
Qed.
Lemma erase_of_bruijn : forall u n, lerase (of_bruijn u n) = UntypedL.of_bruijn (berase u) n.
Proof using.
	intros u; induction u as [x|k|u IHu v IHv|u IH|u IHu v IHv]; intros n.
	- exact eq_refl.
	- exact eq_refl.
	- cbn; exact (f_equal2 _ (IHu _) (IHv _)).
	- cbn; exact (f_equal _ (IH _)).
	- cbn; exact (f_equal2 (fun a b => UntypedL.LApp (UntypedL.LAbs _ a) b) (IHu _) (IHv _)).
Qed.

Fixpoint incr_bound u k := match u with
	| BVar y => BVar y
	| BBound n => BBound (if k <=? n then S n else n)
	| BApp u v => BApp (incr_bound u k) (incr_bound v k)
	| BAbs u => BAbs (incr_bound u (S k))
	| BStar u v => BStar (incr_bound u (S k)) (incr_bound v k)
end.
Fixpoint bsubstb u n v := match u with
	| BVar y => u
	| BBound k => if k <? n then BBound k else if k =? n then v else BBound (pred k)
	| BApp u1 u2 => BApp (bsubstb u1 n v) (bsubstb u2 n v)
	| BAbs u => BAbs (bsubstb u (S n) (incr_bound v O))
	| BStar u1 u2 => BStar (bsubstb u1 (S n) (incr_bound v O)) (bsubstb u2 n v)
end.

Lemma incr_bound_comm : forall {u n1 n2}, n1 <= n2 -> incr_bound (incr_bound u n2) n1 = incr_bound (incr_bound u n1) (S n2).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n1 n2 Hn.
	- exact eq_refl.
	- unfold incr_bound.
	  destruct (le_gt_cases n2 k) as [n2lek|kltn2].
	  1: rewrite (proj2 (leb_le _ _) n2lek), (proj2 (leb_le _ _) (le_trans _ _ _ Hn (le_S _ _ n2lek))).
	  1: rewrite (proj2 (leb_le _ _) (le_trans _ _ _ Hn n2lek)), (proj2 (leb_le _ _) (le_n_S _ _ n2lek)).
	  1: exact eq_refl.
	  rewrite (proj2 (leb_gt _ _) kltn2).
	  destruct (n1 <=? k); [rewrite (proj2 (leb_gt _ _) (le_n_S _ _ kltn2))|rewrite (proj2 (leb_gt _ _) (le_S _ _ kltn2))]; exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _ Hn) (IH2 _ _ Hn)).
	- exact (f_equal _ (IH _ _ (le_n_S _ _ Hn))).
	- exact (f_equal2 _ (IH1 _ _ (le_n_S _ _ Hn)) (IH2 _ _ Hn)).
Qed.

Lemma erase_incr_bound : forall u n, berase (incr_bound u n) = UntypedL.incr_bound (berase u) n.
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _) (IH2 _)).
	- exact (f_equal _ (IH _)).
	- exact (f_equal2 (fun a b => UntypedL.BApp (UntypedL.BAbs a) b) (IH1 _) (IH2 _)).
Qed.
Lemma erase_bsubstb : forall u n v, berase (bsubstb u n v) = UntypedL.bsubstb (berase u) n (berase v).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v.
	- exact eq_refl.
	- unfold bsubstb, UntypedL.bsubstb, berase; fold berase.
	  destruct (k <? n); [exact eq_refl|destruct (k =? n); exact eq_refl].
	- exact (f_equal2 _ (IH1 _ _) (IH2 _ _)).
	- exact (f_equal UntypedL.BAbs (eq_trans (IH _ _) (f_equal (fun a => UntypedL.bsubstb _ _ a) (erase_incr_bound _ _)))).
	- cbn; refine (f_equal2 (fun a b => UntypedL.BApp (UntypedL.BAbs a) b)
	                 (eq_trans (IH1 _ _) (f_equal (fun a => UntypedL.bsubstb _ _ a) (erase_incr_bound _ _)))
	                 (IH2 _ _)).
Qed.

Inductive betastar : relation bsterm :=
	| BetaStar : forall u v, betastar (BStar u v) (bsubstb u O v).
Lemma betastar_irrefl : forall u, ~ betastar u u.
Proof using.
	intros u H; inversion H; subst; clear H; rename u0 into u, H2 into H.
	pose (count_spots := fix count_spots u n := match u with
		| BVar _ => O
		| BBound k => if k =? n then S O else O
		| BApp u v => count_spots u n + count_spots v n
		| BAbs u => count_spots u (S n)
		| BStar u v => count_spots u (S n) + count_spots v n
	end).
	pose (cost1 := fix cost u := match u with
		| BVar _ => O
		| BBound _ => O
		| BApp u v => cost u + cost v
		| BAbs u => cost u
		| BStar u v => S (cost u + cost v)
	end).
	assert (cincr : forall u n, cost1 (incr_bound u n) = cost1 u).
	{ clear; intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n.
	  - exact eq_refl.
	  - exact eq_refl.
	  - exact (f_equal2 (fun a b => a + b) (IH1 _) (IH2 _)).
	  - exact (IH _).
	  - exact (f_equal2 (fun a b => S (a + b)) (IH1 _) (IH2 _)). }
	assert (tmp : forall u n v, cost1 (bsubstb u n v) = cost1 u + count_spots u n * cost1 v).
	{ clear - cincr; intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v.
	  - exact eq_refl.
	  - unfold bsubstb, count_spots, cost1.
	    destruct (lt_ge_cases k n) as [kltn|nlek]; [rewrite (proj2 (ltb_lt _ _) kltn)|rewrite (proj2 (ltb_ge _ _) nlek)].
	    1: rewrite (proj2 (eqb_neq _ _) (lt_neq _ _ kltn)); exact eq_refl.
	    destruct (k =? n); [exact (eq_sym (add_0_r _))|exact eq_refl].
	  - cbn; rewrite IH1, IH2, <-!add_assoc; f_equal.
	    rewrite add_assoc, (add_comm _ (cost1 _)), <-add_assoc; exact (f_equal _ (eq_sym (mul_add_distr_r _ _ _))).
	  - cbn; rewrite IH, cincr; exact eq_refl.
	  - cbn; rewrite IH1, IH2, <-!add_assoc, cincr; refine (f_equal (fun a => S (_ + a)) _).
	    rewrite add_assoc, (add_comm _ (cost1 _)), <-add_assoc; exact (f_equal _ (eq_sym (mul_add_distr_r _ _ _))). }
	assert (tmp' := tmp u O v); rewrite H in tmp'; cbn in tmp'.
	rewrite plus_n_Sm in tmp'; apply (f_equal (fun a => a - cost1 u)) in tmp'; rewrite !(add_comm (cost1 u)), !add_sub in tmp'.
	remember (count_spots u 0) as k eqn:eqk; destruct k as [|k].
	1: discriminate tmp'.
	apply (f_equal (fun a => a - cost1 v)) in tmp'.
	rewrite (eq_refl : S (cost1 v) = 1 + _), mul_succ_l, !add_sub in tmp'.
	apply eq_sym, mul_eq_1 in tmp'; destruct tmp' as [-> cost1v].
	destruct u; try discriminate H.
	1: cbn in eqk; destruct (n =? 0); discriminate eqk.
	cbn in H, eqk; injection H as H1 H2.
	assert (tmp' := tmp u1 1 (incr_bound v 0)); rewrite H1 in tmp'; cbn in tmp'; rewrite cincr, cost1v, mul_1_r in tmp'.
	apply (f_equal (fun a => a - cost1 u1)) in tmp'; rewrite plus_n_Sm, !(add_comm (cost1 u1)), !add_sub in tmp'.
	rewrite <-tmp' in eqk; injection eqk as eqk.
	clear H2.
	
	pose (k := O).
	pose (s := (fix inner k := match k with O => count_spots u2 O | S k => count_spots u2 (S k) + inner k end) k).
	fold k in tmp', H1; rewrite (eq_refl : count_spots u2 0 = s) in eqk;
	  rewrite (eq_refl : incr_bound v k = (fix inner k v := match k with O => incr_bound v O | S k => incr_bound (inner k v) O end) k v) in H1.
	subst s.
	generalize dependent k; generalize dependent v; generalize dependent u2; induction u1 as [x| |u1_1 _ u1_2 _| |u1_1 IH1 u1_2 _];
	  intros u2 v cost1v k H eqk tmp'; try discriminate H.
	1: cbn in H; destruct (n <=? k); [discriminate H|remember (n =? S k) as tmp0 eqn:eqn; destruct tmp0; [|discriminate H]].
	1: apply eq_sym, eqb_eq in eqn; subst n; destruct v as [| | | |v1 v2].
	1-5: exfalso; clear - H.
	1: match type of H with ?v0 = _ => assert (tmp : v0 = BVar v); [|rewrite tmp in H; discriminate H] end.
	2: match type of H with ?v0 = _ => assert (tmp : exists j, v0 = BBound j); [|destruct tmp as [j tmp]; rewrite tmp in H; discriminate H] end.
	3: match type of H with ?v0 = _ => assert (tmp : exists u v, v0 = BApp u v); [|destruct tmp as [u [v tmp]]; rewrite tmp in H; discriminate H] end.
	4: match type of H with ?v0 = _ => assert (tmp : exists u, v0 = BAbs u); [|destruct tmp as [u tmp]; rewrite tmp in H; discriminate H] end.
	1-4: clear H; induction k as [|k IH].
	1: exact eq_refl.
	1: cbn; rewrite IH; exact eq_refl.
	1: exists (S n); exact eq_refl.
	1: cbn; destruct IH as [j ->]; exists (S j); exact eq_refl.
	1: exact (ex_intro _ _ (ex_intro _ _ eq_refl)).
	1: destruct IH as [u [v ->]]; exact (ex_intro _ _ (ex_intro _ _ eq_refl)).
	1: exact (ex_intro _ _ eq_refl).
	1: destruct IH as [u ->]; exact (ex_intro _ _ eq_refl).
	1: match type of H with ?f0 k (BStar v1 v2) = _ => assert (tmp : f0 k (BStar v1 v2)
	     = BStar ((fix inner k v := match k with O => incr_bound v (S O) | S k => incr_bound (inner k v) (S O) end) k v1) (f0 k v2)) end.
	1: clear H; induction k as [|k IH].
	1: exact eq_refl.
	1: cbn; rewrite IH; exact eq_refl.
	1: rewrite tmp in H; injection H as H _; clear tmp.
	1: destruct v1 as [|k1| | |].
	1: match type of H with ?v0 = _ => assert (tmp : v0 = BVar v); [|rewrite tmp in H; discriminate H] end.
	2: match type of H with ?v0 = _ => assert (tmp : v0 = BBound (match k1 with O => O | S _ => S (k + k1) end));
	     [|rewrite tmp in H; destruct k1; [discriminate H|injection H as H; rewrite <-plus_n_Sm in H;
		   exact (lt_neq _ _ (le_add_r (S k) _) (eq_sym H))]] end.
	3: match type of H with ?v0 = _ => assert (tmp : exists u v, v0 = BApp u v); [|destruct tmp as [u [v tmp]]; rewrite tmp in H; discriminate H] end.
	4: match type of H with ?v0 = _ => assert (tmp : exists u, v0 = BAbs u); [|destruct tmp as [u tmp]; rewrite tmp in H; discriminate H] end.
	5: match type of H with ?v0 = _ => assert (tmp : exists u v, v0 = BStar u v); [|destruct tmp as [u [v tmp]]; rewrite tmp in H; discriminate H] end.
	1-5: clear H; induction k as [|k IH].
	1: exact eq_refl.
	1: cbn; rewrite IH; exact eq_refl.
	1: destruct k1 as [|k1]; exact eq_refl.
	1: rewrite IH; destruct k1 as [|k1]; exact eq_refl.
	1: exact (ex_intro _ _ (ex_intro _ _ eq_refl)).
	1: destruct IH as [u [v ->]]; exact (ex_intro _ _ (ex_intro _ _ eq_refl)).
	1: exact (ex_intro _ _ eq_refl).
	1: destruct IH as [u ->]; exact (ex_intro _ _ eq_refl).
	1: exact (ex_intro _ _ (ex_intro _ _ eq_refl)).
	1: destruct IH as [u [v ->]]; exact (ex_intro _ _ (ex_intro _ _ eq_refl)).
	injection H as H <-.
	specialize (IH1 u1_2 v cost1v (S k) H); cbn in IH1.
	assert (tmp'' := f_equal cost1 H); rewrite tmp in tmp''; cbn in tmp''; rewrite !cincr in tmp''.
	assert (tmp3 : cost1 u1_1 + count_spots u1_1 (S (S k)) * cost1 v = S (cost1 u1_1 + cost1 u1_2)).
	1: rewrite <-tmp''; refine (f_equal (fun a => _ + _ * a) (eq_sym _)).
	1: clear - cincr; induction k as [|k IH]; [exact (cincr _ _)|rewrite cincr; exact IH].
	clear tmp''; apply (f_equal (fun a => a - cost1 u1_1)) in tmp3; rewrite cost1v, mul_1_r, plus_n_Sm, !(add_comm (cost1 u1_1)), !add_sub in tmp3.
	cbn in tmp'; rewrite tmp3 in tmp'; injection tmp' as tmp'; rewrite tmp' in eqk; clear tmp'; rename tmp3 into tmp'.
	rewrite <-add_assoc in eqk; refine (IH1 (eq_ind _ (fun a => _ = _ + (_ + a)) eqk _ _) (eq_sym tmp')).
	clear.
	assert (tmp2 : forall u n1 n2 v, n1 < n2 -> count_spots (bsubstb u n2 (incr_bound v n1)) n1 = count_spots u n1).
	{ clear; intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n1 n2 v Hn.
	  - exact eq_refl.
	  - unfold bsubstb, count_spots; destruct (lt_ge_cases k n2) as [kltn2|n2lek]; [rewrite (proj2 (ltb_lt _ _) kltn2)|rewrite (proj2 (ltb_ge _ _) n2lek)].
	    1: exact eq_refl.
	    rewrite (eqb_sym k n1), (proj2 (eqb_neq n1 k) (lt_neq _ _ (lt_le_trans _ _ _ Hn n2lek))).
	    inversion n2lek; subst; [rewrite eqb_refl|rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))); cbn].
	    2: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (lt_le_trans _ _ _ Hn H))); exact eq_refl.
	    clear; generalize dependent n1; induction v as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n.
	    1: exact eq_refl.
	    2,4: cbn; rewrite IH1, IH2; exact eq_refl.
	    2: cbn; exact (IH _).
	    cbn; destruct (le_gt_cases n k) as [nlek|kltn]; [rewrite (proj2 (leb_le _ _) nlek)|rewrite (proj2 (leb_gt _ _) kltn)].
	    1: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek))); exact eq_refl.
	    rewrite (proj2 (eqb_neq _ _) (lt_neq _ _ kltn)); exact eq_refl.
	  - cbn; rewrite (IH1 _ _ _ Hn), (IH2 _ _ _ Hn); exact eq_refl.
	  - cbn; rewrite (incr_bound_comm (le_0_n _)), (IH _ _ _ (le_n_S _ _ Hn)); exact eq_refl.
	  - cbn; rewrite (incr_bound_comm (le_0_n _)), (IH1 _ _ _ (le_n_S _ _ Hn)), (IH2 _ _ _ Hn); exact eq_refl. }
	pose (n := k); assert (Hn := le_n _ : k <= n).
	fold n; rewrite (eq_refl : n = k) at 1 2.
	generalize dependent n; induction k as [|k IH]; intros n Hn.
	1: destruct n; exact (tmp2 _ _ _ _ (le_n_S _ _ Hn)).
	refine (f_equal2 Nat.add _ (IH _ (le_S_n _ _ (le_S _ _ Hn)))).
	clear - Hn tmp2; specialize (fun v => tmp2 u1_2 (S k) (S n) v (le_n_S _ _ Hn)).
	refine (match _ with ex_intro _ v Hv => eq_trans (f_equal (fun a => count_spots (bsubstb _ _ a) _) Hv) (tmp2 v) end).
	clear - Hn; generalize dependent k; generalize dependent v; induction n as [|n IH]; intros v k Hk.
	1: inversion Hk.
	destruct k as [|k].
	1: destruct n as [|n]; rewrite (incr_bound_comm (le_0_n _)); exact (ex_intro _ _ eq_refl).
	specialize (IH v _ (le_S_n _ _ Hk)) as [v0 ->].
	rewrite (incr_bound_comm (le_0_n _)); exact (ex_intro _ _ eq_refl).
Qed.

Inductive over_sbcontext {R : relation bsterm} | : relation bsterm :=
	| sbctx_step : forall {u v}, R u v -> over_sbcontext u v
	| sbctx_app_l : forall {u u'} [v], over_sbcontext u u' -> over_sbcontext (BApp u v) (BApp u' v)
	| sbctx_app_r : forall [u] {v v'}, over_sbcontext v v' -> over_sbcontext (BApp u v) (BApp u v')
	| sbctx_abs : forall {u v}, over_sbcontext u v -> over_sbcontext (BAbs u) (BAbs v)
	| sbctx_star_l : forall {u u'} [v], over_sbcontext u u' -> over_sbcontext (BStar u v) (BStar u' v)
	| sbctx_star_r : forall [u] {v v'}, over_sbcontext v v' -> over_sbcontext (BStar u v) (BStar u v').
Arguments over_sbcontext _ _ _ : clear implicits.

Lemma irrefl_over_sbcontext : forall R, (forall u, ~ R u u) -> forall u, ~ over_sbcontext R u u.
Proof using.
	intros R HR u H; remember u as v eqn:eqv; rewrite eqv in H at 1;
	  induction H as [u v H|u u' v H IH|u v v' H IH|u u' H IH|u u' v H IH|u v v' H IH]; subst.
	- exact (HR _ H).
	- injection eqv as eq; exact (IH eq).
	- injection eqv as eq; exact (IH eq).
	- injection eqv as eq; exact (IH eq).
	- injection eqv as eq; exact (IH eq).
	- injection eqv as eq; exact (IH eq).
Qed.

Fixpoint pbsubstb u f := match u with
	| BVar x => BVar x
	| BBound n => f n
	| BApp u v => BApp (pbsubstb u f) (pbsubstb v f)
	| BAbs u => BAbs (pbsubstb u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
	| BStar u v => BStar (pbsubstb u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end)) (pbsubstb v f)
end.

Lemma pbsubstb_ext0 : forall u f1 f2, (forall n, f1 n = f2 n) -> pbsubstb u f1 = pbsubstb u f2.
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros f1 f2 Hf.
	- exact eq_refl.
	- exact (Hf _).
	- exact (f_equal2 _ (IH1 _ _ Hf) (IH2 _ _ Hf)).
	- refine (f_equal _ (IH _ _ _)); intros [|n]; [exact eq_refl|exact (f_equal (fun a => incr_bound a _) (Hf _))].
	- refine (f_equal2 _ (IH1 _ _ _) (IH2 _ _ Hf));
	    intros [|n]; [exact eq_refl|exact (f_equal (fun a => incr_bound a _) (Hf _))].
Qed.

Lemma bsubstb_is_pbsubstb : forall u n v, bsubstb u n v = pbsubstb u (fun k => if k <? n then BBound k else if k =? n then v else BBound (pred k)).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _) (IH2 _ _)).
	- refine (f_equal BAbs (eq_trans (IH _ _) (pbsubstb_ext0 _ _ _ _))).
	  intros [|[|k]]; [exact eq_refl| |rewrite (eq_refl : (S _ <? S _) = (_ <? n)), (eq_refl : (S _ =? S _) = (_ =? n))].
	  1: cbn; destruct n as [|n]; exact eq_refl.
	  destruct (S k <? n); [|destruct (S k =? n)]; exact eq_refl.
	- refine (f_equal2 BStar (eq_trans (IH1 _ _) (pbsubstb_ext0 _ _ _ _)) (IH2 _ _)).
	  intros [|[|k]]; [exact eq_refl| |rewrite (eq_refl : (S _ <? S _) = (_ <? n)), (eq_refl : (S _ =? S _) = (_ =? n))].
	  1: cbn; destruct n as [|n]; exact eq_refl.
	  destruct (S k <? n); [|destruct (S k =? n)]; exact eq_refl.
Qed.

Lemma incr_bsubstb_le : forall {u n v k}, n <= k -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u (S k)) n (incr_bound v k).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v m nlem.
	- exact eq_refl.
	- unfold bsubstb, incr_bound; fold incr_bound.
	  destruct (lt_ge_cases k n) as [kltn|nlek].
	  + rewrite (proj2 (leb_gt _ _) (lt_le_trans _ _ _ kltn (le_S _ _ nlem))), (proj2 (ltb_lt _ _) kltn); cbn.
	    rewrite (proj2 (leb_gt _ _) (lt_le_trans _ _ _ kltn nlem)); exact eq_refl.
	  + rewrite (proj2 (ltb_ge _ _) nlek).
	    inversion nlek as [neqk|k' nlek' eqk]; subst k.
	    1: rewrite (proj2 (leb_gt _ _) (le_n_S _ _ nlem)), (proj2 (ltb_ge n n) (le_n _)), eqb_refl; exact eq_refl.
	    rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek'))); simpl "<=?".
	    destruct (le_gt_cases m k') as [mlek'|mgtk'].
	    1: rewrite (proj2 (leb_le _ _) mlek'), (proj2 (ltb_ge _ _) (le_S _ _ nlek)), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek)));
	         cbn; rewrite (proj2 (leb_le _ _) mlek'); exact eq_refl.
	    rewrite (proj2 (leb_gt _ _) mgtk'), (proj2 (ltb_ge _ _) nlek), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek')));
	      unfold incr_bound, pred.
	    rewrite (proj2 (leb_gt _ _) mgtk'); exact eq_refl.
	- exact (f_equal2 BApp (IH1 _ _ _ nlem) (IH2 _ _ _ nlem)).
	- cbn; refine (f_equal BAbs (eq_trans (IH (S _) _ (S _) (le_n_S _ _ nlem)) (f_equal (fun a => bsubstb _ _ a) _))).
	  exact (eq_sym (incr_bound_comm (le_0_n _))).
	- cbn; refine (f_equal2 BStar (eq_trans (IH1 (S _) _ (S _) (le_n_S _ _ nlem)) (f_equal (fun a => bsubstb _ _ a) _)) (IH2 _ _ _ nlem)).
	  exact (eq_sym (incr_bound_comm (le_0_n _))).
Qed.
Lemma incr_bsubstb_ge : forall {u n v k}, k <= n -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u k) (S n) (incr_bound v k).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v m mlen.
	- exact eq_refl.
	- unfold bsubstb, incr_bound; fold incr_bound.
	  destruct (lt_ge_cases k m) as [kltm|mlek].
	  1: rewrite (proj2 (leb_gt _ _) kltm), (proj2 (ltb_lt _ _) (lt_le_trans _ _ _ kltm mlen)); cbn.
	  1: rewrite (proj2 (leb_gt _ _) kltm), (proj2 (leb_le _ _) (le_S_n _ _ (le_S _ _  (lt_le_trans _ _ _ kltm mlen)))); exact eq_refl.
	  rewrite (proj2 (leb_le _ _) mlek).
	  rewrite (eq_refl : (S _ <? S _) = (k <? _)), (eq_refl : (S _ =? S _) = (k =? _)).
	  destruct (lt_ge_cases k n) as [kltn|nlek].
	  1: rewrite (proj2 (ltb_lt _ _) kltn); cbn; rewrite (proj2 (leb_le _ _) mlek) ; exact eq_refl.
	  rewrite (proj2 (ltb_ge _ _) nlek).
	  inversion nlek as [eq|k' nlek' eq]; subst k.
	  1: rewrite eqb_refl; exact eq_refl.
	  rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek'))); cbn.
	  rewrite (proj2 (leb_le _ _) (le_trans _ _ _ mlen nlek')); exact eq_refl.
	- exact (f_equal2 BApp (IH1 _ _ _ mlen) (IH2 _ _ _ mlen)).
	- cbn; refine (f_equal BAbs (eq_trans (IH (S _) _ (S _) (le_n_S _ _ mlen)) (f_equal (fun a => bsubstb _ _ a) _))).
	  exact (eq_sym (incr_bound_comm (le_0_n _))).
	- cbn; refine (f_equal2 BStar (eq_trans (IH1 (S _) _ (S _) (le_n_S _ _ mlen)) (f_equal (fun a => bsubstb _ _ a) _)) (IH2 _ _ _ mlen)).
	  exact (eq_sym (incr_bound_comm (le_0_n _))).
Qed.

Lemma over_beta_incr : forall u n v, over_sbcontext betastar (incr_bound u n) v -> exists w, over_sbcontext betastar u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u' eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u' v' H|u'1 u'2 v' H IH|u' v'1 v'2 H IH|u'1 u'2 H IH|u'1 u'2 v' H IH|u' v'1 v'2 H IH]; intros u n equ.
	- inversion H; clear H; subst; rename H0 into H.
	  destruct u as [| | | |u1 u2]; try discriminate H.
	  injection H as -> ->.
	  rewrite <-(incr_bsubstb_le (le_0_n _)).
	  refine (ex_intro _ _ (conj (sbctx_step (BetaStar _ _)) eq_refl)).
	- destruct u as [| |u1 u2| | ]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BApp w u2); split; [exact (sbctx_app_l Hw)|exact eq_refl].
	- destruct u as [| |u1 u2| | ]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BApp u1 w); split; [exact (sbctx_app_r Hw)|exact eq_refl].
	- destruct u as [| | |u| ]; try discriminate equ.
	  injection equ as ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BAbs w); split; [exact (sbctx_abs Hw)|exact eq_refl].
	- destruct u as [| | | |u1 u2]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BStar w u2); split; [exact (sbctx_star_l Hw)|exact eq_refl].
	- destruct u as [| | | |u1 u2]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BStar u1 w); split; [exact (sbctx_star_r Hw)|exact eq_refl].
Qed.
Lemma over_beta_t_incr : forall u n v, (over_sbcontext betastar)^+ (incr_bound u n) v -> exists w, (over_sbcontext betastar)^+ u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u0 eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u0 v0 H|u0 v0 w0 _ IH1 _ IH2]; intros u n equ.
	1: subst; destruct (over_beta_incr _ _ _ H) as [v [Hv1 Hv2]]; exists v; split; [exact (t_step Hv1)|exact Hv2].
	specialize (IH1 _ _ equ) as [v [Hv1 Hv2]].
	specialize (IH2 _ _ Hv2) as [w [Hw1 Hw2]].
	exists w; split; [exact (t_trans Hv1 Hw1)|exact Hw2].
Qed.
Lemma over_beta_rt_incr : forall u n v, (over_sbcontext betastar)^* (incr_bound u n) v -> exists w, (over_sbcontext betastar)^* u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u0 eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u0 v0 H|u0|u0 v0 w0 _ IH1 _ IH2]; intros u n equ.
	1: subst; destruct (over_beta_incr _ _ _ H) as [v [Hv1 Hv2]]; exists v; split; [exact (rt_step Hv1)|exact Hv2].
	1: subst; refine (ex_intro _ _ (conj rt_refl eq_refl)).
	specialize (IH1 _ _ equ) as [v [Hv1 Hv2]].
	specialize (IH2 _ _ Hv2) as [w [Hw1 Hw2]].
	exists w; split; [exact (rt_trans Hv1 Hw1)|exact Hw2].
Qed.

Lemma bsubstb_incr : forall {u n v}, bsubstb (incr_bound u n) n v = u.
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v.
	- exact eq_refl.
	- unfold bsubstb, incr_bound; fold incr_bound.
	  destruct (lt_ge_cases k n) as [kltn|nlek].
	  + rewrite (proj2 (leb_gt _ _) kltn), (proj2 (ltb_lt _ _) kltn); exact eq_refl.
	  + rewrite (proj2 (leb_le _ _) nlek).
	    rewrite (proj2 (ltb_ge _ _) (le_S _ _ nlek)), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek))); exact eq_refl.
	- exact (f_equal2 BApp (IH1 _ _) (IH2 _ _)).
	- exact (f_equal BAbs (IH _ _)).
	- exact (f_equal2 BStar (IH1 _ _) (IH2 _ _)).
Qed.

Lemma bsubstb_comm : forall {u1 u2 u3 n1 n2}, n1 <= n2 ->
	bsubstb (bsubstb u1 n1 u2) n2 u3 = bsubstb (bsubstb u1 (S n2) (incr_bound u3 n1)) n1 (bsubstb u2 n2 u3).
Proof using.
	intros u1; induction u1 as [x|k|u11 IH1 u12 IH2|u1 IH|u11 IH1 u12 IH2]; intros u2 u3 n1 n2 Hn.
	- exact eq_refl.
	- unfold bsubstb; fold bsubstb.
	  destruct (lt_ge_cases k n1) as [kltn1|n1lek].
	  2: inversion n1lek as [eq|k' n1lek' eq]; subst k.
	  3: simpl pred; destruct (lt_ge_cases k' n2) as [k'ltn2|n2lek'].
	  4: inversion n2lek' as [eq|k'' n2lek'' eq]; subst k'.
	  + rewrite (proj2 (ltb_lt _ _) kltn1), (proj2 (ltb_lt _ _) (lt_le_trans _ _ _ kltn1 (le_S _ _ Hn))); unfold bsubstb; fold bsubstb.
	    rewrite (proj2 (ltb_lt _ _) kltn1), (proj2 (ltb_lt _ _) (lt_le_trans _ _ _ kltn1 Hn)); exact eq_refl.
	  + rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl, (proj2 (ltb_lt _ _) (le_n_S _ _ Hn)); unfold bsubstb; fold bsubstb.
	    rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl; exact eq_refl.
	  + rewrite (proj2 (ltb_ge _ _) n1lek), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ n1lek'))).
	    rewrite (proj2 (ltb_lt _ _) (le_n_S _ _ k'ltn2)); unfold bsubstb; fold bsubstb.
	    rewrite (proj2 (ltb_ge _ _) n1lek), (proj2 (ltb_lt _ _) k'ltn2),
	      (eqb_sym _ n1), (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ n1lek'))); exact eq_refl.
	  + rewrite (proj2 (ltb_ge _ _) n1lek), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ n1lek'))).
	    rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl; unfold bsubstb; fold bsubstb.
	    rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl; exact (eq_sym bsubstb_incr).
	  + rewrite (proj2 (ltb_ge _ _) n1lek), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ n1lek'))).
	    rewrite (proj2 (ltb_ge _ _) (le_n_S _ _ n2lek')).
	    rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ (le_n_S _ _ n2lek'')))); unfold bsubstb; fold bsubstb.
	    rewrite (proj2 (ltb_ge _ _) n2lek'), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ n2lek''))).
	    rewrite (proj2 (ltb_ge _ _) n1lek'), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ (le_trans _ _ _ Hn n2lek'')))).
	    exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _ _ _ Hn) (IH2 _ _ _ _ Hn)).
	- cbn; specialize (IH (incr_bound u2 0) (incr_bound u3 0) (S _) (S _) (le_n_S _ _ Hn)).
	  f_equal; rewrite IH;
	    exact (f_equal2
	              (fun a b => bsubstb (bsubstb _ _ a) _ b)
	              (eq_sym (incr_bound_comm (le_0_n _)))
	              (eq_sym (incr_bsubstb_ge (le_0_n _)))).
	- cbn; specialize (IH1 (incr_bound u2 0) (incr_bound u3 0) (S _) (S _) (le_n_S _ _ Hn)).
	  refine (f_equal2 _ _ (IH2 _ _ _ _ Hn)).
	  rewrite IH1;
	    exact (f_equal2
	              (fun a b => bsubstb (bsubstb _ _ a) _ b)
	              (eq_sym (incr_bound_comm (le_0_n _)))
	              (eq_sym (incr_bsubstb_ge (le_0_n _)))).
Qed.

Lemma betastar_bsubstb_l : forall u u' n v, (over_sbcontext betastar)^* u u' -> (over_sbcontext betastar)^* (bsubstb u n v) (bsubstb u' n v).
Proof using.
	intros u u' n v H; induction H as [u u' H|u|u1 u2 u3 _ IH1 _ IH2].
	2: exact rt_refl.
	2: exact (rt_trans IH1 IH2).
	refine (rt_step _).
	generalize dependent v; generalize dependent n;
	  induction H as [u u' H|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH|u1 u1' u2 H IH|u1 u2 u2' H IH]; intros n v.
	- inversion H; subst; cbn.
	  refine (sbctx_step (eq_ind _ (fun a => betastar (BStar (bsubstb u0 (S n) (incr_bound v O)) (bsubstb v0 n v)) a) (BetaStar _ _) _ _)).
	  exact (eq_sym (bsubstb_comm (le_0_n _))).
	- exact (sbctx_app_l (IH _ _)).
	- exact (sbctx_app_r (IH _ _)).
	- exact (sbctx_abs (IH _ _)).
	- exact (sbctx_star_l (IH _ _)).
	- exact (sbctx_star_r (IH _ _)).
Qed.
Lemma betastar_bsubstb_r : forall u n v v', (over_sbcontext betastar)^* v v' -> (over_sbcontext betastar)^* (bsubstb u n v) (bsubstb u n v').
Proof using.
	assert (tmp : forall u u' n, (over_sbcontext betastar)^* u u' -> (over_sbcontext betastar)^* (incr_bound u n) (incr_bound u' n)).
	{ intros u u' n H; induction H as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  2: exact rt_refl.
	  2: exact (rt_trans IH1 IH2).
	  refine (rt_step _).
	  generalize dependent n; induction H as [u u' H|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH|u1 u1' u2 H IH|u1 u2 u2' H IH]; intros n.
	  - inversion H; subst; cbn; rewrite (incr_bsubstb_le (le_0_n _)); exact (sbctx_step (BetaStar _ _)).
	  - exact (sbctx_app_l (IH _)).
	  - exact (sbctx_app_r (IH _)).
	  - exact (sbctx_abs (IH _)).
	  - exact (sbctx_star_l (IH _)).
	  - exact (sbctx_star_r (IH _)). }
	intros u;
	  induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v v' Hv.
	1: exact rt_refl.
	1: unfold bsubstb; destruct (k <? n); [exact rt_refl|destruct (k =? n); [exact Hv|exact rt_refl]].
	1: cbn; specialize (IH1 n _ _ Hv); specialize (IH2 n _ _ Hv);
	     match goal with |- clos_refl_trans _ (BApp ?u ?v) (BApp ?u' ?v') =>
	       remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv' end.
	1: refine (rt_trans (y:=BApp u0' v0) _ _); [rename IH1 into H|rename IH2 into H]; clear - H.
	3: cbn; specialize (IH (S n) _ _ (tmp _ _ O Hv)); rename IH into H.
	3: match goal with |- clos_refl_trans _ (BAbs ?u) (BAbs ?u') =>
	     remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv'; clear - H end.
	4: cbn; specialize (IH1 (S n) _ _ (tmp _ _ O Hv)); specialize (IH2 n _ _ Hv);
	     match goal with |- clos_refl_trans _ (BStar ?u ?v) (BStar ?u' ?v') =>
	       remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv' end.
	4: refine (rt_trans (y:=BStar u0' v0) _ _); [rename IH1 into H|rename IH2 into H]; clear - H.
	1,2,3,4,5: induction H as [u v H|u|u v w _ IH1 _ IH2]; [refine (rt_step _)|exact rt_refl|exact (rt_trans IH1 IH2)].
	1: exact (sbctx_app_l H).
	1: exact (sbctx_app_r H).
	1: exact (sbctx_abs H).
	1: exact (sbctx_star_l H).
	1: exact (sbctx_star_r H).
Qed.

Lemma bsubstb_pbsubstb : forall u n v f,
	bsubstb (pbsubstb u f) n v = pbsubstb u (fun k => bsubstb (f k) n v).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH|u1 IH1 u2 IH2]; intros n v f.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _ _) (IH2 _ _ _)).
	- cbn; f_equal; rewrite IH; apply pbsubstb_ext0.
	  intros [|k]; [exact eq_refl|exact (eq_sym (incr_bsubstb_ge (le_0_n _)))].
	- cbn; rewrite IH2; f_equal; rewrite IH1; apply pbsubstb_ext0.
	  intros [|k]; [exact eq_refl|exact (eq_sym (incr_bsubstb_ge (le_0_n _)))].
Qed.

Lemma finite_developments : forall u f,
	(forall n, RewriteSystem.strong_normalizable (over_sbcontext betastar) (f n)) ->
	RewriteSystem.strong_normalizable (over_sbcontext betastar) (pbsubstb u f).
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH|u IHu v IHv]; intros f Hf.
	- cbn; refine (Acc_intro _ _); intros v Hv; inversion Hv; subst; inversion H.
	- cbn; exact (Hf _).
	- specialize (IHu _ Hf); specialize (IHv _ Hf); cbn.
	  remember (pbsubstb u f) as u' eqn:equ; clear u equ.
	  remember (pbsubstb v f) as v' eqn:eqv; clear v eqv.
	  clear f Hf.
	  generalize dependent v'; induction IHu as [u Hu IHu]; intros v Hv; induction Hv as [v Hv IHv].
	  apply Acc_intro; intros w Hw; inversion Hw; subst.
	  1: inversion H.
	  1: exact (IHu _ H2 _ (Acc_intro _ Hv)).
	  1: exact (IHv _ H2).
	- cbn.
	  match goal with |- RewriteSystem.strong_normalizable _ (BAbs (pbsubstb u ?f)) =>
	    remember f as f' eqn:eqf; specialize (IH f'); remember (pbsubstb u f') as u' eqn:equ; clear u equ end.
	  match type of IH with ?p -> _ => assert (tmp : p); [subst f'|specialize (IH tmp); clear f' f Hf eqf tmp] end.
	  { intros [|n].
	    - apply Acc_intro; intros w Hw; inversion Hw; inversion H.
	    - specialize (Hf n); remember (f n) as u; clear - Hf.
	      induction Hf as [u H IH]; apply Acc_intro.
	      intros v Hv; destruct (over_beta_incr _ _ _ Hv) as [w' [H1 ->]]; exact (IH _ H1). }
	  induction IH as [u H IH].
	  apply Acc_intro; intros v Hv; inversion Hv; subst.
	  1: inversion H0.
	  1: exact (IH _ H1).
	- assert (Hbs : forall u' v',
	            (over_sbcontext betastar)^* (pbsubstb u (fun n => match n with O => BBound O | S n0 => incr_bound (f n0) O end)) u'
	            -> (over_sbcontext betastar)^* (pbsubstb v f) v'
	            -> RewriteSystem.strong_normalizable (over_sbcontext betastar) (bsubstb u' O v')).
	  { intros u' v' Hu Hv.
	    assert (snv' := trans_clos_rt (fun x y Px => RewriteSystem.strong_normalizable_trans (over_sbcontext betastar) x Px y) (IHv _ Hf) Hv).
	    clear v Hv IHv.
	    assert (Hu' := betastar_bsubstb_l _ _ O v' Hu).
	    rewrite bsubstb_pbsubstb in Hu'.
	    refine (trans_clos_rt (fun x y Px => RewriteSystem.strong_normalizable_trans (over_sbcontext betastar) x Px y) (IHu _ _) Hu').
	    intros [|n]; [exact snv'|rewrite bsubstb_incr; exact (Hf _)]. }
	  cbn.
	  match goal with |- RewriteSystem.strong_normalizable _ (BStar (pbsubstb u ?f) _) =>
	    remember f as f' eqn:eqf; specialize (IHu f'); remember (pbsubstb u f') as u' eqn:equ; clear u equ end.
	  match type of IHu with ?p -> _ => assert (tmp : p); [subst f'|specialize (IHu tmp); clear tmp] end.
	  { intros [|n].
	    - apply Acc_intro; intros w Hw; inversion Hw; inversion H.
	    - specialize (Hf n); remember (f n) as u; clear - Hf.
	      induction Hf as [u H IHu]; constructor.
	      intros v Hv; destruct (over_beta_incr _ _ _ Hv) as [w' [H1 ->]]; exact (IHu _ H1). }
	  specialize (IHv _ Hf).
	  remember (pbsubstb v f) as v' eqn:eqv; clear v eqv.
	  clear f f' Hf eqf.
	  generalize dependent v'; induction IHu as [u Hu IHu]; intros v Hv Hbs; induction Hv as [v Hv IHv].
	  apply Acc_intro; intros w Hw; inversion Hw; subst.
	  1: inversion H; subst; refine (Hbs _ _ rt_refl rt_refl).
	  1: refine (IHu _ H2 _ (Acc_intro _ Hv) _).
	  2: refine (IHv _ H2 _).
	  1: intros u'' v' Hbu Hbv; refine (Hbs _ _ (rt_trans (rt_step H2) Hbu) Hbv).
	  1: intros u' v'' Hbu Hbv; refine (Hbs _ _ Hbu (rt_trans (rt_step H2) Hbv)).
Qed.

Fixpoint normal_form_of u := match u with
	| BVar x => BVar x
	| BBound n => BBound n
	| BApp u v => BApp (normal_form_of u) (normal_form_of v)
	| BAbs u => BAbs (normal_form_of u)
	| BStar u v => bsubstb (normal_form_of u) O (normal_form_of v)
end.

Lemma pbsubstb_id : forall u, pbsubstb u (fun n => BBound n) = u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH|u IHu v IHv].
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ IHu IHv).
	- refine (f_equal _ (eq_trans (pbsubstb_ext0 _ _ _ _) IH)); intros [|n]; exact eq_refl.
	- refine (f_equal2 _ (eq_trans (pbsubstb_ext0 _ _ _ _) IHu) IHv); intros [|n]; exact eq_refl.
Qed.

Lemma normal_form_of_wd : forall u, RewriteSystem.is_normal_form (over_sbcontext betastar) u (normal_form_of u).
Proof using.
	unfold RewriteSystem.is_normal_form, RewriteSystem.normal_form.
	intros u; split; induction u as [x|n|u IHu v IHv|u IH|u IHu v IHv].
	1,2: exact rt_refl.
	- cbn; remember (normal_form_of u) as u' eqn:eq; refine (rt_trans (y:=BApp u' v) _ _);
	    [rename IHu into H|rename IHv into H; remember (normal_form_of v) as v' eqn:eq'].
	  1,2: clear - H; induction H as [u1 u2 H|u1|u1 u2 u3 _ IH1 _ IH2].
	  1: exact (rt_step (sbctx_app_l H)).
	  3: exact (rt_step (sbctx_app_r H)).
	  1,3: exact rt_refl.
	  1,2: exact (rt_trans IH1 IH2).
	- cbn; remember (normal_form_of u) as u' eqn:eq; clear - IH; induction IH as [u1 u2 H|u1|u1 u2 u3 _ IH1 _ IH2].
	  1: exact (rt_step (sbctx_abs H)).
	  1: exact rt_refl.
	  exact (rt_trans IH1 IH2).
	- cbn; refine (rt_trans _ (rt_step (sbctx_step (BetaStar _ _)))).
	  remember (normal_form_of u) as u' eqn:eq; refine (rt_trans (y:=BStar u' v) _ _);
	    [rename IHu into H|rename IHv into H; remember (normal_form_of v) as v' eqn:eq'].
	  1,2: clear - H; induction H as [u1 u2 H|u1|u1 u2 u3 _ IH1 _ IH2].
	  1: exact (rt_step (sbctx_star_l H)).
	  3: exact (rt_step (sbctx_star_r H)).
	  1,3: exact rt_refl.
	  1,2: exact (rt_trans IH1 IH2).
	- cbn; intros v Hv; inversion Hv; subst; inversion H.
	- cbn; intros v Hv; inversion Hv; subst; inversion H.
	- intros w H; inversion H; subst.
	  1: inversion H0.
	  1: exact (IHu _ H3).
	  exact (IHv _ H3).
	- intros w H; inversion H; subst.
	  1: inversion H0.
	  exact (IH _ H1).
	- cbn; intros w H.
	  remember (normal_form_of u) as u' eqn:equ;
	  remember (normal_form_of v) as v' eqn:eqv;
	  clear u v equ eqv.
	  remember (bsubstb u' 0 v') as u0 eqn:equ; generalize dependent v'; generalize dependent 0; generalize dependent u';
	    induction H as [u w H|u1 u2 v H IH|u v1 v2 H IH|u1 u2 H IH|u1 u2 v H IH|u v1 v2 H IH]; intros u' IHu n v' IHv equ.
	  + subst u; inversion H; subst.
	    destruct u' as [|k| | |u1 u2]; try discriminate H1.
	    2: exact (IHu _ (sbctx_step (BetaStar _ _))).
	    unfold bsubstb in H1; destruct (k <? n); [|destruct (k =? n)]; try discriminate H1; subst.
	    exact (IHv _ (sbctx_step (BetaStar _ _))).
	  + destruct u'; try discriminate equ.
	    2: injection equ as equ1 eqv; exact (IH _ (fun w Hw => IHu _ (sbctx_app_l Hw)) _ _ IHv equ1).
	    unfold bsubstb in equ; destruct (n0 <? n); [|destruct (n0 =? n)]; try discriminate equ; subst.
	    exact (IHv _ (sbctx_app_l H)).
	  + destruct u'; try discriminate equ.
	    2: injection equ as equ eqv1; exact (IH _ (fun w Hw => IHu _ (sbctx_app_r Hw)) _ _ IHv eqv1).
	    unfold bsubstb in equ; destruct (n0 <? n); [|destruct (n0 =? n)]; try discriminate equ; subst.
	    exact (IHv _ (sbctx_app_r H)).
	  + destruct u'; try discriminate equ.
	    2: injection equ as equ; refine (IH _ (fun w Hw => IHu _ (sbctx_abs Hw)) _ _ _ equ).
	    2: subst; intros w Hw; apply over_beta_incr in Hw; destruct Hw as [w0 [Hw0 ->]]; exact (IHv _ Hw0).
	    unfold bsubstb in equ; destruct (n0 <? n); [|destruct (n0 =? n)]; try discriminate equ; subst.
	    exact (IHv _ (sbctx_abs H)).
	  + destruct u'; try discriminate equ.
	    2: exact (IHu _ (sbctx_step (BetaStar _ _))).
	    unfold bsubstb in equ; destruct (n0 <? n); [|destruct (n0 =? n)]; try discriminate equ; subst.
	    exact (IHv _ (sbctx_star_l H)).
	  + destruct u'; try discriminate equ.
	    2: exact (IHu _ (sbctx_step (BetaStar _ _))).
	    unfold bsubstb in equ; destruct (n0 <? n); [|destruct (n0 =? n)]; try discriminate equ; subst.
	    exact (IHv _ (sbctx_star_r H)).
Qed.

Inductive arrow1 : relation UntypedL.bterm :=
	| Arrow1 : forall u, arrow1 (berase u) (berase (normal_form_of u)).

Inductive compatible : relation bsterm :=
	| BCVar : forall {x}, compatible (BVar x) (BVar x)
	| BCBound : forall {n}, compatible (BBound n) (BBound n)
	| BCApp : forall {u u' v v'}, compatible u u' -> compatible v v' -> compatible (BApp u v) (BApp u' v')
	| BCAbs : forall {u u'}, compatible u u' -> compatible (BAbs u) (BAbs u')
	| BCStarApp : forall {u u' v v'}, compatible u u' -> compatible v v' -> compatible (BStar u v) (BApp (BAbs u') v')
	| BCStarStar : forall {u u' v v'}, compatible u u' -> compatible v v' -> compatible (BStar u v) (BStar u' v').

Lemma compatible_refl : forall {u}, compatible u u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH|u IHu v IHv]; constructor; assumption.
Qed.

Lemma compatible_erase : forall {u u'}, compatible u u' -> berase u = berase u'.
Proof using.
	intros u u' H; induction H as [x|n|u u' v v' _ IH1 _ IH2|u u' _ IH|u u' v v' _ IH1 _ IH2|u u' v v' _ IH1 _ IH2].
	1,2: exact eq_refl.
	1: exact (f_equal2 _ IH1 IH2).
	1: exact (f_equal _ IH).
	1,2: exact (f_equal2 (fun a b => UntypedL.BApp (UntypedL.BAbs a) b) IH1 IH2).
Qed.

Lemma compatible_incr : forall {u u'} [n], compatible u u' -> compatible (incr_bound u n) (incr_bound u' n).
Proof using.
	intros u u' n H; generalize dependent n;
	  induction H as [x|k|u u' v v' _ IH1 _ IH2|u u' _ IH|u u' v v' _ IH1 _ IH2|u u' v v' _ IH1 _ IH2]; intros n.
	1,2: constructor.
	1: exact (BCApp (IH1 _) (IH2 _)).
	1: exact (BCAbs (IH _)).
	1: exact (BCStarApp (IH1 _) (IH2 _)).
	exact (BCStarStar (IH1 _) (IH2 _)).
Qed.

Lemma compatible_betastar : forall {u u' v'}, compatible u u' -> over_sbcontext betastar u' v' ->
	exists v, compatible v v' /\ over_sbcontext betastar u v.
Proof using.
	intros u u' v Hc HR; generalize dependent u; induction HR as [u v H|u1 u2 v H IH|u v1 v2 H IH|u1 u2 H IH|u1 u2 v H IH|u v1 v2 H IH];
	  intros u' Hc.
	- inversion H; subst; inversion Hc; subst.
	  refine (ex_intro _ _ (conj _ (sbctx_step (BetaStar _ _)))).
	  clear - H3 H4; generalize dependent v0; generalize dependent v; generalize 0;
	    induction H3 as [x|k|u11 u12 u21 u22 H1 IH1 H2 IH2|u1 u2 H IH|u11 u12 u21 u22 H1 IH1 H2 IH2|u11 u12 u21 u22 H1 IH1 H2 IH2]; intros n v v' Hv.
	  + exact BCVar.
	  + unfold bsubstb; destruct (k <? n); [exact BCBound|destruct (k =? n); [exact Hv|exact BCBound]].
	  + exact (BCApp (IH1 _ _ _ Hv) (IH2 _ _ _ Hv)).
	  + exact (BCAbs (IH _ _ _ (compatible_incr Hv))).
	  + exact (BCStarApp (IH1 _ _ _ (compatible_incr Hv)) (IH2 _ _ _ Hv)).
	  + exact (BCStarStar (IH1 _ _ _ (compatible_incr Hv)) (IH2 _ _ _ Hv)).
	- inversion Hc; subst.
	  1: destruct (IH _ H3) as [w [Hcw Hw]]; refine (ex_intro _ _ (conj _ (sbctx_app_l Hw))).
	  2: destruct (IH _ (BCAbs H3)) as [w [Hcw Hw]]; inversion Hw; subst; [inversion H0|refine (ex_intro _ _ (conj _ (sbctx_star_l H1)))].
	  1: exact (BCApp Hcw H4).
	  inversion Hcw; subst; exact (BCStarApp H2 H4).
	- inversion Hc; subst.
	  1: destruct (IH _ H4) as [w [Hcw Hw]]; refine (ex_intro _ _ (conj _ (sbctx_app_r Hw))).
	  2: destruct (IH _ H4) as [w [Hcw Hw]]; refine (ex_intro _ _ (conj _ (sbctx_star_r Hw))).
	  1: exact (BCApp H3 Hcw).
	  exact (BCStarApp H3 Hcw).
	- inversion Hc; subst.
	  destruct (IH _ H2) as [w [Hcw Hw]]; refine (ex_intro _ _ (conj _ (sbctx_abs Hw))).
	  exact (BCAbs Hcw).
	- inversion Hc; subst.
	  destruct (IH _ H3) as [w [Hcw Hw]]; refine (ex_intro _ _ (conj _ (sbctx_star_l Hw))).
	  exact (BCStarStar Hcw H4).
	- inversion Hc; subst.
	  destruct (IH _ H4) as [w [Hcw Hw]]; refine (ex_intro _ _ (conj _ (sbctx_star_r Hw))).
	  exact (BCStarStar H3 Hcw).
Qed.

Lemma compatible_betastar_clos_t : forall {u u' v'}, compatible u u' -> (over_sbcontext betastar)^+ u' v' ->
	exists v, compatible v v' /\ (over_sbcontext betastar)^+ u v.
Proof using.
	intros u u' v Hc HR; generalize dependent u; induction HR as [u v H|u v w _ IH1 _ IH2]; intros u' Hc.
	1: destruct (compatible_betastar Hc H) as [v' [Hcv' Hv']]; exists v'; split; [exact Hcv'|exact (t_step Hv')].
	specialize (IH1 _ Hc) as [v1 [H11 H12]].
	specialize (IH2 _ H11) as [v2 [H21 H22]].
	exists v2; split; [exact H21|exact (t_trans H12 H22)].
Qed.
Lemma compatible_betastar_clos_rt : forall {u u' v'}, compatible u u' -> (over_sbcontext betastar)^* u' v' ->
	exists v, compatible v v' /\ (over_sbcontext betastar)^* u v.
Proof using.
	intros u u' v Hc HR; apply clos_rt_iff_eq_clos_t in HR; destruct HR as [<-|HR].
	1: exists u; split; [exact Hc|exact rt_refl].
	destruct (compatible_betastar_clos_t Hc HR) as [w [H1 H2]]; exists w; split; [exact H1|exact (proj2 clos_rt_iff_eq_clos_t (or_intror H2))].
Qed.

Lemma local_confluence_betastar : RewriteSystem.local_confluence eq (over_sbcontext betastar).
Proof using.
	intros u v1 v2 Huv1 Huv2.
	refine (match _ with ex_intro _ w (conj H1 H2) =>
	            ex_intro _ w (conj (proj1 (or_comm _ _) (proj1 clos_rt_iff_eq_clos_t H1))
	                               (proj1 (or_comm _ _) (proj1 clos_rt_iff_eq_clos_t H2))) end).
	generalize dependent v2; induction Huv1 as [u v1 H|u1 u1' v1 H IH|u1 v1 v1' H IH|u v1 H IH|u1 u1' v1 H IH|u1 v1 v1' H IH]; intros v2 Huv2.
	- inversion H; subst.
	  inversion Huv2; subst.
	  1: inversion H0; subst; refine (ex_intro _ _ (conj rt_refl rt_refl)).
	  1: exists (bsubstb u' 0 v); split; [exact (betastar_bsubstb_l _ _ _ _ (rt_step H3))|exact (rt_step (sbctx_step (BetaStar _ _)))].
	  exists (bsubstb u0 0 v'); split; [exact (betastar_bsubstb_r _ _ _ _ (rt_step H3))|exact (rt_step (sbctx_step (BetaStar _ _)))].
	- inversion Huv2; subst.
	  1: inversion H0.
	  1: specialize (IH _ H3) as [w1 [Hw1 Hw2]]; exists (BApp w1 v1); split; [rename Hw1 into tmp|rename Hw2 into tmp].
	  1,2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	         [refine (rt_step (sbctx_app_l H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  exists (BApp u1' v'); split; [exact (rt_step (sbctx_app_r H3))|exact (rt_step (sbctx_app_l H))].
	- inversion Huv2; subst.
	  1: inversion H0.
	  1: exists (BApp u' v1'); split; [exact (rt_step (sbctx_app_l H3))|exact (rt_step (sbctx_app_r H))].
	  specialize (IH _ H3) as [w1 [Hw1 Hw2]]; exists (BApp u1 w1); split; [rename Hw1 into tmp|rename Hw2 into tmp].
	  1,2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	         [refine (rt_step (sbctx_app_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	- inversion Huv2; subst.
	  1: inversion H0.
	  specialize (IH _ H1) as [w1 [Hw1 Hw2]]; exists (BAbs w1); split; [rename Hw1 into tmp|rename Hw2 into tmp].
	  1,2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	         [refine (rt_step (sbctx_abs H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	- inversion Huv2; subst.
	  1: inversion H0; subst; exists (bsubstb u1' 0 v1); split; [exact (rt_step (sbctx_step (BetaStar _ _)))|].
	  1: exact (betastar_bsubstb_l _ _ _ _ (rt_step H)).
	  1: specialize (IH _ H3) as [w1 [Hw1 Hw2]]; exists (BStar w1 v1); split; [rename Hw1 into tmp|rename Hw2 into tmp].
	  1,2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	         [refine (rt_step (sbctx_star_l H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  exists (BStar u1' v'); split; [exact (rt_step (sbctx_star_r H3))|exact (rt_step (sbctx_star_l H))].
	- inversion Huv2; subst.
	  1: inversion H0; subst; exists (bsubstb u1 0 v1'); split; [exact (rt_step (sbctx_step (BetaStar _ _)))|].
	  1: exact (betastar_bsubstb_r _ _ _ _ (rt_step H)).
	  1: exists (BStar u' v1'); split; [exact (rt_step (sbctx_star_l H3))|exact (rt_step (sbctx_star_r H))].
	  specialize (IH _ H3) as [w1 [Hw1 Hw2]]; exists (BStar u1 w1); split; [rename Hw1 into tmp|rename Hw2 into tmp].
	  1,2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	         [refine (rt_step (sbctx_star_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.

Lemma confluence_betastar : RewriteSystem.confluence eq (over_sbcontext betastar).
Proof using.
	refine (RewriteSystem.newman _ _ local_confluence_betastar _).
	intros u; rewrite <-pbsubstb_id; apply finite_developments.
	intros n; apply Acc_intro; intros v Hv; inversion Hv; inversion H.
Qed.

Lemma strong_confluence_arrow1 : RewriteSystem.strong_confluence eq arrow1.
Proof using.
	intros u v1 v2 Rxy1 Rxy2.
	inversion Rxy1 as [u1 equ eqv1]; subst; inversion Rxy2 as [u2 equ eqv2]; subst.
	refine (match _ : exists u0, compatible u0 u1 /\ compatible u0 u2 with ex_intro _ u0 (conj H1 H2) =>
	          ex_intro _ (berase (normal_form_of u0)) _ end).
	1:{ clear - equ; generalize dependent u2; induction u1 as [x|n|u11 u01 u12 u02|u1 u0|u11 u01 u12 u02]; intros u2 equ.
	    1: exists (BVar x); split; [|destruct u2; try discriminate equ; injection equ as <-]; exact BCVar.
	    1: exists (BBound n); split; [|destruct u2; try discriminate equ; injection equ as <-]; exact BCBound.
	    1-3: destruct u2; try discriminate equ.
	    1: injection equ as eq1 eq2; specialize (u01 _ eq1) as [u01 [H11 H12]]; specialize (u02 _ eq2) as [u02 [H21 H22]];
	         exists (BApp u01 u02).
	    2: injection equ as eq1 eq2; specialize (u01 (BAbs _) eq1) as [u01 [H11 H12]]; specialize (u02 _ eq2) as [u02 [H21 H22]];
	         inversion H12; subst; inversion H11; subst;
	         exists (BStar u u02).
	    3: injection equ as eq; specialize (u0 _ eq) as [u0 [H1 H2]]; exists (BAbs u0).
	    4: injection equ as eq1 eq2; destruct u2_1; try discriminate eq1; injection eq1 as eq1;
	         specialize (u01 _ eq1) as [u01 [H11 H12]]; specialize (u02 _ eq2) as [u02 [H21 H22]];
	         exists (BStar u01 u02).
	    5: injection equ as eq1 eq2; specialize (u01 _ eq1) as [u01 [H11 H12]]; specialize (u02 _ eq2) as [u02 [H21 H22]];
	         exists (BStar u01 u02).
	    1-5: split; try constructor 3; try constructor 4; try constructor 5; try constructor 6; assumption. }
	clear a; refine (match _ with conj H1 H2 => conj (or_introl H1) (or_introl H2) end).
	destruct (compatible_betastar_clos_rt H1 (proj1 (normal_form_of_wd _))) as [w1 [Hw11 Hw12]].
	destruct (compatible_betastar_clos_rt H2 (proj1 (normal_form_of_wd _))) as [w2 [Hw21 Hw22]].
	rewrite <-(compatible_erase Hw11), <-(compatible_erase Hw21); split.
	assert (tmp := rt_trans Hw12 (proj1 (normal_form_of_wd w1))).
	1: rewrite (RewriteSystem.confluence_is_unf _ _ confluence_betastar u0 _ _
	             (normal_form_of_wd u0)
	             (conj (rt_trans Hw12 (proj1 (normal_form_of_wd w1))) (proj2 (normal_form_of_wd w1)))); exact (Arrow1 _).
	rewrite (RewriteSystem.confluence_is_unf _ _ confluence_betastar u0 _ _
	           (normal_form_of_wd u0)
	           (conj (rt_trans Hw22 (proj1 (normal_form_of_wd w2))) (proj2 (normal_form_of_wd w2)))); exact (Arrow1 _).
Qed.

Lemma normal_form_of_bterm : forall u, normal_form_of (of_bterm u) = of_bterm u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH]; cbn.
	1,2: exact eq_refl.
	1: exact (f_equal2 _ IHu IHv).
	exact (f_equal _ IH).
Qed.

Lemma confluence_untyped : RewriteSystem.confluence eq (UntypedL.over_bcontext UntypedL.beta).
Proof using.
	refine (RewriteSystem.confluence_incl _ _ (RewriteSystem.strong_confluence_is_confluence _ _ strong_confluence_arrow1)).
	- intros u v H; induction H as [u v H|u1 u2 v H IH|u v1 v2 H IH|u v H IH].
	  + inversion H; subst.
	    rewrite <-(berase_of_bterm u0), <-(berase_of_bterm v0),
	            (eq_refl : UntypedL.BApp (UntypedL.BAbs (berase (of_bterm u0))) (berase (of_bterm v0)) = berase (BStar (of_bterm u0) (of_bterm v0))),
	            <-erase_bsubstb.
	    refine (eq_ind _ (fun a => arrow1 (berase (BStar (of_bterm u0) (of_bterm v0))) (berase a)) (Arrow1 _) _ _).
	    cbn; rewrite !normal_form_of_bterm; exact eq_refl.
	  + inversion IH; subst.
	    assert (tmp := Arrow1 (BApp u (of_bterm v))); cbn in tmp.
	    rewrite normal_form_of_bterm, berase_of_bterm in tmp; exact tmp.
	  + inversion IH; subst.
	    assert (tmp := Arrow1 (BApp (of_bterm u) u0)); cbn in tmp.
	    rewrite normal_form_of_bterm, berase_of_bterm in tmp; exact tmp.
	  + inversion IH; subst.
	    exact (Arrow1 (BAbs u0)).
	- intros u v H; inversion H as [u' equ eqv]; subst; clear H.
	  induction u' as [x|n|u IHu v IHv|u IH|u IHu v IHv].
	  + exact rt_refl.
	  + exact rt_refl.
	  + cbn; refine (rt_trans (y:=UntypedL.BApp (berase (normal_form_of u)) (berase v)) _ _); [rename IHu into H|rename IHv into H].
	    1,2: match type of H with clos_refl_trans _ ?u ?v => remember u as u' eqn:equ; remember v as v' eqn:eqv; clear - H end.
	    1,2: induction H as [u' v' H|u'|u' v' w' _ IH1 _ IH2]; [|exact rt_refl|exact (rt_trans IH1 IH2)].
	    1: exact (rt_step (UntypedL.bctx_app_l H)).
	    exact (rt_step (UntypedL.bctx_app_r H)).
	  + cbn.
	    match type of IH with clos_refl_trans _ ?u ?v => remember u as u' eqn:equ; remember v as v' eqn:eqv; clear - IH end.
	    induction IH as [u' v' H|u'|u' v' w' _ IH1 _ IH2]; [|exact rt_refl|exact (rt_trans IH1 IH2)].
	    exact (rt_step (UntypedL.bctx_abs H)).
	  + cbn; refine (rt_trans (y:=UntypedL.BApp (UntypedL.BAbs (berase (normal_form_of u))) (berase (normal_form_of v))) _ _).
	    2: rewrite erase_bsubstb; exact (rt_step (UntypedL.bctx_step (UntypedL.Beta _ _))).
	    cbn; refine (rt_trans (y:=UntypedL.BApp (UntypedL.BAbs (berase (normal_form_of u))) (berase v)) _ _);
	      [rename IHu into H|rename IHv into H].
	    1,2: match type of H with clos_refl_trans _ ?u ?v => remember u as u' eqn:equ; remember v as v' eqn:eqv; clear - H end.
	    1,2: induction H as [u' v' H|u'|u' v' w' _ IH1 _ IH2]; [|exact rt_refl|exact (rt_trans IH1 IH2)].
	    1: exact (rt_step (UntypedL.bctx_app_l (UntypedL.bctx_abs H))).
	    exact (rt_step (UntypedL.bctx_app_r H)).
Qed.

Lemma arrow1_iff : forall u v, arrow1 u v <-> UntypedL.psubst_b u v.
Proof using.
	intros u v; split; intros H.
	- inversion H as [u']; subst; clear H; induction u' as [x|n|u IHu v IHv|u IH|u IHu v IHv].
	  + constructor.
	  + constructor.
	  + cbn; constructor; assumption.
	  + cbn; constructor; assumption.
	  + cbn; rewrite erase_bsubstb; constructor; assumption.
	- induction H as[x|n|u u' v v' Hu IHu Hv IHv|u u' H IH|u u' v v' Hu IHu Hv IHv].
	  + exact (Arrow1 (BVar x)).
	  + exact (Arrow1 (BBound n)).
	  + inversion IHu as [u0]; inversion IHv as [v0]; subst.
	    exact (Arrow1 (BApp u0 v0)).
	  + inversion IH as [u0]; subst.
	    exact (Arrow1 (BAbs u0)).
	  + inversion IHu as [u0]; inversion IHv as [v0]; subst.
	    rewrite <-erase_bsubstb; exact (Arrow1 (BStar u0 v0)).
Qed.

End UntypedLambdaStar.
