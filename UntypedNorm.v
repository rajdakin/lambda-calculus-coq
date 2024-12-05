Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Relations.
Require Import Untyped.

Open Scope nat.

Module UntypedNorm (UntypedL : UntypedLambdaT).
Module Export Vars := UntypedL.Vars.
Import UntypedL.

Fixpoint nlambdas u := match u with
	| BAbs u => S (nlambdas u)
	| BVar _ | BBound _ | BApp _ _ => O
end.
Fixpoint skip_lambdas u := match u with
	| BAbs u => skip_lambdas u
	| BVar _ | BBound _ | BApp _ _ => u
end.
Fixpoint add_lambdas u n := match n with
	| O => u
	| S n => BAbs (add_lambdas u n)
end.
Fixpoint napps u := match u with
	| BApp u _ => S (napps u)
	| BVar _ | BBound _ | BAbs _ => O
end.
Fixpoint acc_apps u := match u with
	| BApp u v => v :: acc_apps u
	| BVar _ | BBound _ | BAbs _ => []
end.
Fixpoint skip_apps u := match u with
	| BApp u v => skip_apps u
	| BVar _ | BBound _ | BAbs _ => u
end.
Fixpoint add_apps u l := match l with
	| [] => u
	| v :: l => BApp (add_apps u l) v
end.
Definition head_form u := (nlambdas u, skip_apps (skip_lambdas u), acc_apps (skip_lambdas u)).
Definition of_head_form n u l := add_lambdas (add_apps u l) n.

Lemma add_lambdas_add : forall u m n, add_lambdas u (m + n) = add_lambdas (add_lambdas u m) n.
Proof using.
	intros u m n; rewrite add_comm; induction n as [|n IHn]; [exact eq_refl|exact (f_equal _ IHn)].
Qed.
Lemma add_skip_lambdas : forall u, add_lambdas (skip_lambdas u) (nlambdas u) = u.
Proof using.
	intros u; induction u as [x|n|u _ v _|u IH]; try exact eq_refl; exact (f_equal _ IH).
Qed.
Lemma skip_add_lambdas : forall u n, skip_lambdas (add_lambdas u n) = skip_lambdas u.
Proof using.
	intros u n; induction n as [|n IHn]; [exact eq_refl|exact IHn].
Qed.
Lemma n_skip_lambdas : forall u, nlambdas (skip_lambdas u) = O.
Proof using.
	intros u; induction u as [x|n|u _ v _|u IH]; try exact eq_refl; exact IH.
Qed.
Lemma n_add_lambdas : forall u n, nlambdas (add_lambdas u n) = n + nlambdas u.
Proof using.
	intros u n; induction n as [|n IHn]; [exact eq_refl|exact (f_equal _ IHn)].
Qed.
Lemma add_apps_app : forall u l m, add_apps u (app l m) = add_apps (add_apps u m) l.
Proof using.
	intros u l m; induction l as [|v l IHl]; [exact eq_refl|cbn; exact (f_equal (fun a => BApp a _) IHl)].
Qed.
Lemma add_skip_apps : forall u, add_apps (skip_apps u) (acc_apps u) = u.
Proof using.
	intros u; induction u as [x|n|u IH v _|u _]; try exact eq_refl; exact (f_equal (fun a => BApp a _) IH).
Qed.
Lemma skip_add_apps : forall u l, skip_apps (add_apps u l) = skip_apps u.
Proof using.
	intros u l; induction l as [|v l IHl]; [exact eq_refl|exact IHl].
Qed.
Lemma n_skip_apps : forall u, napps (skip_apps u) = O.
Proof using.
	intros u; induction u as [x|n|u IH v _|u _]; try exact eq_refl; exact IH.
Qed.
Lemma n_add_apps : forall u l, napps (add_apps u l) = length l + napps u.
Proof using.
	intros u l; induction l as [|v l IHl]; [exact eq_refl|exact (f_equal _ IHl)].
Qed.
Lemma acc_add_apps : forall u l, acc_apps (add_apps u l) = l ++ acc_apps u.
Proof using.
	intros u l; induction l as [|v l IHl]; [exact eq_refl|exact (f_equal _ IHl)].
Qed.

Lemma of_head_form_head_form : forall u, of_head_form (nlambdas u) (skip_apps (skip_lambdas u)) (acc_apps (skip_lambdas u)) = u.
Proof using.
	intros u; unfold of_head_form.
	rewrite add_skip_apps; exact (add_skip_lambdas _).
Qed.

Fixpoint nconstrs u := match u with
	| BVar _ | BBound _ => O
	| BApp u v => S (nconstrs u + nconstrs v)
	| BAbs u => S (nconstrs u)
end.

Lemma nconstrs_in_acc_apps : forall u v, In v (acc_apps u) -> nconstrs v < nconstrs u.
Proof using.
	intros u v; induction u as [x|n|u1 IH1 u2 _|u _]; intros Hv.
	1,2,4: contradiction Hv.
	destruct Hv as [->|Hv].
	1: exact (le_n_S _ _ (le_add_l _ _)).
	cbn; exact (lt_trans _ _ _ (IH1 Hv) (le_n_S _ _ (le_add_r _ _))).
Qed.
Lemma nconstrs_skip_lambdas : forall u, nconstrs (skip_lambdas u) <= nconstrs u.
Proof using.
	intros u; induction u as [x|n|u1 _ u2 _|u IH].
	1,2,3: exact (le_n _).
	exact (le_S _ _ IH).
Qed.
Lemma nconstrs_skip_apps : forall u, nconstrs (skip_apps u) <= nconstrs u.
Proof using.
	intros u; induction u as [x|n|u1 IH1 u2 _|u _].
	1,2,4: exact (le_n _).
	exact (le_trans _ _ _ IH1 (le_S _ _ (le_add_r _ _))).
Qed.

Lemma bterm_head_ind : forall P : bterm -> Prop,
	(forall x, P (BVar x)) ->
	(forall n, P (BBound n)) ->
	(forall u, P (skip_apps (skip_lambdas u)) -> (forall v, In v (acc_apps (skip_lambdas u)) -> P v) -> P u) ->
	forall u, P u.
Proof using.
	intros P Hv Hb H u.
	refine (nat_ind (fun n => forall u, nconstrs u <= n -> P u) _ _ _ _ (le_n _)); clear u.
	1: intros u Hu; destruct u; [exact (Hv _)|exact (Hb _)|inversion Hu|inversion Hu].
	clear Hv Hb; intros n IHn u Hu.
	inversion Hu as [eqsz|n' szulen eq]; [clear Hu|exact (IHn _ szulen)].
	refine (match _ with conj H1 H2 => H _ (IHn _ H1) (fun v Hv => IHn _ (H2 v Hv)) end); clear H P IHn.
	destruct u; try discriminate eqsz; injection eqsz as <-; cbn; split.
	- exact (le_trans _ _ _ (nconstrs_skip_apps _) (le_add_r _ _)).
	- intros v [->|Hv].
	  1: exact (le_add_l _ _).
	  exact (le_trans _ _ _ (le_S_n _ _ (le_S _ _ (nconstrs_in_acc_apps _ _ Hv))) (le_add_r _ _)).
	- exact (le_trans _ _ _ (nconstrs_skip_apps _) (nconstrs_skip_lambdas _)).
	- intros v Hv.
	  exact (le_trans _ _ _ (le_S_n _ _ (le_S _ _ (nconstrs_in_acc_apps _ _ Hv))) (nconstrs_skip_lambdas _)).
Qed.
Lemma bterm_head_rect : forall P : bterm -> Type,
	(forall x, P (BVar x)) ->
	(forall n, P (BBound n)) ->
	(forall u, P (skip_apps (skip_lambdas u)) -> (forall v, In v (acc_apps (skip_lambdas u)) -> P v) -> P u) ->
	forall u, P u.
Proof using.
	intros P Hv Hb H u.
	refine (nat_rect (fun n => forall u, nconstrs u <= n -> P u) _ _ _ _ (le_n _)); clear u.
	1: intros u Hu; destruct u; [exact (Hv _)|exact (Hb _)|exfalso; inversion Hu|exfalso; inversion Hu].
	clear Hv Hb; intros n IHn u Hu.
	assert (tmp : forall m n, m <= S n -> {m <= n} + {m = S n}).
	{ clear; intros m; induction m as [|m IHm]; intros n Hmn.
	  1: left; exact (le_0_n _).
	  destruct n as [|n]; [right; destruct m as [|m]; [exact eq_refl|exfalso; inversion Hmn; inversion H0]|].
	  specialize (IHm _ (le_S_n _ _ Hmn)) as [IH|IH]; [left; exact (le_n_S _ _ IH)|right; subst; exact eq_refl]. }
	specialize (tmp _ _ Hu) as [tmp|eqsz]; [exact (IHn _ tmp)|clear Hu].
	refine (match _ with conj H1 H2 => H _ (IHn _ H1) (fun v Hv => IHn _ (H2 v Hv)) end); clear H P IHn.
	destruct u; try discriminate eqsz; injection eqsz as <-; cbn; split.
	- exact (le_trans _ _ _ (nconstrs_skip_apps _) (le_add_r _ _)).
	- intros v [->|Hv].
	  1: exact (le_add_l _ _).
	  exact (le_trans _ _ _ (le_S_n _ _ (le_S _ _ (nconstrs_in_acc_apps _ _ Hv))) (le_add_r _ _)).
	- exact (le_trans _ _ _ (nconstrs_skip_apps _) (nconstrs_skip_lambdas _)).
	- intros v Hv.
	  exact (le_trans _ _ _ (le_S_n _ _ (le_S _ _ (nconstrs_in_acc_apps _ _ Hv))) (nconstrs_skip_lambdas _)).
Qed.

Inductive beta_head : relation bterm :=
	| BHead : forall n u v l, beta_head (of_head_form n (BAbs u) (l ++ [v])) (of_head_form n (bsubstb u O v) l).

Lemma beta_head_beta : forall u v, beta_head u v -> over_bcontext beta u v.
Proof using.
	intros u v H; inversion H as [n u' v' l eq1 eq2]; subst u v; clear H; rename u' into u, v' into v.
	unfold of_head_form.
	induction n as [|n IHn]; [unfold add_lambdas|rewrite <-add_1_r, !add_lambdas_add; exact (bctx_abs IHn)].
	rewrite add_apps_app; cbn.
	induction l as [|w l IH].
	1: exact (bctx_step (Beta _ _)).
	exact (bctx_app_l IH).
Qed.

Inductive weak_beta_head : relation bterm :=
	| WBHead : forall u v l, weak_beta_head (add_apps (BAbs u) (l ++ [v])) (add_apps (bsubstb u O v) l).

Lemma weak_beta_head_beta_head : forall u v, weak_beta_head u v -> beta_head u v.
Proof using.
	intros u v H; inversion H as [u' v' l eq1 eq2]; subst u v; clear H; rename u' into u, v' into v.
	exact (BHead O _ _ _).
Qed.

Lemma beta_head_abs : forall u v, beta_head u v -> beta_head (BAbs u) (BAbs v).
Proof using.
	intros u v H; inversion H as [n u' v' l eq1 eq2]; subst u v; clear H; rename u' into u, v' into v.
	exact (BHead (S n) _ _ _).
Qed.
Lemma weak_beta_head_app : forall u v w, weak_beta_head u v -> weak_beta_head (BApp u w) (BApp v w).
Proof using.
	intros u v w H; inversion H as [u' v' l eq1 eq2]; subst u v; clear H; rename u' into u, v' into v.
	exact (WBHead u v (w :: l)).
Qed.
Lemma weak_beta_head_step : forall u v, weak_beta_head (BApp (BAbs u) v) (bsubstb u O v).
Proof using.
	intros u v; exact (WBHead _ _ []).
Qed.

Definition normal_head_form u := match skip_apps (skip_lambdas u) with BVar _ | BBound _ => True | BApp _ _ | BAbs _ => False end.

Lemma normal_form_iff : forall u,
	RewriteSystem.normal_form (over_bcontext beta) u <->
	normal_head_form u /\ (forall v, In v (acc_apps (skip_lambdas u)) -> RewriteSystem.normal_form (over_bcontext beta) v).
Proof using.
	intros u; unfold normal_head_form.
	split; induction u as [x|n|u IHu v IHv|u IH]; intros H; cbn.
	1,2: split; [exact I|intros ? []].
	3,4: intros v f; inversion f; inversion H0.
	1: specialize (IHu (fun w Hw => H _ (bctx_app_l Hw))) as [Hu IHu]; specialize (IHv (fun w Hw => H _ (bctx_app_r Hw))) as [Hv IHv].
	2: specialize (IH (fun w Hw => H _ (bctx_abs Hw))) as [Hu IH].
	1,2: split.
	- destruct u; [exact I|exact I|exact Hu|exact (H _ (bctx_step (Beta _ _)))].
	- intros w [->|Hw].
	  1: exact (fun w Hw => H _ (bctx_app_r Hw)).
	  refine (IHu _ _); destruct u; try exact Hw; contradiction (H _ (bctx_step (Beta _ _))).
	- exact Hu.
	- exact IH.
	- intros w Hw; inversion Hw; subst.
	  1: inversion H0; subst; clear Hw H0; rename u0 into u; exact (proj1 H).
	  2: exact (proj2 H _ (or_introl _ eq_refl) _ H3).
	  refine (IHu _ _ H3).
	  destruct u; try contradiction (proj1 H).
	  1,2: split; [exact I|intros ? []].
	  split; [exact (proj1 H)|intros a Ha; exact (proj2 H _ (or_intror Ha))].
	- intros v Hv; inversion Hv; [inversion H0|]; subst; exact (IH H _ H1).
Qed.

Fixpoint standard_aux u v b := match u, v with
	| BVar x, BVar y => x = y
	| BBound m, BBound n => m = n
	| BApp u1 u2, BApp v1 v2 => standard_aux u1 v1 false /\ exists u2', clos_refl_trans beta_head u2 u2' /\ standard_aux u2' v2 true
	| BAbs u, BAbs v => match b with
		| true => standard_aux u v b
		| false => exists u', clos_refl_trans beta_head u u' /\ standard_aux u' v true
		end
	| _, _ => False
end.
Definition standard : relation bterm := fun u v => exists u', clos_refl_trans beta_head u u' /\ standard_aux u' v true.

Fixpoint forall_list2 {A} (P : relation A) l l' := match l with
	| [] => l' = []
	| hd :: tl => match l' with
		| [] => False
		| hd' :: tl' => P hd hd' /\ forall_list2 P tl tl'
	end
end.
Lemma forall_list2_rev : forall {A P l l'}, @forall_list2 A P (rev l) (rev l') -> forall_list2 P l l'.
Proof using.
	intros A P l l'; rewrite <-(rev_involutive l), <-(rev_involutive l') at 2;
	  generalize (rev l'); clear l'; induction (rev l) as [|hd tl IH]; clear l; intros [|hd' tl'] H.
	1: exact eq_refl.
	1: discriminate H.
	1: contradiction H.
	rewrite !rev_cons; cbn in H; destruct H as [H1 H2].
	specialize (IH _ H2); clear H2; rename H1 into H2, IH into H1, tl into l, tl' into l', hd into tl, hd' into tl'.
	generalize dependent (rev l'); clear l'; induction (rev l) as [|hd l0 IH]; clear l; [|rename l0 into l]; intros [|hd' l'] H1.
	1: exact (conj H2 eq_refl).
	1: discriminate H1.
	1: contradiction H1.
	exact (conj (proj1 H1) (IH _ (proj2 H1))).
Qed.

Lemma standard_aux_false_iff : forall u v, standard_aux u v false <->
	match skip_apps u with
		| BVar _ | BBound _ => skip_apps u = skip_apps v
		| BApp _ _ => False
		| BAbs u'' => match skip_apps v with BAbs v'' => standard u'' v'' | _ => False end
	end /\
	forall_list2 standard (acc_apps u) (acc_apps v).
Proof using.
	intros u v; unfold head_form; split.
	- intros H; split.
	  + generalize dependent u; induction v as [y|n|v1 IH1 v2 _|v _]; intros [x|m|u1 u2|u] H; try contradiction H; cbn in H.
	    1,2: exact (f_equal _ H).
	    1: exact (IH1 _ (proj1 H)).
	    exact H.
	  + generalize dependent u; induction v as [y|n|v1 IH1 v2 _|v _];
	      intros [x|m|u1 u2|u] H1; try contradiction H1; simpl acc_apps.
	    1,2,4: exact eq_refl.
	    split; [exact (proj2 H1)|exact (IH1 _ (proj1 H1))].
	- intros [H1 H2].
	  generalize dependent v; induction u as [x|n|u1 IH1 u2 _|u _]; intros [y|m|v1 v2|v] H1 H2;
	    try contradiction H1; try discriminate H1; try contradiction H2; try discriminate H2.
	  1,2: injection H1 as H1; exact H1.
	  2: exact H1.
	  exact (conj (IH1 v1 H1 (proj2 H2)) (proj1 H2)).
Qed.
Lemma standard_aux_true_iff : forall u v, standard_aux u v true <->
	nlambdas u = nlambdas v /\
	match skip_apps (skip_lambdas u) with
		| BVar _ | BBound _ => skip_apps (skip_lambdas u) = skip_apps (skip_lambdas v)
		| BApp _ _ => False
		| BAbs u'' => match skip_apps (skip_lambdas v) with BAbs v'' => standard u'' v'' | _ => False end
	end /\
	forall_list2 standard (acc_apps (skip_lambdas u)) (acc_apps (skip_lambdas v)).
Proof using.
	intros u v; split.
	- intros H; split.
	  + generalize dependent u; induction v as [y|n|v1 _ v2 _|v IH]; intros [x|m|u1 u2|u] H; try contradiction H; cbn in H.
	    1-3: exact eq_refl.
	    exact (f_equal S (IH _ H)).
	  + generalize dependent u; induction v as [y|n|v1 _ v2 _|v IH]; intros [x|m|u1 u2|u] H1; try contradiction H1; cbn in *.
	    1,2: split; [exact (f_equal _ H1)|exact eq_refl].
	    2: exact (IH _ H1).
	    exact (match proj1 (standard_aux_false_iff _ _) (proj1 H1) with conj H1' H2' => conj H1' (conj (proj2 H1) H2') end).
	- intros [H1 [H2 H3]].
	  generalize dependent u; induction v as [y|k|v1 _ v2 _|v IH]; intros u H1 H2 H3; cbn.
	  1,2: destruct u; try discriminate H1; try discriminate H2; [injection H2 as eq; exact eq|contradiction H3].
	  2: destruct u; try discriminate H1; injection H1 as H1; exact (IH _ H1 H2 H3).
	  cbn in H1, H2, H3.
	  destruct u; try discriminate H1; try solve [cbn in H3; destruct (acc_apps v1); discriminate H3].
	  clear H1; cbn in H2, H3.
	  rewrite standard_aux_false_iff.
	  exact (conj (conj H2 (proj2 H3)) (proj1 H3)).
Qed.
Lemma standard_iff : forall u v, standard u v <->
	exists u' l,
		u' = skip_apps (skip_lambdas (add_apps u' l)) /\
		clos_refl_trans beta_head u (of_head_form (nlambdas v) u' l) /\
		match u' with
			| BVar _ | BBound _ => u' = skip_apps (skip_lambdas v)
			| BApp _ _ => False
			| BAbs u'' => match skip_apps (skip_lambdas v) with BAbs v'' => standard u'' v'' | _ => False end
		end /\
		forall_list2 standard l (acc_apps (skip_lambdas v)).
Proof using.
	intros u v; unfold standard; split.
	- intros [u' [H1 H2]].
	  rewrite standard_aux_true_iff in H2; destruct H2 as [H2 [H3 H4]].
	  refine (ex_intro _ _ (ex_intro _ _ (conj _ (conj (rt_trans H1 _) (conj H3 H4))))).
	  2: rewrite <-H2, of_head_form_head_form; exact rt_refl.
	  rewrite add_skip_apps; f_equal.
	  clear; induction u' as [| | |u IH]; try exact eq_refl; exact IH.
	- intros (u' & l & H1 & H2 & H3 & H4).
	  refine (ex_intro _ _ (conj H2 (proj2 (standard_aux_true_iff _ _) _))); clear u H2; rename u' into u, H3 into H2, H4 into H3.
	  unfold of_head_form in *.
	  rewrite skip_add_lambdas, <-H1.
	  rewrite n_add_lambdas, add_comm; refine (match _ with conj H1 H3 => conj (f_equal (fun a => a + _) (H1 : _ = O)) (conj H2 H3) end).
	  destruct l; cbn in *.
	  2: refine (conj eq_refl _).
	  1: destruct u; [refine (conj eq_refl _)|refine (conj eq_refl _)|refine (conj eq_refl _)|contradict H1; cbn; clear].
	  4: intros H; assert (tmp := f_equal nconstrs (eq_sym H)); contradict tmp; clear H; cbn;
	       exact (lt_neq _ _ (le_n_S _ _ (le_trans _ _ _ (nconstrs_skip_apps _) (nconstrs_skip_lambdas _)))).
	  1-3: cbn in *.
	  1,2: induction v as [| |v1 _ v2 _|v IHv]; try discriminate H2; try discriminate H3; try exact eq_refl; exact (IHv H2 H3).
	  1: contradict H1; clear; intros H.
	  1: assert (f : match skip_apps u1 with BApp _ _ => True | _ => False end) by (rewrite <-H; exact I); contradict f; clear.
	  1: induction u1 as [| |u IHu v _|]; try exact (fun f => f); exact IHu.
	  rewrite acc_add_apps.
	  assert (tmp : acc_apps u = []).
	  1: destruct u; try exact eq_refl; contradict H1; cbn; clear; intros H.
	  1:{ assert (f : match skip_apps (add_apps (BApp u1 u2) l) with BApp _ _ => True | _ => False end) by (rewrite <-H; exact I); contradict f; clear.
	      induction (add_apps (BApp u1 u2) l) as [| |u IHu v _|]; try exact (fun f => f); exact IHu. }
	  rewrite tmp, app_nil_r; exact H3.
Qed.

Lemma standard_refl : forall u, standard u u.
Proof using.
	intros u; refine (bterm_head_ind (fun u => standard u u) _ _ _ u); clear u.
	1,2: intros ?; refine (ex_intro _ _ (conj rt_refl _)); exact eq_refl.
	intros u Hhd Hvs.
	apply standard_iff.
	refine (ex_intro _ _ (ex_intro _ _
	          (conj _ (conj (eq_ind _ (fun a => beta_head^* a _) rt_refl _ (of_head_form_head_form _)) (conj _ _))))).
	1: rewrite add_skip_apps; f_equal; clear; induction u as [| | |u IH]; try exact eq_refl; exact IH.
	2: remember (acc_apps (skip_lambdas u)) as l eqn:eql; clear - Hvs.
	2: induction l as [|hd tl IH]; [exact eq_refl|split; [exact (Hvs _ (or_introl eq_refl))|exact (IH (fun v Hv => Hvs _ (or_intror Hv)))]].
	clear Hvs; induction u as [x|n|u _ v _|u IH]; cbn.
	1,2: exact eq_refl.
	2: exact (IH Hhd).
	cbn in Hhd; clear v; induction u as [x|n|u IH v _|u _]; cbn.
	1,2: exact eq_refl.
	1: exact (IH Hhd).
	cbn in Hhd.
	rewrite standard_iff in Hhd |- *.
	destruct Hhd as (u' & l & equ & H1 & H2 & H3).
	exists u', l; split; [exact equ|split; [|split; [exact H2|exact H3]]].
	clear - H1; unfold of_head_form in *; cbn in H1.
	match goal with |- clos_refl_trans _ _ ?v0 => remember v0 as v eqn:eqv; clear u' l eqv end.
	remember (BAbs u) as u' eqn:equ; remember (BAbs v) as v' eqn:eqv; generalize dependent v; generalize dependent u;
	  apply clos_rt_rt1n in H1; induction H1 as [u'|u' v' w' H1 _ IH2]; intros u equ v eqv.
	1: rewrite equ in eqv; injection eqv as <-; exact rt_refl.
	subst u' w'; rename v into w; specialize (fun v Hv => IH2 v Hv _ eq_refl).
	assert (tmp : exists v, v' = BAbs v /\ beta_head u v).
	{ clear w IH2; inversion H1; subst; destruct n; [contradict H0|].
	  1: cbn; rewrite add_apps_app; cbn; destruct l; discriminate.
	  injection H0 as <-; refine (ex_intro _ _ (conj eq_refl (BHead _ _ _ _))). }
	destruct tmp as [v [-> H2]].
	exact (rt_trans (rt_step H2) (IH2 _ eq_refl)).
Qed.
Lemma standard_aux_refl : forall u b, standard_aux u u b.
Proof using.
	intros u [|].
	- rewrite standard_aux_true_iff; split; [exact eq_refl|split].
	  2: generalize (acc_apps (skip_lambdas u)); clear u; intros l; induction l as [|hd l IH];
	       [exact eq_refl|exact (conj (standard_refl _) IH)].
	  induction u as [x|n|u _ v _|u IH]; [exact eq_refl|exact eq_refl| |exact IH].
	  cbn; clear v; induction u as [x|n|u IHu v _|u _]; [exact eq_refl|exact eq_refl|exact IHu|exact (standard_refl _)].
	- rewrite standard_aux_false_iff; split.
	  2: generalize (acc_apps u); clear u; intros l; induction l as [|hd l IH];
	       [exact eq_refl|exact (conj (standard_refl _) IH)].
	  induction u as [x|n|u IHu v _|u _]; [exact eq_refl|exact eq_refl|exact IHu|exact (standard_refl _)].
Qed.

Lemma head_is_standard : forall u v, clos_refl_trans beta_head u v -> standard u v.
Proof using.
	intros u v H.
	exists v; split; [exact H|exact (standard_aux_refl _ _)].
Qed.

Lemma head_standard_is_standard : forall u v w, clos_refl_trans beta_head u v -> standard v w -> standard u w.
Proof using.
	intros u v w Huv [v' [Hvv' Hvw]].
	exists v'; split; [exact (rt_trans Huv Hvv')|exact Hvw].
Qed.

Lemma beta_head_abs_inv : forall u v, beta_head (BAbs u) v -> exists v', beta_head u v' /\ v = BAbs v'.
Proof using.
	intros u v H; inversion H as [n u' v' l eq1 eq2]; subst v; clear H.
	destruct n; [|injection eq1 as <-; refine (ex_intro _ _ (conj (BHead _ _ _ _) eq_refl))].
	contradict eq1; unfold of_head_form, add_lambdas; cbn; generalize (BAbs u'); clear u'; intros u'.
	generalize dependent v'; generalize dependent u'; induction l as [|hd l IHl];
	  intros u' v'; discriminate.
Qed.
Corollary rt_beta_head_abs_inv : forall u v, beta_head^* (BAbs u) v -> exists v', beta_head^* u v' /\ v = BAbs v'.
Proof using.
	intros u' v H; remember (BAbs u') as u eqn:equ; generalize dependent u';
	  induction H as [u v H|u|u v w _ IH1 _ IH2]; intros u' ->.
	1: specialize (beta_head_abs_inv _ _ H) as [v' [H1 H2]]; exists v'; split; [exact (rt_step H1)|exact H2].
	1: refine (ex_intro _ _ (conj rt_refl eq_refl)).
	specialize (IH1 _ eq_refl) as [v' [Hv1 Hv2]].
	specialize (IH2 _ Hv2) as [w' [Hw1 Hw2]].
	exists w'; split; [exact (rt_trans Hv1 Hw1)|exact Hw2].
Qed.

Lemma standard_abs_inv : forall u' v, standard (BAbs u') v -> exists v', standard u' v' /\ v = BAbs v'.
Proof using.
	intros u' v [u [H1 H2]].
	specialize (rt_beta_head_abs_inv _ _ H1) as [u'' [Hu ->]].
	destruct v as [| | |v]; try contradiction H2.
	refine (ex_intro _ _ (conj (ex_intro _ _ (conj Hu H2)) eq_refl)).
Qed.

Lemma head_app_r_weak : forall u v, nlambdas v = O -> beta_head^* u v -> weak_beta_head^* u v.
Proof using.
	intros u v H1 H2.
	refine (proj1 (_ : _ /\ nlambdas u = O)).
	induction H2 as [u v H2|u|u v w _ IH1 _ IH2]; [|split; [exact rt_refl|exact H1]|specialize (IH2 H1); specialize (IH1 (proj2 IH2))].
	2: split; [exact (rt_trans (proj1 IH1) (proj1 IH2))|exact (proj2 IH1)].
	refine (match _ with conj H1 H2 => conj (rt_step H1) H2 end).
	inversion H2 as [n u' v' l eq1 eq2]; subst.
	destruct n; [unfold of_head_form, add_lambdas in *|discriminate H1].
	split; [exact (WBHead _ _ _)|destruct l; exact eq_refl].
Qed.

Lemma standard_app : forall u1 u2 v1 v2, standard u1 v1 -> standard u2 v2 -> standard (BApp u1 u2) (BApp v1 v2).
Proof using.
	intros u1 u2 v1 v2 [u1' [H11 H12]] H2.
	remember (nlambdas u1') as n eqn:eq1; destruct n.
	- rewrite <-(of_head_form_head_form u1'), <-eq1 in H11; cbn in H11; rewrite add_skip_apps in H11.
	  assert (tmp : skip_lambdas u1' = u1') by (destruct u1'; try exact eq_refl; discriminate eq1).
	  rewrite tmp in H11; clear tmp.
	  assert (H11' := head_app_r_weak _ _ (eq_sym eq1) H11); clear H11.
	  exists (BApp u1' u2); split.
	  1: clear - H11'; induction H11' as [u1 u1' H11'|u1|u1 u1' u1'' _ IH1 _ IH2]; [|exact rt_refl|exact (rt_trans IH1 IH2)].
	  1: exact (rt_step (weak_beta_head_beta_head _ _ (weak_beta_head_app _ _ _ H11'))).
	  split; [clear H11' H2|exact H2].
	  destruct u1'; try discriminate eq1; destruct v1; try contradiction H12; exact H12.
	- destruct u1'; try discriminate eq1; injection eq1 as ->.
	  assert (tmp : exists u0, weak_beta_head^* u1 (BAbs u0) /\ beta_head^* u0 u1').
	  { clear H12 H2 u2 v1 v2; rename u1 into u, u1' into v'.
	    remember (BAbs v') as v eqn:eqv; generalize dependent v'.
	    apply clos_rt_rt1n in H11; induction H11 as [u|u v w H1 H2 IH]; intros w' ->.
	    1: exact (ex_intro _ _ (conj rt_refl rt_refl)).
	    destruct u as [x|k|u1 u2|u].
	    1,2: inversion H1; subst; destruct n; [destruct l|]; discriminate H0.
	    2: specialize (rt_beta_head_abs_inv _ _ (rt_trans (rt_step H1) (clos_rt1n_rt _ _ _ _ H2))) as [v' [H1' [=->]]].
	    2: exists u; exact (conj rt_refl H1').
	    destruct v as [x|k|v1 v2|v].
	    1,2: inversion H2; subst; inversion H; subst; destruct n; [destruct l|]; discriminate H4.
	    1: specialize (IH _ eq_refl) as [v0 [IH1 IH2]]; exists v0; split;
	         [refine (rt_trans (head_app_r_weak _ (BApp _ _) eq_refl (rt_step H1)) IH1)|exact IH2].
	    exists v; split.
	    2: specialize (rt_beta_head_abs_inv _ _ (clos_rt1n_rt _ _ _ _ H2)) as [v' [H1' [=->]]].
	    2: exact H1'.
	    refine (rt_step _).
	    inversion H1; destruct n; [exact (WBHead _ _ _)|discriminate H0]. }
	  destruct tmp as [u0 [H111 H112]]; clear H11; rename u1' into u1'', u0 into u1', H111 into H11, H112 into H12, H12 into H13.
	  exists (BApp (BAbs u1') u2); split.
	  1: remember (BAbs u1') as u0; clear - H11; induction H11 as [u v H|u|u v w _ IH1 _ IH2];
	       [exact (rt_step (weak_beta_head_beta_head _ _ (weak_beta_head_app _ _ _ H)))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  cbn; refine (conj _ H2).
	  destruct v1; try contradiction H13; cbn in *.
	  exact (ex_intro _ _ (conj H12 H13)).
Qed.

Lemma standard_abs : forall u v, standard u v -> standard (BAbs u) (BAbs v).
Proof using.
	intros u v [u' [H1 H2]].
	exists (BAbs u'); split.
	1: clear v H2; induction H1 as [u v H|u|u v w _ IH1 _ IH2];
	     [exact (rt_step (beta_head_abs _ _ H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	exact H2.
Qed.

Lemma standard_iff' : forall n u l v l', standard u v -> forall_list2 standard l l' -> standard (of_head_form n u l) (of_head_form n v l').
Proof using.
	intros n u l v l' Hh Hl; induction n as [|n IHn]; cbn.
	2: exact (standard_abs _ _ IHn).
	generalize dependent l'; induction l as [|hd l IHl]; intros [|hd' l'] Hl.
	1: exact Hh.
	1: discriminate Hl.
	1: contradiction Hl.
	exact (standard_app _ _ _ _ (IHl _ (proj2 Hl)) (proj1 Hl)).
Qed.

Lemma rt_beta_head_bsubstb : forall u u' n v, beta_head^* u u' -> beta_head^* (bsubstb u n v) (bsubstb u' n v).
Proof using.
	intros u u' n v H; induction H as [u u' H|u|u u' u'' _ IH1 _ IH2];
	  [|exact rt_refl|exact (rt_trans IH1 IH2)].
	inversion H as [k u1 u2 l eq1 eq2]; subst; refine (rt_step _); clear H.
	unfold of_head_form; generalize dependent v; generalize dependent n; induction k as [|k IHk]; intros n v.
	2: exact (beta_head_abs _ _ (IHk (S n) (incr_bound v O))).
	unfold add_lambdas; refine (weak_beta_head_beta_head _ _ _).
	induction l as [|hd l IHl].
	1: cbn; rewrite (bsubstb_comm (le_0_n _)); exact (WBHead _ _ []).
	exact (weak_beta_head_app _ _ _ IHl).
Qed.

Lemma incr_add_lambdas : forall u n k, incr_bound (add_lambdas u n) k = add_lambdas (incr_bound u (n + k)) n.
Proof using.
	intros u n k; generalize dependent k; induction n as [|n IHn]; intros k.
	1: exact eq_refl.
	cbn; rewrite plus_n_Sm; exact (f_equal _ (IHn _)).
Qed.
Lemma incr_add_apps : forall u l n, incr_bound (add_apps u l) n = add_apps (incr_bound u n) (map (fun v => incr_bound v n) l).
Proof using.
	intros u l n; induction l as [|v l IHl].
	1: exact eq_refl.
	exact (f_equal (fun a => BApp a _) IHl).
Qed.
Lemma rt_beta_head_incr : forall u v n, beta_head^* u v -> beta_head^* (incr_bound u n) (incr_bound v n).
Proof using.
	intros u v n H; induction H as [u v H|u|u v w _ IH1 _ IH2];
	  [refine (rt_step _)|exact rt_refl|exact (rt_trans IH1 IH2)].
	inversion H as [k u' v' l eq1 eq2]; subst; rename u' into u, v' into v; clear H.
	unfold of_head_form; rewrite !incr_add_lambdas, !incr_add_apps, (incr_bsubstb_le (le_0_n _)), map_app.
	exact (BHead _ _ _ _).
Qed.
Lemma standard_incr : forall u v n, standard u v -> standard (incr_bound u n) (incr_bound v n).
Proof using.
	intros u v n [u' [H1 H2]].
	refine (ex_intro _ _ (conj (rt_beta_head_incr _ _ _ H1) _)); clear u H1; rename u' into u.
	generalize dependent n; generalize dependent u; generalize true; induction v as [y|m|v1 IH1 v2 IH2|v IH]; intros b [x|k|u1 u2|u] H n;
	  try contradiction H.
	1: exact H.
	1: cbn in H; subst m; exact eq_refl.
	2: destruct b.
	- cbn in *; destruct H as [H1 [u2' [H21 H22]]].
	  exact (conj (IH1 _ _ H1 _) (ex_intro _ _ (conj (rt_beta_head_incr _ _ _ H21) (IH2 _ _ H22 _)))).
	- cbn in *; exact (IH _ _ H _).
	- cbn in *; destruct H as [u' [H1 H2]].
	  refine (ex_intro _ _ (conj (rt_beta_head_incr _ _ _ H1) (IH _ _ H2 _))).
Qed.

Lemma standard_bsubstb : forall u' w' n u1 w1, standard u' w' -> standard u1 w1 -> standard (bsubstb u' n u1) (bsubstb w' n w1).
Proof using.
	intros u' w'; generalize dependent u'.
	refine ((fun Hv Hb => bterm_head_ind (fun w' => _) Hv Hb _ w') _ _); clear w'; swap 1 2; swap 2 3.
	1: intros x u' n u1 w1 [u'' [H11 H12]] H2; destruct u''; try contradiction H12; cbn in *; subst.
	1: exists (BVar x); split; [exact (rt_beta_head_bsubstb _ _ _ _ H11)|exact eq_refl].
	1: intros k u' n u1 w1 [u'' [H11 H12]] H2; destruct u''; try contradiction H12; cbn in H12; subst.
	1: refine (head_standard_is_standard _ _ _ (rt_beta_head_bsubstb _ _ _ _ H11) _); unfold bsubstb.
	1: destruct (k <? n); [|destruct (k =? n); [exact H2|]]; exact (standard_refl _).
	lazy beta in Hv, Hb; intros w' Hh Hl u' n u1 w1 H1 H2.
	apply standard_iff in H1; destruct H1 as (u'0 & l & H11 & H12 & H13 & H14).
	refine (head_standard_is_standard _ _ _ (rt_beta_head_bsubstb _ _ _ _ H12) _); clear u' H12.
	generalize dependent w1; generalize dependent u1; generalize dependent n;
	  induction w' as [x|k|w'1 _ w'2 _|w' IHw']; intros n u1 w1 H2.
	1: refine (Hv _ _ _ _ _ _ H2); destruct l;
	     [destruct u'0; try contradiction H13; [injection H13 as <-; exact (standard_refl _)|discriminate H13]|contradiction H14].
	1: refine (Hb _ _ _ _ _ _ H2); destruct l;
	     [destruct u'0; try contradiction H13; [discriminate H13|injection H13 as <-; exact (standard_refl _)]|contradiction H14].
	2: exact (standard_abs _ _ (IHw' Hh Hl H13 H14 _ _ _ (standard_incr _ _ _ H2))).
	cbn in Hh, Hl, H13, H14 |- *.
	destruct l as [|u'2 l]; [discriminate H14|cbn in H14; destruct H14 as [H14 H15]]; cbn.
	refine (standard_app _ _ _ _ _ (Hl _ (or_introl eq_refl) _ _ _ _ H14 H2)).
	specialize (fun v Hv => Hl v (or_intror Hv)); cbn in H11; clear H14 u'2 w'2; rename H15 into H14.
	generalize dependent w1; generalize dependent u1; generalize dependent n; generalize dependent l;
	  induction w'1 as [x|k|w'1 IHw' w'2 _|w' _]; intros l H11 H14 n u1 w1 H2.
	1: refine (Hv _ _ _ _ _ _ H2); destruct l;
	     [destruct u'0; try contradiction H13; [injection H13 as <-; exact (standard_refl _)|discriminate H13]|contradiction H14].
	1: refine (Hb _ _ _ _ _ _ H2); destruct l;
	     [destruct u'0; try contradiction H13; [discriminate H13|injection H13 as <-; exact (standard_refl _)]|contradiction H14].
	1: destruct l as [|u'2 l]; [discriminate H14|cbn in H14; destruct H14 as [H14 H15]]; cbn.
	1: exact (standard_app _ _ _ _ (IHw' Hh (fun w Hw => Hl _ (or_intror Hw)) H13 l H11 H15 _ _ _ H2)
	            (Hl _ (or_introl eq_refl) _ _ _ _ H14 H2)).
	destruct l; [cbn in Hh, H13 |- *|contradiction H14].
	destruct u'0 as [| | |u'0]; try discriminate H13; [contradiction H13|clear H11 H14].
	cbn; exact (Hh _ _ _ _ (standard_abs _ _ H13) H2).
Qed.

Lemma sorting_lemma : forall u w v, standard u w -> over_bcontext beta w v -> standard u v.
Proof using.
	intros u w v [u' [H1 H2]] H3.
	refine (head_standard_is_standard _ _ _ H1 _); clear u H1; rename u' into u, H2 into H1, H3 into H2.
	pose (b := true); fold b in H1.
	generalize dependent b; generalize dependent u; induction H2 as [w v H2|w v v' H2 IH|v w' v' H2 IH|w v H2 IH]; intros u b H1.
	- inversion H2 as [w1 w2 eq1 eq2]; clear H2; subst.
	  destruct u as [| |u1 u2|]; try contradiction H1.
	  cbn in H1; destruct H1 as [H1 H2].
	  destruct u1 as [| | |u1]; try contradiction H1.
	  refine (head_standard_is_standard _ _ _ (rt_step (BHead O _ _ [])) _); cbn.
	  exact (standard_bsubstb _ _ _ _ _ H1 H2).
	- destruct u as [| |u1 u2|]; try contradiction H1.
	  cbn in H1; destruct H1 as [H11 H12].
	  exact (standard_app _ _ _ _ (IH _ _ H11) H12).
	- destruct u as [| |u1 u2|]; try contradiction H1.
	  cbn in H1; destruct H1 as [H11 H12].
	  destruct H12 as [u2' [H12 H13]].
	  refine (standard_app _ _ _ _ _ (head_standard_is_standard _ _ _ H12 (IH _ _ H13))).
	  clear - H11; rename u1 into u.
	  destruct v as [y|n|v1 v2|v]; destruct u as [x|m|u1 u2|u]; try contradiction H11; cbn in *.
	  1,2: rewrite H11; exact (standard_refl _).
	  1: exact (ex_intro _ _ (conj rt_refl H11)).
	  exact (standard_abs _ _ H11).
	- destruct u as [| |u1 u2|]; try contradiction H1.
	  cbn in H1.
	  destruct b; [exact (standard_abs _ _ (IH _ _ H1))|].
	  destruct H1 as [u' [H11 H12]].
	  exact (standard_abs _ _ (head_standard_is_standard _ _ _ H11 (IH _ _ H12))).
Qed.

Corollary arrow_is_standard : forall u v, (over_bcontext beta)^* u v <-> standard u v.
Proof using.
	intros u v; split.
	- intros H; apply clos_rt_rtn1 in H; induction H as [|v w H2 _ IH1].
	  1: exact (standard_refl _).
	  exact (sorting_lemma _ _ _ IH1 H2).
	- generalize dependent u; generalize dependent v; refine (bterm_head_ind _ _ _ _).
	  1,2: intros x u [[| | |] [H1 H2]]; try contradiction H2; cbn in H2; subst.
	  1,2: induction H1 as [u v H|u|u v w _ IH1 _ IH2]; [refine (rt_step _)|exact rt_refl|exact (rt_trans IH1 IH2)].
	  1,2: inversion H; subst; induction n as [|n IHn]; [|exact (bctx_abs (IHn (BHead _ _ _ _)))].
	  1,2: cbn in *; induction l as [|w l IH]; [exact (bctx_step (Beta _ _))|exact (bctx_app_l (IH (BHead O _ _ _)))].
	  intros v Hh Hl u [u' [H1 H2]].
	  refine (rt_trans (y:=u') _ _).
	  1: clear v Hh Hl H2; induction H1 as [u v H|u|u v w _ IH1 _ IH2]; [refine (rt_step _)|exact rt_refl|exact (rt_trans IH1 IH2)].
	  1: inversion H; subst; induction n as [|n IHn]; [|exact (bctx_abs (IHn (BHead _ _ _ _)))].
	  1: cbn in *; induction l as [|w l IH]; [exact (bctx_step (Beta _ _))|exact (bctx_app_l (IH (BHead O _ _ _)))].
	  clear H1 u; rename u' into u; generalize dependent u; induction v as [y|n|v1 _ v2 _|v IH];
	    intros [x|m|u1 u2|u] H; try contradiction H.
	  1,2: cbn in H; subst; exact rt_refl.
	  2: exact (clos_rt_over_bcontext_ctx (BCAbs BCHole) (IH Hh Hl _ H)).
	  cbn in Hh, Hl, H; destruct H as [H1 H2].
	  refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l BCHole _) _)
	                   (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (Hl _ (or_introl eq_refl) _ H2))); cbn.
	  specialize (fun v Hv => Hl v (or_intror Hv)).
	  clear u2 v2 H2.
	  rename u1 into u, v1 into v; generalize dependent u; induction v as [y|n|v1 IH v2 _|v _];
	    intros [x|m|u1 u2|u] H; try contradiction H.
	  1,2: cbn in H; subst; exact rt_refl.
	  1: exact (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l BCHole _) (IH Hh (fun v Hv => Hl _ (or_intror Hv)) _ (proj1 H)))
	                      (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (Hl _ (or_introl eq_refl) _ (proj2 H)))).
	  exact (Hh _ (standard_abs _ _ H)).
Qed.

End UntypedNorm.
