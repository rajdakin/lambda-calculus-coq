Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Dcpo.
Require Import Relations.
Require Import Untyped.

Open Scope nat.

Module UntypedModels (UntypedL : UntypedLambdaT).
Module Export Vars := UntypedL.Vars.
Import UntypedL.

Module Type ModelDefs.
Parameter (D : Type) (eval : bterm -> D).
Parameter (equiv : relation D) (He : Equiv equiv).

Parameter coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u) (eval v).
End ModelDefs.

Module TrivialModel <: ModelDefs.
Definition D := unit.
Definition eval (_ : bterm) := tt.
Definition equiv := @eq D.
Definition He := eq_equiv D.
Lemma coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> eval u = eval v.
Proof using.
	intros u v _; unfold eval; exact eq_refl.
Qed.
End TrivialModel.

Module CorrectModel <: ModelDefs.
Definition D := bterm.
Definition eval (u : bterm) := u.
Definition equiv := clos_refl_sym_trans (over_bcontext beta).
#[local] Instance equiv_crst_beta : Equiv equiv := {
	equiv_refl := @rst_refl _ _;
	equiv_sym := @rst_sym _ _;
	equiv_trans := @rst_trans _ _;
}.
Definition He := equiv_crst_beta.
Lemma coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u) (eval v).
Proof using.
	intros u v H; exact H.
Qed.

Lemma non_trivial : exists u v, ~ equiv (eval u) (eval v).
Proof using.
	exists (BBound O), (BBound (S O)); unfold equiv; intros H.
	destruct (proj1 (proj1 (RewriteSystem.confluence_iff_church_rosser _ _) confluence_beta) _ _ (or_intror H))
	  as [OeqSO|H2]; clear H.
	1: discriminate OeqSO.
	destruct H2 as [u [H1 H2]].
	apply clos_rt_rt1n in H1; inversion H1; subst.
	2: inversion H; inversion H3.
	apply clos_rt_rt1n in H2; inversion H2; subst.
	inversion H; inversion H3.
Qed.
End CorrectModel.

Module Type EnvModelDefs.
Parameter (D : Type) (eval : bterm -> (V -> D) -> (nat -> D) -> D).
Parameter (equiv : relation D) (He : Equiv equiv).

Parameter (coherent_eval : forall u v rho rhob, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u rho rhob) (eval v rho rhob)).
End EnvModelDefs.

Module ToModelDefs(EM : EnvModelDefs) <: ModelDefs.
Definition D := (V -> EM.D) -> (nat -> EM.D) -> EM.D.
Definition eval := EM.eval.
Definition equiv : relation D := fun x y => forall rho rhob, EM.equiv (x rho rhob) (y rho rhob).
#[local] Instance to_md_equiv : Equiv equiv := {
	equiv_refl := fun u rho rhob => @equiv_refl _ _ EM.He _;
	equiv_sym := fun u v Huv rho rhob => @equiv_sym _ _ EM.He _ _ (Huv rho rhob);
	equiv_trans := fun u v w Huv Hvw rho rhob => @equiv_trans _ _ EM.He _ _ _ (Huv rho rhob) (Hvw rho rhob);
}.
Definition He := to_md_equiv.
Lemma coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u) (eval v).
Proof using.
	intros u v Huv rho rhob; exact (EM.coherent_eval _ _ _ _ Huv).
Qed.
End ToModelDefs.

Module Type EnvModelDcpoReqs.
Parameter (D : Type) (equiv : relation D) (Hd : Dcpo equiv).
#[local] Instance Hd' : Dcpo equiv := Hd.
Parameter (get_lub : (D -> Prop) -> D) (get_lub_wd : forall C, dcpo_is_lub C (get_lub C)).
Parameter r : D -> { f : D -> D | scott_continuity f }.
Parameter Hr : scott_continuity (H2:=FunDcpo get_lub get_lub_wd) r.
Parameter i : { f : D -> D | scott_continuity f } -> D.
Parameter Hi : scott_continuity (H1:=FunDcpo get_lub get_lub_wd) i.
Parameter r_i_id : forall (f : D -> D) (Hf : scott_continuity f) x, dcpo_equiv (f x) (proj1_sig (r (i (exist _ f Hf))) x).
End EnvModelDcpoReqs.

Module EnvModelDcpo (M : EnvModelDcpoReqs) <: EnvModelDefs.
Definition D := M.D.
Definition equiv := M.equiv.
#[local] Instance Hd : Dcpo equiv := M.Hd.
Definition He : Equiv equiv := dcpo_He.

Fixpoint insert_at {T} (f : nat -> T) k v n := match k, n with
	| O, O => v
	| O, S n => f n
	| S k, O => f O
	| S k, S n => insert_at (fun n => f (S n)) k v n
end.
Lemma insert_at_lt : forall {T} f k v n, n < k -> @insert_at T f k v n = f n.
Proof using.
	intros T f k v n H.
	generalize dependent f; generalize dependent n; induction k as [|k IHk]; intros n nltk f; cbn.
	1: inversion nltk.
	destruct n as [|n]; [exact eq_refl|exact (IHk _ (le_S_n _ _ nltk) _)].
Qed.
Lemma insert_at_eq : forall {T} f k v, @insert_at T f k v k = v.
Proof using.
	intros T f k v.
	generalize dependent f; induction k as [|k IHk]; intros f; cbn.
	1: exact eq_refl.
	exact (IHk _).
Qed.
Lemma insert_at_gt : forall {T} f k v n, k <= n -> @insert_at T f k v (S n) = f n.
Proof using.
	intros T f k v n H.
	generalize dependent f; generalize dependent n; induction k as [|k IHk]; intros n klen f; cbn.
	1: exact eq_refl.
	destruct n as [|n]; [inversion klen|exact (IHk _ (le_S_n _ _ klen) _)].
Qed.
Lemma insert_at_comm : forall {T} f k1 v1 k2 v2, k1 <= k2 -> forall n,
	insert_at (@insert_at T f k1 v1) (S k2) v2 n = insert_at (insert_at f k2 v2) k1 v1 n.
Proof using.
	intros T f k1 v1 k2 v2 k1lek2 n.
	destruct (lt_ge_cases n k1) as [nltk1|ngek1].
	1: rewrite (insert_at_lt _ _ _ _ nltk1), (insert_at_lt _ _ _ _ (le_trans _ _ _ nltk1 k1lek2)),
	           (insert_at_lt _ _ _ _ (le_S _ _ (le_trans _ _ _ nltk1 k1lek2)));
	   exact (insert_at_lt _ _ _ _ nltk1).
	inversion ngek1; subst.
	1: rewrite insert_at_eq, (insert_at_lt _ _ _ _ (le_n_S _ _ k1lek2)); exact (insert_at_eq _ _ _).
	rewrite (insert_at_gt _ _ _ _ H).
	destruct (lt_ge_cases m k2) as [mltk2|mgek2].
	1: rewrite (insert_at_lt _ _ _ _ mltk2), (insert_at_lt _ _ _ _ (le_n_S _ _ mltk2)); exact (insert_at_gt _ _ _ _ H).
	inversion mgek2; subst.
	1: rewrite !insert_at_eq; exact eq_refl.
	rewrite (insert_at_gt _ _ _ _ H0), (insert_at_gt _ _ _ _ (le_n_S _ _ H0)); exact (insert_at_gt _ _ _ _ (le_trans _ _ _ k1lek2 H0)).
Qed.
Lemma insert_at_ext : forall {T} (R : relation T) f1 f2 k v1 v2,
	R v1 v2 -> (forall n, R (f1 n) (f2 n)) -> forall n, R (insert_at f1 k v1 n) (insert_at f2 k v2 n).
Proof using.
	intros T R f1 f2 k v1 v2 Rv Rf n.
	destruct (lt_ge_cases n k) as [nltk|klen].
	1: rewrite !(insert_at_lt _ _ _ _ nltk); exact (Rf _).
	inversion klen; subst.
	1: rewrite !insert_at_eq; exact Rv.
	rewrite !(insert_at_gt _ _ _ _ H); exact (Rf _).
Qed.

Fixpoint eval0 (u : bterm) (rho : V -> D) {struct u} :
	{ f : (nat -> D) -> D
	| (forall rhob1 rhob2, (forall n, dcpo_equiv (rhob1 n) (rhob2 n)) -> dcpo_equiv (f rhob1) (f rhob2))
	  /\ forall rhob k, scott_continuity (fun v => f (insert_at rhob k v)) }.
Proof using.
	destruct u as [x|n|u v|u].
	1: refine (exist _ (fun rhob => rho x) _).
	2: refine (exist _ (fun rhob => rhob n) _).
	3: refine (exist _ (fun rhob => proj1_sig (M.r (proj1_sig (eval0 u rho) rhob)) (proj1_sig (eval0 v rho) rhob)) _).
	4: unshelve refine (exist _ (fun rhob => M.i (exist _ _ (proj2 (proj2_sig (eval0 u rho)) rhob O))) _).
	1-4: split; [intros rhob1 rhob2 Hrhos|intros rhob k].
	- exact equiv_refl.
	- exact (scott_continuity_const _).
	- exact (Hrhos _).
	- destruct (lt_ge_cases n k) as [nltk|klen].
	  1: exact (scott_continuity_fun_ext (fun v => eq_ind _ _ equiv_refl _ (eq_sym (insert_at_lt rhob _ v _ nltk)))
	               (scott_continuity_const _)).
	  inversion klen; subst.
	  2: exact (scott_continuity_fun_ext (fun v => eq_ind _ _ equiv_refl _ (eq_sym (insert_at_gt rhob _ v _ H)))
	               (scott_continuity_const _)).
	  exact (scott_continuity_fun_ext (fun v => eq_ind _ _ equiv_refl _ (eq_sym (insert_at_eq rhob _ v))) scott_continuity_id).
	- refine (equiv_trans (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ (proj1 (proj2_sig (eval0 _ _)) _ _ Hrhos)) _).
	  exact (scott_continuity_is_wd _ M.Hr _ _ (proj1 (proj2_sig (eval0 _ _)) _ _ Hrhos) _).
	- refine (scott_continuity_appl2 (fun d => proj1_sig (M.r (proj1_sig (eval0 u rho) (insert_at rhob k d)))) _ _ _ _).
	  3: exact (proj2 (proj2_sig (eval0 _ _)) _ _).
	  2: intros x; exact (proj2_sig (M.r _)).
	  intros y; refine (scott_continuity_comp _ (scott_continuity_appl _ _ _)).
	  refine (scott_continuity_comp (proj2 (proj2_sig (eval0 _ _)) _ _) M.Hr).
	- refine (scott_continuity_is_wd _ M.Hi _ _ _); intros x.
	  refine (proj1 (proj2_sig (eval0 _ _)) _ _ (insert_at_ext _ _ _ _ _ _ equiv_refl Hrhos)).
	- refine (scott_continuity_comp _ M.Hi); apply scott_continuity_fun_iff; intros y; lazy beta delta [proj1_sig] iota.
	  refine (scott_continuity_fun_ext (f1:=fun x => proj1_sig (eval0 u rho) (insert_at (insert_at rhob O y) (S k) x)) _ _).
	  1: intros x; refine (proj1 (proj2_sig (eval0 _ _)) _ _ _); intros n;
	       rewrite (insert_at_comm rhob O y k x (le_0_n _) _); exact equiv_refl.
	  exact (proj2 (proj2_sig (eval0 _ _)) _ _).
Defined.

Definition eval u rho rhob := proj1_sig (eval0 u rho) rhob.
Lemma eval_def : forall u rho rhob, eval u rho rhob = match u with
	| BVar v => rho v
	| BBound n => rhob n
	| BApp u v => proj1_sig (M.r (eval u rho rhob)) (eval v rho rhob)
	| BAbs u => M.i (exist _ (fun v => eval u rho (fun n => match n with O => v | S n => rhob n end)) (proj2 (proj2_sig (eval0 u rho)) rhob O))
end.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH]; intros rho rhob.
	- exact eq_refl.
	- exact eq_refl.
	- exact eq_refl.
	- exact eq_refl.
Qed.
Opaque eval.

Lemma eval_ext : forall u rho1 rhob1 rho2 rhob2,
	(forall v, dcpo_equiv (rho1 v) (rho2 v)) -> (forall n, dcpo_equiv (rhob1 n) (rhob2 n)) ->
	dcpo_equiv (eval u rho1 rhob1) (eval u rho2 rhob2).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros rho1 rhob1 rho2 rhob2 Hv Hb.
	- rewrite eval_def, eval_def; exact (Hv _).
	- rewrite eval_def, eval_def; exact (Hb _).
	- rewrite !(eval_def (BApp _ _)).
	  refine (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ (IH1 _ _ _ _ Hv Hb) _) _).
	  exact (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ (IH2 _ _ _ _ Hv Hb)).
	- rewrite !(eval_def (BAbs _)).
	  refine (scott_continuity_is_wd _ M.Hi _ _ _); intros d; unfold proj1_sig.
	  refine (IH _ _ _ _ Hv _).
	  intros [|n]; [exact equiv_refl|exact (Hb _)].
Qed.
Lemma eval_incr : forall u n rho rhob v, dcpo_equiv (eval u rho rhob) (eval (incr_bound u n) rho (insert_at rhob n v)).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n rho rhob v.
	- unfold incr_bound; rewrite eval_def, eval_def; exact equiv_refl.
	- unfold incr_bound; rewrite eval_def, eval_def.
	  destruct (le_gt_cases n k) as [nlek|kltn].
	  1: rewrite (proj2 (leb_le _ _) nlek); rewrite (insert_at_gt _ _ _ _ nlek); exact equiv_refl.
	  rewrite (proj2 (leb_gt _ _) kltn); rewrite (insert_at_lt _ _ _ _ kltn); exact equiv_refl.
	- simpl incr_bound; rewrite !(eval_def (BApp _ _)).
	  refine (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ (IH1 n _ _ v) _) _).
	  exact (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ (IH2 _ _ _ _)).
	- simpl incr_bound; rewrite !(eval_def (BAbs _)).
	  refine (scott_continuity_is_wd _ M.Hi _ _ _); intros d; unfold proj1_sig.
	  exact (IH _ _ _ _).
Qed.

Lemma coherent_eval : forall u v rho rhob, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u rho rhob) (eval v rho rhob).
Proof using.
	intros u v rho rhob H; induction H as [u v H|u|u v _ IH|u v w _ IH1 _ IH2]; [|exact equiv_refl|exact (equiv_sym IH)|exact (equiv_trans IH1 IH2)].
	generalize dependent rhob; induction H as [u v H|u u' v H IH|u v v' H IH|u v H IH]; intros rhob.
	- inversion H as [u' v' eq1 eq2]; subst; rename u' into u, v' into v; clear H.
	  rewrite eval_def, eval_def; refine (equiv_trans (equiv_sym (M.r_i_id _ _ _)) _).
	  match goal with |- dcpo_equiv (eval _ _ ?r) _ => rewrite (eq_refl : r = insert_at rhob O (eval v rho rhob)) end.
	  generalize O; generalize dependent rhob; generalize dependent v; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros v rhob n.
	  + unfold bsubstb; rewrite eval_def, eval_def; exact equiv_refl.
	  + unfold bsubstb; rewrite eval_def, (eval_def (if _ <? _ then _ else _)).
	    destruct (lt_ge_cases k n) as [kltn|kgen].
	    1: rewrite (proj2 (ltb_lt _ _) kltn), (insert_at_lt _ _ _ _ kltn); exact equiv_refl.
	    rewrite (proj2 (ltb_ge _ _) kgen); inversion kgen; subst.
	    1: rewrite eqb_refl, insert_at_eq, <-eval_def; exact equiv_refl.
	    rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))), (insert_at_gt _ _ _ _ H); exact equiv_refl.
	  + simpl bsubstb; rewrite !(eval_def (BApp _ _)).
	    exact (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ (IH1 _ _ _) _) (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ (IH2 _ _ _))).
	  + simpl bsubstb; rewrite !(eval_def (BAbs _)).
	    refine (scott_continuity_is_wd _ M.Hi _ _ _); intros x; unfold proj1_sig.
	    refine (equiv_trans (proj1 (proj2_sig (eval0 _ _)) _ _ _) (IH (incr_bound v O) (insert_at rhob O x) (S n))).
	    intros [|k]; [exact equiv_refl|rewrite (insert_at_comm _ _ _ _ _ (le_0_n _) (S _) : _ = insert_at rhob n _ k)].
	    exact (insert_at_ext _ _ _ _ _ _ (eval_incr _ _ _ _ _) (fun _ => equiv_refl) _).
	- rewrite !(eval_def (BApp _ _)); exact (scott_continuity_is_wd _ M.Hr _ _ (IH _) _).
	- rewrite !(eval_def (BApp _ _)); exact (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ (IH _)).
	- rewrite !(eval_def (BAbs _)); refine (scott_continuity_is_wd _ M.Hi _ _ _); intros x; unfold proj1_sig.
	  exact (IH _).
Qed.

End EnvModelDcpo.

Module PomegaModel <: EnvModelDefs.
Module Reqs <: EnvModelDcpoReqs.
Definition D : Type := nat -> Prop.
Definition equiv : relation D := fun A B => forall x, A x <-> B x.
Definition Hd : Dcpo equiv := SetDcpo _.
#[local] Instance Hd' : Dcpo equiv := Hd.
Definition get_lub : (D -> Prop) -> D := lub_set.
Definition get_lub_wd : forall C, dcpo_is_lub C (get_lub C) := lub_set_is_lub.
Definition r : D -> { f : D -> D | scott_continuity f } := r.
Definition Hr : scott_continuity r := r_gbl_continuity.
Definition i : { f : D -> D | scott_continuity f } -> D := i.
Definition Hi : scott_continuity i := i_gbl_continuity.
Definition r_i_id : forall (f : D -> D) (Hf : scott_continuity f) x, dcpo_equiv (f x) (proj1_sig (r (i (exist _ f Hf))) x) := r_i_id.
End Reqs.
Include EnvModelDcpo(Reqs).

Lemma eval_id : forall rho rhob n,
	eval (BAbs (BBound O)) rho rhob n <-> In (code_pi2 n) (decode_finite_set (code_pi1 n)).
Proof using.
	intros rho rhob n.
	rewrite eval_def; unfold Reqs.i, i, proj1_sig, i0.
	rewrite eval_def; exact (iff_refl _).
Qed.
Lemma eval_id_eta : forall rho rhob n,
	eval (BAbs (BAbs (BApp (BBound (S O)) (BBound O)))) rho rhob n <->
	(exists l : list nat,
		(forall m, In m l -> In m (decode_finite_set (code_pi1 (code_pi2 n)))) /\
		In (code_pair (code_finite_set l) (code_pi2 (code_pi2 n))) (decode_finite_set (code_pi1 n))).
Proof using.
	intros rho rhob n.
	rewrite eval_def; unfold Reqs.i, i, proj1_sig, i0.
	rewrite eval_def; unfold Reqs.i, i, proj1_sig, i0.
	rewrite eval_def; unfold Reqs.r, r, proj1_sig, r0.
	rewrite eval_def, eval_def; unfold dcpo_le, SetDcpo.
	split.
	- intros [f [H1 [l [H2 H3]]]]; exists l; split; [exact (fun m Hm => H1 _ (proj2 (H2 _) Hm))|exact H3].
	- intros [l [H1 H2]]; exists (fun m => In m l); split; [exact H1|exists l; split; [intros m; exact (iff_refl _)|exact H2]].
Qed.
Lemma eval_id_neq_eta : forall rho rhob, exists n,
	~ eval (BAbs (BBound O)) rho rhob n /\ eval (BAbs (BAbs (BApp (BBound (S O)) (BBound O)))) rho rhob n.
Proof using.
	intros rho rhob.
	exists (code_pair (code_finite_set [code_pair (code_finite_set []) O]) (code_pair (code_finite_set [O]) O));
	  rewrite eval_id, eval_id_eta, !code_pi2_pair, !code_pi1_pair; split.
	2: exists []; split; [intros ? []|].
	1,2: rewrite <-decode_code_finite_set.
	1: intros [f|[]]; discriminate f.
	left; exact eq_refl.
Qed.
End PomegaModel.

End UntypedModels.

Require Import UntypedFelleisen.

Module UntypedModelsC (UntypedL : UntypedLambdaFT).
Module Export Vars := UntypedL.Vars.
Import UntypedL.

Module Type ModelDefs.
Parameter (D : Type) (eval : bterm -> D).
Parameter (equiv : relation D) (He : Equiv equiv).

Parameter coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u) (eval v).
End ModelDefs.

Module TrivialModel <: ModelDefs.
Definition D := unit.
Definition eval (_ : bterm) := tt.
Definition equiv := @eq D.
Definition He := eq_equiv D.
Lemma coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> eval u = eval v.
Proof using.
	intros u v _; unfold eval; exact eq_refl.
Qed.
End TrivialModel.

Module CorrectModel <: ModelDefs.
Definition D := bterm.
Definition eval (u : bterm) := u.
Definition equiv := clos_refl_sym_trans (over_bcontext beta).
#[local] Instance equiv_crst_beta : Equiv equiv := {
	equiv_refl := @rst_refl _ _;
	equiv_sym := @rst_sym _ _;
	equiv_trans := @rst_trans _ _;
}.
Definition He := equiv_crst_beta.
Lemma coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u) (eval v).
Proof using.
	intros u v H; exact H.
Qed.

Lemma non_trivial : exists u v, ~ equiv (eval u) (eval v).
Proof using.
	exists (BBound O), (BBound (S O)); unfold equiv; intros H.
	destruct (proj1 (proj1 (RewriteSystem.confluence_iff_church_rosser _ _) confluence_beta) _ _ (or_intror H))
	  as [OeqSO|H2]; clear H.
	1: discriminate OeqSO.
	destruct H2 as [u [H1 H2]].
	apply clos_rt_rt1n in H1; inversion H1; subst.
	2: inversion H; inversion H3.
	apply clos_rt_rt1n in H2; inversion H2; subst.
	inversion H; inversion H3.
Qed.
End CorrectModel.

Module Type EnvModelDefs.
Parameter (D : Type).
Parameter (equiv : relation D) (He : Equiv equiv) (Hd : Dcpo equiv).
#[local] Instance Hd' : Dcpo equiv := Hd.
Parameter (eval : bterm -> (V -> D) -> (nat -> D) -> { k : D -> D | scott_continuity k } -> D).

Parameter coherent_eval : forall {u v} [rho rhob kappa],
	clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u rho rhob kappa) (eval v rho rhob kappa).
End EnvModelDefs.

Module ToModelDefs(EM : EnvModelDefs) <: ModelDefs.
#[local] Instance Hd' : Dcpo EM.equiv := EM.Hd.
Definition D := (V -> EM.D) -> (nat -> EM.D) -> { k : EM.D -> EM.D | scott_continuity k } -> EM.D.
Definition eval := EM.eval.
Definition equiv : relation D := fun x y => forall rho rhob kappa, EM.equiv (x rho rhob kappa) (y rho rhob kappa).
#[local] Instance to_md_equiv : Equiv equiv := {
	equiv_refl := fun u rho rhob kappa => @equiv_refl _ _ EM.He _;
	equiv_sym := fun u v Huv rho rhob kappa => @equiv_sym _ _ EM.He _ _ (Huv rho rhob kappa);
	equiv_trans := fun u v w Huv Hvw rho rhob kappa => @equiv_trans _ _ EM.He _ _ _ (Huv rho rhob kappa) (Hvw rho rhob kappa);
}.
Definition He := to_md_equiv.
Lemma coherent_eval : forall u v, clos_refl_sym_trans (over_bcontext beta) u v -> equiv (eval u) (eval v).
Proof using.
	intros u v Huv rho rhob kappa; exact (EM.coherent_eval Huv).
Qed.
End ToModelDefs.

Module Type EnvModelDcpoReqs.
Parameter (D : Type) (equiv : relation D) (Hd : Dcpo equiv).
#[local] Instance Hd' : Dcpo equiv := Hd.
Parameter (bot : D) (bot_is_bot : forall d, dcpo_le bot d).
Parameter (get_lub : (D -> Prop) -> D) (get_lub_wd : forall C, dcpo_is_lub C (get_lub C)).
#[local] Instance FunD : Dcpo _ := FunDcpo (H1:=Hd) _ get_lub_wd.
#[local] Instance FunDD : Dcpo _ := FunDcpo (H1:=FunD) (H2:=FunD) _ (lub_fun_is_lub _ get_lub_wd).
Parameter r : D -> { f : { k : D -> D | scott_continuity k } -> { f : D -> D | scott_continuity f } | scott_continuity f }.
Parameter Hr : scott_continuity r.
Parameter i : { f : { k : D -> D | scott_continuity k } -> { f : D -> D | scott_continuity f } | scott_continuity f } -> D.
Parameter Hi : scott_continuity i.
Parameter r_i_id : forall f Hf k x, dcpo_equiv (proj1_sig (f k) x) (proj1_sig (proj1_sig (r (i (exist _ f Hf))) k) x).
End EnvModelDcpoReqs.

Module EnvModelDcpo (M : EnvModelDcpoReqs) <: EnvModelDefs.
Definition D := M.D.
Definition Hd := M.Hd.
Definition equiv := M.equiv.
#[local] Instance Hd' : Dcpo equiv := Hd.
Definition He : Equiv equiv := dcpo_He.

Fixpoint insert_at {T} (f : nat -> T) k v n := match k, n with
	| O, O => v
	| O, S n => f n
	| S k, O => f O
	| S k, S n => insert_at (fun n => f (S n)) k v n
end.
Lemma insert_at_lt : forall {T} f k v n, n < k -> @insert_at T f k v n = f n.
Proof using.
	intros T f k v n H.
	generalize dependent f; generalize dependent n; induction k as [|k IHk]; intros n nltk f; cbn.
	1: inversion nltk.
	destruct n as [|n]; [exact eq_refl|exact (IHk _ (le_S_n _ _ nltk) _)].
Qed.
Lemma insert_at_eq : forall {T} f k v, @insert_at T f k v k = v.
Proof using.
	intros T f k v.
	generalize dependent f; induction k as [|k IHk]; intros f; cbn.
	1: exact eq_refl.
	exact (IHk _).
Qed.
Lemma insert_at_gt : forall {T} f k v n, k <= n -> @insert_at T f k v (S n) = f n.
Proof using.
	intros T f k v n H.
	generalize dependent f; generalize dependent n; induction k as [|k IHk]; intros n klen f; cbn.
	1: exact eq_refl.
	destruct n as [|n]; [inversion klen|exact (IHk _ (le_S_n _ _ klen) _)].
Qed.
Lemma insert_at_comm : forall {T} f k1 v1 k2 v2, k1 <= k2 -> forall n,
	insert_at (@insert_at T f k1 v1) (S k2) v2 n = insert_at (insert_at f k2 v2) k1 v1 n.
Proof using.
	intros T f k1 v1 k2 v2 k1lek2 n.
	destruct (lt_ge_cases n k1) as [nltk1|ngek1].
	1: rewrite (insert_at_lt _ _ _ _ nltk1), (insert_at_lt _ _ _ _ (le_trans _ _ _ nltk1 k1lek2)),
	           (insert_at_lt _ _ _ _ (le_S _ _ (le_trans _ _ _ nltk1 k1lek2)));
	   exact (insert_at_lt _ _ _ _ nltk1).
	inversion ngek1; subst.
	1: rewrite insert_at_eq, (insert_at_lt _ _ _ _ (le_n_S _ _ k1lek2)); exact (insert_at_eq _ _ _).
	rewrite (insert_at_gt _ _ _ _ H).
	destruct (lt_ge_cases m k2) as [mltk2|mgek2].
	1: rewrite (insert_at_lt _ _ _ _ mltk2), (insert_at_lt _ _ _ _ (le_n_S _ _ mltk2)); exact (insert_at_gt _ _ _ _ H).
	inversion mgek2; subst.
	1: rewrite !insert_at_eq; exact eq_refl.
	rewrite (insert_at_gt _ _ _ _ H0), (insert_at_gt _ _ _ _ (le_n_S _ _ H0)); exact (insert_at_gt _ _ _ _ (le_trans _ _ _ k1lek2 H0)).
Qed.
Lemma insert_at_ext : forall {T} (R : relation T) f1 f2 k v1 v2,
	R v1 v2 -> (forall n, R (f1 n) (f2 n)) -> forall n, R (insert_at f1 k v1 n) (insert_at f2 k v2 n).
Proof using.
	intros T R f1 f2 k v1 v2 Rv Rf n.
	destruct (lt_ge_cases n k) as [nltk|klen].
	1: rewrite !(insert_at_lt _ _ _ _ nltk); exact (Rf _).
	inversion klen; subst.
	1: rewrite !insert_at_eq; exact Rv.
	rewrite !(insert_at_gt _ _ _ _ H); exact (Rf _).
Qed.

Lemma evalC_wd : scott_continuity (H1:=M.FunD) (H2:=M.FunD)
	             (fun k' => exist _ _
	                (scott_continuity_comp M.Hr
	                   (scott_continuity_comp
	                      (scott_continuity_appl _ (lub_fun_is_lub _ M.get_lub_wd) (exist _ _ (scott_continuity_const M.bot)))
	                      (scott_continuity_appl _ M.get_lub_wd (M.i (exist _ _ (scott_continuity_const k'))))))).
Proof using.
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros k'; cbn.
	refine (scott_continuity_comp _ (proj2_sig (proj1_sig (M.r _) _))).
	refine (scott_continuity_comp _ M.Hi).
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros x; exact scott_continuity_id.
Qed.
Lemma eval_app_wd1 :
	forall (peval : { f : { k : D -> D | scott_continuity k } -> D | scott_continuity (H1:=M.FunD) (H2:=M.Hd) f }) k,
	scott_continuity (fun f => proj1_sig peval (exist _ _ (proj2_sig (proj1_sig (M.r f) k)))).
Proof using.
	intros e k.
	refine (scott_continuity_comp (f1:=fun f => exist _ _ (proj2_sig (proj1_sig (M.r f) k))) _ (proj2_sig e)).
	exact (scott_continuity_comp M.Hr (scott_continuity_appl _ _ k)).
Qed.
Lemma eval_app_wd2 :
	forall (peval1 peval2 : { f : { k : D -> D | scott_continuity k } -> D | scott_continuity (H1:=M.FunD) (H2:=M.Hd) f }),
	scott_continuity (H1:=M.FunD) (H2:=M.Hd)
		(fun k => proj1_sig peval1 (exist _ _ (eval_app_wd1 peval2 k))).
Proof using.
	intros peval1 peval2.
	refine (scott_continuity_comp _ (proj2_sig peval1)).
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros k'; cbn.
	refine (scott_continuity_comp _ (proj2_sig peval2)).
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros x; cbn.
	refine (scott_continuity_appl2 (fun v w => proj1_sig w x) _
	          (fun _ => scott_continuity_const _)
	          (fun _ => scott_continuity_appl _ _ _)
	          (proj2_sig (M.r _))).
Qed.
Lemma eval_abs_wd :
	forall (peval :
		{ f : (nat -> D) -> { f : { k : D -> D | scott_continuity k } -> D | scott_continuity (H1:=M.FunD) (H2:=M.Hd) f }
		| (forall rhob1 rhob2 k, (forall n, dcpo_equiv (rhob1 n) (rhob2 n)) -> dcpo_equiv (proj1_sig (f rhob1) k) (proj1_sig (f rhob2) k))
		  /\ forall rhob k kappa, scott_continuity (fun v => proj1_sig (f (insert_at rhob k v)) kappa) }) rhob,
	scott_continuity (H1:=M.FunD) (H2:=M.FunD) (fun k => exist _ _ (proj2 (proj2_sig peval) rhob 0 k)).
Proof using.
	intros peval rhob.
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros k'; cbn.
	exact (proj2_sig (proj1_sig peval _)).
Qed.

Fixpoint eval0 (u : bterm) (rho : V -> D) {struct u} :
	{ f : (nat -> D) -> { f : { k : D -> D | scott_continuity k } -> D | scott_continuity (H1:=M.FunD) (H2:=M.Hd) f }
	| (forall rhob1 rhob2 k, (forall n, dcpo_equiv (rhob1 n) (rhob2 n)) -> dcpo_equiv (proj1_sig (f rhob1) k) (proj1_sig (f rhob2) k))
	  /\ forall rhob k kappa, scott_continuity (fun v => proj1_sig (f (insert_at rhob k v)) kappa) }.
Proof using.
	destruct u as [|x|n|u v|u].
	1: refine (exist _ (fun rhob => exist _ _ (scott_continuity_appl _ _ (M.i (exist _ _ evalC_wd)))) _).
	2: refine (exist _ (fun rhob => exist _ _ (scott_continuity_appl _ _ (rho x))) _).
	3: refine (exist _ (fun rhob => exist _ _ (scott_continuity_appl _ _ (rhob n))) _).
	4: refine (exist _ (fun rhob => exist _ _ (eval_app_wd2 (proj1_sig (eval0 u rho) rhob) (proj1_sig (eval0 v rho) rhob))) _).
	5: refine (exist _ (fun rhob => exist _ _ (scott_continuity_appl _ _ (M.i (exist _ _ (eval_abs_wd (eval0 u rho) rhob))))) _).
	1-5: split; [intros rhob1 rhob2 kappa Hrhos|intros rhob k kappa].
	- refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ _).
	  refine (scott_continuity_is_wd _ M.Hi _ _ _); intros f x; cbn.
	  refine (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ _).
	  refine (scott_continuity_is_wd _ M.Hi _ _ _); intros g y; exact equiv_refl.
	- exact (scott_continuity_const _).
	- exact equiv_refl.
	- exact (scott_continuity_const _).
	- exact (scott_continuity_is_wd _ (proj2_sig kappa) _ _ (Hrhos _)).
	- refine (scott_continuity_comp _ (proj2_sig kappa)).
	  destruct (lt_ge_cases n k) as [nltk|klen].
	  1: exact (scott_continuity_fun_ext (fun v => eq_ind _ _ equiv_refl _ (eq_sym (insert_at_lt rhob _ v _ nltk)))
	               (scott_continuity_const _)).
	  inversion klen; subst.
	  2: exact (scott_continuity_fun_ext (fun v => eq_ind _ _ equiv_refl _ (eq_sym (insert_at_gt rhob _ v _ H)))
	               (scott_continuity_const _)).
	  exact (scott_continuity_fun_ext (fun v => eq_ind _ _ equiv_refl _ (eq_sym (insert_at_eq rhob _ v))) scott_continuity_id).
	- refine (equiv_trans (proj1 (proj2_sig (eval0 _ _)) _ _ _ Hrhos)
	            (scott_continuity_is_wd _ (proj2_sig (proj1_sig (eval0 _ _) _)) _ _ _)).
	  intros x; cbn.
	  exact (proj1 (proj2_sig (eval0 _ _)) _ _ _ Hrhos).
	- refine (scott_continuity_appl2 (fun v => proj1_sig (proj1_sig (eval0 u rho) (insert_at rhob k v))) _ _ _ _).
	  1: intros k'; exact (proj2 (proj2_sig (eval0 _ _)) _ _ _).
	  1: intros x; exact (proj2_sig (proj1_sig (eval0 _ _) _)).
	  apply scott_continuity_fun_iff; intros y; exact (proj2 (proj2_sig (eval0 _ _)) _ _ _).
	- refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ (scott_continuity_is_wd _ M.Hi _ _ _)); intros k' x.
	  refine (proj1 (proj2_sig (eval0 _ _)) _ _ _ (insert_at_ext _ _ _ _ _ _ equiv_refl Hrhos)).
	- refine (scott_continuity_comp (scott_continuity_comp _ M.Hi) (proj2_sig kappa)).
	  apply scott_continuity_fun_iff; intros k'; lazy beta delta [proj1_sig] iota.
	  apply scott_continuity_fun_iff; intros y; lazy beta delta [proj1_sig] iota.
	  refine (scott_continuity_fun_ext (f1:=fun x => proj1_sig (proj1_sig (eval0 u rho) (insert_at (insert_at rhob O y) (S k) x)) k') _ _).
	  1: intros x; refine (proj1 (proj2_sig (eval0 _ _)) _ _ _ _); intros n;
	       rewrite (insert_at_comm rhob O y k x (le_0_n _) _); exact equiv_refl.
	  exact (proj2 (proj2_sig (eval0 _ _)) _ _ _).
Defined.

Definition eval u rho rhob kappa := proj1_sig (proj1_sig (eval0 u rho) rhob) kappa.
Lemma eval_def : forall u rho rhob kappa, eval u rho rhob kappa = match u with
	| BCFelleisen => proj1_sig kappa (M.i (exist _ _ evalC_wd))
	| BVar v => proj1_sig kappa (rho v)
	| BBound n => proj1_sig kappa (rhob n)
	| BApp u v => eval u rho rhob (exist _ _ (eval_app_wd1 (proj1_sig (eval0 v rho) rhob) kappa))
	| BAbs u => proj1_sig kappa (M.i (exist _ _ (eval_abs_wd (eval0 u rho) rhob)))
end.
Proof using.
	intros [|x|n|u v|u]; intros rho rhob kappa; exact eq_refl.
Qed.
Opaque eval0 eval.

Lemma eval_ext : forall u rho1 rhob1 kappa1 rho2 rhob2 kappa2,
	(forall v, dcpo_equiv (rho1 v) (rho2 v)) -> (forall n, dcpo_equiv (rhob1 n) (rhob2 n)) ->
	(forall v1 v2, dcpo_equiv v1 v2 -> dcpo_equiv (proj1_sig kappa1 v1) (proj1_sig kappa2 v2)) ->
	dcpo_equiv (eval u rho1 rhob1 kappa1) (eval u rho2 rhob2 kappa2).
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros rho1 rhob1 kappa1 rho2 rhob2 kappa2 Hv Hb Hk.
	- rewrite eval_def, eval_def; exact (Hk _ _ equiv_refl).
	- rewrite eval_def, eval_def; exact (Hk _ _ (Hv _)).
	- rewrite eval_def, eval_def; exact (Hk _ _ (Hb _)).
	- rewrite !(eval_def (BApp _ _)).
	  refine (IH1 _ _ _ _ _ _ Hv Hb _).
	  cbn; intros v1 v2 v1eqv2; refine (IH2 _ _ _ _ _ _ Hv Hb _); intros v3 v4 v3eqv4; cbn.
	  refine (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ v1eqv2 _ _) _).
	  refine (equiv_trans (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ (fun x => Hk x x equiv_refl) _) _).
	  exact (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ v3eqv4).
	- rewrite !(eval_def (BAbs _)).
	  refine (Hk _ _ _).
	  refine (scott_continuity_is_wd _ M.Hi _ _ _); intros f d; unfold proj1_sig.
	  refine (IH _ _ _ _ _ _ Hv _ (fun v1 v2 v1eqv2 => scott_continuity_is_wd _ (proj2_sig f) _ _ v1eqv2)).
	  intros [|n]; [exact equiv_refl|exact (Hb _)].
Qed.
Lemma eval_incr : forall u n rho rhob v kappa, dcpo_equiv (eval u rho rhob kappa) (eval (incr_bound u n) rho (insert_at rhob n v) kappa).
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros n rho rhob v kappa.
	- unfold incr_bound; rewrite eval_def, eval_def; exact equiv_refl.
	- unfold incr_bound; rewrite eval_def, eval_def; exact equiv_refl.
	- unfold incr_bound; rewrite eval_def, eval_def.
	  destruct (le_gt_cases n k) as [nlek|kltn].
	  1: rewrite (proj2 (leb_le _ _) nlek); rewrite (insert_at_gt _ _ _ _ nlek); exact equiv_refl.
	  rewrite (proj2 (leb_gt _ _) kltn); rewrite (insert_at_lt _ _ _ _ kltn); exact equiv_refl.
	- simpl incr_bound; rewrite !(eval_def (BApp _ _)).
	  refine (equiv_trans (IH1 n _ _ v _) (scott_continuity_is_wd _ (proj2_sig (proj1_sig (eval0 _ _) _)) _ _ _)).
	  intros f; cbn.
	  exact (IH2 _ _ _ _ _).
	- simpl incr_bound; rewrite !(eval_def (BAbs _)).
	  refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ (scott_continuity_is_wd _ M.Hi _ _ _)); intros [f Hf] d.
	  rewrite !(eq_refl : proj1_sig (proj1_sig (exist _ (fun k => exist _ (fun v0 => proj1_sig _ _) _) _) _) _ = eval _ _ _ _).
	  refine (equiv_trans (IH (S n) _ _ v _) _).
	  refine (eval_ext _ _ _ (exist _ f Hf) _ _ (exist _ f Hf) (fun _ => equiv_refl) _ (scott_continuity_is_wd _ Hf)).
	  intros k; rewrite (insert_at_comm _ _ _ _ _ (le_0_n _) _); exact equiv_refl.
Qed.

Lemma eval_app_C : forall u rho rhob kappa, dcpo_equiv (eval (BApp BCFelleisen u) rho rhob kappa) (eval u rho rhob (exist _ _
	                (scott_continuity_comp M.Hr
	                   (scott_continuity_comp
	                      (scott_continuity_appl _ (lub_fun_is_lub _ M.get_lub_wd) (exist _ _ (scott_continuity_const M.bot)))
	                      (scott_continuity_appl _ M.get_lub_wd (M.i (exist _ _ (scott_continuity_const kappa)))))))).
Proof using.
	intros u rho rhob kappa.
	rewrite eval_def, eval_def, (eq_refl : proj1_sig (exist _ (fun f => proj1_sig (proj1_sig _ _) _) _) _ = eval _ _ _ _).
	assert (tmp : forall x : sig scott_continuity, exist (fun f : D -> D => scott_continuity f) (proj1_sig x) (proj2_sig x) = x)
	  by (intros [x H]; exact eq_refl); rewrite !tmp; clear tmp.
	refine (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _).
	cbn; intros v1 v2 v1eqv2.
	refine (equiv_trans (equiv_sym (M.r_i_id _ _ _ _)) _); cbn.
	exact (scott_continuity_is_wd _ M.Hr _ _ v1eqv2 _ _).
Qed.

Lemma eval_normal_ret : forall u rho rhob d, (forall kappa, dcpo_equiv (eval u rho rhob kappa) (proj1_sig kappa d)) ->
	forall kappa, dcpo_equiv (eval (BApp BCFelleisen (BAbs (incr_bound u O))) rho rhob kappa) M.bot.
Proof using.
	intros u rho rhob d Hu k; refine (equiv_trans (eval_app_C _ _ _ _) _).
	rewrite eval_def; rewrite (eq_refl : proj1_sig (exist _ (fun x => _) _) _ = proj1_sig (proj1_sig _ _) _).
	refine (equiv_trans (equiv_sym (M.r_i_id _ _ _ _)) _).
	rewrite (eq_refl : proj1_sig (exist _ (fun x => proj1_sig (proj1_sig (eval0 _ _) _) _) _) _ = eval _ _ _ _).
	refine (equiv_trans (equiv_sym (eval_incr _ _ _ _ _ _)) _).
	exact (Hu _).
Qed.

Lemma eval_beta_redex : forall u v rho rhob kappa,
	dcpo_equiv (eval (BApp (BAbs u) v) rho rhob kappa)
	           (eval v rho rhob (exist _ (fun d => eval u rho (insert_at rhob O d) kappa) (proj2 (proj2_sig (eval0 u rho)) rhob 0 kappa))).
Proof using.
	intros u v rho rhob kappa; rewrite eval_def, eval_def; cbn; rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	refine (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _).
	intros v1 v2 v1eqv2; cbn.
	refine (equiv_trans (equiv_sym (M.r_i_id _ _ _ _)) _); cbn; rewrite !(eq_refl : proj1_sig _ _ = eval _ _ _ _).
	refine (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) _ (scott_continuity_is_wd _ (proj2_sig kappa))).
	intros [|n]; [exact v1eqv2|exact equiv_refl].
Qed.

Lemma eval_pvalue :
	forall u, Pvalue u -> forall rho rhob, exists d, forall kappa, eval u rho rhob kappa = proj1_sig kappa d.
Proof using.
	intros u H; inversion H as [v|n|u']; subst; [| |rename u' into u]; clear H; intros rho rhob.
	1: exists (rho v).
	2: exists (rhob n).
	3: eexists.
	1-3: intros kappa; rewrite eval_def; exact eq_refl.
Qed.

Lemma coherent_eval : forall u v rho rhob kappa, clos_refl_sym_trans (over_bcontext beta) u v ->
	equiv (eval u rho rhob kappa) (eval v rho rhob kappa).
Proof using.
	intros u v rho rhob kappa H; induction H as [u v H|u|u v _ IH|u v w _ IH1 _ IH2]; [|exact equiv_refl|exact (equiv_sym IH)|exact (equiv_trans IH1 IH2)].
	generalize dependent kappa; generalize dependent rhob; induction H as [u v H|u u' v H IH|u v v' H IH|u v H IH]; intros rhob kappa.
	- inversion H as [u' v' H' eq1 eq2|u' v' eq1 eq2|u' v' H' eq1 eq2]; subst; rename u' into u, v' into v; clear H.
	  + refine (equiv_trans (eval_beta_redex _ _ _ _ _) _).
	    specialize (eval_pvalue _ H' rho rhob) as [d Hd']; clear H'; rewrite Hd'; unfold proj1_sig.
	    assert (Hd : forall kappa, dcpo_equiv (eval v rho rhob kappa) (proj1_sig kappa d))
	      by (intros k; rewrite Hd'; exact equiv_refl); clear Hd'.
	    generalize O; generalize dependent kappa; generalize dependent rhob; generalize dependent v;
	      induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros v rhob Hd kappa n.
	    * rewrite !(eval_def BCFelleisen); exact equiv_refl.
	    * rewrite !(eval_def (BVar _)); exact equiv_refl.
	    * unfold bsubstb.
	      destruct (lt_ge_cases k n) as [kltn|kgen].
	      1: rewrite (proj2 (ltb_lt _ _) kltn), !eval_def, (insert_at_lt _ _ _ _ kltn); exact equiv_refl.
	      rewrite (proj2 (ltb_ge _ _) kgen); inversion kgen; subst.
	      2: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))), !eval_def, (insert_at_gt _ _ _ _ H); exact equiv_refl.
	      rewrite eqb_refl, eval_def, insert_at_eq; exact (equiv_sym (Hd _)).
	    * simpl bsubstb; rewrite !(eval_def (BApp _ _)).
	      refine (equiv_trans (IH1 _ _ Hd _ _) (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _)).
	      intros v1 v2 v1eqv2; cbn.
	      refine (equiv_trans (IH2 _ _ Hd _ _) (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _)).
	      intros v3 v4 v3eqv4; cbn.
	      exact (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ v1eqv2 _ _) (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ v3eqv4)).
	    * simpl bsubstb; rewrite !(eval_def (BAbs _)).
	      refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ (scott_continuity_is_wd _ M.Hi _ _ _)).
	      intros [f Hf] x; unfold proj1_sig; rewrite !(eq_refl : (let (a, _) := (let (a, _) := eval0 _ _ in a) _ in a) _ = eval _ _ _ _).
	      refine (equiv_trans _ (IH _ _ _ _ _)).
	      2: intros k'; refine (equiv_trans (equiv_sym (eval_incr _ _ _ _ _ _)) (Hd _)).
	      refine (eval_ext _ _ _ (exist _ f Hf) _ _ (exist _ f Hf) (fun _ => equiv_refl) _ (scott_continuity_is_wd _ Hf)).
	      intros k; rewrite (insert_at_comm _ _ _ _ _ (le_0_n _) _); exact equiv_refl.
	  + rewrite eval_def.
	    refine (equiv_trans (eval_app_C _ _ _ _) (equiv_trans _ (equiv_sym (eval_app_C _ _ _ _)))).
	    rewrite (eval_def (BAbs _)).
	    refine (equiv_trans _ (M.r_i_id _ _ _ _)); cbn.
	    rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BApp _ _)); refine (equiv_trans _ (eval_incr _ _ _ _ _ _)).
	    refine (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _); intros v1 v2 v1eqv2; cbn.
	    rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BAbs _)); cbn.
	    refine (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ v1eqv2 _ _)
	              (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ (scott_continuity_is_wd _ M.Hi _ _ _)));
	      clear v1 v2 v1eqv2.
	    intros f d; cbn.
	    rewrite !(eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BApp _ _)), (eval_def (BBound _)); cbn; rewrite !(eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BApp _ _)), (eval_def (BBound _)); cbn; rewrite !(eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    refine (equiv_trans (eval_incr _ O _ _ _ _)
	             (equiv_trans (eval_incr _ O _ _ _ _)
	               (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _))); cbn.
	    intros v1 v2 Hv; refine (equiv_trans (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ Hv) _); clear u v v1 Hv.
	    refine (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ _ _); intros x; clear v2.
	    exact (M.r_i_id _ _ _ _).
	  + refine (equiv_trans _ (equiv_sym (eval_app_C _ _ _ _))).
	    rewrite (eval_def (BApp _ _)), (eval_def (BAbs _)); cbn; refine (equiv_trans _ (M.r_i_id _ _ _ _)); cbn.
	    specialize (eval_pvalue _ H' rho rhob) as [d Hd']; clear H'; rewrite Hd'; cbn.
	    rewrite !(eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    refine (equiv_trans (eval_app_C _ _ _ _) _).
	    rewrite (eval_def (BApp _ _)); refine (equiv_trans _ (eval_incr _ _ _ _ _ _)).
	    refine (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _); intros v1 v2 Hv; cbn.
	    assert (tmp : forall v : sig (fun f : D -> D => scott_continuity f), exist _ (proj1_sig v) (proj2_sig v) = v)
	      by (intros [? ?]; exact eq_refl); rewrite !tmp; clear tmp.
	    rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BAbs _)).
	    refine (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ Hv _ _) (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ _));
	      clear v1 v2 Hv.
	    refine (scott_continuity_is_wd _ M.Hi _ _ _); intros f x; cbn.
	    rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BApp _ _)), (eval_def (BBound _)); cbn.
	    rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BApp _ _)); refine (equiv_trans (equiv_trans _ (eval_incr _ _ _ _ _ _)) (eval_incr _ _ _ _ _ _)).
	    rewrite Hd'; cbn.
	    rewrite (eq_refl : proj1_sig _ _ = eval _ _ _ _).
	    rewrite (eval_def (BBound _)); cbn.
	    refine (scott_continuity_is_wd _ (proj2_sig (M.r _)) _ _ _ _); intros y; cbn.
	    destruct kappa as [k Hk]; exact (M.r_i_id _ _ _ _).
	- rewrite !(eval_def (BApp _ _)); exact (IH _ _).
	- rewrite !(eval_def (BApp _ _)); refine (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _).
	  intros v1 v2 Hv; refine (equiv_trans (eval_ext _ _ _ _ _ _ _ (fun _ => equiv_refl) (fun _ => equiv_refl) _) (IH _ _)).
	  intros v3 v4 Hv2; exact (equiv_trans (scott_continuity_is_wd _ M.Hr _ _ Hv _ _)
	                                       (scott_continuity_is_wd _ (proj2_sig (proj1_sig (M.r _) _)) _ _ Hv2)).
	- rewrite !(eval_def (BAbs _)); refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ (scott_continuity_is_wd _ M.Hi _ _ _));
	    intros x d; cbn.
	  exact (IH _ _).
Qed.

End EnvModelDcpo.

Module PomegaModel <: EnvModelDefs.
Module Reqs <: EnvModelDcpoReqs.
Definition D : Type := nat -> Prop.
Definition equiv : relation D := fun A B => forall x, A x <-> B x.
Definition Hd : Dcpo equiv := SetDcpo _.
#[local] Instance Hd' : Dcpo equiv := Hd.
Definition get_lub : (D -> Prop) -> D := lub_set.
Definition get_lub_wd : forall C, dcpo_is_lub C (get_lub C) := lub_set_is_lub.
#[local] Instance FunD : Dcpo _ := FunDcpo (H1:=Hd) _ get_lub_wd.
#[local] Instance FunDD : Dcpo _ := FunDcpo (H1:=FunD) (H2:=FunD) _ (lub_fun_is_lub _ get_lub_wd).
Definition r : D -> { f : { f : D -> D | scott_continuity f } -> { f : D -> D | scott_continuity f } | scott_continuity f }.
Proof using.
	intros d.
	specialize (r d : sig (fun f : D -> D => scott_continuity f)) as rd.
	unshelve refine (exist _ (fun k : sig (fun f : D -> D => scott_continuity f) => r (proj1_sig rd (i k))) _).
	exact (scott_continuity_comp (scott_continuity_comp i_gbl_continuity (proj2_sig rd)) r_gbl_continuity).
Defined.
Definition Hr : scott_continuity r.
Proof using.
	unfold r; refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros k; cbn.
	refine (scott_continuity_comp _ r_gbl_continuity).
	exact (scott_continuity_comp r_gbl_continuity (scott_continuity_appl _ _ _)).
Qed.
Definition i : { f : { f : D -> D | scott_continuity f } -> { f : D -> D | scott_continuity f } | scott_continuity f } -> D.
Proof using.
	intros f; refine (Dcpo.i (exist _ (fun k => Dcpo.i (proj1_sig f (Dcpo.r k))) _)).
	refine (scott_continuity_comp (scott_continuity_comp r_gbl_continuity (proj2_sig f)) i_gbl_continuity).
Defined.
Definition Hi : scott_continuity i.
Proof using.
	refine (scott_continuity_comp _ i_gbl_continuity).
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros k; cbn.
	exact (scott_continuity_comp (scott_continuity_appl _ _ _) i_gbl_continuity).
Qed.
Lemma r_i_id : forall f Hf k x, dcpo_equiv (proj1_sig (f k) x) (proj1_sig (proj1_sig (r (i (exist _ f Hf))) k) x).
Proof using.
	intros f Hf k x; unfold r, i; cbn.
	refine (equiv_trans _ (scott_continuity_is_wd _ r_gbl_continuity _ _ (r_i_id _ _ _) _)).
	refine (equiv_trans _ (r_i_id _ (proj2_sig (f _)) _)).
	exact (scott_continuity_is_wd _ Hf _ _ (fun _ => r_i_id _ (proj2_sig k) _) _).
Qed.
Definition bot : D := fun _ => False.
Lemma bot_is_bot : forall A, dcpo_le bot A.
Proof using.
	intros A n [].
Qed.
End Reqs.
Include EnvModelDcpo(Reqs).

Lemma eval_id : forall rho rhob kappa,
	dcpo_equiv (eval (BAbs (BBound O)) rho rhob kappa)
		(proj1_sig kappa (fun mn =>
			exists l, (forall m, In m l -> In m (decode_finite_set (code_pi1 (code_pi2 mn))))
			       /\ In (code_pair (code_finite_set l) (code_pi2 (code_pi2 mn))) (decode_finite_set (code_pi1 mn)))).
Proof using.
	intros rho rhob kappa.
	rewrite eval_def; refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ _).
	refine (equiv_trans (y:=Reqs.i (exist _ _ scott_continuity_id)) _ _).
	1: refine (scott_continuity_is_wd _ Reqs.Hi _ _ _); intros k' d; unfold proj1_sig.
	1: rewrite (eq_refl : (let (a, _) := (let (a, _) := eval0 _ _ in a) _ in a) _ = eval _ _ _ _).
	1: rewrite eval_def, insert_at_eq; exact equiv_refl.
	unfold Reqs.i, i, i0, r, r0, proj1_sig; intros mn; split.
	1: intros [y [yle [l [leq lmnin]]]]; refine (ex_intro _ _ (conj (fun m min => yle _ (proj2 (leq _) min)) lmnin)).
	intros [l [lle lmnin]]; refine (ex_intro _ _ (conj lle (ex_intro _ _ (conj (fun _ => iff_refl _) lmnin)))).
Qed.
Lemma eval_id_eta_wd : scott_continuity (fun k' : @sig (Reqs.D -> Reqs.D) scott_continuity =>
	exist _ (fun f => proj1_sig k' (Reqs.i (Reqs.r f))) (scott_continuity_comp (scott_continuity_comp Reqs.Hr Reqs.Hi) (proj2_sig k'))).
Proof using.
	refine (proj2 (scott_continuity_fun_iff _ _ _) _); intros k'0; cbn.
	exact (scott_continuity_appl _ _ _).
Qed.
Lemma eval_id_eta : forall rho rhob kappa,
	dcpo_equiv
		(eval (BAbs (BAbs (BApp (BBound (S O)) (BBound O)))) rho rhob kappa)
		(proj1_sig kappa (fun mn : nat =>
			exists l1,
				In (code_pair (code_finite_set l1) (code_pi2 (code_pi2 mn))) (decode_finite_set (code_pi1 mn)) /\
				forall x,
					In x l1 ->
					exists l2,
						(forall x0, In x0 l2 -> In x0 (decode_finite_set (code_pi1 (code_pi2 x)))) /\
						exists l3,
							In (code_pair (code_finite_set l3) (code_pair (code_finite_set l2) (code_pi2 (code_pi2 x)))) (decode_finite_set (code_pi1 (code_pi2 mn))) /\
							forall x0,
								In x0 l3 ->
								exists l4,
									In (code_pair (code_finite_set l4) (code_pi2 x0)) (decode_finite_set (code_pi1 x)) /\
									forall x1, In x1 l4 -> In x1 (decode_finite_set (code_pi1 x0)))).
Proof using.
	intros rho rhob kappa.
	rewrite eval_def; refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ _); clear kappa.
	refine (equiv_trans (y:=Reqs.i (exist _ _ eval_id_eta_wd)) (scott_continuity_is_wd _ Reqs.Hi _ _ _) _); [intros kappa f; unfold proj1_sig|].
	1: rewrite (eq_refl : (let (a, _) := (let (a, _) := eval0 _ _ in a) _ in a) _ = eval _ _ _ _).
	1: rewrite eval_def; refine (scott_continuity_is_wd _ (proj2_sig kappa) _ _ _); clear kappa.
	1: refine (scott_continuity_is_wd _ Reqs.Hi _ _ _); intros kappa d; unfold proj1_sig.
	1: rewrite (eq_refl : (let (a, _) := (let (a, _) := eval0 _ _ in a) _ in a) _ = eval _ _ _ _).
	1: rewrite eval_def, eval_def; unfold proj1_sig.
	1: rewrite (eq_refl : (let (a, _) := (let (a, _) := eval0 _ _ in a) _ in a) _ = eval _ _ _ _).
	1: rewrite eval_def, (insert_at_gt _ _ _ _ (le_n _)), !insert_at_eq.
	1: exact equiv_refl.
	intros mn; unfold Reqs.i, Reqs.r, i, i0, r, r0, proj1_sig; split.
	- intros [y1 [y1le [l1 [y1eq lmnin]]]].
	  refine (ex_intro _ _ (conj lmnin _)); intros n1 n1in.
	  specialize (y1le _ (proj2 (y1eq _) n1in)) as [y2 [y2le [l2 [y2eq [y3 [y3le [l3 [y3eq l3l2n1in]]]]]]]].
	  refine (ex_intro _ _ (conj (fun n nin => y2le _ (proj2 (y2eq _) nin)) (ex_intro _ _ (conj l3l2n1in _)))).
	  intros n2 n2in; specialize (y3le _ (proj2 (y3eq _) n2in)) as [y4 [y4le [l4 [y4eq ln2in]]]].
	  exact (ex_intro _ _ (conj ln2in (fun n nin => y4le _ (proj2 (y4eq _) nin)))).
	- intros [l1 [in1 H]].
	  refine (ex_intro _ _ (conj _ (ex_intro _ _ (conj (fun _ => iff_refl _) in1)))); intros n1 in2.
	  specialize (H _ in2) as [l2 [l2le [l3 [in3 H]]]].
	  refine (ex_intro _ _ (conj l2le (ex_intro _ _
	            (conj (fun _ => iff_refl _) (ex_intro _ _ (conj _ (ex_intro _ _ (conj (fun _ => iff_refl _) in3)))))))).
	  intros n2 in4; specialize (H _ in4) as [l4 [in5 l4le]].
	  exact (ex_intro _ _ (conj l4le (ex_intro _ _ (conj (fun _ => iff_refl _) in5)))).
Qed.
Lemma eval_id_neq_eta : forall rho rhob, exists n,
	~ eval (BAbs (BBound O)) rho rhob (exist _ _ scott_continuity_id) n /\
	eval (BAbs (BAbs (BApp (BBound (S O)) (BBound O)))) rho rhob (exist _ _ scott_continuity_id) n.
Proof using.
	intros rho rhob.
	pose (n := code_pair
	             (code_finite_set [code_pair (code_finite_set [S (S O)]) (code_pair (code_finite_set [])
	               (code_pi2 (code_pi2 (code_pair (code_finite_set [code_pair (code_finite_set []) (code_pi2 (S (S O)))]) O))))])
	             O).
	exists (code_pair (code_finite_set [code_pair (code_finite_set [(code_pair (code_finite_set [code_pair (code_finite_set []) (code_pi2 (S (S O)))]) O)])
	                                       (code_pi2 n)]) n).
	rewrite (eval_id _ _ _ _), (eval_id_eta _ _ _ _); unfold proj1_sig.
	rewrite code_pi2_pair, code_pi1_pair; split.
	+ intros [l [lle Hin]].
	  rewrite <-decode_code_finite_set in Hin; destruct Hin as [Hin|[]].
	  apply (f_equal code_pi1) in Hin; rewrite !code_pi1_pair in Hin.
	  specialize (lle (code_pair (code_finite_set [code_pair (code_finite_set []) (code_pi2 (S (S O)))]) O)); rewrite decode_code_finite_set, Hin, <-decode_code_finite_set in lle.
	  specialize (lle (or_introl eq_refl)).
	  refine (False_ind _ (_ lle)); clear lle.
	  unfold n; rewrite code_pi1_pair, <-decode_code_finite_set; intros [h|[]].
	  apply (f_equal code_pi1) in h; rewrite code_pi1_pair, code_pi1_pair in h; discriminate h.
	+ exists [(code_pair (code_finite_set [code_pair (code_finite_set []) (code_pi2 (S (S O)))]) O)]; split; [rewrite <-decode_code_finite_set; left; exact eq_refl|].
	  intros x [->|[]].
	  exists []; split; [intros ? []|].
	  unfold n; rewrite code_pi1_pair, code_pi1_pair, code_pi2_pair.
	  exists [S (S O)]; split; [rewrite <-decode_code_finite_set; left; exact eq_refl|intros ? [->|[]]].
	  exists []; split; [|intros ? []].
	  rewrite <-decode_code_finite_set; left; exact eq_refl.
Qed.
End PomegaModel.

End UntypedModelsC.
