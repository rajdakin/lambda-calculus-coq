Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Relations.
Require Untyped.

Module Type UntypedLambdaFT.
Declare Module Export Vars : VarPropsT.

Inductive bterm : Type :=
	| BCFelleisen : bterm
	| BVar : V -> bterm
	| BBound : nat -> bterm
	| BApp : bterm -> bterm -> bterm
	| BAbs : bterm -> bterm.

Coercion BApp : bterm >-> Funclass.

Module Import UntypedBNotation.
Notation "<{  b  }>" := b (b custom bterms).

Notation "{ v }" := v (in custom bterms at level 0, v constr).
Notation "( v )" := v (in custom bterms at level 0, v custom bterms at level 2).
Notation "'C;'" := BCFelleisen (in custom bterms at level 0).
Notation "< n >" := (BBound n) (in custom bterms at level 0, n constr at level 1, format "< n >").
Notation "^ M" := (BAbs M) (in custom bterms at level 2, M custom bterms, format "^ M").
Notation "M N" := (BApp M N) (in custom bterms at level 1, M custom bterms, N custom bterms, left associativity).
End UntypedBNotation.

Implicit Types (x y : V).

Fixpoint valid_bpath u p := match p, u with
	| [], _ => True
	| Untyped.OFun :: p, BApp u v => valid_bpath u p
	| Untyped.OArg :: p, BApp u v => valid_bpath v p
	| Untyped.OBdy :: p, BAbs u => valid_bpath u p
	| _ :: _, _ => False
end.

Fixpoint subbterm (u : bterm) (p : list Untyped.occpart) : valid_bpath u p -> bterm.
Proof using.
	destruct p as [|[| |] p].
	1: intros _; exact u.
	1-3: destruct u as [|x|n|u v|u]; intros H; try contradiction H; exact (subbterm _ p H).
Defined.

Inductive bcontext : Type :=
	| BCHole : bcontext
	| BCApp_l : bcontext -> bterm -> bcontext
	| BCApp_r : bterm -> bcontext -> bcontext
	| BCAbs : bcontext -> bcontext.

Fixpoint subst_bcontext (c : bcontext) u {struct c} : bterm := match c with
	| BCHole => u
	| BCApp_l c' v => (subst_bcontext c' u) v
	| BCApp_r v c' => v (subst_bcontext c' u)
	| BCAbs c' => BAbs (subst_bcontext c' u)
end.

Fixpoint csubst_bcontext c c' := match c with
	| BCHole => c'
	| BCApp_l c v => BCApp_l (csubst_bcontext c c') v
	| BCApp_r v c => BCApp_r v (csubst_bcontext c c')
	| BCAbs c => BCAbs (csubst_bcontext c c')
end.

Fixpoint offset_lcontext c := match c with
	| BCHole => O
	| BCApp_l c' v => offset_lcontext c'
	| BCApp_r u c' => offset_lcontext c'
	| BCAbs c' => S (offset_lcontext c')
end.

Inductive over_bcontext {R : relation bterm} | : relation bterm :=
	| bctx_step : forall {u v}, R u v -> over_bcontext u v
	| bctx_app_l : forall {u u'} [v], over_bcontext u u' -> over_bcontext (BApp u v) (BApp u' v)
	| bctx_app_r : forall [u] {v v'}, over_bcontext v v' -> over_bcontext (BApp u v) (BApp u v')
	| bctx_abs : forall {u v}, over_bcontext u v -> over_bcontext (BAbs u) (BAbs v).
Arguments over_bcontext _ _ _ : clear implicits.

Parameter over_bcontext_iff : forall R u v,
	over_bcontext R u v <-> exists C u' v', R u' v' /\ u = subst_bcontext C u' /\ v = subst_bcontext C v'.
Parameter over_bcontext_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_bcontext R1) (over_bcontext R2).
Parameter over_bcontext_union : forall R1 R2 u v, over_bcontext (union _ R1 R2) u v <-> over_bcontext R1 u v \/ over_bcontext R2 u v.
Parameter over_bcontext_transp : forall {R u v}, over_bcontext R u v -> over_bcontext (transp R) v u.
Parameter over_bcontext_transp_comm : forall {R u v}, (over_bcontext R)^t u v <-> over_bcontext (R^t) u v.
Parameter clos_rt_over_bcontext_ctx : forall {R} c [u v], (over_bcontext R)^* u v -> (over_bcontext R)^* (subst_bcontext c u) (subst_bcontext c v).

Fixpoint incr_bound u k := match u with
	| BCFelleisen => BCFelleisen
	| BVar y => BVar y
	| BBound n => BBound (if k <=? n then S n else n)
	| BApp u v => BApp (incr_bound u k) (incr_bound v k)
	| BAbs u => BAbs (incr_bound u (S k))
end.
Fixpoint bsubst u x v := match u with
	| BCFelleisen => BCFelleisen
	| BVar y => if dec_V x y then v else u
	| BBound _ => u
	| BApp u1 u2 => BApp (bsubst u1 x v) (bsubst u2 x v)
	| BAbs u => BAbs (bsubst u x (incr_bound v O))
end.
Fixpoint bsubstb u n v := match u with
	| BCFelleisen => BCFelleisen
	| BVar y => BVar y
	| BBound k => if k <? n then BBound k else if k =? n then v else BBound (pred k)
	| BApp u1 u2 => BApp (bsubstb u1 n v) (bsubstb u2 n v)
	| BAbs u => BAbs (bsubstb u (S n) (incr_bound v O))
end.

Inductive bfv {x} | : bterm -> Prop :=
	| BFV_Var : bfv (BVar x)
	| BFV_App_l : forall {u v}, bfv u -> bfv (BApp u v)
	| BFV_App_r : forall {u v}, bfv v -> bfv (BApp u v)
	| BFV_Abs : forall {u}, bfv u -> bfv <{ ^{u} }>.
Inductive bfb | : nat -> bterm -> Prop :=
	| BFB_Var : forall {n}, bfb n (BBound n)
	| BFB_App_l : forall {n u v}, bfb n u -> bfb n (BApp u v)
	| BFB_App_r : forall {n u v}, bfb n v -> bfb n (BApp u v)
	| BFB_Abs : forall {n u}, bfb (S n) u -> bfb n <{ ^{u} }>.
Arguments bfv _ _ : clear implicits.

Fixpoint min_gt_bvars u := match u with
	| BCFelleisen => O
	| BVar x => match onat_of_V x with None => O | Some n => S n end
	| BBound _ => O
	| BApp u v => max (min_gt_bvars u) (min_gt_bvars v)
	| BAbs u => min_gt_bvars u
end.
Fixpoint min_gt_fbound u := match u with
	| BCFelleisen => O
	| BVar x => O
	| BBound n => S n
	| BApp u v => max (min_gt_fbound u) (min_gt_fbound v)
	| BAbs u => pred (min_gt_fbound u)
end.

Parameter min_gt_bvars_fv : forall u n, min_gt_bvars u <= n -> ~ bfv (V_of_nat n) u.
Parameter min_gt_fbound_fb : forall u n, min_gt_fbound u <= n -> ~ bfb n u.
Parameter bsubst_nfv : forall u x v, ~ bfv x u -> bsubst u x v = u.
Parameter le_is_ex_add : forall m n, m <= n -> exists k, n = Nat.add k m.
Parameter incr_nfb : forall u n, (forall k, n <= k -> ~ bfb k u) -> incr_bound u n = u.

Fixpoint bruijn_of_var x l n := match l with
	| [] => BVar x
	| hd :: tl => if dec_V hd x then BBound n else bruijn_of_var x tl (S n)
end.
Fixpoint babstract u l n := match u with
	| BCFelleisen => BCFelleisen
	| BVar x => bruijn_of_var x l n
	| BBound k => BBound (if k <? n then k else k + length l)
	| BApp u v => BApp (babstract u l n) (babstract v l n)
	| BAbs u => BAbs (babstract u l (S n))
end.
Fixpoint bconcrete u f := match u with
	| BCFelleisen => BCFelleisen
	| BVar x => BVar x
	| BBound k => f k
	| BApp u v => BApp (bconcrete u f) (bconcrete v f)
	| BAbs u => BAbs (bconcrete u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
end.

Parameter bruijn_of_var_eq : forall x l n,
	(exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ bruijn_of_var x l n = BBound (length l1 + n)) \/
	(~ In x l /\ bruijn_of_var x l n = BVar x).
Parameter bconcrete_ext : forall u f1 f2, (forall k, bfb k u -> f1 k = f2 k) ->
	bconcrete u f1 = bconcrete u f2.
Parameter babstract_bconcrete : forall u l n,
	bconcrete (babstract u l n) (fun k => if k <? n then BBound k else nth (map BVar l) (k - n) (BBound (k - length l))) = u.
Parameter bconcrete_bsubst : forall u n v,
	bconcrete u (fun k => if k <? n then BBound k else if k =? n then v else BBound (pred k)) = bsubstb u n v.

Inductive Pvalue : bterm -> Prop :=
	| PVVar : forall x, Pvalue (BVar x)
	| PVBound : forall n, Pvalue (BBound n)
	| PVAbs : forall u, Pvalue (BAbs u).

Inductive beta : relation bterm :=
	| Beta : forall u v, Pvalue v -> beta <{ (^{u}) {v} }> (bsubstb u O v)
	| BetaCl : forall u v, beta <{ C; {u} {v} }> <{ C; (^{incr_bound u O} (^<1> (<0> {incr_bound (incr_bound v O) O}))) }>
	| BetaCr : forall V u, Pvalue V -> beta <{ {V} (C; {u}) }> <{ C; (^{incr_bound u O} (^<1> ({incr_bound (incr_bound V O) O} <0>))) }>.

Parameter ctx_beta_CFelleisen_inv : forall x v, ~ (over_bcontext beta) BCFelleisen v.
Parameter ctx_beta_Var_inv : forall x v, ~ (over_bcontext beta) (BVar x) v.
Parameter ctx_beta_Bound_inv : forall n v, ~ (over_bcontext beta) (BBound n) v.
Parameter ctx_beta_App_inv : forall u v w, over_bcontext beta <{ {u} {v} }> w ->
	(exists u', u = BAbs u' /\ Pvalue v /\ w = bsubstb u' O v) \/
	(exists u', u = BApp BCFelleisen u' /\ w = <{ C; (^{incr_bound u' O} (^<1> (<0> {incr_bound (incr_bound v O) O})))}>) \/
	(exists v', Pvalue u /\ v = BApp BCFelleisen v' /\ w = <{ C; (^{incr_bound v' O} (^<1> ({incr_bound (incr_bound u O) O} <0>)))}>) \/
	(exists u', over_bcontext beta u u' /\ w = BApp u' v) \/ (exists v', over_bcontext beta v v' /\ w = BApp u v').
Parameter ctx_beta_Abs_inv : forall u v, over_bcontext beta (BAbs u) v ->
	exists v', over_bcontext beta u v' /\ v = BAbs v'.

Definition normal_form := RewriteSystem.normal_form (over_bcontext beta).
Definition normalizable := RewriteSystem.normalizable (over_bcontext beta).
Definition strong_normalizable:= RewriteSystem.strong_normalizable (over_bcontext beta).

Definition delta := <{ ^<0> <0> }>.
Definition Omega := BApp delta delta.

Parameter beta_delta : forall u, ~ over_bcontext beta delta u.
Parameter beta_Omega_Omega : forall u, over_bcontext beta Omega u <-> u = Omega.

Inductive eta : relation bterm :=
	| Eta : forall u, eta (BAbs (BApp (incr_bound u O) (BBound O))) u
	| EtaC : forall u, eta (BApp BCFelleisen (BAbs (BApp (BBound O) (incr_bound u O)))) u.

Inductive psubstb : relation bterm :=
	| PS_C : psubstb BCFelleisen BCFelleisen
	| PS_Var : forall {x}, psubstb (BVar x) (BVar x)
	| PS_Bound : forall {n}, psubstb (BBound n) (BBound n)
	| PS_App : forall {u u' v v'}, psubstb u u' -> psubstb v v' -> psubstb (BApp u v) (BApp u' v')
	| PS_Abs : forall {u u'}, psubstb u u' -> psubstb (BAbs u) (BAbs u')
	| PS_Beta : forall {u u' v v'}, psubstb u u' -> psubstb v v' -> Pvalue v' -> psubstb (BApp (BAbs u) v) (bsubstb u' O v')
	| PS_BetaCl : forall {u u' v v'}, psubstb u u' -> psubstb v v' ->
			psubstb (BApp (BApp BCFelleisen u) v) <{ C; (^{incr_bound u' O} (^<1> (<0> {incr_bound (incr_bound v' O) O}))) }>
	| PS_BetaCr : forall {u u' v v'}, psubstb u u' -> psubstb v v' -> Pvalue u' ->
			psubstb (BApp u (BApp BCFelleisen v)) <{ C; (^{incr_bound v' O} (^<1> ({incr_bound (incr_bound u' O) O} <0>))) }>.

Parameter psubstb_refl : forall {u}, psubstb u u.
Parameter incr_bound_comm : forall {u n1 n2}, n1 <= n2 -> incr_bound (incr_bound u n2) n1 = incr_bound (incr_bound u n1) (S n2).
Parameter incr_bsubstb_le : forall {u n v k}, n <= k -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u (S k)) n (incr_bound v k).
Parameter incr_bsubstb_ge : forall {u n v k}, k <= n -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u k) (S n) (incr_bound v k).
Parameter bsubstb_incr : forall {u n v}, bsubstb (incr_bound u n) n v = u.
Parameter bsubstb_comm : forall {u1 u2 u3 n1 n2}, n1 <= n2 ->
	bsubstb (bsubstb u1 n1 u2) n2 u3 = bsubstb (bsubstb u1 (S n2) (incr_bound u3 n1)) n1 (bsubstb u2 n2 u3).
Parameter pvalue_incr : forall {u n}, Pvalue u -> Pvalue (incr_bound u n).
Parameter psubstb_incr : forall {u v n}, psubstb u v -> psubstb (incr_bound u n) (incr_bound v n).
Parameter psubstb_bsubstb : forall {u1 u2 u1' u2' n},
	psubstb u1 u1' -> psubstb u2 u2' -> Pvalue u2' -> psubstb (bsubstb u1 n u2) (bsubstb u1' n u2').
Parameter pvalue_psubstb : forall {u v}, Pvalue u -> psubstb u v -> Pvalue v.
Parameter psubstb_strong_confluence : RewriteSystem.strong_confluence eq psubstb.
Parameter beta_is_psubstb : forall {u v}, over_bcontext beta u v -> psubstb u v.
Parameter psubstb_is_betas : forall {u v}, psubstb u v -> (over_bcontext beta)^* u v.
Parameter confluence_beta : RewriteSystem.confluence eq (over_bcontext beta).
Parameter bsubstb_nfb : forall u n v, (forall k, n <= k -> ~ bfb k u) -> bsubstb u n v = u.
Parameter bfv_incr_iff : forall x u n, bfv x (incr_bound u n) <-> bfv x u.
Parameter bfb_incr_iff : forall k u n, bfb (if n <=? k then S k else k) (incr_bound u n) <-> bfb k u.

End UntypedLambdaFT.

Module UntypedLambdaF (Vars0 : VarPropsT) <: UntypedLambdaFT.
Module Export Vars := Vars0.

Inductive bterm : Type :=
	| BCFelleisen : bterm
	| BVar : V -> bterm
	| BBound : nat -> bterm
	| BApp : bterm -> bterm -> bterm
	| BAbs : bterm -> bterm.

Coercion BApp : bterm >-> Funclass.

Module Import UntypedBNotation.
Notation "<{  b  }>" := b (b custom bterms).

Notation "{ v }" := v (in custom bterms at level 0, v constr).
Notation "( v )" := v (in custom bterms at level 0, v custom bterms at level 2).
Notation "'C;'" := BCFelleisen (in custom bterms at level 0).
Notation "< n >" := (BBound n) (in custom bterms at level 0, n constr at level 1, format "< n >").
Notation "^ M" := (BAbs M) (in custom bterms at level 2, M custom bterms, format "^ M").
Notation "M N" := (BApp M N) (in custom bterms at level 1, M custom bterms, N custom bterms, left associativity).
End UntypedBNotation.

Implicit Types (x y : V).

Fixpoint valid_bpath u p := match p, u with
	| [], _ => True
	| Untyped.OFun :: p, BApp u v => valid_bpath u p
	| Untyped.OArg :: p, BApp u v => valid_bpath v p
	| Untyped.OBdy :: p, BAbs u => valid_bpath u p
	| _ :: _, _ => False
end.

Fixpoint subbterm (u : bterm) (p : list Untyped.occpart) : valid_bpath u p -> bterm.
Proof using.
	destruct p as [|[| |] p].
	1: intros _; exact u.
	1-3: destruct u as [|x|n|u v|u]; intros H; try contradiction H; exact (subbterm _ p H).
Defined.

Inductive bcontext : Type :=
	| BCHole : bcontext
	| BCApp_l : bcontext -> bterm -> bcontext
	| BCApp_r : bterm -> bcontext -> bcontext
	| BCAbs : bcontext -> bcontext.

Fixpoint subst_bcontext (c : bcontext) u {struct c} : bterm := match c with
	| BCHole => u
	| BCApp_l c' v => (subst_bcontext c' u) v
	| BCApp_r v c' => v (subst_bcontext c' u)
	| BCAbs c' => BAbs (subst_bcontext c' u)
end.

Fixpoint csubst_bcontext c c' := match c with
	| BCHole => c'
	| BCApp_l c v => BCApp_l (csubst_bcontext c c') v
	| BCApp_r v c => BCApp_r v (csubst_bcontext c c')
	| BCAbs c => BCAbs (csubst_bcontext c c')
end.

Fixpoint offset_lcontext c := match c with
	| BCHole => O
	| BCApp_l c' v => offset_lcontext c'
	| BCApp_r u c' => offset_lcontext c'
	| BCAbs c' => S (offset_lcontext c')
end.

Inductive over_bcontext {R : relation bterm} | : relation bterm :=
	| bctx_step : forall {u v}, R u v -> over_bcontext u v
	| bctx_app_l : forall {u u'} [v], over_bcontext u u' -> over_bcontext (BApp u v) (BApp u' v)
	| bctx_app_r : forall [u] {v v'}, over_bcontext v v' -> over_bcontext (BApp u v) (BApp u v')
	| bctx_abs : forall {u v}, over_bcontext u v -> over_bcontext (BAbs u) (BAbs v).
Arguments over_bcontext _ _ _ : clear implicits.

Lemma over_bcontext_iff : forall R u v,
	over_bcontext R u v <-> exists C u' v', R u' v' /\ u = subst_bcontext C u' /\ v = subst_bcontext C v'.
Proof using.
	intros R u v; split; [intros H|intros (C & u' & v' & H & -> & ->)].
	- induction H as [u v HR|u u' v H (C & u1 & u2 & IH & -> & ->)|u v v' H (C & v1 & v2 & IH & -> & ->)|u v H (C & u' & v' & IH & -> & ->)].
	  1: exists BCHole, u, v; easy.
	  1: exists (BCApp_l C v), u1, u2; easy.
	  1: exists (BCApp_r u C), v1, v2; easy.
	  1: exists (BCAbs C), u', v'; easy.
	- induction C as [|C IH v|u C IH|C IH].
	  1: exact (bctx_step H).
	  1: exact (bctx_app_l IH).
	  1: exact (bctx_app_r IH).
	  1: exact (bctx_abs IH).
Qed.

Lemma over_bcontext_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_bcontext R1) (over_bcontext R2).
Proof using.
	intros R1 R2 HR u v; rewrite !over_bcontext_iff; intros (c & u' & v' & HR1 & equ & eqv).
	exists c, u', v'; split; [exact (HR _ _ HR1)|split; assumption].
Qed.

Lemma over_bcontext_union : forall R1 R2 u v, over_bcontext (union _ R1 R2) u v <-> over_bcontext R1 u v \/ over_bcontext R2 u v.
Proof using.
	intros R1 R2 u v; split.
	2: intros [H|H]; refine (over_bcontext_ext _ _ _ H); intros u' v' H'.
	2: left; exact H'.
	2: right; exact H'.
	intros H; induction H as [u v [H|H]|u u' v H [IH|IH]|u v v' H [IH|IH]|u v H [IH|IH]].
	1,3,5,7: left.
	5-8: right.
	1,5: exact (bctx_step H).
	1,4: exact (bctx_app_l IH).
	1,3: exact (bctx_app_r IH).
	1,2: exact (bctx_abs IH).
Qed.

Lemma over_bcontext_transp : forall {R u v}, over_bcontext R u v -> over_bcontext (transp R) v u.
Proof using.
	intros R u v H;
	  induction H as [u v HR|u u' v H IH|u v v' H IH|u v H IH].
	- exact (bctx_step HR).
	- exact (bctx_app_l IH).
	- exact (bctx_app_r IH).
	- exact (bctx_abs IH).
Qed.
Lemma over_bcontext_transp_comm : forall {R u v}, (over_bcontext R)^t u v <-> over_bcontext (R^t) u v.
Proof using.
	intros R u v; split; exact over_bcontext_transp.
Qed.

Lemma clos_rt_over_bcontext_ctx : forall {R} c [u v], (over_bcontext R)^* u v -> (over_bcontext R)^* (subst_bcontext c u) (subst_bcontext c v).
Proof using.
	intros R c u v H; induction H as [u v H|u|u v w _ IH1 _ IH2]; [|exact rt_refl|exact (rt_trans IH1 IH2)].
	refine (rt_step _).
	induction c as [|c IH v'|u' c IH|c IH].
	- exact H.
	- exact (bctx_app_l IH).
	- exact (bctx_app_r IH).
	- exact (bctx_abs IH).
Qed.

Fixpoint incr_bound u k := match u with
	| BCFelleisen => BCFelleisen
	| BVar y => BVar y
	| BBound n => BBound (if k <=? n then S n else n)
	| BApp u v => BApp (incr_bound u k) (incr_bound v k)
	| BAbs u => BAbs (incr_bound u (S k))
end.
Fixpoint bsubst u x v := match u with
	| BCFelleisen => BCFelleisen
	| BVar y => if dec_V x y then v else u
	| BBound _ => u
	| BApp u1 u2 => BApp (bsubst u1 x v) (bsubst u2 x v)
	| BAbs u => BAbs (bsubst u x (incr_bound v O))
end.
Fixpoint bsubstb u n v := match u with
	| BCFelleisen => BCFelleisen
	| BVar y => BVar y
	| BBound k => if k <? n then BBound k else if k =? n then v else BBound (pred k)
	| BApp u1 u2 => BApp (bsubstb u1 n v) (bsubstb u2 n v)
	| BAbs u => BAbs (bsubstb u (S n) (incr_bound v O))
end.

Inductive bfv {x} | : bterm -> Prop :=
	| BFV_Var : bfv (BVar x)
	| BFV_App_l : forall {u v}, bfv u -> bfv (BApp u v)
	| BFV_App_r : forall {u v}, bfv v -> bfv (BApp u v)
	| BFV_Abs : forall {u}, bfv u -> bfv <{ ^{u} }>.
Inductive bfb | : nat -> bterm -> Prop :=
	| BFB_Var : forall {n}, bfb n (BBound n)
	| BFB_App_l : forall {n u v}, bfb n u -> bfb n (BApp u v)
	| BFB_App_r : forall {n u v}, bfb n v -> bfb n (BApp u v)
	| BFB_Abs : forall {n u}, bfb (S n) u -> bfb n <{ ^{u} }>.
Arguments bfv _ _ : clear implicits.

Fixpoint min_gt_bvars u := match u with
	| BCFelleisen => O
	| BVar x => match onat_of_V x with None => O | Some n => S n end
	| BBound _ => O
	| BApp u v => max (min_gt_bvars u) (min_gt_bvars v)
	| BAbs u => min_gt_bvars u
end.
Fixpoint min_gt_fbound u := match u with
	| BCFelleisen => O
	| BVar x => O
	| BBound n => S n
	| BApp u v => max (min_gt_fbound u) (min_gt_fbound v)
	| BAbs u => pred (min_gt_fbound u)
end.

Lemma min_gt_bvars_fv : forall u n, min_gt_bvars u <= n -> ~ bfv (V_of_nat n) u.
Proof using.
	intros u n Hn; induction u as [|x|k|u IHu v IHv|u IH].
	- intros H; inversion H.
	- simpl in Hn; intros H; inversion H; subst; rewrite onat_of_nat in Hn; exact (nle_succ_diag_l _ Hn).
	- intros H; inversion H.
	- simpl in Hn; intros H; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  inversion H; subst; [exact (IHu Hu H1)|exact (IHv Hv H1)].
	- simpl in Hn; intros H.
	  inversion H; subst; exact (IH Hn H1).
Qed.
Lemma min_gt_fbound_fb : forall u n, min_gt_fbound u <= n -> ~ bfb n u.
Proof using.
	intros u; induction u as [|x|k|u IHu v IHv|u IH]; intros n Hn.
	- intros H; inversion H.
	- intros H; inversion H.
	- cbn in Hn; intros H; inversion H; subst; exact (lt_neq _ _ Hn eq_refl).
	- cbn in Hn; intros H; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  inversion H; subst; [exact (IHu _ Hu H2)|exact (IHv _ Hv H2)].
	- cbn in Hn; intros H.
	  inversion H; subst; refine (IH (S _) (le_trans _ _ _ _ (le_n_S _ _ Hn)) H2).
	  destruct (min_gt_fbound u); [exact (le_0_n _)|exact (le_n _)].
Qed.

Lemma bsubst_nfv : forall u x v, ~ bfv x u -> bsubst u x v = u.
Proof using.
	intros u x; induction u as [|y|n|u1 IH1 u2 IH2|u IH]; intros v H.
	- exact eq_refl.
	- cbn; refine (if_dec_neq _ _ _ _ _); intros <-; exact (H BFV_Var).
	- exact eq_refl.
	- cbn; f_equal; [exact (IH1 _ (fun H' => H (BFV_App_l H')))|exact (IH2 _ (fun H' => H (BFV_App_r H')))].
	- cbn; f_equal; exact (IH _ (fun H' => H (BFV_Abs H'))).
Qed.


Lemma le_is_ex_add : forall m n, m <= n -> exists k, n = Nat.add k m.
Proof using.
	intros m n H; induction H as [|n H [k ->]].
	1: exists O; exact eq_refl.
	exists (S k); exact eq_refl.
Qed.


Lemma incr_nfb : forall u n, (forall k, n <= k -> ~ bfb k u) -> incr_bound u n = u.
Proof using.
	intros u; induction u as [|x|k|u IHu v IHv|u IH]; intros n Hn.
	- exact eq_refl.
	- exact eq_refl.
	- cbn; rewrite (proj2 (leb_nle _ _) (fun nlek => Hn _ nlek BFB_Var)); exact eq_refl.
	- exact (f_equal2 _ (IHu _ (fun k Hk Hf => Hn _ Hk (BFB_App_l Hf))) (IHv _ (fun k Hk Hf => Hn _ Hk (BFB_App_r Hf)))).
	- refine (f_equal _ (IH _ _)); intros [|k] Hk Hf; [inversion Hk|exact (Hn _ (le_S_n _ _ Hk) (BFB_Abs Hf))].
Qed.


Fixpoint bruijn_of_var x l n := match l with
	| [] => BVar x
	| hd :: tl => if dec_V hd x then BBound n else bruijn_of_var x tl (S n)
end.
Fixpoint babstract u l n := match u with
	| BCFelleisen => BCFelleisen
	| BVar x => bruijn_of_var x l n
	| BBound k => BBound (if k <? n then k else k + length l)
	| BApp u v => BApp (babstract u l n) (babstract v l n)
	| BAbs u => BAbs (babstract u l (S n))
end.
Fixpoint bconcrete u f := match u with
	| BCFelleisen => BCFelleisen
	| BVar x => BVar x
	| BBound k => f k
	| BApp u v => BApp (bconcrete u f) (bconcrete v f)
	| BAbs u => BAbs (bconcrete u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
end.

Lemma bruijn_of_var_eq : forall x l n,
	(exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ bruijn_of_var x l n = BBound (length l1 + n)) \/
	(~ In x l /\ bruijn_of_var x l n = BVar x).
Proof using.
	intros x l; induction l as [|h l IH]; intros n.
	1: right; split; [intros []|exact eq_refl].
	cbn; destruct (dec_V h x) as [->|hnex].
	1: left; exists [], l; split; [exact eq_refl|split; [intros []|exact eq_refl]].
	specialize (IH (S n)) as [(l1 & l2 & eql & Hl1 & IH)|[xnil IH]]; [left|right].
	1: exists (h :: l1), l2; split; [exact (f_equal _ eql)|split; [|rewrite <-plus_n_Sm in IH; exact IH]].
	1: intros [eq|xinl1]; [exact (hnex (eq_sym eq))|exact (Hl1 xinl1)].
	split; [intros [eq|H]; [exact (hnex (eq_sym eq))|exact (xnil H)]|exact IH].
Qed.

Lemma bconcrete_ext : forall u f1 f2, (forall k, bfb k u -> f1 k = f2 k) ->
	bconcrete u f1 = bconcrete u f2.
Proof using.
	intros u; induction u as [|x|k|u IHu v IHv|u IH]; intros f1 f2 Hf1f2.
	- exact eq_refl.
	- exact eq_refl.
	- exact (Hf1f2 _ BFB_Var).
	- exact (f_equal2 _ (IHu _ _ (fun k Hk => Hf1f2 _ (BFB_App_l Hk))) (IHv _ _ (fun k Hk => Hf1f2 _ (BFB_App_r Hk)))).
	- refine (f_equal _ (IH _ _ _)); intros [|k] Hk; [exact eq_refl|exact (f_equal (fun a => incr_bound a O) (Hf1f2 _ (BFB_Abs Hk)))].
Qed.
Lemma babstract_bconcrete : forall u l n,
	bconcrete (babstract u l n) (fun k => if k <? n then BBound k else nth (map BVar l) (k - n) (BBound (k - length l))) = u.
Proof using.
	intros u; induction u as [|x|k|u IHu v IHv|u IH]; intros l n.
	- exact eq_refl.
	- simpl babstract; destruct (bruijn_of_var_eq x l n) as [(l1 & l2 & eql & xnil1 & eq)|[xnil eq]]; rewrite eq;
	    [clear eq; simpl bconcrete|exact eq_refl].
	  rewrite (proj2 (ltb_ge _ _) (le_add_l _ _)).
	  rewrite <-nth_default_eq, add_sub, eql, map_app; unfold nth_default.
	  generalize (BBound (length l1 + n - length (l1 ++ x :: l2))); intros d; clear; induction l1 as [|hd l1 IH]; [exact eq_refl|cbn; exact IH].
	- unfold babstract, bconcrete.
	  remember (k <? n) as tmp eqn:kltn; destruct tmp.
	  1: rewrite <-kltn; exact eq_refl.
	  apply eq_sym, ltb_ge in kltn.
	  rewrite (proj2 (ltb_ge _ _) (le_trans _ _ _ kltn (le_add_r _ _))); rewrite <-nth_default_eq, add_sub; cbn.
	  rewrite (add_sub_swap _ _ _ kltn), add_comm; generalize (k - n); clear; intros n.
	  induction l as [|hd tl IH]; [destruct n; exact eq_refl|exact IH].
	- exact (f_equal2 _ (IHu _ _) (IHv _ _)).
	- refine (f_equal BAbs _); fold bconcrete babstract.
	  rewrite <-(IH l (S n)) at 2; clear IH; refine (bconcrete_ext _ _ _ _).
	  intros [|k] _; [exact eq_refl|rewrite (eq_refl : (S k <? S n) = (k <? n)), (eq_refl : (S k - S n) = (k - n))].
	  remember (k <? n) as tmp eqn:nlek; destruct tmp; [exact eq_refl|apply eq_sym, ltb_ge in nlek].
	  apply le_is_ex_add in nlek; destruct nlek as [k' ->]; rename k' into k.
	  rewrite add_sub, <-plus_Sn_m.
	  generalize dependent k; induction l as [|hd l IH]; intros [|k].
	  1: exact (f_equal (fun a => BBound (S a)) (sub_0_r _)).
	  1,2: exact eq_refl.
	  exact (IH _).
Qed.

Lemma bconcrete_bsubst : forall u n v,
	bconcrete u (fun k => if k <? n then BBound k else if k =? n then v else BBound (pred k)) = bsubstb u n v.
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros n v.
	- exact eq_refl.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _) (IH2 _ _)).
	- lazy beta delta [bconcrete bsubstb] iota; fold bconcrete bsubstb.
	  rewrite <-(IH (S n) (incr_bound v 0)); refine (f_equal BAbs (bconcrete_ext _ _ _ _)).
	  intros [|k] _; [exact eq_refl|].
	  rewrite (eq_refl : (S _ <? S _) = (k <? _)), (eq_refl : (S _ =? S _) = (k =? _)).
	  remember (k <? n) as tmp eqn:nlek; destruct tmp; [exact eq_refl|].
	  apply eq_sym, ltb_ge, le_is_ex_add in nlek; destruct nlek as [[|k'] ->].
	  1: cbn; rewrite eqb_refl; exact eq_refl.
	  rewrite (proj2 (eqb_neq (S k' + n) n) (fun H => lt_neq _ _ (le_n_S _ _ (le_add_l _ _)) (eq_sym H))).
	  exact eq_refl.
Qed.


Inductive Pvalue : bterm -> Prop :=
	| PVVar : forall x, Pvalue (BVar x)
	| PVBound : forall n, Pvalue (BBound n)
	| PVAbs : forall u, Pvalue (BAbs u).

Inductive beta : relation bterm :=
	| Beta : forall u v, Pvalue v -> beta <{ (^{u}) {v} }> (bsubstb u O v)
	| BetaCl : forall u v, beta <{ C; {u} {v} }> <{ C; (^{incr_bound u O} (^<1> (<0> {incr_bound (incr_bound v O) O}))) }>
	| BetaCr : forall V u, Pvalue V -> beta <{ {V} (C; {u}) }> <{ C; (^{incr_bound u O} (^<1> ({incr_bound (incr_bound V O) O} <0>))) }>.

Lemma ctx_beta_CFelleisen_inv : forall x v, ~ (over_bcontext beta) BCFelleisen v.
Proof using.
	intros x v H.
	apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & eqx & eqv)].
	destruct c as [| | |]; try discriminate eqx.
	cbn in eqx; subst u'; inversion H.
Qed.
Lemma ctx_beta_Var_inv : forall x v, ~ (over_bcontext beta) (BVar x) v.
Proof using.
	intros x v H.
	apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & eqx & eqv)].
	destruct c as [| | |]; try discriminate eqx.
	cbn in eqx; subst u'; inversion H.
Qed.
Lemma ctx_beta_Bound_inv : forall n v, ~ (over_bcontext beta) (BBound n) v.
Proof using.
	intros x v H.
	apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & eqx & eqv)].
	destruct c as [| | |]; try discriminate eqx.
	cbn in eqx; subst u'; inversion H.
Qed.
Lemma ctx_beta_App_inv : forall u v w, over_bcontext beta <{ {u} {v} }> w ->
	(exists u', u = BAbs u' /\ Pvalue v /\ w = bsubstb u' O v) \/
	(exists u', u = BApp BCFelleisen u' /\ w = <{ C; (^{incr_bound u' O} (^<1> (<0> {incr_bound (incr_bound v O) O})))}>) \/
	(exists v', Pvalue u /\ v = BApp BCFelleisen v' /\ w = <{ C; (^{incr_bound v' O} (^<1> ({incr_bound (incr_bound u O) O} <0>)))}>) \/
	(exists u', over_bcontext beta u u' /\ w = BApp u' v) \/ (exists v', over_bcontext beta v v' /\ w = BApp u v').
Proof using.
	intros u v w H; apply over_bcontext_iff in H;
	  destruct H as [c (u' & v' & H & equv & eqw)].
	destruct c as [|c v0|u0 c|]; try discriminate equv.
	- cbn in equv, eqw; subst u' v'.
	  inversion H as [u' v' H' eq1 eq2|u' v' eq1 eq2|V u' H' eq1 eq2]; subst u v w; clear H.
	  1: left; refine (ex_intro _ _ (conj eq_refl (conj H' eq_refl))).
	  1: right; left; refine (ex_intro _ _ (conj eq_refl eq_refl)).
	  1: right; right; left; refine (ex_intro _ _ (conj H' (conj eq_refl eq_refl))).
	- right; right; right; left.
	  injection equv as equ eqv; subst; cbn.
	  refine (ex_intro _ _ (conj _ eq_refl)).
	  apply over_bcontext_iff; exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj H (conj eq_refl eq_refl))))).
	- right; right; right; right.
	  injection equv as equ eqv; subst; cbn.
	  refine (ex_intro _ _ (conj _ eq_refl)).
	  apply over_bcontext_iff; exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj H (conj eq_refl eq_refl))))).
Qed.
Lemma ctx_beta_Abs_inv : forall u v, over_bcontext beta (BAbs u) v ->
	exists v', over_bcontext beta u v' /\ v = BAbs v'.
Proof using.
	intros u v H; apply over_bcontext_iff in H; destruct H as ([| | |c] & u' & v' & H & equ & eqv);
	  try discriminate equ.
	1: cbn in equ; rewrite <-equ in H; inversion H.
	subst; cbn; refine (ex_intro _ _ (conj _ eq_refl)).
	injection equ as ->.
	apply over_bcontext_iff; exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj H (conj eq_refl eq_refl))))).
Qed.

Definition normal_form := RewriteSystem.normal_form (over_bcontext beta).
Definition normalizable := RewriteSystem.normalizable (over_bcontext beta).
Definition strong_normalizable:= RewriteSystem.strong_normalizable (over_bcontext beta).

Definition delta := <{ ^<0> <0> }>.
Definition Omega := BApp delta delta.

Lemma beta_delta : forall u, ~ over_bcontext beta delta u.
Proof using.
	intros u H; inversion H; subst.
	1: inversion H0.
	inversion H1; subst.
	1: inversion H0.
	1,2: inversion H4; subst.
	1,2: inversion H0.
Qed.

Lemma beta_Omega_Omega : forall u, over_bcontext beta Omega u <-> u = Omega.
Proof using.
	intros u; split.
	- intros H; apply ctx_beta_App_inv in H;
	     destruct H as [(u' & [=<-] & Hdelta & ->)|[(u' & f & _)|[(v' & _ & f & _)|[(u' & H & ->)|(v' & H & ->)]]]].
	  + exact eq_refl.
	  + discriminate f.
	  + discriminate f.
	  + contradiction (beta_delta _ H).
	  + contradiction (beta_delta _ H).
	- intros ->; exact (bctx_step (Beta _ _ (PVAbs _))).
Qed.

Goal ~normalizable Omega.
Proof using.
	intros [v [Hv1 Hv2]].
	assert (tmp : v = Omega).
	{ clear Hv2.
	  remember Omega as u eqn:equ; induction Hv1 as [u v H|u|u v w _ IH1 _ IH2]; subst.
	  1: exact (proj1 (beta_Omega_Omega _) H).
	  1: exact eq_refl.
	  specialize (IH1 eq_refl); subst; exact (IH2 eq_refl). }
	clear Hv1; subst; unfold RewriteSystem.normal_form in Hv2.
	exact (Hv2 _ (proj2 (beta_Omega_Omega _) eq_refl)).
Qed.

Goal normalizable <{ C; (^<1>) {Omega} }> /\ ~ strong_normalizable <{ C; (^<1>) {Omega} }>.
Proof using.
	split.
	- exists (BApp BCFelleisen (BAbs (BBound (S O)))); split; [|intros v H].
	  2: inversion H; subst; [|inversion H3|inversion H3; subst; [|inversion H1]]; inversion H0.
	  refine (rt_trans (rt_step (bctx_step (BetaCl (BAbs (BBound (S O))) Omega))) _).
	  refine (clos_rt_over_bcontext_ctx (BCApp_r _ (BCAbs BCHole)) _); cbn.
	  exact (rt_step (bctx_step (Beta _ _ (PVAbs _)))).
	- intros f; unfold strong_normalizable in f.
	  match type of f with RewriteSystem.strong_normalizable _ ?v => remember v as u eqn:equ end.
	  induction f as [u H IH]; subst.
	  refine (IH _ _ eq_refl).
	  exact (bctx_app_r (proj2 (beta_Omega_Omega _) eq_refl)).
Qed.

Inductive eta : relation bterm :=
	| Eta : forall u, eta (BAbs (BApp (incr_bound u O) (BBound O))) u
	| EtaC : forall u, eta (BApp BCFelleisen (BAbs (BApp (BBound O) (incr_bound u O)))) u.

Inductive psubstb : relation bterm :=
	| PS_C : psubstb BCFelleisen BCFelleisen
	| PS_Var : forall {x}, psubstb (BVar x) (BVar x)
	| PS_Bound : forall {n}, psubstb (BBound n) (BBound n)
	| PS_App : forall {u u' v v'}, psubstb u u' -> psubstb v v' -> psubstb (BApp u v) (BApp u' v')
	| PS_Abs : forall {u u'}, psubstb u u' -> psubstb (BAbs u) (BAbs u')
	| PS_Beta : forall {u u' v v'}, psubstb u u' -> psubstb v v' -> Pvalue v' -> psubstb (BApp (BAbs u) v) (bsubstb u' O v')
	| PS_BetaCl : forall {u u' v v'}, psubstb u u' -> psubstb v v' ->
			psubstb (BApp (BApp BCFelleisen u) v) <{ C; (^{incr_bound u' O} (^<1> (<0> {incr_bound (incr_bound v' O) O}))) }>
	| PS_BetaCr : forall {u u' v v'}, psubstb u u' -> psubstb v v' -> Pvalue u' ->
			psubstb (BApp u (BApp BCFelleisen v)) <{ C; (^{incr_bound v' O} (^<1> ({incr_bound (incr_bound u' O) O} <0>))) }>.

Lemma psubstb_refl : forall {u}, psubstb u u.
Proof using.
	intros u; induction u as [|x|n|u IHu v IHv|u IH].
	- exact PS_C.
	- exact PS_Var.
	- exact PS_Bound.
	- exact (PS_App IHu IHv).
	- exact (PS_Abs IH).
Qed.

Lemma incr_bound_comm : forall {u n1 n2}, n1 <= n2 -> incr_bound (incr_bound u n2) n1 = incr_bound (incr_bound u n1) (S n2).
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros n1 n2 Hn.
	- exact eq_refl.
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
Qed.
Lemma incr_bsubstb_le : forall {u n v k}, n <= k -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u (S k)) n (incr_bound v k).
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros n v m nlem.
	- exact eq_refl.
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
Qed.
Lemma incr_bsubstb_ge : forall {u n v k}, k <= n -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u k) (S n) (incr_bound v k).
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros n v m mlen.
	- exact eq_refl.
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
Qed.

Lemma bsubstb_incr : forall {u n v}, bsubstb (incr_bound u n) n v = u.
Proof using.
	intros u; induction u as [|x|k|u1 IH1 u2 IH2|u IH]; intros n v.
	- exact eq_refl.
	- exact eq_refl.
	- unfold bsubstb, incr_bound; fold incr_bound.
	  destruct (lt_ge_cases k n) as [kltn|nlek].
	  + rewrite (proj2 (leb_gt _ _) kltn), (proj2 (ltb_lt _ _) kltn); exact eq_refl.
	  + rewrite (proj2 (leb_le _ _) nlek).
	    rewrite (proj2 (ltb_ge _ _) (le_S _ _ nlek)), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ nlek))); exact eq_refl.
	- exact (f_equal2 BApp (IH1 _ _) (IH2 _ _)).
	- exact (f_equal BAbs (IH _ _)).
Qed.

Lemma bsubstb_comm : forall {u1 u2 u3 n1 n2}, n1 <= n2 ->
	bsubstb (bsubstb u1 n1 u2) n2 u3 = bsubstb (bsubstb u1 (S n2) (incr_bound u3 n1)) n1 (bsubstb u2 n2 u3).
Proof using.
	intros u1; induction u1 as [|x|k|u11 IH1 u12 IH2|u1 IH]; intros u2 u3 n1 n2 Hn.
	- exact eq_refl.
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
Qed.

Lemma pvalue_incr : forall {u n}, Pvalue u -> Pvalue (incr_bound u n).
Proof using.
	intros [| |k| |] n H; inversion H; constructor.
Qed.

Lemma psubstb_incr : forall {u v n}, psubstb u v -> psubstb (incr_bound u n) (incr_bound v n).
Proof using.
	intros u v n H; generalize dependent n.
	induction H as [|x|k|u1 v1 u2 v2 H1 IH1 H2 IH2|u v H IH|u1 v1 u2 v2 H1 IH1 H2 IH2 H
	               |u1 v1 u2 v2 H1 IH1 H2 IH2|u1 v1 u2 v2 H1 IH1 H2 IH2 H];
	  intros n.
	- exact PS_C.
	- exact PS_Var.
	- exact PS_Bound.
	- exact (PS_App (IH1 _) (IH2 _)).
	- exact (PS_Abs (IH _)).
	- cbn; rewrite (incr_bsubstb_le (le_0_n _)); exact (PS_Beta (IH1 _) (IH2 _) (pvalue_incr H)).
	- cbn; rewrite <-!(incr_bound_comm (le_0_n _)); exact (PS_BetaCl (IH1 _) (IH2 _)).
	- cbn; rewrite <-!(incr_bound_comm (le_0_n _)); exact (PS_BetaCr (IH1 _) (IH2 _) (pvalue_incr H)).
Qed.

Lemma psubstb_bsubstb : forall {u1 u2 u1' u2' n},
	psubstb u1 u1' -> psubstb u2 u2' -> Pvalue u2' -> psubstb (bsubstb u1 n u2) (bsubstb u1' n u2').
Proof using.
	refine (fun u1 u2 u1' u2' n H1 => (_ : forall u2 u2' n, _) u2 u2' n); clear u2 u2' n.
	induction H1 as [|x|k|u11 u11' u12 u12' H11 IH11 H12 IH12|u1 u1' H1 IH1|u11 u11' u12 u12' H11 IH11 H12 IH12 H
	                |u11 u11' u12 u12' H11 IH11 H12 IH12|u11 u11' u12 u12' H11 IH11 H12 IH12 H];
	  intros u2 u2' n H2 Hu2'.
	- exact PS_C.
	- exact PS_Var.
	- unfold bsubstb; destruct (k <? n); [|destruct (k =? n); [exact H2|]]; exact PS_Bound.
	- exact (PS_App (IH11 _ _ _ H2 Hu2') (IH12 _ _ _ H2 Hu2')).
	- exact (PS_Abs (IH1 _ _ _ (psubstb_incr H2) (pvalue_incr Hu2'))).
	- cbn.
	  rewrite (bsubstb_comm (le_0_n _)).
	  refine (PS_Beta (IH11 _ _ _ (psubstb_incr H2) (pvalue_incr Hu2')) (IH12 _ _ _ H2 Hu2') _).
	  inversion H; subst; [exact (PVVar _)|unfold bsubstb|exact (PVAbs _)].
	  clear - Hu2'; destruct (n0 <? n); [|destruct (n0 =? n)]; try exact (PVBound _); exact Hu2'.
	- cbn.
	  rewrite <-!(incr_bsubstb_ge (le_0_n _)).
	  exact (PS_BetaCl (IH11 _ _ _ H2 Hu2') (IH12 _ _ _ H2 Hu2')).
	- cbn.
	  rewrite <-!(incr_bsubstb_ge (le_0_n _)).
	  refine (PS_BetaCr (IH11 _ _ _ H2 Hu2') (IH12 _ _ _ H2 Hu2') _).
	  inversion H; subst; [exact (PVVar _)|unfold bsubstb|exact (PVAbs _)].
	  clear - Hu2'; destruct (n0 <? n); [|destruct (n0 =? n)]; try exact (PVBound _); exact Hu2'.
Qed.

Lemma pvalue_psubstb : forall {u v}, Pvalue u -> psubstb u v -> Pvalue v.
Proof using.
	intros u v H1 H2; inversion H1; subst; inversion H2; subst; constructor.
Qed.

Lemma psubstb_strong_confluence : RewriteSystem.strong_confluence eq psubstb.
Proof using.
	unfold RewriteSystem.strong_confluence.
	refine (fun u u1 u2 H1 H2 => match _ with ex_intro _ u' (conj H1 H2) => ex_intro _ u' (conj (or_introl H1) (or_introl H2)) end).
	generalize dependent u2; generalize dependent u1; induction u as [|x|n|u IHu v IHv|u IH]; intros u1 H1 u2 H2.
	1: inversion H1; inversion H2; subst; exact (ex_intro _ _ (conj PS_C PS_C)).
	1-4: inversion H1 as [|x1 eqx1 eq1|n1 eqn1 eq1|u11 u11' u12 u12' H11 H12 eq11 eq1|u10 u1' H1' eq10 eq1|u11 u11' u12 u12' H11 H12 H1' eq11 eq1
	                     |u11 u11' u12 u12' H11 H12 eq11 eq1|u11 u11' u12 u12' H11 H12 H1' eq11 eq1];
	       subst; clear H1.
	1-5: inversion H2 as [|x2 eqx2 eq2|n2 eqn2 eq2|u21 u21' u22 u22' H21 H22 eq21 eq2|u20 u2' H2' eq20 eq2|u21 u21' u22 u22' H21 H22 H2' eq21 eq2
	                     |u21 u21' u22 u22' H21 H22 eq21 eq2|u21 u21' u22 u22' H21 H22 H2' eq21 eq2];
	       subst; clear H2.
	- exists (BVar x); split; exact PS_Var.
	- exists (BBound n); split; exact PS_Bound.
	- specialize (IHu _ H11 _ H21) as [u1 [Hu11 Hu12]].
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (BApp u1 u2); split; refine (PS_App _ _); assumption.
	- inversion H11 as [| | | |u10 u11 H0 eq10 eq1| | |]; subst; clear H11; rename H0 into H11.
	  specialize (IHu _ (PS_Abs H11) _ (PS_Abs H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11' as [| | | |u10 u1 Hu11 eq10 eq1| | |]; clear Hu11'; subst.
	  inversion Hu12' as [| | | |u10 u1' Hu12 eq10 eq1| | |]; clear Hu12'; subst.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (bsubstb u1 O u2); split.
	  2: exact (psubstb_bsubstb Hu12 Hu22 (pvalue_psubstb H2' Hu22)).
	  exact (PS_Beta Hu11 Hu21 (pvalue_psubstb H2' Hu22)).
	- inversion H11 as [| | |a|u10 u11 H0 eq10 eq1| | |a]; subst; clear H11; rename H0 into H11.
	  2: inversion H; subst; inversion H1.
	  inversion H; clear H; subst.
	  specialize (IHu _ (PS_App PS_C H11) _ (PS_App PS_C H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11' as [| | | |u10 u1 Hu11 eq10 eq1| | |]; clear Hu11'; subst.
	  2: inversion H; subst; inversion H1.
	  inversion Hu12' as [| | | |u10 u1' Hu12 eq10 eq1| | |]; clear Hu12'; subst.
	  2: inversion H1; subst; inversion H3.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exact (ex_intro _ _ (conj (PS_BetaCl H0 Hu21)
	                             (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H2)
	                                (PS_Abs (PS_App PS_Bound (PS_App PS_Bound (psubstb_incr (psubstb_incr Hu22)))))))))).
	- inversion H12 as [| | |a|u10 u11 H0 eq10 eq1| | |a]; subst; clear H12; rename H0 into H12.
	  2: inversion H; subst; inversion H1.
	  inversion H; clear H; subst.
	  specialize (IHv _ (PS_App PS_C H12) _ (PS_App PS_C H22)) as [u1' [Hu11' Hu12']].
	  inversion Hu11' as [| | | |u10 u1 Hu11 eq10 eq1| | |]; clear Hu11'; subst.
	  2: inversion H; subst; inversion H1.
	  inversion Hu12' as [| | | |u10 u1' Hu12 eq10 eq1| | |]; clear Hu12'; subst.
	  2: inversion H1; subst; inversion H3.
	  specialize (IHu _ H11 _ H21) as [u2 [Hu21 Hu22]].
	  exact (ex_intro _ _ (conj (PS_BetaCr Hu21 H0 (pvalue_psubstb H2' Hu22))
	                             (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H2)
	                                (PS_Abs (PS_App PS_Bound (PS_App (psubstb_incr (psubstb_incr Hu22)) PS_Bound)))))))).
	- inversion H21 as [| | | |u10 u21 H0 eq10 eq1| | |]; subst; clear H21; rename H0 into H21.
	  specialize (IHu _ (PS_Abs H11) _ (PS_Abs H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11' as [| | | |u10 u1 Hu11 eq10 eq1| | |]; clear Hu11'; subst.
	  inversion Hu12' as [| | | |u10 u1' Hu12 eq10 eq1| | |]; clear Hu12'; subst.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (bsubstb u1 O u2); split.
	  1: exact (psubstb_bsubstb Hu11 Hu21 (pvalue_psubstb H1' Hu21)).
	  exact (PS_Beta Hu12 Hu22 (pvalue_psubstb H1' Hu21)).
	- specialize (IHu _ (PS_Abs H11) _ (PS_Abs H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11'; subst; clear Hu11'; rename H0 into Hu11, u' into u1.
	  inversion Hu12'; subst; clear Hu12'; rename H1 into Hu12.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (bsubstb u1 0 u2).
	  split; refine (psubstb_bsubstb _ _ _); try assumption; exact (pvalue_psubstb H2' Hu22).
	- inversion H12 as [| | | | | | |]; subst; clear H12; rename H0 into H12; inversion H1'.
	- inversion H21 as [| | |a|u20 u21 H0 eq10 eq1| | |a]; subst; clear H21; rename H0 into H21.
	  2: inversion H; subst; inversion H1.
	  inversion H; clear H; subst.
	  specialize (IHu _ (PS_App PS_C H11) _ (PS_App PS_C H21)) as [u2' [Hu21' Hu22']].
	  inversion Hu21' as [| | | |u20 u2 Hu21 eq10 eq1| | |]; clear Hu21'; subst.
	  2: inversion H; subst; inversion H1.
	  inversion Hu22' as [| | | |u20 u2' Hu22 eq10 eq1| | |]; clear Hu22'; subst.
	  2: inversion H1; subst; inversion H3.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exact (ex_intro _ _ (conj (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H0)
	                                (PS_Abs (PS_App PS_Bound (PS_App PS_Bound (psubstb_incr (psubstb_incr Hu21))))))))
	                             (PS_BetaCl H2 Hu22))).
	- specialize (IHu _ (PS_App PS_C H11) _ (PS_App PS_C H21)) as [u1 [IH11 IH12]].
	  specialize (IHv _ H12 _ H22) as [u2 [IH21 IH22]].
	  inversion IH11; subst.
	  2: inversion H1; subst; inversion H4.
	  inversion IH12; subst.
	  2: inversion H5; subst; inversion H7.
	  exact (ex_intro _ _ (conj
	     (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H3) (PS_Abs (PS_App PS_Bound (PS_App PS_Bound (psubstb_incr (psubstb_incr IH21))))))))
	     (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H6) (PS_Abs (PS_App PS_Bound (PS_App PS_Bound (psubstb_incr (psubstb_incr IH22)))))))))).
	- inversion H21; subst; inversion H2'.
	- inversion H2; subst.
	  2: inversion H3; subst; inversion H5.
	  2: inversion H11; subst; inversion H1'.
	  1,2: specialize (IHu _ H11 _ H1) as [u1 [IH11 IH12]].
	  1: inversion H4; subst; inversion H3; subst.
	  2: inversion H7.
	  1: specialize (IHv _ (PS_App PS_C H12) _ (PS_App PS_C H6)) as [u2 [IH21 IH22]].
	  1: inversion IH21; subst; [|inversion H5; subst; inversion H9].
	  1: inversion IH22; subst; [|inversion H10; subst; inversion H14].
	  1: exact (ex_intro _ _ (conj (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H8)
	                                    (PS_Abs (PS_App PS_Bound (PS_App (psubstb_incr (psubstb_incr IH11)) PS_Bound))))))
	                                (PS_BetaCr IH12 H13 (pvalue_psubstb H1' IH11)))).
	  specialize (IHv _ (PS_App PS_C H12) _ (PS_App PS_C H3)) as [u2 [IH21 IH22]].
	  inversion IH21; subst; [|inversion H4; subst; inversion H8].
	  inversion IH22; subst; [|inversion H9; subst; inversion H13].
	  exact (ex_intro _ _ (conj (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H7)
	                                 (PS_Abs (PS_App PS_Bound (PS_App (psubstb_incr (psubstb_incr IH11)) PS_Bound))))))
	                             (PS_App PS_C (PS_Abs (PS_App (psubstb_incr H10)
	                                 (PS_Abs (PS_App PS_Bound (PS_App (psubstb_incr (psubstb_incr IH12)) PS_Bound)))))))).
	- inversion H2; subst; rename H0 into H2'.
	  specialize (IH _ H1' _ H2') as [u'' [IH1 IH2]].
	  exists (BAbs u''); split; refine (PS_Abs _); assumption.
Qed.

Lemma beta_is_psubstb : forall {u v}, over_bcontext beta u v -> psubstb u v.
Proof using.
	intros u v H; apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & -> & ->)].
	induction c as [|c IH v|u c IH|c IH].
	2: exact (PS_App IH psubstb_refl).
	2: exact (PS_App psubstb_refl IH).
	2: exact (PS_Abs IH).
	cbn; inversion H as [u v H' eq1 eq2|u v eq1 eq2|V u H' eq1 eq2]; subst; clear H.
	1: exact (PS_Beta psubstb_refl psubstb_refl H').
	1: exact (PS_BetaCl psubstb_refl psubstb_refl).
	1: exact (PS_BetaCr psubstb_refl psubstb_refl H').
Qed.
Lemma psubstb_is_betas : forall {u v}, psubstb u v -> (over_bcontext beta)^* u v.
Proof using.
	intros u v H; induction H as [|x|n|u u' v v' _ IH1 _ IH2|u v _ IH|u u' v v' _ IH1 _ IH2 Hv'|u u' v v' _ IH1 _ IH2|u u' v v' _ IH1 _ IH2 Hv'].
	1,2,3: exact rt_refl.
	- refine (rt_trans (y:=BApp u' v) _ _).
	  1: clear - IH1; induction IH1 as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  4: clear - IH2; induction IH2 as [v v' H|v|v v' v'' _ IH1 _ IH2].
	  2,5: exact rt_refl.
	  2,4: exact (rt_trans IH1 IH2).
	  1: exact (rt_step (bctx_app_l H)).
	  1: exact (rt_step (bctx_app_r H)).
	- induction IH as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  1: exact (rt_step (bctx_abs H)).
	  1: exact rt_refl.
	  exact (rt_trans IH1 IH2).
	- refine (rt_trans (y:=BApp (BAbs u') v') (rt_trans (y:=BApp (BAbs u') v) _ _) (rt_step (bctx_step (Beta _ _ Hv')))).
	  1: clear - IH1; induction IH1 as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  4: clear - IH2; induction IH2 as [v v' H|v|v v' v'' _ IH1 _ IH2].
	  2,5: exact rt_refl.
	  2,4: exact (rt_trans IH1 IH2).
	  1: exact (rt_step (bctx_app_l (bctx_abs H))).
	  1: exact (rt_step (bctx_app_r H)).
	- refine (rt_trans (y:=BApp (BApp BCFelleisen u') v') (rt_trans (y:=BApp (BApp BCFelleisen u') v) _ _) (rt_step (bctx_step (BetaCl _ _)))).
	  1: clear - IH1; induction IH1 as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  4: clear - IH2; induction IH2 as [v v' H|v|v v' v'' _ IH1 _ IH2].
	  2,5: exact rt_refl.
	  2,4: exact (rt_trans IH1 IH2).
	  1: exact (rt_step (bctx_app_l (bctx_app_r H))).
	  1: exact (rt_step (bctx_app_r H)).
	- refine (rt_trans (rt_trans (y:=BApp u' (BApp BCFelleisen v)) _ _) (rt_step (bctx_step (BetaCr _ _ Hv')))).
	  1: clear - IH1; induction IH1 as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  4: clear - IH2; induction IH2 as [v v' H|v|v v' v'' _ IH1 _ IH2].
	  2,5: exact rt_refl.
	  2,4: exact (rt_trans IH1 IH2).
	  1: exact (rt_step (bctx_app_l H)).
	  1: exact (rt_step (bctx_app_r (bctx_app_r H))).
Qed.

Lemma confluence_beta : RewriteSystem.confluence eq (over_bcontext beta).
Proof using.
	exact (RewriteSystem.confluence_incl (@beta_is_psubstb) (@psubstb_is_betas)
	          (RewriteSystem.strong_confluence_is_confluence _ _ psubstb_strong_confluence)).
Qed.

Lemma bsubstb_nfb : forall u n v, (forall k, n <= k -> ~ bfb k u) -> bsubstb u n v = u.
Proof using.
	intros u n v H.
	rewrite <-(incr_nfb u n H), bsubstb_incr, (incr_nfb u n H); exact eq_refl.
Qed.

Lemma bfv_incr_iff : forall x u n, bfv x (incr_bound u n) <-> bfv x u.
Proof using.
	intros x u n; split; generalize dependent n; induction u as [|y|k|u IHu v IHv|u IH]; intros n H.
	- inversion H.
	- inversion H; exact BFV_Var.
	- inversion H.
	- inversion H; [exact (BFV_App_l (IHu _ H1))|exact (BFV_App_r (IHv _ H1))].
	- inversion H; exact (BFV_Abs (IH _ H1)).
	- inversion H.
	- inversion H; exact BFV_Var.
	- inversion H.
	- inversion H; [exact (BFV_App_l (IHu _ H1))|exact (BFV_App_r (IHv _ H1))].
	- inversion H; exact (BFV_Abs (IH _ H1)).
Qed.
Lemma bfb_incr_iff : forall k u n, bfb (if n <=? k then S k else k) (incr_bound u n) <-> bfb k u.
Proof using.
	intros k u n; split; generalize dependent n; generalize dependent k; induction u as [|y|m|u IHu v IHv|u IH]; intros k n H.
	- inversion H.
	- inversion H.
	- inversion H; subst.
	  destruct (le_gt_cases n m) as [nlem|mltn].
	  1: rewrite (proj2 (leb_le _ _) nlem) in H2.
	  2: rewrite (proj2 (leb_gt _ _) mltn) in H2; subst.
	  1,2: destruct (le_gt_cases n k) as [nlek|kltn].
	  1,3: rewrite (proj2 (leb_le _ _) nlek) in *.
	  3,4: rewrite (proj2 (leb_gt _ _) kltn) in *; subst.
	  1: injection H2 as <-; exact BFB_Var.
	  1: contradiction (lt_neq _ _ (lt_le_trans _ _ _ mltn (le_S _ _ nlek)) eq_refl).
	  1: contradiction (lt_neq _ _ (lt_le_trans _ _ _ kltn (le_S _ _ nlem)) eq_refl).
	  1: exact BFB_Var.
	- inversion H; [exact (BFB_App_l (IHu _ _ H2))|exact (BFB_App_r (IHv _ _ H2))].
	- inversion H; specialize (IH (S k) (S n)); rewrite (eq_refl : (S _ <=? S _) = (n <=? k)) in IH.
	  destruct (n <=? k); exact (BFB_Abs (IH H2)).
	- inversion H.
	- inversion H.
	- inversion H; exact BFB_Var.
	- inversion H; [exact (BFB_App_l (IHu _ _ H2))|exact (BFB_App_r (IHv _ _ H2))].
	- inversion H; specialize (IH (S k) (S n)); rewrite (eq_refl : (S _ <=? S _) = (n <=? k)) in IH.
	  destruct (n <=? k); exact (BFB_Abs (IH H2)).
Qed.

End UntypedLambdaF.
