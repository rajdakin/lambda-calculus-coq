Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Relations.

Inductive occpart := OFun | OArg | OBdy.

Declare Custom Entry lterms.
Declare Custom Entry bterms.

Module Type UntypedLambdaT.
Declare Module Export Vars : VarPropsT.
Declare Module VarMapReqs : Assoc.AssocReqs
	with Definition key := V
	with Definition key_dec := dec_V.
Module VarMap := Assoc.Make(VarMapReqs).

Inductive lterm : Type :=
	| LVar : V -> lterm
	| LApp : lterm -> lterm -> lterm
	| LAbs : V -> lterm -> lterm.

Coercion LVar : V >-> lterm.
Coercion LApp : lterm >-> Funclass.

Module Import UntypedLNotation.
Notation "{{  l  }}" := l (l custom lterms).

Notation "{ v }" := v (in custom lterms at level 0, v constr).
Notation "( v )" := v (in custom lterms at level 0, v custom lterms at level 2).
Notation "^ x , M" := (LAbs x M) (in custom lterms at level 2, x constr, M custom lterms, format "^ x ,  M").
Notation "M N" := (LApp M N) (in custom lterms at level 1, M custom lterms, N custom lterms, left associativity).
End UntypedLNotation.

Inductive bterm : Type :=
	| BVar : V -> bterm
	| BBound : nat -> bterm
	| BApp : bterm -> bterm -> bterm
	| BAbs : bterm -> bterm.

Coercion BApp : bterm >-> Funclass.

Module Import UntypedBNotation.
Notation "<{  b  }>" := b (b custom bterms).

Notation "{ v }" := v (in custom bterms at level 0, v constr).
Notation "( v )" := v (in custom bterms at level 0, v custom bterms at level 2).
Notation "< n >" := (BBound n) (in custom bterms at level 0, n constr at level 1, format "< n >").
Notation "^ M" := (BAbs M) (in custom bterms at level 2, M custom bterms, format "^ M").
Notation "M N" := (BApp M N) (in custom bterms at level 1, M custom bterms, N custom bterms, left associativity).
End UntypedBNotation.

Fixpoint bruijn_of_var x l n := match l with
	| [] => BVar x
	| hd :: tl => if dec_V hd x then BBound n else bruijn_of_var x tl (S n)
end.
Fixpoint bruijn_of u l := match u with
	| LVar x => bruijn_of_var x l O
	| LApp u v => BApp (bruijn_of u l) (bruijn_of v l)
	| LAbs x u => BAbs (bruijn_of u (x :: l))
end.
Fixpoint of_bruijn (u : bterm) n := match u with
	| BVar x => LVar x
	| BBound i => LVar (Nat.sub n (S i))
	| BApp u v => LApp (of_bruijn u n) (of_bruijn v n)
	| BAbs u => LAbs n (of_bruijn u (S n))
end.

Fixpoint valid_lpath u p := match p, u with
	| [], _ => True
	| OFun :: p, LApp u v => valid_lpath u p
	| OArg :: p, LApp u v => valid_lpath v p
	| OBdy :: p, LAbs _ u => valid_lpath u p
	| _ :: _, _ => False
end.
Fixpoint valid_bpath u p := match p, u with
	| [], _ => True
	| OFun :: p, BApp u v => valid_bpath u p
	| OArg :: p, BApp u v => valid_bpath v p
	| OBdy :: p, BAbs u => valid_bpath u p
	| _ :: _, _ => False
end.

Fixpoint sublterm (u : lterm) (p : list occpart) : valid_lpath u p -> lterm.
Proof using.
	destruct p as [|[| |] p].
	1: intros _; exact u.
	1-3: destruct u as [x|u v|x u]; intros H; try contradiction H; exact (sublterm _ p H).
Defined.
Fixpoint subbterm (u : bterm) (p : list occpart) : valid_bpath u p -> bterm.
Proof using.
	destruct p as [|[| |] p].
	1: intros _; exact u.
	1-3: destruct u as [x|n|u v|u]; intros H; try contradiction H; exact (subbterm _ p H).
Defined.

Inductive lcontext : Type :=
	| LCHole : lcontext
	| LCApp_l : lcontext -> lterm -> lcontext
	| LCApp_r : lterm -> lcontext -> lcontext
	| LCAbs : V -> lcontext -> lcontext.

Fixpoint subst_lcontext (c : lcontext) u {struct c} : lterm := match c with
	| LCHole => u
	| LCApp_l c' v => (subst_lcontext c' u) v
	| LCApp_r v c' => v (subst_lcontext c' u)
	| LCAbs x c' => LAbs x (subst_lcontext c' u)
end.

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

Fixpoint csubst_lcontext c c' := match c with
	| LCHole => c'
	| LCApp_l c v => LCApp_l (csubst_lcontext c c') v
	| LCApp_r v c => LCApp_r v (csubst_lcontext c c')
	| LCAbs x c => LCAbs x (csubst_lcontext c c')
end.
Fixpoint csubst_bcontext c c' := match c with
	| BCHole => c'
	| BCApp_l c v => BCApp_l (csubst_bcontext c c') v
	| BCApp_r v c => BCApp_r v (csubst_bcontext c c')
	| BCAbs c => BCAbs (csubst_bcontext c c')
end.

Fixpoint bcontext_of c l := match c with
	| LCHole => BCHole
	| LCApp_l c' v => BCApp_l (bcontext_of c' l) (bruijn_of v l)
	| LCApp_r u c' => BCApp_r (bruijn_of u l) (bcontext_of c' l)
	| LCAbs x c' => BCAbs (bcontext_of c' (x :: l))
end.
Fixpoint of_bcontext c n := match c with
	| BCHole => LCHole
	| BCApp_l c' v => LCApp_l (of_bcontext c' n) (of_bruijn v n)
	| BCApp_r u c' => LCApp_r (of_bruijn u n) (of_bcontext c' n)
	| BCAbs c' => LCAbs n (of_bcontext c' (S n))
end.
Fixpoint lsubst_bcontext c := match c with
	| LCHole => []
	| LCApp_l c' v => lsubst_bcontext c'
	| LCApp_r u c' => lsubst_bcontext c'
	| LCAbs x c' => lsubst_bcontext c' ++ [x]
end.
Fixpoint offset_lcontext c := match c with
	| BCHole => O
	| BCApp_l c' v => offset_lcontext c'
	| BCApp_r u c' => offset_lcontext c'
	| BCAbs c' => S (offset_lcontext c')
end.

Parameter bruijn_of_lsubst : forall c u l, bruijn_of (subst_lcontext c u) l = subst_bcontext (bcontext_of c l) (bruijn_of u (lsubst_bcontext c ++ l)).
Parameter of_bruijn_csubst : forall c u n, of_bruijn (subst_bcontext c u) n = subst_lcontext (of_bcontext c n) (of_bruijn u (offset_lcontext c + n)).
Parameter lsubst_bctx_of : forall c n, lsubst_bcontext (of_bcontext c n) = rev (map V_of_nat (seq n (offset_lcontext c))).

Inductive over_lcontext {R : relation lterm} | : relation lterm :=
	| lctx_step : forall {u v}, R u v -> over_lcontext u v
	| lctx_app_l : forall {u u'} [v], over_lcontext u u' -> over_lcontext (LApp u v) (LApp u' v)
	| lctx_app_r : forall [u] {v v'}, over_lcontext v v' -> over_lcontext (LApp u v) (LApp u v')
	| lctx_abs : forall [x] {u v}, over_lcontext u v -> over_lcontext (LAbs x u) (LAbs x v).
Inductive over_bcontext {R : relation bterm} | : relation bterm :=
	| bctx_step : forall {u v}, R u v -> over_bcontext u v
	| bctx_app_l : forall {u u'} [v], over_bcontext u u' -> over_bcontext (BApp u v) (BApp u' v)
	| bctx_app_r : forall [u] {v v'}, over_bcontext v v' -> over_bcontext (BApp u v) (BApp u v')
	| bctx_abs : forall {u v}, over_bcontext u v -> over_bcontext (BAbs u) (BAbs v).
Arguments over_lcontext _ _ _ : clear implicits.
Arguments over_bcontext _ _ _ : clear implicits.

Parameter over_lcontext_iff : forall R u v, over_lcontext R u v <-> exists C u' v', R u' v' /\ u = subst_lcontext C u' /\ v = subst_lcontext C v'.
Parameter over_bcontext_iff : forall R u v, over_bcontext R u v <-> exists C u' v', R u' v' /\ u = subst_bcontext C u' /\ v = subst_bcontext C v'.
Parameter over_lcontext_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_lcontext R1) (over_lcontext R2).
Parameter over_bcontext_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_bcontext R1) (over_bcontext R2).
Parameter over_lcontext_union : forall R1 R2 u v, over_lcontext (union _ R1 R2) u v <-> over_lcontext R1 u v \/ over_lcontext R2 u v.
Parameter over_bcontext_union : forall R1 R2 u v, over_bcontext (union _ R1 R2) u v <-> over_bcontext R1 u v \/ over_bcontext R2 u v.
Parameter over_lcontext_transp : forall {R u v}, over_lcontext R u v -> over_lcontext (transp R) v u.
Parameter over_lcontext_transp_comm : forall {R u v}, (over_lcontext R)^t u v <-> over_lcontext (R^t) u v.
Parameter over_bcontext_transp : forall {R u v}, over_bcontext R u v -> over_bcontext (transp R) v u.
Parameter over_bcontext_transp_comm : forall {R u v}, (over_bcontext R)^t u v <-> over_bcontext (R^t) u v.
Parameter clos_rt_over_bcontext_ctx : forall {R} c [u v], (over_bcontext R)^* u v -> (over_bcontext R)^* (subst_bcontext c u) (subst_bcontext c v).

Fixpoint lsubst u x v := match u with
	| LVar y => if dec_V x y then v else u
	| LApp u1 u2 => LApp (lsubst u1 x v) (lsubst u2 x v)
	| LAbs y u => LAbs y (lsubst u x v)
end.
Fixpoint lsubst_full u x v := match u with
	| LVar y => if dec_V x y then v else u
	| LApp u1 u2 => LApp (lsubst_full u1 x v) (lsubst_full u2 x v)
	| LAbs y u => if dec_V x y then LAbs y u else LAbs y (lsubst_full u x v)
end.
Fixpoint incr_bound u k := match u with
	| BVar y => BVar y
	| BBound n => BBound (if k <=? n then S n else n)
	| BApp u v => BApp (incr_bound u k) (incr_bound v k)
	| BAbs u => BAbs (incr_bound u (S k))
end.
Fixpoint bsubst u x v := match u with
	| BVar y => if dec_V x y then v else u
	| BBound _ => u
	| BApp u1 u2 => BApp (bsubst u1 x v) (bsubst u2 x v)
	| BAbs u => BAbs (bsubst u x (incr_bound v O))
end.
Fixpoint bsubstb u n v := match u with
	| BVar y => u
	| BBound k => if k <? n then BBound k else if k =? n then v else BBound (pred k)
	| BApp u1 u2 => BApp (bsubstb u1 n v) (bsubstb u2 n v)
	| BAbs u => BAbs (bsubstb u (S n) (incr_bound v O))
end.

Inductive lfv {x : V} | : lterm -> Prop :=
	| LFV_Var : lfv x
	| LFV_App_l : forall {u v}, lfv u -> lfv (LApp u v)
	| LFV_App_r : forall {u v}, lfv v -> lfv (LApp u v)
	| LFV_Abs : forall {y u}, x <> y -> lfv u -> lfv {{ ^y, {u} }}.
Inductive lbv {x : V} | : lterm -> Prop :=
	| LBV_Bound : forall {u}, lbv {{ ^x, {u} }}
	| LBV_App_l : forall {u v}, lbv u -> lbv (LApp u v)
	| LBV_App_r : forall {u v}, lbv v -> lbv (LApp u v)
	| LBV_Abs : forall {y u}, lbv u -> lbv {{ ^y, {u} }}.
Arguments lfv _ _ : clear implicits.
Arguments lbv _ _ : clear implicits.
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

Inductive alpha : lterm -> lterm -> Prop :=
	| Alpha : forall x y u (H1 : ~ lbv x u) (H2 : ~ lbv y u) (H3 : ~ lfv y u),
		alpha {{ ^x, {u} }} {{ ^y, {lsubst u x y} }}.
Definition alpha_eq : lterm -> lterm -> Prop := (over_lcontext alpha)^*.

Section Alpha.

Fixpoint min_gt_vars u := match u with
	| LVar x => match onat_of_V x with None => O | Some n => S n end
	| LApp u v => max (min_gt_vars u) (min_gt_vars v)
	| LAbs x u => max (match onat_of_V x with None => O | Some n => S n end) (min_gt_vars u)
end.
Fixpoint min_gt_bvars u := match u with
	| BVar x => match onat_of_V x with None => O | Some n => S n end
	| BBound _ => O
	| BApp u v => max (min_gt_bvars u) (min_gt_bvars v)
	| BAbs u => min_gt_bvars u
end.
Fixpoint min_gt_fbound u := match u with
	| BVar x => O
	| BBound n => S n
	| BApp u v => max (min_gt_fbound u) (min_gt_fbound v)
	| BAbs u => pred (min_gt_fbound u)
end.

Parameter min_gt_vars_fv : forall u n, min_gt_vars u <= n -> ~ lfv (V_of_nat n) u.
Parameter min_gt_vars_bv : forall u n, min_gt_vars u <= n -> ~ lbv (V_of_nat n) u.
Parameter min_gt_bvars_fv : forall u n, min_gt_bvars u <= n -> ~ bfv (V_of_nat n) u.
Parameter min_gt_fbound_fb : forall u n, min_gt_fbound u <= n -> ~ bfb n u.
Parameter lbv_of_bruijn_inv : forall x u n, lbv x (of_bruijn u n) -> exists k, x = V_of_nat k /\ n <= k.
Parameter lfv_of_bruijn_inv : forall x u n,
	lfv x (of_bruijn u n) -> (fix inner u o := match u with
		| BVar y => x = y
		| BBound i => o <= i /\ x = ((o + n) - (S i))%nat
		| BApp u v => inner u o \/ inner v o
		| BAbs u => inner u (S o)
	end) u O.
Parameter lfv_of_bruijn_of : forall (x : V) u l n, In x l -> length l + min_gt_vars x <= n -> ~ lfv x (of_bruijn (bruijn_of u l) n).
Parameter alpha_eq_of_bruijn_of : forall u n, min_gt_vars u <= n -> alpha_eq (of_bruijn (bruijn_of u []) n) u.
Parameter lsubst_same : forall u x, lsubst u x x = u.
Parameter lsubst_full_same : forall u x, lsubst_full u x x = u.
Parameter lsubst_full_nfv : forall u x v, ~ lfv x u -> lsubst_full u x v = u.
Parameter alpha_sym : inclusion alpha alpha^t.
Parameter alpha_transp : same_relation alpha alpha^t.
Parameter alpha_eq_sym : inclusion alpha_eq alpha_eq^t.
Parameter alpha_eq_transp : same_relation alpha_eq alpha_eq^t.
Parameter alpha_eq_iff : forall u v l, alpha_eq u v <-> bruijn_of u l = bruijn_of v l.
Parameter always_subst : forall u x v, exists u', alpha_eq u u' /\ ~ lbv x u' /\ forall x, ~ (lfv x v /\ lbv x u').
Parameter alpha_eq_Var : forall (x : V), alpha_eq x x.
Parameter alpha_eq_App : forall {u u' v v'}, alpha_eq u u' -> alpha_eq v v' -> alpha_eq (u v) (u' v').
Parameter alpha_eq_Abs : forall (x : V) u u', alpha_eq u u' -> alpha_eq (LAbs x u) (LAbs x u').
Parameter alpha_eq_Var_inv : forall (x : V) v, alpha_eq x v -> v = x.
Parameter alpha_eq_App_inv : forall {u u' v}, alpha_eq (LApp u u') v -> exists v1 v2, v = LApp v1 v2 /\ alpha_eq u v1 /\ alpha_eq u' v2.

#[export] Declare Instance alpha_eq_equiv : Equiv alpha_eq.

End Alpha.

Parameter bruijn_of_var_eq : forall x l n,
	(exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ bruijn_of_var x l n = BBound (length l1 + n)) \/
	(~ In x l /\ bruijn_of_var x l n = BVar x).
Parameter min_gt_bvars_le_vars : forall u l, min_gt_bvars (bruijn_of u l) <= min_gt_vars u.
Parameter min_gt_fbound_of : forall u l, min_gt_fbound (bruijn_of u l) <= length l.
Parameter lsubst_is_full : forall u x v, ~ lbv x u -> lsubst u x v = lsubst_full u x v.
Parameter bsubst_nfv : forall u x v, ~ bfv x u -> bsubst u x v = u.
Parameter bruijn_of_fv : forall u l x, bfv x (bruijn_of u l) <-> lfv x u /\ ~ In x l.
Parameter bruijn_of_app_in : forall u l1 x l2, In x l1 -> bruijn_of u (l1 ++ x :: l2) = incr_bound (bruijn_of u (l1 ++ l2)) (length l1).
Parameter bruijn_of_app_nfv : forall u l1 x l2, ~ lfv x u -> bruijn_of u (l1 ++ x :: l2) = incr_bound (bruijn_of u (l1 ++ l2)) (length l1).
Parameter bruijn_of_cons_nfv : forall u x l, ~ lfv x u -> bruijn_of u (x :: l) = incr_bound (bruijn_of u l) O.
Parameter of_lsubst_is_bsubst_of : forall u x v l,
	(forall y, lbv y u -> ~ lfv y v) -> ~ In x l ->
	bruijn_of (lsubst_full u x v) l = bsubst (bruijn_of u l) x (bruijn_of v l).
Parameter of_lsubst_is_bsubstb_of : forall u x v l1 l2,
	(forall y, lbv y u -> ~ lfv y v) -> ~ In x l1 ->
	bruijn_of (lsubst_full u x v) (l1 ++ l2) = bsubstb (bruijn_of u (l1 ++ x :: l2)) (length l1) (bruijn_of v (l1 ++ l2)).
Parameter of_lsubst_is_bsubstb_of' : forall u x v l1 l2,
	(forall y, lbv y u -> ~ lfv y v) -> ~ In x l1 ->
	bruijn_of (lsubst_full u x v) (l1 ++ x :: l2) =
	  bsubstb (incr_bound (bruijn_of u (l1 ++ x :: l2)) (S (length l1))) (length l1) (bruijn_of v (l1 ++ x :: l2)).
Parameter subst_alpha : forall u u' x v v', alpha_eq u u' -> alpha_eq v v' ->
	(forall y, lbv y u -> ~ lfv y v) ->
	(forall y, lbv y u' -> ~ lfv y v') ->
	alpha_eq (lsubst_full u x v) (lsubst_full u' x v').
Parameter bruijn_of_bruijn_eq : forall u n k, min_gt_bvars u <= n -> min_gt_fbound u <= k ->
	bruijn_of (of_bruijn u (n + k)) (rev (map V_of_nat (seq n k))) = u.
Parameter bruijn_of_bruijn_of : forall u l n, min_gt_vars u <= n ->
	bruijn_of u l = bruijn_of (of_bruijn (bruijn_of u l) (length l + n)) (rev (map V_of_nat (seq n (length l)))).
Parameter alpha_eq_Abs_inv : forall x u v, alpha_eq (LAbs x u) v -> exists y v', v = LAbs y v' /\ bruijn_of u [x] = bruijn_of v' [y].

Definition arrow (R : relation bterm) : relation lterm := fun u v => over_bcontext R (bruijn_of u []) (bruijn_of v []).
Definition congruence (R : relation bterm) : relation lterm := union _ alpha_eq (clos_refl_sym_trans (arrow R)).

Parameter arrow_alphaeq : forall {R u u' v' v}, alpha_eq u u' -> arrow R u' v' -> alpha_eq v' v -> arrow R u v.
Parameter congruence_alphaeq : forall {R u u' v' v}, alpha_eq u u' -> congruence R u' v' -> alpha_eq v' v -> congruence R u v.

Declare Instance arrow_alpha_eq R : Respects alpha_eq (arrow R).
Declare Instance congruence_alpha_eq R : Respects alpha_eq (congruence R).

Parameter congruence_refl : forall {R u}, congruence R u u.
Parameter congruence_trans : forall {R u v w}, congruence R u v -> congruence R v w -> congruence R u w.
Parameter congruence_sym : forall {R u v}, congruence R u v -> congruence R v u.

Declare Instance congruence_equiv R : Equiv (congruence R).

Parameter congruence_Var : forall {R} (x : V), congruence R x x.
Parameter congruence_App : forall {R} {u u' v v'}, congruence R u u' -> congruence R v v' -> congruence R (u v) (u' v').
(* congruence_Abs is false, for example for the weak head beta-reduction *)

Definition is_arrow_of (Rl : relation lterm) (R : relation bterm) :=
	forall u v, arrow R u v <-> exists u' v', alpha_eq u u' /\ alpha_eq v v' /\ over_lcontext Rl u' v'.
Parameter is_arrow_is_congruence : forall {Rl R},
	is_arrow_of Rl R -> forall u v, congruence R u v <-> (over_lcontext (union _ alpha (union _ Rl Rl^t)))^* u v.
Parameter arrow_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (arrow R1) (arrow R2).
Parameter congruence_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (congruence R1) (congruence R2).

Module Import ArrowNotation.
Notation "u -->_ R v" := (arrow R u v) (at level 70, R at level 5, no associativity, format "u  -->_ R  v").
Notation "u -->_ R ^+ v" := (arrow R^+ u v) (at level 70, R at level 5, no associativity, format "u  -->_ R ^+  v").
Notation "u -->_ R ^* v" := (arrow R^* u v) (at level 70, R at level 5, no associativity, format "u  -->_ R ^*  v").
Notation "u ===_ R v" := (congruence R u v) (at level 70, R at level 5, no associativity, format "u  ===_ R  v").
End ArrowNotation.

Parameter le_is_ex_add : forall m n, m <= n -> exists k, n = Nat.add k m.
Parameter incr_nfb : forall u n, (forall k, n <= k -> ~ bfb k u) -> incr_bound u n = u.

Fixpoint babstract u l n := match u with
	| BVar x => bruijn_of_var x l n
	| BBound k => BBound (if k <? n then k else k + length l)
	| BApp u v => BApp (babstract u l n) (babstract v l n)
	| BAbs u => BAbs (babstract u l (S n))
end.
Fixpoint bconcrete u f := match u with
	| BVar x => BVar x
	| BBound k => f k
	| BApp u v => BApp (bconcrete u f) (bconcrete v f)
	| BAbs u => BAbs (bconcrete u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
end.

Parameter bruijn_of_app : forall u l1 l2 l3, (forall x, In x l2 -> ~ In x l3) ->
	bruijn_of u (l1 ++ l2 ++ l3) = babstract (bruijn_of u (l1 ++ l3)) l2 (length l1).
Parameter bruijn_of_app_l : forall u l1 l2, (forall x, In x l1 -> ~ In x l2) -> bruijn_of u (l1 ++ l2) = babstract (bruijn_of u l2) l1 O.
Parameter bruijn_of_app_r : forall u l1 l2, bruijn_of u (l1 ++ l2) = babstract (bruijn_of u l1) l2 (length l1).
Parameter bconcrete_ext : forall u f1 f2, (forall k, bfb k u -> f1 k = f2 k) -> bconcrete u f1 = bconcrete u f2.
Parameter babstract_bconcrete : forall u l n,
	bconcrete (babstract u l n) (fun k => if k <? n then BBound k else nth (map BVar l) (k - n) (BBound (k - length l))) = u.
Parameter bconcrete_bsubst : forall u n v,
	bconcrete u (fun k => if k <? n then BBound k else if k =? n then v else BBound (pred k)) = bsubstb u n v.

Inductive beta : relation bterm :=
	| Beta : forall u v, beta <{ (^{u}) {v} }> (bsubstb u O v).
Inductive lbeta : relation lterm :=
	| LBeta : forall x u v, (forall y, lbv y u -> ~ lfv y v) -> lbeta {{ (^x, {u}) {v} }} (lsubst_full u x v).

Parameter beta_is_lbeta : is_arrow_of lbeta beta.
Parameter ctx_beta_Var_inv : forall x v, ~ (over_bcontext beta) (BVar x) v.
Parameter ctx_beta_App_inv : forall u v w, over_bcontext beta <{ {u} {v} }> w ->
	(exists u', u = BAbs u' /\ w = bsubstb u' O v) \/
	(exists u', over_bcontext beta u u' /\ w = BApp u' v) \/ (exists v', over_bcontext beta v v' /\ w = BApp u v').
Parameter ctx_beta_Abs_inv : forall u v, over_bcontext beta (BAbs u) v ->
	exists v', over_bcontext beta u v' /\ v = BAbs v'.
Parameter Beta_Var_inv : forall (x : V) v, ~ x -->_beta v.
Parameter Beta_App_inv : forall u v w, {{ {u} {v} }} -->_beta w ->
	(exists x u' v', (forall y, ~ (lfv y v' /\ lbv y u')) /\ alpha_eq u (LAbs x u') /\ alpha_eq v v' /\ alpha_eq w (lsubst_full u' x v')) \/
	(exists u' v', u -->_beta u' /\ alpha_eq v v' /\ w = u' v') \/ (exists u' v', alpha_eq u u' /\ v -->_beta v' /\ w = u' v').
Parameter Beta_Abs_inv : forall x u v, (LAbs x u) -->_beta v ->
	exists y u' v', alpha_eq (LAbs x u) (LAbs y u') /\ u' -->_beta v' /\ alpha_eq (LAbs y v') v.

Definition normal_form := RewriteSystem.normal_form (arrow beta).
Definition normalizable := RewriteSystem.normalizable (arrow beta).
Definition strong_normalizable:= RewriteSystem.strong_normalizable (arrow beta).

Definition delta := {{ ^0, {0} {0} }}.
Definition Omega := delta delta.

Parameter alpha_delta_delta : forall v, alpha_eq delta v <-> exists x, v = LAbs x (x x).
Parameter beta_Omega_Omega : forall u v, alpha_eq u Omega -> u -->_beta v <-> alpha_eq v Omega.

Inductive eta : relation bterm :=
	| Eta : forall u, eta (BAbs (BApp (incr_bound u O) (BBound O))) u.
Definition leta u v := exists x, ~ lfv x v /\ u = LAbs x (v x).

Parameter eta_is_leta : is_arrow_of leta eta.

Inductive psubst_b : relation bterm :=
	| PS_Var : forall {x}, psubst_b (BVar x) (BVar x)
	| PS_Bound : forall {n}, psubst_b (BBound n) (BBound n)
	| PS_App : forall {u u' v v'}, psubst_b u u' -> psubst_b v v' -> psubst_b (BApp u v) (BApp u' v')
	| PS_Abs : forall {u u'}, psubst_b u u' -> psubst_b (BAbs u) (BAbs u')
	| PS_Beta : forall {u u' v v'}, psubst_b u u' -> psubst_b v v' -> psubst_b (BApp (BAbs u) v) (bsubstb u' O v').

Parameter psubst_b_refl : forall {u}, psubst_b u u.
Parameter incr_bound_comm : forall {u n1 n2}, n1 <= n2 -> incr_bound (incr_bound u n2) n1 = incr_bound (incr_bound u n1) (S n2).
Parameter incr_bsubstb_le : forall {u n v k}, n <= k -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u (S k)) n (incr_bound v k).
Parameter incr_bsubstb_ge : forall {u n v k}, k <= n -> incr_bound (bsubstb u n v) k = bsubstb (incr_bound u k) (S n) (incr_bound v k).
Parameter bsubstb_incr : forall {u n v}, bsubstb (incr_bound u n) n v = u.
Parameter bsubstb_comm : forall {u1 u2 u3 n1 n2}, n1 <= n2 ->
	bsubstb (bsubstb u1 n1 u2) n2 u3 = bsubstb (bsubstb u1 (S n2) (incr_bound u3 n1)) n1 (bsubstb u2 n2 u3).
Parameter psubst_b_bsubstb : forall {u1 u2 u1' u2' n}, psubst_b u1 u1' -> psubst_b u2 u2' -> psubst_b (bsubstb u1 n u2) (bsubstb u1' n u2').
Parameter psubst_b_strong_confluence : RewriteSystem.strong_confluence eq psubst_b.
Parameter arrow_is_psubst_b : forall {u v}, over_bcontext beta u v -> psubst_b u v.
Parameter psubst_b_is_arrows : forall {u v}, psubst_b u v -> (over_bcontext beta)^* u v.
Parameter confluence_beta : RewriteSystem.confluence eq (over_bcontext beta).
Parameter confluence_arrow_beta : RewriteSystem.confluence alpha_eq (arrow beta).
Parameter normal_form_of_if : forall u u', bruijn_of u [] = u' -> (forall v', ~ over_bcontext beta u' v') -> normal_form u.
Parameter bsubstb_nfb : forall u n v, (forall k, n <= k -> ~ bfb k u) -> bsubstb u n v = u.
Parameter bfv_incr_iff : forall x u n, bfv x (incr_bound u n) <-> bfv x u.
Parameter bfb_incr_iff : forall k u n, bfb (if n <=? k then S k else k) (incr_bound u n) <-> bfb k u.
Parameter bfb_incr_eq : forall u n, ~ bfb n (incr_bound u n).

End UntypedLambdaT.

Module UntypedLambda (Vars0 : VarPropsT) <: UntypedLambdaT.
Module Export Vars := Vars0.
Module VarMapReqs <: Assoc.AssocReqs.
Definition key := V.
Definition key_dec := dec_V.
End VarMapReqs.
Module VarMap := Assoc.Make(VarMapReqs).

Inductive lterm : Type :=
	| LVar : V -> lterm
	| LApp : lterm -> lterm -> lterm
	| LAbs : V -> lterm -> lterm.

Coercion LVar : V >-> lterm.
Coercion LApp : lterm >-> Funclass.

Module Import UntypedLNotation.
Notation "{{  l  }}" := l (l custom lterms).

Notation "{ v }" := v (in custom lterms at level 0, v constr).
Notation "( v )" := v (in custom lterms at level 0, v custom lterms at level 2).
Notation "^ x , M" := (LAbs x M) (in custom lterms at level 2, x constr, M custom lterms, format "^ x ,  M").
Notation "M N" := (LApp M N) (in custom lterms at level 1, M custom lterms, N custom lterms, left associativity).
End UntypedLNotation.

Inductive bterm : Type :=
	| BVar : V -> bterm
	| BBound : nat -> bterm
	| BApp : bterm -> bterm -> bterm
	| BAbs : bterm -> bterm.

Coercion BApp : bterm >-> Funclass.

Module Import UntypedBNotation.
Notation "<{  b  }>" := b (b custom bterms).

Notation "{ v }" := v (in custom bterms at level 0, v constr).
Notation "( v )" := v (in custom bterms at level 0, v custom bterms at level 2).
Notation "< n >" := (BBound n) (in custom bterms at level 0, n constr at level 1, format "< n >").
Notation "^ M" := (BAbs M) (in custom bterms at level 2, M custom bterms, format "^ M").
Notation "M N" := (BApp M N) (in custom bterms at level 1, M custom bterms, N custom bterms, left associativity).
End UntypedBNotation.

Implicit Types (x y : V).

Fixpoint bruijn_of_var x l n := match l with
	| [] => BVar x
	| hd :: tl => if dec_V hd x then BBound n else bruijn_of_var x tl (S n)
end.
Fixpoint bruijn_of u l := match u with
	| LVar x => bruijn_of_var x l O
	| LApp u v => BApp (bruijn_of u l) (bruijn_of v l)
	| LAbs x u => BAbs (bruijn_of u (x :: l))
end.
Fixpoint of_bruijn (u : bterm) n := match u with
	| BVar x => LVar x
	| BBound i => LVar (Nat.sub n (S i))
	| BApp u v => LApp (of_bruijn u n) (of_bruijn v n)
	| BAbs u => LAbs n (of_bruijn u (S n))
end.

Fixpoint valid_lpath u p := match p, u with
	| [], _ => True
	| OFun :: p, LApp u v => valid_lpath u p
	| OArg :: p, LApp u v => valid_lpath v p
	| OBdy :: p, LAbs _ u => valid_lpath u p
	| _ :: _, _ => False
end.
Fixpoint valid_bpath u p := match p, u with
	| [], _ => True
	| OFun :: p, BApp u v => valid_bpath u p
	| OArg :: p, BApp u v => valid_bpath v p
	| OBdy :: p, BAbs u => valid_bpath u p
	| _ :: _, _ => False
end.

Fixpoint sublterm (u : lterm) (p : list occpart) : valid_lpath u p -> lterm.
Proof using.
	destruct p as [|[| |] p].
	1: intros _; exact u.
	1-3: destruct u as [x|u v|x u]; intros H; try contradiction H; exact (sublterm _ p H).
Defined.
Fixpoint subbterm (u : bterm) (p : list occpart) : valid_bpath u p -> bterm.
Proof using.
	destruct p as [|[| |] p].
	1: intros _; exact u.
	1-3: destruct u as [x|n|u v|u]; intros H; try contradiction H; exact (subbterm _ p H).
Defined.

Inductive lcontext : Type :=
	| LCHole : lcontext
	| LCApp_l : lcontext -> lterm -> lcontext
	| LCApp_r : lterm -> lcontext -> lcontext
	| LCAbs : V -> lcontext -> lcontext.

Fixpoint subst_lcontext (c : lcontext) u {struct c} : lterm := match c with
	| LCHole => u
	| LCApp_l c' v => (subst_lcontext c' u) v
	| LCApp_r v c' => v (subst_lcontext c' u)
	| LCAbs x c' => LAbs x (subst_lcontext c' u)
end.

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

Fixpoint csubst_lcontext c c' := match c with
	| LCHole => c'
	| LCApp_l c v => LCApp_l (csubst_lcontext c c') v
	| LCApp_r v c => LCApp_r v (csubst_lcontext c c')
	| LCAbs x c => LCAbs x (csubst_lcontext c c')
end.
Fixpoint csubst_bcontext c c' := match c with
	| BCHole => c'
	| BCApp_l c v => BCApp_l (csubst_bcontext c c') v
	| BCApp_r v c => BCApp_r v (csubst_bcontext c c')
	| BCAbs c => BCAbs (csubst_bcontext c c')
end.

Fixpoint bcontext_of c l := match c with
	| LCHole => BCHole
	| LCApp_l c' v => BCApp_l (bcontext_of c' l) (bruijn_of v l)
	| LCApp_r u c' => BCApp_r (bruijn_of u l) (bcontext_of c' l)
	| LCAbs x c' => BCAbs (bcontext_of c' (x :: l))
end.
Fixpoint of_bcontext c n := match c with
	| BCHole => LCHole
	| BCApp_l c' v => LCApp_l (of_bcontext c' n) (of_bruijn v n)
	| BCApp_r u c' => LCApp_r (of_bruijn u n) (of_bcontext c' n)
	| BCAbs c' => LCAbs n (of_bcontext c' (S n))
end.
Fixpoint lsubst_bcontext c := match c with
	| LCHole => []
	| LCApp_l c' v => lsubst_bcontext c'
	| LCApp_r u c' => lsubst_bcontext c'
	| LCAbs x c' => lsubst_bcontext c' ++ [x]
end.
Fixpoint offset_lcontext c := match c with
	| BCHole => O
	| BCApp_l c' v => offset_lcontext c'
	| BCApp_r u c' => offset_lcontext c'
	| BCAbs c' => S (offset_lcontext c')
end.
Lemma bruijn_of_lsubst : forall c u l, bruijn_of (subst_lcontext c u) l = subst_bcontext (bcontext_of c l) (bruijn_of u (lsubst_bcontext c ++ l)).
Proof using.
	intros c w; induction c as [|c IH v|u c IH|x c IH]; intros l.
	- exact eq_refl.
	- cbn; f_equal; exact (IH _).
	- cbn; f_equal; exact (IH _).
	- cbn; rewrite app_assoc; f_equal; exact (IH _).
Qed.
Lemma of_bruijn_csubst : forall c u n, of_bruijn (subst_bcontext c u) n = subst_lcontext (of_bcontext c n) (of_bruijn u (offset_lcontext c + n)).
Proof using.
	intros c w; induction c as [|c IH v|u c IH|c IH]; intros n.
	- exact eq_refl.
	- cbn; f_equal; exact (IH _).
	- cbn; f_equal; exact (IH _).
	- cbn; f_equal; rewrite plus_n_Sm; exact (IH _).
Qed.

Lemma lsubst_bctx_of : forall c n, lsubst_bcontext (of_bcontext c n) = rev (map V_of_nat (seq n (offset_lcontext c))).
Proof using.
	intros c; induction c as [|c IH v|u c IH|c IH]; intros n.
	- exact eq_refl.
	- exact (IH _).
	- exact (IH _).
	- cbn; rewrite (rev_append_r _ [] [_] : rev_append _ [_] = rev _ ++ [_]); exact (f_equal (fun a => a ++ _) (IH _)).
Qed.

Inductive over_lcontext {R : relation lterm} | : relation lterm :=
	| lctx_step : forall {u v}, R u v -> over_lcontext u v
	| lctx_app_l : forall {u u'} [v], over_lcontext u u' -> over_lcontext (LApp u v) (LApp u' v)
	| lctx_app_r : forall [u] {v v'}, over_lcontext v v' -> over_lcontext (LApp u v) (LApp u v')
	| lctx_abs : forall [x] {u v}, over_lcontext u v -> over_lcontext (LAbs x u) (LAbs x v).
Inductive over_bcontext {R : relation bterm} | : relation bterm :=
	| bctx_step : forall {u v}, R u v -> over_bcontext u v
	| bctx_app_l : forall {u u'} [v], over_bcontext u u' -> over_bcontext (BApp u v) (BApp u' v)
	| bctx_app_r : forall [u] {v v'}, over_bcontext v v' -> over_bcontext (BApp u v) (BApp u v')
	| bctx_abs : forall {u v}, over_bcontext u v -> over_bcontext (BAbs u) (BAbs v).
Arguments over_lcontext _ _ _ : clear implicits.
Arguments over_bcontext _ _ _ : clear implicits.

Lemma over_lcontext_iff : forall R u v,
	over_lcontext R u v <-> exists C u' v', R u' v' /\ u = subst_lcontext C u' /\ v = subst_lcontext C v'.
Proof using.
	intros R u v; split; [intros H|intros (C & u' & v' & H & -> & ->)].
	- induction H as [u v HR|u u' v H (C & u1 & u2 & IH & -> & ->)|u v v' H (C & v1 & v2 & IH & -> & ->)|x u v H (C & u' & v' & IH & -> & ->)].
	  1: exists LCHole, u, v; easy.
	  1: exists (LCApp_l C v), u1, u2; easy.
	  1: exists (LCApp_r u C), v1, v2; easy.
	  1: exists (LCAbs x C), u', v'; easy.
	- induction C as [|C IH v|u C IH|x C IH].
	  1: exact (lctx_step H).
	  1: exact (lctx_app_l IH).
	  1: exact (lctx_app_r IH).
	  1: exact (lctx_abs IH).
Qed.
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

Lemma over_lcontext_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_lcontext R1) (over_lcontext R2).
Proof using.
	intros R1 R2 HR u v; rewrite !over_lcontext_iff; intros (c & u' & v' & HR1 & equ & eqv).
	exists c, u', v'; split; [exact (HR _ _ HR1)|split; assumption].
Qed.
Lemma over_bcontext_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_bcontext R1) (over_bcontext R2).
Proof using.
	intros R1 R2 HR u v; rewrite !over_bcontext_iff; intros (c & u' & v' & HR1 & equ & eqv).
	exists c, u', v'; split; [exact (HR _ _ HR1)|split; assumption].
Qed.

Lemma over_lcontext_union : forall R1 R2 u v, over_lcontext (union _ R1 R2) u v <-> over_lcontext R1 u v \/ over_lcontext R2 u v.
Proof using.
	intros R1 R2 u v; split.
	2: intros [H|H]; refine (over_lcontext_ext _ _ _ H); intros u' v' H'.
	2: left; exact H'.
	2: right; exact H'.
	intros H; induction H as [u v [H|H]|u u' v H [IH|IH]|u v v' H [IH|IH]|x u v H [IH|IH]].
	1,3,5,7: left.
	5-8: right.
	1,5: exact (lctx_step H).
	1,4: exact (lctx_app_l IH).
	1,3: exact (lctx_app_r IH).
	1,2: exact (lctx_abs IH).
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

Lemma over_lcontext_transp : forall {R u v}, over_lcontext R u v -> over_lcontext (transp R) v u.
Proof using.
	intros R u v H;
	  induction H as [u v HR|u u' v H IH|u v v' H IH|x u v H IH].
	- exact (lctx_step HR).
	- exact (lctx_app_l IH).
	- exact (lctx_app_r IH).
	- exact (lctx_abs IH).
Qed.
Lemma over_lcontext_transp_comm : forall {R u v}, (over_lcontext R)^t u v <-> over_lcontext (R^t) u v.
Proof using.
	intros R u v; split; exact over_lcontext_transp.
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

Fixpoint lsubst u x v := match u with
	| LVar y => if dec_V x y then v else u
	| LApp u1 u2 => LApp (lsubst u1 x v) (lsubst u2 x v)
	| LAbs y u => LAbs y (lsubst u x v)
end.
Fixpoint lsubst_full u x v := match u with
	| LVar y => if dec_V x y then v else u
	| LApp u1 u2 => LApp (lsubst_full u1 x v) (lsubst_full u2 x v)
	| LAbs y u => if dec_V x y then LAbs y u else LAbs y (lsubst_full u x v)
end.
Fixpoint incr_bound u k := match u with
	| BVar y => BVar y
	| BBound n => BBound (if k <=? n then S n else n)
	| BApp u v => BApp (incr_bound u k) (incr_bound v k)
	| BAbs u => BAbs (incr_bound u (S k))
end.
Fixpoint bsubst u x v := match u with
	| BVar y => if dec_V x y then v else u
	| BBound _ => u
	| BApp u1 u2 => BApp (bsubst u1 x v) (bsubst u2 x v)
	| BAbs u => BAbs (bsubst u x (incr_bound v O))
end.
Fixpoint bsubstb u n v := match u with
	| BVar y => u
	| BBound k => if k <? n then BBound k else if k =? n then v else BBound (pred k)
	| BApp u1 u2 => BApp (bsubstb u1 n v) (bsubstb u2 n v)
	| BAbs u => BAbs (bsubstb u (S n) (incr_bound v O))
end.

Inductive lfv {x} | : lterm -> Prop :=
	| LFV_Var : lfv x
	| LFV_App_l : forall {u v}, lfv u -> lfv (LApp u v)
	| LFV_App_r : forall {u v}, lfv v -> lfv (LApp u v)
	| LFV_Abs : forall {y u}, x <> y -> lfv u -> lfv {{ ^y, {u} }}.
Inductive lbv {x} | : lterm -> Prop :=
	| LBV_Bound : forall {u}, lbv {{ ^x, {u} }}
	| LBV_App_l : forall {u v}, lbv u -> lbv (LApp u v)
	| LBV_App_r : forall {u v}, lbv v -> lbv (LApp u v)
	| LBV_Abs : forall {y u}, lbv u -> lbv {{ ^y, {u} }}.
Arguments lfv _ _ : clear implicits.
Arguments lbv _ _ : clear implicits.
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

Inductive alpha : lterm -> lterm -> Prop :=
	| Alpha : forall x y u (H1 : ~ lbv x u) (H2 : ~ lbv y u) (H3 : ~ lfv y u),
		alpha {{ ^x, {u} }} {{ ^y, {lsubst u x y} }}.
Definition alpha_eq : lterm -> lterm -> Prop := (over_lcontext alpha)^*.

Section Alpha.

Fixpoint min_gt_vars u := match u with
	| LVar x => match onat_of_V x with None => O | Some n => S n end
	| LApp u v => max (min_gt_vars u) (min_gt_vars v)
	| LAbs x u => max (match onat_of_V x with None => O | Some n => S n end) (min_gt_vars u)
end.
Fixpoint min_gt_bvars u := match u with
	| BVar x => match onat_of_V x with None => O | Some n => S n end
	| BBound _ => O
	| BApp u v => max (min_gt_bvars u) (min_gt_bvars v)
	| BAbs u => min_gt_bvars u
end.
Fixpoint min_gt_fbound u := match u with
	| BVar x => O
	| BBound n => S n
	| BApp u v => max (min_gt_fbound u) (min_gt_fbound v)
	| BAbs u => pred (min_gt_fbound u)
end.

Lemma min_gt_vars_fv : forall u n, min_gt_vars u <= n -> ~ lfv (V_of_nat n) u.
Proof using.
	intros u n Hn; induction u as [x|u IHu v IHv|x u IH].
	- simpl in Hn; intros H; inversion H; subst; rewrite onat_of_nat in Hn; exact (nle_succ_diag_l _ Hn).
	- simpl in Hn; intros H; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  inversion H; subst; [exact (IHu Hu H1)|exact (IHv Hv H1)].
	- simpl in Hn; intros H; assert (Hx := max_lub_l _ _ _ Hn); assert (Hu := max_lub_r _ _ _ Hn).
	  inversion H; subst; exact (IH Hu H3).
Qed.
Lemma min_gt_vars_bv : forall u n, min_gt_vars u <= n -> ~ lbv (V_of_nat n) u.
Proof using.
	intros u n Hn; induction u as [x|u IHu v IHv|x u IH].
	- simpl in Hn; intros H; inversion H; subst; rewrite onat_of_nat in Hn; exact (nle_succ_diag_l _ Hn).
	- simpl in Hn; intros H; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  inversion H; subst; [exact (IHu Hu H1)|exact (IHv Hv H1)].
	- simpl in Hn; intros H; assert (Hx := max_lub_l _ _ _ Hn); assert (Hu := max_lub_r _ _ _ Hn).
	  inversion H; subst; [rewrite onat_of_nat in Hx; exact (nle_succ_diag_l _ Hx)|exact (IH Hu H1)].
Qed.
Lemma min_gt_bvars_fv : forall u n, min_gt_bvars u <= n -> ~ bfv (V_of_nat n) u.
Proof using.
	intros u n Hn; induction u as [x|k|u IHu v IHv|u IH].
	- simpl in Hn; intros H; inversion H; subst; rewrite onat_of_nat in Hn; exact (nle_succ_diag_l _ Hn).
	- intros H; inversion H.
	- simpl in Hn; intros H; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  inversion H; subst; [exact (IHu Hu H1)|exact (IHv Hv H1)].
	- simpl in Hn; intros H.
	  inversion H; subst; exact (IH Hn H1).
Qed.
Lemma min_gt_fbound_fb : forall u n, min_gt_fbound u <= n -> ~ bfb n u.
Proof using.
	intros u; induction u as [x|k|u IHu v IHv|u IH]; intros n Hn.
	- intros H; inversion H.
	- cbn in Hn; intros H; inversion H; subst; exact (lt_neq _ _ Hn eq_refl).
	- cbn in Hn; intros H; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  inversion H; subst; [exact (IHu _ Hu H2)|exact (IHv _ Hv H2)].
	- cbn in Hn; intros H.
	  inversion H; subst; refine (IH (S _) (le_trans _ _ _ _ (le_n_S _ _ Hn)) H2).
	  destruct (min_gt_fbound u); [exact (le_0_n _)|exact (le_n _)].
Qed.

Lemma lbv_of_bruijn_inv : forall x u n, lbv x (of_bruijn u n) -> exists k, x = V_of_nat k /\ n <= k.
Proof using.
	intros x u n H; remember (of_bruijn u n) as u' eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u|u v H IH|u v H IH|y u H IH]; intros [k'|x'|u' v'|u'] n equ; try discriminate equ.
	1-4: injection equ as -> ->.
	- exists n; split; [exact eq_refl|exact (le_n _)].
	- exact (IH _ _ eq_refl).
	- exact (IH _ _ eq_refl).
	- specialize (IH _ _ eq_refl) as [k [eqx Hk]]; exists k; split; [exact eqx|exact (le_S_n _ _ (le_S _ _ Hk))].
Qed.

Lemma lfv_of_bruijn_inv : forall x u n,
	lfv x (of_bruijn u n) -> (fix inner u o := match u with
		| BVar y => x = y
		| BBound i => o <= i /\ x = ((o + n) - (S i))%nat
		| BApp u v => inner u o \/ inner v o
		| BAbs u => inner u (S o)
	end) u O.
Proof using.
	intros x u n H.
	assert (Hx : match onat_of_V x with None => True | Some k => ~ (n <= k < 0 + n) end)
	  by (destruct (onat_of_V x) as [k|]; [intros [H1' H2']; exact (lt_neq _ _ (le_lt_trans _ _ _ H1' H2') eq_refl)|exact I]).
	remember (of_bruijn u n) as u' eqn:equ; rewrite (eq_refl : n = Nat.add 0 n) in equ;
	  generalize dependent 0; generalize dependent u;
	  induction H as [|u v H IH|u v H IH|y u xney H IH]; intros [k'|x'|u' v'|u'] o equ Hx; try discriminate equ.
	- injection equ as equ; exact equ.
	- injection equ as equ; refine (conj _ equ).
	  rewrite (proj2 (onat_Some_iff _ _) equ) in Hx; clear equ x; rename x' into k.
	  destruct (le_gt_cases o k) as [h|ogtk]; [exact h|contradict Hx; split].
	  1: rewrite (add_sub_swap _ _ _ ogtk); exact (le_add_l _ _).
	  rewrite (add_sub_swap _ _ _ ogtk); refine (add_le_mono (S _) _ _ _ _ (le_n _)).
	  rewrite <-(sub_succ_l _ _ ogtk).
	  exact (le_sub_l _ k).
	- injection equ as -> _; left; exact (IH _ _ eq_refl Hx).
	- injection equ as _ ->; right; exact (IH _ _ eq_refl Hx).
	- injection equ as -> ->; refine (IH _ (S _) eq_refl _).
	  remember (onat_of_V x) as tmp eqn:eqox; destruct tmp as [k|]; [intros [nlek kltSon]|exact I].
	  inversion kltSon as [eqk|k' klton eqk']; [subst k; clear kltSon nlek Hx IH|exact (Hx (conj nlek klton))].
	  assert (tmp := proj1 (onat_Some_iff _ _) (eq_sym eqox)); subst x; exact (xney eq_refl).
Qed.
Lemma lfv_of_bruijn_of : forall x u l n, In x l -> length l + min_gt_vars x <= n -> ~ lfv x (of_bruijn (bruijn_of u l) n).
Proof using.
	intros x u l n H1 H2 H3; apply lfv_of_bruijn_inv in H3.
	rewrite (eq_refl : n = 0 + n)%nat in H2; generalize dependent 0; generalize dependent l;
	  induction u as [y|u IHu v IHv|y u IH]; intros l H1 o H2 H3.
	- cbn in H3.
	  pose (o' := O); fold o' in H3.
	  rewrite (eq_refl : length l = o' + length l)%nat in H2.
	  generalize dependent o'; induction l as [|hd tl IH]; intros o' H2 H3.
	  1: contradiction H1.
	  cbn in H3; destruct (dec_V hd y) as [->|hdney]; [destruct H3 as [_ H3]|].
	  1: subst x; clear - H2; simpl in H2; rewrite onat_of_nat in H2.
	  1: rewrite <-(plus_n_Sm o' _ : S o' + _ = _)%nat in H2.
	  1: refine (lt_neq _ _ (lt_le_trans _ _ _ _ H2) eq_refl).
	  1: rewrite (add_comm (S _)), <-!add_assoc, <-plus_n_Sm, add_sub_assoc, (add_comm (S o')), add_sub.
	  2: exact (le_trans _ _ _ (le_trans _ _ _ (le_add_r _ _) (le_add_r _ _)) H2).
	  1: exact (le_add_l _ _).
	  rewrite <-(plus_n_Sm _ _ : S _ + length _ = _ + length (_ :: _))%nat in H2.
	  destruct H1 as [<-|H1]; [clear IH|exact (IH H1 _ H2 H3)].
	  remember (S o') as o'' eqn:eq; clear eq o'; rename tl into l, o'' into o', hdney into xney.
	  generalize dependent o'; induction l as [|hd tl IH]; intros o' H2 H3. (* Simplifiable using lfv (of_b_of u) -> lfv u *)
	  1: exact (xney H3).
	  cbn in H3; destruct (dec_V hd y) as [->|hdney]; [destruct H3 as [_ H3]|].
	  1: subst x; clear - H2; simpl in H2; rewrite onat_of_nat in H2.
	  1: rewrite <-(plus_n_Sm o' _ : S o' + _ = _)%nat in H2.
	  1: refine (lt_neq _ _ (lt_le_trans _ _ _ _ H2) eq_refl).
	  1: rewrite (add_comm (S _)), <-!add_assoc, <-plus_n_Sm, add_sub_assoc, (add_comm (S o')), add_sub.
	  2: exact (le_trans _ _ _ (le_trans _ _ _ (le_add_r _ _) (le_add_r _ _)) H2).
	  1: exact (le_add_l _ _).
	  rewrite <-(plus_n_Sm _ _ : S _ + length _ = _ + length (_ :: _))%nat in H2.
	  exact (IH _ H2 H3).
	- destruct H3 as [H3|H3].
	  1: exact (IHu _ H1 _ H2 H3).
	  1: exact (IHv _ H1 _ H2 H3).
	- cbn in H3.
	  exact (IH (_ :: _) (or_intror H1) (S _) (le_n_S _ _ H2) H3).
Qed.

Lemma alpha_eq_of_bruijn_of : forall u n, min_gt_vars u <= n -> alpha_eq (of_bruijn (bruijn_of u []) n) u.
Proof using.
	intros u n H.
	apply clos_refl_trans_iff.
	pose (renorm_steps := fix inner u n := match u with
	         | LVar _ => []
	         | LApp u v => map (fun v' => LApp (of_bruijn (bruijn_of u []) n) v') (inner v n)
	                    ++ map (fun u' => LApp u' v) (inner u n)
	         | LAbs x u => (LAbs x (of_bruijn (bruijn_of u []) (S n))) :: map (fun u' => LAbs x u') (inner u (S n)) end).
	exists (renorm_steps u n); simpl.
	generalize dependent n; induction u as [x|u IHu v IHv|x u IH]; intros n Hn.
	- exact eq_refl.
	- simpl renorm_steps; refine (proj2 (proj2 (rt_iff_app (y:=of_bruijn (bruijn_of u []) n v)) _)).
	  specialize (IHu _ (max_lub_l _ _ _ Hn)).
	  specialize (IHv _ (max_lub_r _ _ _ Hn)).
	  split.
	  + simpl.
	    remember (of_bruijn (bruijn_of v []) n) as v' eqn:eqv; clear - IHv.
	    generalize dependent v'; induction (renorm_steps v n) as [|hd tl IH]; intros v' H.
	    1: simpl; f_equal; exact H.
	    simpl in *; exact (conj (lctx_app_r (proj1 H)) (IH _ (proj2 H))).
	  + simpl.
	    remember (of_bruijn (bruijn_of u []) n) as u' eqn:equ; clear - IHu.
	    generalize dependent u'; induction (renorm_steps u n) as [|hd tl IH]; intros u' H.
	    1: simpl; f_equal; exact H.
	    simpl in *; exact (conj (lctx_app_l (proj1 H)) (IH _ (proj2 H))).
	- simpl renorm_steps; simpl.
	  specialize (IH _ (le_S _ _ (max_lub_r _ _ _ Hn))).
	  split; [apply lctx_step|].
	  + assert (tmp := Alpha n x (of_bruijn (bruijn_of u [x]) (S n))).
	    match type of tmp with ?h1 -> ?h2 -> ?h3 -> _ =>
	      assert (H : h1 /\ h2 /\ h3); [clear tmp; split; [|split]|specialize (tmp (proj1 H) (proj1 (proj2 H)) (proj2 (proj2 H)))] end.
	    4: refine (eq_ind _ (fun w => alpha _ (LAbs _ w)) tmp _ _); clear tmp H.
	    * intros H; apply lbv_of_bruijn_inv in H; destruct H as [k [eq Hk]].
	      exact (lt_neq _ _ Hk (V_inj _ _ eq)).
	    * intros H; apply lbv_of_bruijn_inv in H; destruct H as [k [-> Hk]].
	      exact (min_gt_vars_bv _ _ (lt_le_incl _ _ (le_lt_trans _ _ _ Hn Hk)) LBV_Bound).
	    * intros H; exact (lfv_of_bruijn_of _ _ [_] _ (or_introl eq_refl) (le_n_S _ _ (max_lub_l _ _ _ Hn)) H).
	    * clear - Hn; cbn in Hn; apply max_lub_r in Hn.
	      rewrite (eq_refl : [x] = [] ++ [x]);
	        remember [] as l eqn:eql; rewrite eql at 2.
	      rewrite (f_equal (fun w => length w + _)%nat (eq_sym eql) : S n = length l + S n)%nat.
	      clear eql; generalize dependent n; generalize dependent l; induction u as [y|u IHu v IHv|y u IH]; intros l n Hn.
	      2: simpl; f_equal; [exact (IHu _ _ (max_lub_l _ _ _ Hn))|exact (IHv _ _ (max_lub_r _ _ _ Hn))].
	      2: simpl; f_equal; exact (IH (y :: l) n (max_lub_r _ _ _ Hn)).
	      cbn; rewrite (eq_refl : length l = 0 + length l)%nat;
	        generalize dependent O; induction l as [|hd tl IH]; intros o.
	      1: cbn; rewrite add_0_r; destruct (dec_V x y) as [<-|xney]; cbn.
	      1: rewrite <-plus_n_Sm, <-plus_Sn_m, add_comm, add_sub; exact (if_dec_refl _ _ _).
	      1: refine (if_dec_neq _ _ _ _ _); intros <-; cbn in Hn; rewrite onat_of_nat in Hn; exact (lt_neq _ _ Hn eq_refl).
	      cbn.
	      destruct (dec_V hd y) as [->|hdney].
	      1: cbn; refine (if_dec_neq _ _ _ _ _); intros f; apply V_inj in f;
	           rewrite <-(plus_n_Sm _ _ : S o + _ = _)%nat, <-add_assoc, add_comm, add_sub in f.
	      1: exact (lt_neq _ _ (le_add_l _ _) f).
	      rewrite <-(plus_n_Sm _ _ : S o + _ = _)%nat; exact (IH _).
	  + remember (of_bruijn (bruijn_of u []) (S n)) as u' eqn:equ; clear - IH.
	    generalize dependent u'; induction (renorm_steps u (S n)) as [|hd tl IH']; intros u' H.
	    1: simpl in *; f_equal; exact H.
	    simpl in *; refine (conj (lctx_abs (proj1 H)) (IH' _ (proj2 H))).
Qed.

Lemma lsubst_same : forall u x, lsubst u x x = u.
Proof using.
	intros u x; induction u as [y|u IHu v IHv|y u IH].
	- cbn; destruct (dec_V x y) as [<-|_]; exact eq_refl.
	- exact (f_equal2 _ IHu IHv).
	- exact (f_equal _ IH).
Qed.
Lemma lsubst_full_same : forall u x, lsubst_full u x x = u.
Proof using.
	intros u x; induction u as [y|u IHu v IHv|y u IH].
	- cbn; destruct (dec_V x y) as [<-|_]; exact eq_refl.
	- exact (f_equal2 _ IHu IHv).
	- cbn; destruct (dec_V x y); [exact eq_refl|exact (f_equal _ IH)].
Qed.
Lemma lsubst_full_nfv : forall u x v, ~ lfv x u -> lsubst_full u x v = u.
Proof using.
	intros u x v Hx; induction u as [y|u1 IH1 u2 IH2|y u IH].
	- cbn; refine (if_dec_neq _ _ _ _ _); intros <-; exact (Hx LFV_Var).
	- exact (f_equal2 _ (IH1 (fun H => Hx (LFV_App_l H))) (IH2 (fun H => Hx (LFV_App_r H)))).
	- cbn; destruct (dec_V x y); [exact eq_refl|exact (f_equal _ (IH (fun H => Hx (LFV_Abs n H))))].
Qed.

Lemma alpha_sym : inclusion alpha alpha^t.
Proof using.
	intros u v H; inversion H; subst; clear H.
	rename u0 into u, H1 into H01, H2 into H02, H3 into H03.
	unshelve refine (eq_ind _ (fun v => alpha (LAbs y (lsubst u x y)) (LAbs x v)) (Alpha _ _ _ _ _ _) _ _).
	- clear - H02; induction u as [z|u IHu v IHv|z u IH].
	  + cbn; destruct (dec_V x z) as [<-|xnez]; [intros f; inversion f|exact H02].
	  + cbn; intros f; inversion f; subst; [exact (IHu (fun H => H02 (LBV_App_l H)) H0)|exact (IHv (fun H => H02 (LBV_App_r H)) H0)].
	  + cbn; intros f; inversion f; subst; [exact (H02 LBV_Bound)|exact (IH (fun H => H02 (LBV_Abs H)) H0)].
	- clear - H01; induction u as [z|u IHu v IHv|z u IH].
	  + cbn; destruct (dec_V x z) as [<-|xnez]; [intros f; inversion f|exact H01].
	  + cbn; intros f; inversion f; subst; [exact (IHu (fun H => H01 (LBV_App_l H)) H0)|exact (IHv (fun H => H01 (LBV_App_r H)) H0)].
	  + cbn; intros f; inversion f; subst; [exact (H01 LBV_Bound)|exact (IH (fun H => H01 (LBV_Abs H)) H0)].
	- destruct (dec_V x y) as [<-|xney].
	  1: rewrite lsubst_same; exact H03.
	  clear - xney; induction u as [z|u IHu v IHv|z u IH].
	  + cbn; destruct (dec_V x z) as [<-|xnez]; intros f; inversion f; subst; [exact (xney eq_refl)|exact (xnez eq_refl)].
	  + cbn; intros f; inversion f; subst; [exact (IHu H0)|exact (IHv H0)].
	  + cbn; intros f; inversion f; subst; exact (IH H2).
	- induction u as [z|u IHu v IHv|z u IH].
	  + simpl in *; destruct (dec_V x z) as [eq|ne]; simpl.
	    1: rewrite (if_dec_eq _ _ _ _ eq_refl); exact (f_equal _ eq).
	    refine (if_dec_neq _ _ _ _ _); intros <-; exact (H03 LFV_Var).
	  + simpl; f_equal;
	      [exact (IHu (fun H => H01 (LBV_App_l H)) (fun H => H02 (LBV_App_l H)) (fun H => H03 (LFV_App_l H)))
	      |exact (IHv (fun H => H01 (LBV_App_r H)) (fun H => H02 (LBV_App_r H)) (fun H => H03 (LFV_App_r H)))].
	  + simpl; f_equal; apply IH.
	    1: exact (fun H => H01 (LBV_Abs H)).
	    1: exact (fun H => H02 (LBV_Abs H)).
	  intros f; refine (H03 (LFV_Abs _ f)).
	  intros <-; exact (H02 LBV_Bound).
Qed.
Lemma alpha_transp : same_relation alpha alpha^t.
Proof using.
	split; [exact alpha_sym|].
	intros u v; exact (alpha_sym v u).
Qed.
Lemma alpha_eq_sym : inclusion alpha_eq alpha_eq^t.
Proof using.
	unfold alpha_eq; intros u v H; unfold transp.
	apply clos_refl_trans_transp_permute in H; unfold transp in H.
	refine (clos_refl_trans_ext _ _ _ H).
	intros x y H'.
	exact (over_lcontext_ext (proj2 alpha_transp) _ _ (proj1 (@over_lcontext_transp_comm alpha x y) H')).
Qed.
Lemma alpha_eq_transp : same_relation alpha_eq alpha_eq^t.
Proof using.
	split; [exact alpha_eq_sym|].
	intros u v; exact (alpha_eq_sym v u).
Qed.

Lemma alpha_eq_iff : forall u v l, alpha_eq u v <-> bruijn_of u l = bruijn_of v l.
Proof using.
	intros u v l; split.
	- intros H; induction H as [u v H|u|u v w H1 IH1 H2 IH2].
	  2: exact eq_refl.
	  2: exact (eq_trans IH1 IH2).
	  generalize dependent l; induction H as [u v H|u u' v H IH|u v v' H IH|x u v H IH]; intros l.
	  + inversion H as [x y u' H1 H2 H3]; clear H; subst; cbn; f_equal.
	    pose (l' := @nil V); rewrite (eq_refl : x :: l = l' ++ x :: l), (eq_refl : y :: l = l' ++ y :: l).
	    assert (xni : ~ In x l') by intros [];
	    assert (yni : ~ In y l') by intros [].
	    generalize dependent l'; induction u' as [z|u IHu v IHv|z u IH]; intros l' xni yni.
	    * cbn; remember (dec_V x z) as tmp eqn:eq; destruct tmp as [<-|ne]; cbn.
	      1,2: generalize O; induction l' as [|hd l' IH]; intros n.
	      1: cbn; rewrite !if_dec_refl; exact eq_refl.
	      1: cbn; rewrite (if_dec_neq _ _ _ _ (fun H => yni (or_introl (eq_sym H)))), (if_dec_neq _ _ _ _ (fun H => xni (or_introl (eq_sym H)))).
	      1: exact (IH (fun H => xni (or_intror H)) (fun H => yni (or_intror H)) _).
	      1: cbn; rewrite <-eq; exact (eq_sym (if_dec_neq y z _ _ ltac:(intros <-; exact (H3 LFV_Var)))).
	      cbn; exact (f_equal (fun w => if dec_V _ _ then _ else w) (IH (fun H => xni (or_intror H)) (fun H => yni (or_intror H)) _)).
	    * cbn; refine (f_equal2 _ (IHu _ _ _ _ xni yni) (IHv _ _ _ _ xni yni)).
	      1: exact (fun H => H1 (LBV_App_l H)).
	      1: exact (fun H => H2 (LBV_App_l H)).
	      1: exact (fun H => H3 (LFV_App_l H)).
	      1: exact (fun H => H1 (LBV_App_r H)).
	      1: exact (fun H => H2 (LBV_App_r H)).
	      1: exact (fun H => H3 (LFV_App_r H)).
	    * cbn; refine (f_equal _ (IH _ _ _ (_ :: _) _ _)).
	      1: exact (fun H => H1 (LBV_Abs H)).
	      1: exact (fun H => H2 (LBV_Abs H)).
	      1: exact (fun H => H3 (LFV_Abs (x:=y) (y:=z) ltac:(intros <-; exact (H2 LBV_Bound)) H)).
	      1,2: intros [<-|H].
	      1: exact (H1 LBV_Bound).
	      1: exact (xni H).
	      1: exact (H2 LBV_Bound).
	      1: exact (yni H).
	  + cbn; f_equal; exact (IH _).
	  + cbn; f_equal; exact (IH _).
	  + cbn; f_equal; exact (IH _).
	- intros H.
	  assert (tmp : bruijn_of u [] = bruijn_of v []).
	  { pose (lx := @nil V); pose (ly := @nil V); assert (Hlen := eq_refl : length lx = length ly);
	      rewrite (eq_refl : l = lx ++ l) in H at 1; rewrite (eq_refl : [] = lx) at 1;
	      rewrite (eq_refl : l = ly ++ l) in H at 2; rewrite (eq_refl : [] = ly);
	      generalize dependent ly; generalize dependent lx; generalize dependent v;
	      induction u as [x|u1 IH1 u2 IH2|x u IH]; intros [y|v1 v2|y v] lx ly H Hlen; try discriminate H.
	    2,3: cbn in H; exfalso.
	    2: remember (bruijn_of v1 (ly ++ l)) as w1 eqn:eql; remember (bruijn_of v2 (ly ++ l)) as w2 eqn:eqr; clear eql eqr.
	    3: remember (bruijn_of v (y :: ly ++ l)) as w1 eqn:eql; clear eql.
	    2,3: generalize dependent 0; induction (lx ++ l) as [|hd tl IH]; intros o H;
	           [discriminate H|cbn in H; destruct (dec_V hd x); [discriminate H|exact (IH _ H)]].
	    2,4: cbn in H; clear - H; exfalso.
	    2: remember (bruijn_of u1 (lx ++ l)) as w1 eqn:eql; remember (bruijn_of u2 (lx ++ l)) as w2 eqn:eqr; clear eql eqr.
	    3: remember (bruijn_of u (x :: lx ++ l)) as w1 eqn:eql; clear eql.
	    2,3: generalize dependent 0; induction (ly ++ l) as [|hd tl IH]; intros o H;
	           [discriminate H|cbn in H; destruct (dec_V hd y); [discriminate H|exact (IH _ H)]].
	    - cbn in *.
	      generalize dependent 0; generalize dependent ly; induction lx as [|hdx lx IH]; intros [|hdy ly] Hlen.
	      2,3: discriminate Hlen.
	      1: cbn; clear Hlen; induction l as [|hd l IH]; intros n H.
	      1: exact H.
	      1: cbn in H; destruct (dec_V hd x) as [<-|hdnex]; destruct (dec_V hd y) as [->|hdney].
	      1: exact eq_refl.
	      1: rename y into x.
	      1,2: exfalso; clear - H; remember (S n) as m eqn:eq; assert (Hm : n < m) by (subst m; exact (le_n _));
	             clear eq; generalize dependent m; induction l as [|hd l IH]; intros m H Hm; [discriminate H|cbn in H].
	      1,2: destruct (dec_V hd x); [injection H as H; refine (lt_neq _ _ Hm _); easy|exact (IH _ H (le_S _ _ Hm))].
	      1: exact (IH _ H).
	      injection Hlen as Hlen; cbn; intros n H.
	      destruct (dec_V hdx x) as [->|hdnex]; destruct (dec_V hdy y) as [->|hdney].
	      1: exact eq_refl.
	      1,2: exfalso; clear - H.
	      1: rename y into x, ly into lx.
	      1,2: remember (S n) as m eqn:eq; assert (Hm : n < m) by (subst m; exact (le_n _));
	             clear eq; generalize dependent m; induction (lx ++ l) as [|hd l' IH]; clear lx l; intros m H Hm; [discriminate H|cbn in H].
	      1,2: destruct (dec_V hd x); [injection H as H; refine (lt_neq _ _ Hm _); easy|exact (IH _ H (le_S _ _ Hm))].
	      exact (IH _ Hlen _ H).
	    - cbn; injection H as H1 H2; f_equal; [exact (IH1 _ _ _ H1 Hlen)|exact (IH2 _ _ _ H2 Hlen)].
	    - cbn; injection H as H; f_equal; exact (IH _ (_ :: _) (_ :: _) H (f_equal S Hlen)). }
	  refine (rt_trans _ (alpha_eq_of_bruijn_of _ (max (min_gt_vars u) (min_gt_vars v)) (le_max_r _ _))).
	  apply alpha_eq_sym.
	  rewrite <-tmp; exact (alpha_eq_of_bruijn_of _ _ (le_max_l _ _)).
Qed.

Lemma always_subst : forall u x v, exists u', alpha_eq u u' /\ ~ lbv x u' /\ forall x, ~ (lfv x v /\ lbv x u').
Proof using.
	intros u x v; exists (of_bruijn (bruijn_of u []) (max (max (min_gt_vars u) (min_gt_vars v)) (min_gt_vars x))).
	split; [|split].
	1: exact (alpha_eq_sym _ _ (alpha_eq_of_bruijn_of _ _ (le_trans _ _ _ (le_max_l _ _) (le_max_l _ _)))).
	1: intros H; apply lbv_of_bruijn_inv in H; destruct H as [k [eqx Hk]]; cbn in Hk; rewrite (proj2 (onat_Some_iff _ _) eqx) in Hk.
	1: refine (lt_neq _ _ (lt_le_trans _ _ _ (le_max_r _ _) Hk) eq_refl).
	intros y [fvyv bvy]; apply lbv_of_bruijn_inv in bvy; destruct bvy as [k [-> Hk]].
	exact (min_gt_vars_fv _ _ (le_trans _ _ _ (le_trans _ _ _ (le_max_r _ _) (le_max_l _ _)) Hk) fvyv).
Qed.

Lemma alpha_eq_Var : forall x, alpha_eq x x.
Proof using. intros x; exact rt_refl. Qed.
Lemma alpha_eq_App : forall {u u' v v'}, alpha_eq u u' -> alpha_eq v v' -> alpha_eq (u v) (u' v').
Proof using.
	intros u u' v v' Hu Hv.
	refine (rt_trans (y:=(u' v)) _ _).
	1: induction Hu as [u u' H|u|u u' u'' _ IH1 _ IH2]; [exact (rt_step (lctx_app_l H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	1: induction Hv as [v v' H|v|v v' v'' _ IH1 _ IH2]; [exact (rt_step (lctx_app_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.
Lemma alpha_eq_Abs : forall x u u', alpha_eq u u' -> alpha_eq (LAbs x u) (LAbs x u').
Proof using.
	intros x u u' H.
	induction H as [u u' H|u|u u' u'' _ IH1 _ IH2]; [exact (rt_step (lctx_abs H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.

Lemma alpha_eq_Var_inv : forall x v, alpha_eq x v -> v = x.
Proof using.
	intros x v H; apply clos_rt_rt1n in H.
	inversion H; [exact eq_refl|].
	inversion H0; inversion H3.
Qed.
Lemma alpha_eq_App_inv : forall {u u' v}, alpha_eq (LApp u u') v -> exists v1 v2, v = LApp v1 v2 /\ alpha_eq u v1 /\ alpha_eq u' v2.
Proof using.
	intros u u' v H.
	remember (LApp u u') as u0 eqn:equ;
	  generalize dependent u'; generalize dependent u;
	  induction H as [u0 u1 H|u0|u0 u1 u2 H1 IH1 H2 IH2];
	  intros u u' ->.
	- inversion H; subst.
	  1: inversion H0.
	  1,2: refine (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj _ _)))).
	  2,3: exact rt_refl.
	  1,2: exact (rt_step H3).
	- refine (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj rt_refl rt_refl)))).
	- specialize (IH1 _ _ eq_refl) as (u11 & u12 & eq1 & H11 & H12).
	  specialize (IH2 _ _ eq1) as (u21 & u22 & eq2 & H21 & H22).
	  exact (ex_intro _ _ (ex_intro _ _ (conj eq2 (conj (rt_trans H11 H21) (rt_trans H12 H22))))).
Qed.

#[refine,export] Instance alpha_eq_equiv : Equiv alpha_eq := {}.
Proof using.
	- intros x; rewrite (alpha_eq_iff _ _ []); exact eq_refl.
	- intros x y H; rewrite !(alpha_eq_iff _ _ []) in *; exact (eq_sym H).
	- intros x y z H1 H2; rewrite !(alpha_eq_iff _ _ []) in *; exact (eq_trans H1 H2).
Qed.

End Alpha.

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

Lemma min_gt_bvars_le_vars : forall u l, min_gt_bvars (bruijn_of u l) <= min_gt_vars u.
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH]; intros l; cbn.
	- destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq)|[_ eq]]; rewrite eq; [exact (le_0_n _)|exact (le_n _)].
	- exact (max_lub _ _ _ (le_trans _ _ _ (IHu _) (le_max_l _ _)) (le_trans _ _ _ (IHv _) (le_max_r _ _))).
	- exact (le_trans _ _ _ (IH _) (le_max_r _ _)).
Qed.
Lemma min_gt_fbound_of : forall u l, min_gt_fbound (bruijn_of u l) <= length l.
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH]; intros l.
	- cbn; destruct (bruijn_of_var_eq x l 0) as [(l1 & l2 & eql & xnil1 & eq)|[_ eq]]; [|rewrite eq; exact (le_0_n _)].
	  rewrite eq, add_0_r; cbn; clear - eql.
	  rewrite eql, length_app, <-(plus_n_Sm _ _ : S (length _) + length _ = length _ + length (_ :: _))%nat.
	  exact (le_add_r _ _).
	- exact (max_lub _ _ _ (IHu _) (IHv _)).
	- cbn; refine (proj2 (le_pred_le_succ _ _) (IH (_ :: _))).
Qed.

Lemma lsubst_is_full : forall u x v, ~ lbv x u -> lsubst u x v = lsubst_full u x v.
Proof using.
	intros u x v; induction u as [y|u1 IH1 u2 IH2|y u IH]; intros H.
	- exact eq_refl.
	- simpl; f_equal; [exact (IH1 (fun H' => H (LBV_App_l H')))|exact (IH2 (fun H' => H (LBV_App_r H')))].
	- simpl; rewrite (IH (fun H' => H (LBV_Abs H'))).
	  refine (eq_sym (if_dec_neq _ _ _ _ _)).
	  intros <-; exact (H LBV_Bound).
Qed.
Lemma bsubst_nfv : forall u x v, ~ bfv x u -> bsubst u x v = u.
Proof using.
	intros u x; induction u as [y|n|u1 IH1 u2 IH2|u IH]; intros v H.
	- cbn; refine (if_dec_neq _ _ _ _ _); intros <-; exact (H BFV_Var).
	- exact eq_refl.
	- cbn; f_equal; [exact (IH1 _ (fun H' => H (BFV_App_l H')))|exact (IH2 _ (fun H' => H (BFV_App_r H')))].
	- cbn; f_equal; exact (IH _ (fun H' => H (BFV_Abs H'))).
Qed.

Lemma bruijn_of_fv : forall u l x, bfv x (bruijn_of u l) <-> lfv x u /\ ~ In x l.
Proof using.
	intros u; induction u as [y|u IHu v IHv|y u IH]; intros l x; split.
	1,3,5: intros H.
	4-6: intros [H1 H2].
	- cbn in H; generalize dependent 0; induction l as [|hd tl IH]; intros o H.
	  1: split; [inversion H; exact LFV_Var|intros []].
	  cbn in H; destruct (dec_V hd y) as [|ne]; [inversion H|].
	  specialize (IH _ H) as [IH1 IH2]; split; [exact IH1|intros [f|f]; [|exact (IH2 f)]].
	  inversion IH1; exact (ne (eq_trans (eq_sym f) H1)).
	- cbn in H; inversion H; subst; [specialize (proj1 (IHu _ _) H1) as [IH1 IH2]|specialize (proj1 (IHv _ _) H1) as [IH1 IH2]].
	  1,2: split; [|exact IH2].
	  1: exact (LFV_App_l IH1).
	  exact (LFV_App_r IH1).
	- cbn in H; inversion H; subst; specialize (proj1 (IH _ _) H1) as [IH1 IH2]; split.
	  2: exact (fun H => IH2 (or_intror H)).
	  refine (LFV_Abs _ IH1); intros <-; exact (IH2 (or_introl eq_refl)).
	- inversion H1; subst y; clear - H2.
	  cbn; generalize dependent 0; induction l as [|hd tl IH]; intros o.
	  1: exact BFV_Var.
	  cbn; rewrite (if_dec_neq _ _ _ _ (fun H => H2 (or_introl (eq_sym H)))); exact (IH (fun H => H2 (or_intror H)) _).
	- inversion H1; subst;
	    [exact (BFV_App_l (proj2 (IHu _ _) (conj H0 H2)))|exact (BFV_App_r (proj2 (IHv _ _) (conj H0 H2)))].
	- inversion H1; subst; refine (BFV_Abs (proj2 (IH _ _) (conj H4 _))).
	  intros [H|H]; [exact (H3 H)|exact (H2 H)].
Qed.

Lemma bruijn_of_app_in : forall u l1 x l2,
  In x l1 -> bruijn_of u (l1 ++ x :: l2) = incr_bound (bruijn_of u (l1 ++ l2)) (length l1).
Proof using.
	intros u; induction u as [y|u IHu v IHv|y u IH]; intros l1 x l2 Hx; cbn.
	- destruct (bruijn_of_var_eq y (l1 ++ x :: l2) 0) as [(l1' & l2' & eql & ynil1' & eq)|[yni eq]]; rewrite eq; clear eq.
	  + rewrite add_0_r.
	    destruct (bruijn_of_var_eq y (l1 ++ l2) 0) as [(l1'' & l2'' & eql2 & ynil1'' & eq)|[yni eq]]; rewrite eq.
	    1: cbn; f_equal; rewrite add_0_r; clear eq.
	    1: destruct (dec_V x y) as [<-|xney]; [|clear Hx].
	    1,2: generalize dependent l1''; generalize dependent l1'; induction l1 as [|hd l1 IH].
	    1,2: intros l1' H1 eq1 l1'' H2 eq2.
	    3,4: intros l1' eq1 H1 l1'' eq2 H2.
	    1: contradiction Hx.
	    2: cbn in eq1, eq2 |- *; subst l2; destruct l1' as [|hd' l1']; [injection eq1 as eq _; contradiction (xney eq)|].
	    2: injection eq1 as <- eq1; refine (f_equal S _); assert (H' : ~ In y l1') by (intros H; exact (H1 (or_intror H))); clear H1.
	    2: fold @length; generalize dependent l1''; induction l1' as [|hd l1 IH]; intros [|hd' l1'] eq H1.
	    2: exact eq_refl.
	    2: injection eq as eq _; contradiction (H1 (or_introl (eq_sym eq))).
	    2: injection eq as eq _; contradiction (H' (or_introl eq)).
	    2: injection eq as _ eq; exact (f_equal S (IH (fun H => H' (or_intror H)) _ eq (fun H => H1 (or_intror H)))).
	    1,2: destruct l1'' as [|hd'' l1'']; simpl length.
	    1,3: destruct l1' as [|hd' l1']; [exact eq_refl|injection eq2 as -> _; injection eq1 as eq _; contradiction (H1 (or_introl eq))].
	    1,2: destruct l1' as [|hd' l1']; cbn.
	    1,3: injection eq1 as -> _; injection eq2 as eq _; contradiction (H2 (or_introl eq)).
	    1,2: injection eq1 as <- eq1; injection eq2 as <- eq2.
	    2: rewrite (IH _ eq1 (fun H => H1 (or_intror H)) _ eq2 (fun H => H2 (or_intror H)));
	         destruct (length l1 <=? length l1''); exact eq_refl.
	    1: destruct Hx as [eq|Hx]; [contradiction (H1 (or_introl eq))|].
	    1: rewrite (IH Hx _ (fun H => H1 (or_intror H)) eq1 _ (fun H => H2 (or_intror H)) eq2);
	         destruct (length l1 <=? length l1''); exact eq_refl.
	    contradict yni; rewrite in_app.
	    assert (tmp := proj1 (in_app y l1 (x :: l2))).
	    rewrite eql in tmp; specialize (tmp (proj2 (in_app _ _ (_ :: _)) (or_intror (or_introl eq_refl)))).
	    destruct tmp as [tmp|[tmp|tmp]]; [left; exact tmp|subst y; left; exact Hx|right; exact tmp].
	  + destruct (bruijn_of_var_eq y (l1 ++ l2) 0) as [(l1'' & l2'' & eql2 & ynil1'' & eq)|[yni' eq]];
	      [|exact (f_equal (fun w => incr_bound w _) (eq_sym eq))].
	    contradict yni; refine (proj2 (in_app _ _ (_ :: _))
	         (match proj1 (in_app _ _ _) _ with
	         | or_introl H => or_introl H
	         | or_intror H => or_intror (or_intror H) end)); rewrite eql2, in_app; right; left; exact eq_refl.
	- exact (f_equal2 _ (IHu _ _ _ Hx) (IHv _ _ _ Hx)).
	- exact (f_equal _ (IH (_ :: _) _ _ (or_intror Hx))).
Qed.
Lemma bruijn_of_app_nfv : forall u l1 x l2,
  ~ lfv x u -> bruijn_of u (l1 ++ x :: l2) = incr_bound (bruijn_of u (l1 ++ l2)) (length l1).
Proof using.
	intros u; induction u as [y|u IHu v IHv|y u IH]; intros l1 x l2 Hx; cbn.
	- assert (xney : x <> y) by (intros <-; exact (Hx LFV_Var)); clear Hx.
	  destruct (bruijn_of_var_eq y (l1 ++ x :: l2) 0) as [(l1' & l2' & eql & ynil1' & eq)|[yni eq]]; rewrite eq; clear eq.
	  + rewrite add_0_r.
	    destruct (bruijn_of_var_eq y (l1 ++ l2) 0) as [(l1'' & l2'' & eql2 & ynil1'' & eq)|[yni eq]]; rewrite eq.
	    2: contradict yni; exact (proj2 (in_app y l1 l2)
	         (match proj1 (in_app y l1 (x :: l2)) ltac:(rewrite eql, in_app; right; left; exact eq_refl) with
	         | or_introl H => or_introl H
	         | or_intror (or_introl H) => False_ind _ (xney (eq_sym H))
	         | or_intror (or_intror H) => or_intror H end)).
	    cbn; f_equal; rewrite add_0_r; clear eq.
	    generalize dependent l1''; generalize dependent l1'; induction l1 as [|hd l1 IH]; intros l1' eq1 H1 l1'' eq2 H2.
	    1: cbn in eq1, eq2 |- *; destruct l1' as [|hd l1']; [injection eq1 as eq _; contradiction (xney eq)|].
	    1: injection eq1 as <- ->; cbn; f_equal.
	    1: assert (H1' : ~ In y l1') by (intros H; exact (H1 (or_intror H))); clear H1.
	    1: generalize dependent l1''; induction l1' as [|hd l1 IH]; intros [|hd' l1'] eq H.
	    1: exact eq_refl.
	    1: injection eq as <- _; contradiction (H (or_introl eq_refl)).
	    1: injection eq as -> _; contradiction (H1' (or_introl eq_refl)).
	    1: injection eq as _ eq; refine (f_equal S (IH (fun H => H1' (or_intror H)) _ eq (fun H' => H (or_intror H')))).
	    destruct l1'' as [|hd'' l1'']; simpl length.
	    1: destruct l1' as [|hd' l1']; [exact eq_refl|injection eq2 as -> _; injection eq1 as eq _; contradiction (H1 (or_introl eq))].
	    destruct l1' as [|hd' l1']; cbn.
	    1: injection eq1 as -> _; injection eq2 as eq _; contradiction (H2 (or_introl eq)).
	    injection eq1 as _ eq1; injection eq2 as _ eq2.
	    rewrite (IH _ eq1 (fun H => H1 (or_intror H)) _ eq2 (fun H => H2 (or_intror H)));
	      destruct (length l1 <=? length l1''); exact eq_refl.
	  + destruct (bruijn_of_var_eq y (l1 ++ l2) 0) as [(l1'' & l2'' & eql2 & ynil1'' & eq)|[yni' eq]];
	      [|exact (f_equal (fun w => incr_bound w _) (eq_sym eq))].
	    contradict yni; refine (proj2 (in_app _ _ (_ :: _))
	         (match proj1 (in_app _ _ _) _ with
	         | or_introl H => or_introl H
	         | or_intror H => or_intror (or_intror H) end)); rewrite eql2, in_app; right; left; exact eq_refl.
	- f_equal; [exact (IHu _ _ _ (fun H => Hx (LFV_App_l H)))|exact (IHv _ _ _ (fun H => Hx (LFV_App_r H)))].
	- f_equal; cbn.
	  destruct (dec_V x y) as [<-|xney].
	  1: exact (bruijn_of_app_in _ (_ :: _) _ _ (or_introl eq_refl)).
	  exact (IH (_ :: _) _ _ (fun H => Hx (LFV_Abs xney H))).
Qed.
Lemma bruijn_of_cons_nfv : forall u x l, ~ lfv x u -> bruijn_of u (x :: l) = incr_bound (bruijn_of u l) O.
Proof using.
	intros u; exact (bruijn_of_app_nfv _ []).
Qed.

Lemma of_lsubst_is_bsubst_of : forall u x v l,
	(forall y, lbv y u -> ~ lfv y v) -> ~ In x l ->
	bruijn_of (lsubst_full u x v) l = bsubst (bruijn_of u l) x (bruijn_of v l).
Proof using.
	intros u x v l H1 xnil.
	pose (l' := @nil V); rewrite (eq_refl : l = l' ++ l) at 1 2;
	  rewrite (eq_refl : bruijn_of v l = (fix inner l u := match l with [] => u | _ :: l => incr_bound (inner l u) O end) l' (bruijn_of v l));
	  assert (xnil' : ~ In x l') by intros []; assert (H2 : forall y, In y l' -> ~ lfv y v) by intros ? [].
	generalize dependent l'; induction u as [y|u1 IH1 u2 IH2|y u IH]; intros l' xnil' H2.
	- cbn.
	  remember (dec_V x y) as tmp eqn:eqxeqy; destruct tmp as [<-|xney].
	  + assert (tmp : bruijn_of_var x (l' ++ l) 0 = BVar x); [|rewrite tmp; clear tmp].
	    { specialize (bruijn_of_var_eq x (l' ++ l) 0) as [(l1 & l2 & eq & _)|[_ H]]; [exfalso|exact H].
	      refine (or_ind xnil' xnil (proj1 (in_app _ _ _) _)).
	      rewrite eq; clear; induction l1 as [|h l1 IH]; [left; exact eq_refl|right; exact IH]. }
	    cbn; rewrite if_dec_refl.
	    clear - H2.
	    remember 0 as o eqn:eqo; pose (l'' := @nil V); rewrite (eq_refl : 0 = length l'') in eqo; subst o.
	    rewrite (eq_refl : l' ++ l = l'' ++ (l' ++ l)), (eq_refl : bruijn_of _ l = bruijn_of _ (l'' ++ l)).
	    assert (H : forall y, In y l' -> lfv y v -> In y l'') by (intros y H H'; exact (H2 y H H')); clear H2.
	    generalize dependent l''; induction v as [x|u IHu v IHv|x u IH]; intros l'' H.
	    2: cbn; rewrite (IHu _ (fun y H1 H2 => H _ H1 (LFV_App_l H2))), (IHv _ (fun y H1 H2 => H _ H1 (LFV_App_r H2))).
	    3: cbn; rewrite (IH
	              (_ :: _)
	              (fun y H1 H2 =>
	               ltac:(destruct (dec_V y x) as [eq|H3];
	                     [exact (or_introl eq)|exact (or_intror (H y H1 (LFV_Abs H3 H2)))]))
	              : bruijn_of u (x :: l'' ++ l' ++ l) = _).
	    2-3: clear; induction l' as [|h l' IH]; [exact eq_refl|exact (f_equal (fun w => incr_bound w (length l'')) IH)].
	    cbn; specialize (fun H1 => H _ H1 LFV_Var).
	    specialize (bruijn_of_var_eq x (l'' ++ l' ++ l) 0) as [(l1 & l2 & eql & xnil1 & eq)|[xnilll eq]]; rewrite eq; clear eq.
	    2: specialize (bruijn_of_var_eq x (l'' ++ l) 0) as [(l1 & l2 & eql & _)|[_ eq]]; [|rewrite eq].
	    2: refine (False_ind _ (xnilll (proj2 (in_app _ _ _)
	                   (match proj1 (in_app _ _ _) _ with
	                    | or_introl H => or_introl H
	                    | or_intror H => or_intror (proj2 (in_app _ _ _) (or_intror H)) end))));
	         rewrite eql; refine (proj2 (in_iff _ _) _); exists l1, l2; exact eq_refl.
	    2: clear; induction l' as [|_ l' IH]; [exact eq_refl|rewrite <-IH; exact eq_refl].
	    specialize (bruijn_of_var_eq x (l'' ++ l) 0) as [(l1' & l2' & eql' & xnil1' & eq)|[H1 H2]]; [rewrite eq; clear eq|].
	    2: refine (False_ind _ (H1 (proj2 (in_app _ _ _)
	                   (match _ with
	                    | or_introl H => or_introl H
	                    | or_intror (or_introl H') => or_introl (H H')
	                    | or_intror (or_intror H) => or_intror H end))));
	         rewrite <-!in_app, eql; refine (proj2 (in_iff _ _) _); exists l1, l2; exact eq_refl.
	    assert (tmp : l1' = l1 /\ length l1 < length l'' \/ exists l1'', l1 = l'' ++ l' ++ l1'' /\ l1' = l'' ++ l1'').
	    { generalize dependent l1; generalize dependent l1'; induction l'' as [|h l'' IH]; intros l1' eq2 H2 l1 eq1 H1.
	      - right; exists l1'; split; [cbn in *|exact eq_refl].
	        subst l; generalize dependent l1; induction l' as [|h l' IH]; intros l1 eq H1.
	        2: destruct l1 as [|h1 l1]; [injection eq as eq _; contradiction (H (or_introl (eq_sym eq)))|].
	        2: injection eq as <- eq; refine (f_equal _ (IH (fun f => H (or_intror f)) _ eq (fun f => H1 (or_intror f)))).
	        simpl in *; clear H.
	        generalize dependent l1'; induction l1 as [|h l1 IH]; intros [|h' l1'] xni'.
	        1: intros _; exact eq_refl.
	        1: intros [= eq _]; contradiction (xni' (or_introl (eq_sym eq))).
	        1: intros [= eq _]; contradiction (H1 (or_introl eq)).
	        intros [= eqh eq]; exact (f_equal2 _ (eq_sym eqh) (IH (fun f => H1 (or_intror f)) _ (fun f => xni' (or_intror f)) eq)).
	      - destruct l1 as [|h1 l1]; destruct l1' as [|h' l1'].
	        1: left; split; [exact eq_refl|exact (le_n_S _ _ (le_0_n _))].
	        1: injection eq1 as eq1 _; injection eq2 as eq2 _; contradiction (H2 (or_introl (eq_trans (eq_sym eq1) eq2))).
	        1: injection eq1 as eq1 _; injection eq2 as eq2 _; contradiction (H1 (or_introl (eq_trans (eq_sym eq2) eq1))).
	        injection eq1 as <- eq1; injection eq2 as <- eq2;
	          specialize (IH (fun xin => match H xin with or_introl f => False_ind _ (H1 (or_introl f)) | or_intror H => H end)
	                        _ eq2 (fun f => H2 (or_intror f)) _ eq1 (fun f => H1 (or_intror f))) as [[eq Hlen]|[l1'' [eql1 eql1']]].
	        1: left; split; [exact (f_equal _ eq)|exact (le_n_S _ _ Hlen)].
	        right; exists l1''; split; [exact (f_equal _ eql1)|exact (f_equal _ eql1')]. }
	    rewrite !add_0_r; destruct tmp as [[-> Hlen]|[l1'' [-> ->]]].
	    1: clear - Hlen; induction l' as [|h l' IH]; [exact eq_refl|rewrite <-IH; cbn; rewrite (proj2 (leb_gt _ _) Hlen); exact eq_refl].
	    clear; induction l' as [|h l' IH]; [exact eq_refl|rewrite <-IH; cbn;
	      rewrite length_app, (length_app l'' (l' ++ _)), (proj2 (leb_le _ _) (le_add_r _ _))];
	      exact (f_equal _ (eq_sym (plus_n_Sm _ _ : S (_ + length (_ ++ _)) = _ + length (_ :: _ ++ _))))%nat.
	  + unfold bruijn_of; specialize (bruijn_of_var_eq y (l' ++ l) 0) as [(l1 & l2 & eqll & ynil1 & eq)|[H eq]]; rewrite eq.
	    1: exact eq_refl.
	    cbn; rewrite <-eqxeqy; exact eq_refl.
	- cbn; f_equal;
	    [exact (IH1 (fun y H => H1 y (LBV_App_l H)) _ xnil' H2)
	    |exact (IH2 (fun y H => H1 y (LBV_App_r H)) _ xnil' H2)].
	- cbn; destruct (dec_V x y) as [<-|xney].
	  1: cbn; f_equal; refine (eq_sym (bsubst_nfv _ _ _ _)).
	  1: rewrite bruijn_of_fv; intros [H3 H4]; exact (H4 (or_introl eq_refl)).
	  cbn; f_equal.
	  refine (IH (fun y H => H1 y (LBV_Abs H)) (_ :: _) _ _).
	  1: intros [eq|xinl']; [exact (xney eq)|exact (xnil' xinl')].
	  1: intros z [->|zinl']; [exact (H1 _ LBV_Bound)|exact (H2 _ zinl')].
Qed.
Lemma of_lsubst_is_bsubstb_of : forall u x v l1 l2,
	(forall y, lbv y u -> ~ lfv y v) -> ~ In x l1 ->
	bruijn_of (lsubst_full u x v) (l1 ++ l2) = bsubstb (bruijn_of u (l1 ++ x :: l2)) (length l1) (bruijn_of v (l1 ++ l2)).
Proof using.
	intros u x v l1 l2 H1 xnil1.
	pose (l' := @nil V); rewrite (eq_refl : l1 = l' ++ l1);
	  assert (xnil' : ~ In x l') by intros [].
	generalize dependent l'; induction u as [y|u1 IH1 u2 IH2|y u IH]; intros l' xnil'.
	- cbn.
	  remember (dec_V x y) as tmp eqn:eqxeqy; destruct tmp as [<-|xney].
	  + assert (tmp : bruijn_of_var x ((l' ++ l1) ++ x :: l2) 0 = BBound (length (l' ++ l1))); [|rewrite tmp; clear tmp].
	    { specialize (bruijn_of_var_eq x ((l' ++ l1) ++ x :: l2) 0) as [(l1' & l2' & eq1 & xnil1' & eq2)|[H _]]; [|exfalso].
	      2: exact (H (proj2 (in_app _ _ (_ :: _)) (or_intror (or_introl eq_refl)))).
	      rewrite eq2, add_0_r; clear eq2; refine (f_equal (fun w => BBound (length w)) _).
	      clear - xnil1' xnil1 xnil' eq1; generalize dependent l1'; induction l' as [|hd l' IH].
	      2: intros [|hd' l1'] eq H; [injection eq as eq _; contradiction (xnil' (or_introl (eq_sym eq)))|injection eq as eq1 eq2].
	      2: exact (f_equal2 _ (eq_sym eq1) (IH (fun h => xnil' (or_intror h)) _ eq2 (fun h => H (or_intror h)))).
	      cbn; clear xnil'.
	      induction l1 as [|hd tl IH]; intros [|hd' tl'] eq H.
	      1: exact eq_refl.
	      1: injection eq as eq _; contradiction (H (or_introl eq)).
	      1: injection eq as eq _; contradiction (xnil1 (or_introl (eq_sym eq))).
	      injection eq as eq1 eq2; exact (f_equal2 _ (eq_sym eq1) (IH (fun h => xnil1 (or_intror h)) _ eq2 (fun h => H (or_intror h)))). }
	    unfold bsubstb; rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl; exact eq_refl.
	  + specialize (bruijn_of_app_nfv y (l' ++ l1) x l2 ltac:(intros H; inversion H; easy)) as tmp; cbn in tmp; rewrite tmp; clear tmp.
	    specialize (bruijn_of_var_eq y ((l' ++ l1) ++ l2) 0) as [(l1' & l2' & eqll & ynil1' & eq)|[H eq]]; cbn; rewrite eq; clear eq.
	    2: exact eq_refl.
	    unfold incr_bound; rewrite add_0_r.
	    remember (l' ++ l1) as l1'' eqn:eq;
	      assert (H : ~ In x l1'') by (subst l1''; rewrite in_app; intros [H|H]; [exact (xnil' H)|exact (xnil1 H)]); clear eq l' l1 xnil' xnil1 H1.
	    remember (length l1'' <=? length l1') as tmp eqn:leq; destruct tmp; unfold bsubstb.
	    1: apply eq_sym, leb_le in leq; rewrite (proj2 (ltb_ge _ _) (le_S _ _ leq)).
	    1: rewrite (proj2 (eqb_neq (S (length l1')) (length l1'')) (fun H => lt_neq _ _ (le_n_S _ _ leq) (eq_sym H))).
	    1: exact eq_refl.
	    rewrite ltb_antisym, <-leq; exact eq_refl.
	- cbn; f_equal;
	    [exact (IH1 (fun y H => H1 y (LBV_App_l H)) _ xnil')
	    |exact (IH2 (fun y H => H1 y (LBV_App_r H)) _ xnil')].
	- cbn; f_equal.
	  destruct (dec_V x y) as [<-|xney]; cbn; f_equal; swap 1 2.
	  1: specialize (IH (fun y H => H1 y (LBV_Abs H)) (y :: l') ltac:(intros [h|h]; [exact (xney h)|exact (xnil' h)])).
	  1: cbn in IH; rewrite (bruijn_of_cons_nfv v _ _ (H1 _ LBV_Bound)) in IH; exact IH.
	  generalize (incr_bound (bruijn_of v ((l' ++ l1) ++ l2)) 0); generalize (l' ++ l1); clear.
	  intros l1' w.
	  pose (l1 := x :: l1'); assert (xinl1 := or_introl eq_refl : In x l1);
	    rewrite !(eq_refl : x :: l1' ++ _ = l1 ++ _), (eq_refl : S (length l1') = length l1).
	  generalize dependent w; generalize dependent l1; clear l1'; induction u as [y|u IHu v IHv|y u IH]; intros l1 xinl1 w.
	  + cbn.
	    rewrite (bruijn_of_app_in y l1 x l2 xinl1 : bruijn_of_var _ _ _ = incr_bound (bruijn_of_var _ _ _) _).
	    clear xinl1.
	    generalize 0; generalize (length l1); generalize (l1 ++ l2); clear.
	    intros l; induction l as [|hd tl IH]; intros o n.
	    1: exact eq_refl.
	    cbn; destruct (dec_V hd y) as [->|hdney].
	    1: unfold incr_bound, bsubstb; remember (o <=? n) as tmp eqn:olen; destruct tmp.
	    1: apply eq_sym, leb_le in olen; rewrite (proj2 (ltb_ge _ _) (le_S _ _ olen));
	         rewrite (proj2 (eqb_neq _ _) (fun eq => lt_neq _ _ (le_n_S _ _ olen) (eq_sym eq))); exact eq_refl.
	    1: apply eq_sym, leb_gt in olen; rewrite (proj2 (ltb_lt _ _) olen); exact eq_refl.
	    exact (IH _ _).
	  + exact (f_equal2 _ (IHu _ xinl1 _) (IHv _ xinl1 _)).
	  + cbn; refine (f_equal _ (IH (_ :: _) (or_intror xinl1) _)).
Qed.
Lemma of_lsubst_is_bsubstb_of' : forall u x v l1 l2,
	(forall y, lbv y u -> ~ lfv y v) -> ~ In x l1 ->
	bruijn_of (lsubst_full u x v) (l1 ++ x :: l2) =
	  bsubstb (incr_bound (bruijn_of u (l1 ++ x :: l2)) (S (length l1))) (length l1) (bruijn_of v (l1 ++ x :: l2)).
Proof using.
	intros u x v l1 l2 H1 H2; rewrite (of_lsubst_is_bsubstb_of _ _ _ _ (_ :: _) H1 H2); f_equal.
	assert (tmp := bruijn_of_app_in u (l1 ++ [x]) x l2 (proj2 (in_app _ _ [_]) (or_intror (or_introl eq_refl)))).
	rewrite !app_assoc in tmp; cbn in tmp; refine (eq_trans tmp (f_equal _ _)).
	rewrite length_app, add_comm; exact eq_refl.
Qed.

Lemma subst_alpha : forall u u' x v v', alpha_eq u u' -> alpha_eq v v' ->
	(forall y, lbv y u -> ~ lfv y v) ->
	(forall y, lbv y u' -> ~ lfv y v') ->
	alpha_eq (lsubst_full u x v) (lsubst_full u' x v').
Proof using.
	intros u u' x v v' Hau Hav H H'.
	rewrite (alpha_eq_iff _ _ []).
	rewrite (of_lsubst_is_bsubstb_of u x v [] [] H ltac:(intros []) : bruijn_of _ [] = _).
	rewrite (of_lsubst_is_bsubstb_of u' x v' [] [] H' ltac:(intros []) : bruijn_of _ [] = _).
	cbn; exact (f_equal2 (fun a b => bsubstb a _ b) (proj1 (alpha_eq_iff _ _ _) Hau) (proj1 (alpha_eq_iff _ _ _) Hav)).
Qed.

Lemma bruijn_of_bruijn_eq : forall u n k, min_gt_bvars u <= n -> min_gt_fbound u <= k ->
	bruijn_of (of_bruijn u (n + k)) (rev (map V_of_nat (seq n k))) = u.
Proof using.
	intros u; induction u as [x|b|u IHu v IHv|u IH]; intros n k Hn Hk; cbn.
	- destruct (bruijn_of_var_eq x (rev (map V_of_nat (seq n k))) 0) as [(l1 & l2 & eq & _)|[H eq]]; [|exact eq].
	  clear Hk; cbn in Hn.
	  exfalso; generalize dependent k; induction l1 as [|hd l1 IH]; intros [|k] eq.
	  1,3: discriminate eq.
	  1,2: rewrite seq_r, map_app, rev_app_distr in eq.
	  2: injection eq as _ eq; exact (IH _ eq).
	  injection eq as eq _; rewrite (proj2 (onat_Some_iff _ _) (eq_sym eq)) in Hn; exact (lt_neq _ _ (le_lt_trans _ _ _ (le_add_r _ _) Hn) eq_refl).
	- cbn in Hk; clear Hn.
	  destruct (bruijn_of_var_eq (n + k - S b) (rev (map V_of_nat (seq n k))) 0) as [(l1 & l2 & eq1 & nil1 & eq)|[H eq]].
	  2: contradict H; clear - Hk; generalize dependent b; induction k as [|k IH]; intros b Hb.
	  2: inversion Hb.
	  2: destruct b as [|b]; rewrite seq_r, map_app, rev_app_distr, <-plus_n_Sm;
	       [rewrite sub_1_r; left; exact eq_refl|right; exact (IH _ (le_S_n _ _ Hb))].
	  rewrite eq; clear eq.
	  rewrite add_0_r; f_equal; generalize dependent l1; generalize dependent b; induction k as [|k IH]; intros b Hb.
	  1: inversion Hb.
	  rewrite seq_r, map_app, rev_app_distr, <-plus_n_Sm.
	  intros [|hd l1] [=eq1 eq2] nil1; destruct b as [|b].
	  1: exact eq_refl.
	  1: apply V_inj in eq1; contradict eq1.
	  1: refine (fun H => lt_neq _ _ _ (eq_sym H)); destruct k as [|k]; [apply le_S_n in Hb; inversion Hb|rewrite <-plus_n_Sm; cbn; unfold "<"].
	  1: rewrite <-(sub_succ_l _ _ (le_trans _ _ _ (le_S_n _ _ (le_S_n _ _ Hb)) (le_add_l _ _))).
	  1: exact (le_sub_l _ _).
	  1: rewrite sub_1_r in nil1; contradiction (nil1 (or_introl eq1)).
	  refine (f_equal S (IH _ (le_S_n _ _ Hb) _ eq2 (fun H => nil1 (or_intror H)))).
	- f_equal; [exact (IHu _ _ (max_lub_l _ _ _ Hn) (max_lub_l _ _ _ Hk))
	           |exact (IHv _ _ (max_lub_r _ _ _ Hn) (max_lub_r _ _ _ Hk))].
	- f_equal; specialize (IH n (S k) Hn (proj1 (le_pred_le_succ _ _) Hk)).
	  rewrite seq_r, map_app, rev_app_distr, <-plus_n_Sm in IH; exact IH.
Qed.

Lemma bruijn_of_bruijn_of : forall u l n, min_gt_vars u <= n ->
	bruijn_of u l = bruijn_of (of_bruijn (bruijn_of u l) (length l + n)) (rev (map V_of_nat (seq n (length l)))).
Proof using.
	intros u l n Hn; rewrite add_comm;
	  exact (eq_sym (bruijn_of_bruijn_eq _ _ _ (le_trans _ _ _ (min_gt_bvars_le_vars _ _) Hn) (min_gt_fbound_of _ _))).
Qed.

Lemma alpha_eq_Abs_inv : forall x u v, alpha_eq (LAbs x u) v -> exists y v', v = LAbs y v' /\ bruijn_of u [x] = bruijn_of v' [y].
Proof using.
	intros x u v H.
	apply clos_rt_rt1n in H; remember (LAbs x u) as u0 eqn:equ; generalize dependent u; generalize dependent x;
	  induction H as [u|u v w H _ IH]; intros x u' ->.
	1: exists x, u'; split; exact eq_refl.
	inversion H; subst.
	1: inversion H0; rewrite (lsubst_is_full _ _ _ H3) in H5; subst.
	1,2: specialize (IH _ _ eq_refl) as (z & v' & eq & Ha); exists z, v'; split; [exact eq|].
	- rewrite <-Ha; clear eq Ha v' w H0 H z.
	  assert (tmp := of_lsubst_is_bsubstb_of u' x y [] [y] ltac:(intros ? H1 H2; inversion H2; subst; exact (H4 H1)) ltac:(intros []));
	    cbn in tmp; rewrite tmp, if_dec_refl; clear tmp.
	  pose (l := @nil V); rewrite (eq_refl : [_] = l ++ [_]), <-(app_assoc l [_] [_] : (l ++ [_]) ++ [_] = [_; _]).
	  rewrite (eq_refl : 0 = length l).
	  generalize dependent l; clear H3; induction u' as [z|u IHu v IHv|z u IH]; intros l.
	  + unfold bruijn_of; destruct (bruijn_of_var_eq z (l ++ [x]) 0) as [(l1 & l2 & eql & znil1 & eq)|[H eq]]; rewrite eq; clear eq.
	    1,2: destruct (bruijn_of_var_eq z ((l ++ [x]) ++ [y]) 0) as [(l1' & l2' & eql' & znil1' & eq)|[H' eq]]; rewrite eq; clear eq.
	    4: exact eq_refl.
	    2: rewrite eql in H'; contradict H'; rewrite !in_app; left; right; left; exact eq_refl.
	    2: refine (False_ind _ (H6 ((ltac:(intros <-; exact LFV_Var) : y = z -> lfv y z) _))); clear - eql' H.
	    2: generalize dependent l1'; induction (l ++ [x]) as [|hd l' IH]; intros [|hd' l1] eq.
	    2: injection eq as eq _; exact eq.
	    2: injection eq as _ eq; destruct l1; discriminate eq.
	    2: injection eq as eq _; contradiction (H (or_introl (eq_sym eq))).
	    2: injection eq as _ eq; exact (IH (fun H' => H (or_intror H')) _ eq).
	    rewrite !add_0_r; unfold bsubstb; clear H4 H6.
	    assert (tmp : length l1' = length l1 /\ length l1' <= length l).
	    2: destruct tmp as [tmp1 tmp2]; inversion tmp2; subst.
	    2: rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl; exact (f_equal _ (eq_sym tmp1)).
	    2: rewrite (proj2 (ltb_lt _ _) (le_n_S _ _ H0)); exact (f_equal _ (eq_sym tmp1)).
	    generalize dependent l1; generalize dependent l1'; induction l as [|hd l IH]; intros l1' eq2 zni' l1 eq zni.
	    1: destruct l1 as [|hd ?]; [injection eq as eq _|destruct l1; discriminate eq].
	    1: destruct l1'; [split; [exact eq_refl|exact (le_n _)]|injection eq2 as eq2 _; contradiction (zni' (or_introl (eq_trans (eq_sym eq) eq2)))].
	    destruct l1' as [|hd1' l1']; [split; [|exact (le_0_n _)]|].
	    1,2: destruct l1 as [|hd1 l1].
	    1: exact eq_refl.
	    1: injection eq as eq _; injection eq2 as eq2 _; contradiction (zni (or_introl (eq_trans (eq_sym eq2) eq))).
	    1: injection eq as eq _; injection eq2 as eq2 _; contradiction (zni' (or_introl (eq_trans (eq_sym eq) eq2))).
	    injection eq as _ eq; injection eq2 as _ eq2;
	      specialize (IH _ eq2 (fun H => zni' (or_intror H)) _ eq (fun H => zni (or_intror H))) as [IH1 IH2].
	    split; [exact (f_equal S IH1)|exact (le_n_S _ _ IH2)].
	  + exact (f_equal2 _ (IHu (fun H => H4 (LBV_App_l H)) (fun H => H6 (LFV_App_l H)) _)
	                      (IHv (fun H => H4 (LBV_App_r H)) (fun H => H6 (LFV_App_r H)) _)).
	  + exact (f_equal BAbs (IH (fun H => H4 (LBV_Abs H)) (fun H => H6 (@LFV_Abs y z _ ltac:(intros <-; exact (H4 LBV_Bound)) H)) (_ :: _))).
	- rewrite <-Ha; clear w eq H Ha v' z.
	  apply alpha_eq_iff.
	  exact (rt_step H3).
Qed.

Definition arrow (R : relation bterm) : relation lterm := fun u v => over_bcontext R (bruijn_of u []) (bruijn_of v []).
Definition congruence (R : relation bterm) : relation lterm := union _ alpha_eq (clos_refl_sym_trans (arrow R)).

Lemma arrow_alphaeq : forall {R u u' v' v}, alpha_eq u u' -> arrow R u' v' -> alpha_eq v' v -> arrow R u v.
Proof using.
	intros R u u' v' v H1 H2 H3; unfold arrow in *.
	rewrite (proj1 (alpha_eq_iff _ _ []) H1), <-(proj1 (alpha_eq_iff _ _ []) H3); exact H2.
Qed.
Lemma congruence_alphaeq : forall {R u u' v' v}, alpha_eq u u' -> congruence R u' v' -> alpha_eq v' v -> congruence R u v.
Proof using.
	intros R u u' v' v H1 H2 H3; unfold congruence, union, arrow in *.
	destruct H2 as [H2|H2]; [left; exact (rt_trans H1 (rt_trans H2 H3))|].
	generalize dependent v; generalize dependent u; induction H2 as [u' v' H2|u'|u' v' H2 IH|u' w' v' H21 IH1 H22 IH2];
	  intros u H1 v H3.
	1: right; exact (rst_step (arrow_alphaeq H1 H2 H3)).
	1: left; exact (rt_trans H1 H3).
	1: specialize (IH _ (alpha_eq_sym _ _ H3) _ (alpha_eq_sym _ _ H1)) as [IH|IH]; [left; exact (alpha_eq_sym _ _ IH)|right; exact (rst_sym IH)].
	destruct (IH1 _ H1 _ rt_refl) as [IH1'|IH1'].
	1: exact (IH2 _ IH1' _ H3).
	specialize (IH2 _ rt_refl _ H3) as [IH2|IH2].
	1: exact (IH1 _ H1 _ IH2).
	right; exact  (rst_trans IH1' IH2).
Qed.

#[refine,export] Instance arrow_alpha_eq R : Respects alpha_eq (arrow R) := {}.
Proof using.
	refine ((fun H u u' v v' Hx Hy => conj (H u u' v v' Hx Hy) (H _ _ _ _ (equiv_sym Hx) (equiv_sym Hy))) _).
	intros x x' y y' Hx Hy H; exact (arrow_alphaeq (equiv_sym Hx) H Hy).
Qed.
#[refine,export] Instance congruence_alpha_eq R : Respects alpha_eq (congruence R) := {}.
Proof using.
	refine ((fun H u u' v v' Hx Hy => conj (H u u' v v' Hx Hy) (H _ _ _ _ (equiv_sym Hx) (equiv_sym Hy))) _).
	intros x x' y y' Hx Hy H; exact (congruence_alphaeq (equiv_sym Hx) H Hy).
Qed.

Lemma congruence_refl : forall {R u}, congruence R u u.
Proof using.
	intros R u; left; exact rt_refl.
Qed.
Lemma congruence_trans : forall {R u v w}, congruence R u v -> congruence R v w -> congruence R u w.
Proof using.
	intros R u v w [Huv|Huv] [Hvw|Hvw].
	1: left; exact (rt_trans Huv Hvw).
	1: exact (congruence_alphaeq Huv (or_intror Hvw) rt_refl).
	1: exact (congruence_alphaeq rt_refl (or_intror Huv) Hvw).
	right; exact (rst_trans Huv Hvw).
Qed.
Lemma congruence_sym : forall {R u v}, congruence R u v -> congruence R v u.
Proof using.
	intros R u v [Huv|Huv].
	1: left; exact (alpha_eq_sym _ _ Huv).
	right; exact (rst_sym Huv).
Qed.

#[refine,export] Instance congruence_equiv R : Equiv (congruence R) := {}.
Proof using.
	1: exact (@congruence_refl _).
	1: exact (@congruence_sym _).
	1: exact (@congruence_trans _).
Qed.

Lemma congruence_Var : forall {R} x, congruence R x x.
Proof using. intros R x; left; exact rt_refl. Qed.
Lemma congruence_App : forall {R} {u u' v v'}, congruence R u u' -> congruence R v v' -> congruence R (u v) (u' v').
Proof using.
	intros R u u' v v' Hu Hv.
	refine (congruence_trans (v:=LApp u' v) _ _).
	1: destruct Hu as [Hu|Hu]; [left; exact (alpha_eq_App Hu rt_refl)|right].
	1: induction Hu as [u u' H|u|u u' H IH|u u' u'' _ IH1 _ IH2]; [|exact rst_refl|exact (rst_sym IH)|exact (rst_trans IH1 IH2)].
	1: refine (rst_step _); unfold arrow; cbn; exact (bctx_app_l H).
	destruct Hv as [Hv|Hv]; [left; exact (alpha_eq_App rt_refl Hv)|right].
	induction Hv as [v v' H|v|v v' H IH|v v' v'' _ IH1 _ IH2]; [|exact rst_refl|exact (rst_sym IH)|exact (rst_trans IH1 IH2)].
	refine (rst_step _); unfold arrow; cbn; exact (bctx_app_r H).
Qed.
(* congruence_Abs is false, for example for the weak head beta-reduction *)

Definition is_arrow_of (Rl : relation lterm) (R : relation bterm) :=
	forall u v, arrow R u v <-> exists u' v', alpha_eq u u' /\ alpha_eq v v' /\ over_lcontext Rl u' v'.
Lemma is_arrow_is_congruence : forall {Rl R},
	is_arrow_of Rl R -> forall u v, congruence R u v <-> (over_lcontext (union _ alpha (union _ Rl Rl^t)))^* u v.
Proof using.
	intros Rl R HR u v; split.
	1: intros [H|H]; [|induction H as [u v H|u|u v H IH|u v w H1 IH1 H2 IH2]].
	6: intros H; unfold congruence; induction H as [u v H|u|u v w H1 [IH1|IH1] H2 [IH2|IH2]].
	- exact (clos_refl_trans_ext (over_lcontext_ext (fun u v H => or_introl H)) _ _ H).
	- rewrite (HR u v) in H; destruct H as [u' [v' [Hu [Hv H]]]].
	  refine (rt_trans _ (rt_trans (rt_step (over_lcontext_ext (fun u v H => or_intror (or_introl H)) _ _ H)) _)).
	  1: refine (clos_refl_trans_ext _ _ _ Hu).
	  2: refine (clos_refl_trans_ext _ _ _ (alpha_eq_sym _ _ Hv)).
	  1,2: exact (over_lcontext_ext (fun u v H => or_introl H)).
	- exact rt_refl.
	- apply clos_refl_trans_transp_permute.
	  refine (clos_refl_trans_ext _ _ _ IH); clear; intros u v H.
	  refine (over_lcontext_transp (over_lcontext_ext _ _ _ H)); clear; intros u v [H|[H|H]];
	    [left; exact (alpha_sym _ _ H)|right; right; exact H|right; left; exact H].
	- exact (rt_trans IH1 IH2).
	- rewrite !over_lcontext_union in H; destruct H as [H|[H|H]].
	  1: left; exact (rt_step H).
	  1,2: right.
	  1: refine (rst_step _).
	  2: refine (rst_sym (rst_step _)).
	  1,2: rewrite (HR _ _); refine (ex_intro _ _ (ex_intro _ _ (conj rt_refl (conj rt_refl _)))).
	  1: exact H.
	  1: exact (over_lcontext_transp H).
	- left; exact rt_refl.
	- left; exact (rt_trans IH1 IH2).
	- clear H1 H2; assert (H1 := or_introl IH1 : alpha_eq u v \/ alpha_eq u w);
	    assert (tmp : union _ alpha_eq (clos_refl_sym_trans (arrow R)) u v /\ union _ alpha_eq (clos_refl_sym_trans (arrow R)) u w);
	    [|exact (proj2 tmp)].
	    clear IH1; generalize dependent u; induction IH2 as [v w IH2|v|v w H2 IH2|v w x H2 IH2 H3 IH3]; intros u IH1.
	  2: destruct IH1 as [H|H]; split; left; exact H.
	  2: exact (proj1 (and_comm _ _) (IH2 _ (proj1 (or_comm _ _) IH1))).
	  2: destruct IH1 as [H|H].
	  2: specialize (IH2 _ (or_introl H)) as [IH21 IH22]; split;
	       [exact IH21|destruct IH22 as [IH22|IH22]; [exact (proj2 (IH3 _ (or_introl IH22)))|right; exact (rst_trans IH22 H3)]].
	  2: specialize (IH3 _ (or_intror H)) as [IH31 IH32]; split;
	       [destruct IH31 as [IH31|IH31]; [exact (proj1 (IH2 _ (or_intror IH31)))|right; exact (rst_trans IH31 (rst_sym H2))]|exact IH32].
	  destruct IH1 as [IH1|IH1]; split.
	  1,4: left; exact IH1.
	  1,2: rewrite (HR _ _) in IH2; destruct IH2 as (u' & v' & IH21 & IH22 & IH23).
	  1: right; refine (rst_step _); rewrite (HR _ _); exists u', v'; split; [exact (rt_trans IH1 IH21)|easy].
	  right; refine (rst_sym (rst_step _)); rewrite (HR _ _); exists u', v'; split; [exact IH21|split; [exact (rt_trans IH1 IH22)|exact IH23]].
	- clear H1 H2; assert (H1 := or_introl IH2 : alpha_eq v w \/ alpha_eq u w);
	    assert (tmp : union _ alpha_eq (clos_refl_sym_trans (arrow R)) u w /\ union _ alpha_eq (clos_refl_sym_trans (arrow R)) v w);
	    [|exact (proj1 tmp)].
	    clear IH2; generalize dependent w; induction IH1 as [u v IH1|u|u v H2 IH1|u v w H2 IH1 H3 IH3]; intros x IH2.
	  2: destruct IH2 as [H|H]; split; left; exact H.
	  2: exact (proj1 (and_comm _ _) (IH1 _ (proj1 (or_comm _ _) IH2))).
	  2: destruct IH2 as [H|H]; split.
	  3,4: left; exact H.
	  2: specialize (IH3 _ (or_introl H)) as [IH31 IH32];
	       destruct IH31 as [IH31|IH31]; [exact (proj1 (IH1 _ (or_introl IH31)))|right; exact (rst_trans H2 IH31)].
	  2: specialize (IH1 _ (or_intror H)) as [IH31 IH32];
	       destruct IH32 as [IH32|IH32]; [exact (proj2 (IH3 _ (or_intror IH32)))|right; exact (rst_trans (rst_sym H3) IH32)].
	  destruct IH2 as [IH2|IH2]; split.
	  2,3: left; exact IH2.
	  1,2: rewrite (HR _ _) in IH1; destruct IH1 as (u' & v' & IH11 & IH12 & IH13).
	  1: right; refine (rst_step _); rewrite (HR _ _); exists u', v'; split; [exact IH11|split; [exact (rt_trans (alpha_eq_sym _ _ IH2) IH12)|exact IH13]].
	  right; refine (rst_sym (rst_step _)); rewrite (HR _ _); exists u', v'; split; [exact (rt_trans (alpha_eq_sym _ _ IH2) IH11)|easy].
	- right; exact (rst_trans IH1 IH2).
Qed.

Lemma arrow_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (arrow R1) (arrow R2).
Proof using.
	intros R1 R2 H u v; exact (over_bcontext_ext H _ _).
Qed.
Lemma congruence_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (congruence R1) (congruence R2).
Proof using.
	intros R1 R2 H1 u v [H2|H2]; [left; exact H2|right; exact (clos_refl_sym_trans_ext (arrow_ext H1) _ _ H2)].
Qed.

Module Import ArrowNotation.
Notation "u -->_ R v" := (arrow R u v) (at level 70, R at level 5, no associativity, format "u  -->_ R  v").
Notation "u -->_ R ^+ v" := (arrow R^+ u v) (at level 70, R at level 5, no associativity, format "u  -->_ R ^+  v").
Notation "u -->_ R ^* v" := (arrow R^* u v) (at level 70, R at level 5, no associativity, format "u  -->_ R ^*  v").
Notation "u ===_ R v" := (congruence R u v) (at level 70, R at level 5, no associativity, format "u  ===_ R  v").
End ArrowNotation.


Lemma le_is_ex_add : forall m n, m <= n -> exists k, n = Nat.add k m.
Proof using.
	intros m n H; induction H as [|n H [k ->]].
	1: exists O; exact eq_refl.
	exists (S k); exact eq_refl.
Qed.


Lemma incr_nfb : forall u n, (forall k, n <= k -> ~ bfb k u) -> incr_bound u n = u.
Proof using.
	intros u; induction u as [x|k|u IHu v IHv|u IH]; intros n Hn.
	- exact eq_refl.
	- cbn; rewrite (proj2 (leb_nle _ _) (fun nlek => Hn _ nlek BFB_Var)); exact eq_refl.
	- exact (f_equal2 _ (IHu _ (fun k Hk Hf => Hn _ Hk (BFB_App_l Hf))) (IHv _ (fun k Hk Hf => Hn _ Hk (BFB_App_r Hf)))).
	- refine (f_equal _ (IH _ _)); intros [|k] Hk Hf; [inversion Hk|exact (Hn _ (le_S_n _ _ Hk) (BFB_Abs Hf))].
Qed.


Fixpoint babstract u l n := match u with
	| BVar x => bruijn_of_var x l n
	| BBound k => BBound (if k <? n then k else k + length l)
	| BApp u v => BApp (babstract u l n) (babstract v l n)
	| BAbs u => BAbs (babstract u l (S n))
end.
Fixpoint bconcrete u f := match u with
	| BVar x => BVar x
	| BBound k => f k
	| BApp u v => BApp (bconcrete u f) (bconcrete v f)
	| BAbs u => BAbs (bconcrete u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
end.

Lemma bruijn_of_app : forall u l1 l2 l3, (forall x, In x l2 -> ~ In x l3) ->
	bruijn_of u (l1 ++ l2 ++ l3) = babstract (bruijn_of u (l1 ++ l3)) l2 (length l1).
Proof using.
	intros u l1 l2 l3 H23; generalize dependent l1; induction u as [x|u IHu v IHv|x u IH]; intros l1.
	- cbn; destruct (bruijn_of_var_eq x (l1 ++ l2 ++ l3) 0) as [(l1' & l2' & eqlll & xnil1' & eq)|[xnilll eq]]; rewrite eq; clear eq.
	  2: destruct (bruijn_of_var_eq x (l1 ++ l3) 0) as [(l1' & l2' & eqll & _)|[_ eq]]; [|rewrite eq; clear eq].
	  2: contradict xnilll; rewrite !in_app;
	       refine (match proj1 (in_app _ _ _) _ with or_introl H => or_introl H | or_intror H => or_intror (or_intror H) end).
	  2: rewrite eqll, !in_app; right; left; exact eq_refl.
	  2: destruct (bruijn_of_var_eq x l2 (length l1)) as [(l1' & l2' & eql2 & _)|[_ eq]]; [|exact (eq_sym eq)].
	  2: rewrite eql2, !in_app in xnilll; contradict xnilll; right; left; right; left; exact eq_refl.
	  rewrite add_0_r; destruct (bruijn_of_var_eq x (l1 ++ l3) 0) as [(l1'' & l2'' & eql1 & xnil1'' & eq)|[xnil1 eq]]; rewrite eq; clear eq.
	  1:{ simpl babstract; rewrite add_0_r; f_equal.
	      generalize dependent l1''; generalize dependent l1'; induction l1 as [|hd l1 IH]; intros l1' eq1 xni1 l1'' eq2 xni2.
	      1: cbn in eq1, eq2 |- *; subst l3;
	           specialize (fun H => H23 _ H (proj2 (in_app _ _ (_ :: _)) (or_intror (or_introl eq_refl)))).
	      1: generalize dependent l1'; induction l2 as [|hd l2 IH]; intros l1' eq xni1; [cbn in eq; rewrite add_0_r|].
	      1:{ generalize dependent l1'; induction l1'' as [|hd l1'' IH]; intros [|hd' l1'] eq xni.
	          1: exact eq_refl.
	          1: injection eq as eq _; contradiction (xni (or_introl eq)).
	          1: injection eq as eq _; contradiction (xni2 (or_introl (eq_sym eq))).
	          cbn; injection eq as _ eq;
	            exact (f_equal S (IH (fun H => xni2 (or_intror H)) _ eq (fun H => xni (or_intror H)))). }
	      1: destruct l1' as [|hd' l1'].
	      1: injection eq as eq _; contradiction (H23 (or_introl (eq_sym eq))).
	      1: injection eq as _ eq; assert (xnil2 := (fun H => H23 (or_intror H)) : ~ In _ _);
	         assert (xnil1' := (fun H => xni1 (or_intror H)) : ~ In _ _); cbn; clear hd hd' H23 xni1;
	         rewrite <-plus_n_Sm; refine (f_equal S _).
	      1: exact (IH xnil2 _ eq xnil1').
	      destruct l1' as [|hd' l1']; [injection eq1 as eq _|injection eq1 as -> eq1].
	      1: destruct l1'' as [|hd'' l1'']; [exact eq_refl|injection eq2 as eq2 _; contradiction (xni2 (or_introl (eq_trans (eq_sym eq) eq2)))].
	      destruct l1'' as [|hd'' l1'']; [injection eq2 as eq _|injection eq2 as _ eq2].
	      1: contradiction (xni1 (or_introl (eq_sym eq))).
	      simpl length; rewrite (eq_refl : (S _ <? S _) = (length _ <? _)).
	      rewrite (IH _ eq1 (fun H => xni1 (or_intror H)) _ eq2 (fun H => xni2 (or_intror H))).
	      destruct (length l1'' <? length l1); exact eq_refl. }
	  cbn; destruct (bruijn_of_var_eq x l2 (length l1)) as [(l1'' & l2'' & eql1 & xnil1'' & eq)|[xnil2 _]]; [rewrite eq; clear eq|].
	  1:{ f_equal; clear H23.
	      rewrite add_comm; subst; generalize dependent l1'; induction l1 as [|hd l1 IH]; intros l1' eq xnil1'.
	      1:{ cbn in eq |- *; generalize dependent l1''; induction l1' as [|hd' l1' IH]; intros [|hd'' l1''] xni2 eq.
	          1: exact eq_refl.
	          1: injection eq as eq _; contradiction (xni2 (or_introl (eq_sym eq))).
	          1: injection eq as eq _; contradiction (xnil1' (or_introl eq)).
	          injection eq as _ eq; exact (f_equal S (IH (fun H => xnil1' (or_intror H)) _ (fun H => xni2 (or_intror H)) eq)). }
	      destruct l1' as [|hd' l1'].
	      1: injection eq as eq _; contradiction (xnil1 (or_introl (eq_sym eq))).
	      cbn; injection eq as _ eq;
	        exact (f_equal S (IH (fun H => xnil1 (or_intror H)) _ eq (fun H => xnil1' (or_intror H)))). }
	  exfalso; refine (match or_ind (fun H => or_introl H) (fun H => or_intror (proj1 (in_app _ _ _) H)) (proj1 (in_app _ _ _) _) with
	                   | or_introl H => xnil1 (proj2 (in_app _ _ _) (or_introl H))
	                   | or_intror (or_introl H) => xnil2 H
	                   | or_intror (or_intror H) => xnil1 (proj2 (in_app _ _ _) (or_intror H)) end).
	  rewrite eqlll, in_app; right; left; exact eq_refl.
	- exact (f_equal2 _ (IHu _) (IHv _)).
	- exact (f_equal _ (IH (_ :: _))).
Qed.
Lemma bruijn_of_app_l : forall u l1 l2, (forall x, In x l1 -> ~ In x l2) -> bruijn_of u (l1 ++ l2) = babstract (bruijn_of u l2) l1 O.
Proof using.
	intros u l1 l2 H; exact (bruijn_of_app u [] l1 l2 H).
Qed.
Lemma bruijn_of_app_r : forall u l1 l2, bruijn_of u (l1 ++ l2) = babstract (bruijn_of u l1) l2 (length l1).
Proof using.
	intros u l1 l2; assert (tmp := bruijn_of_app u l1 l2 [] ltac:(intros ? ? [])).
	rewrite !app_nil_r in tmp; exact tmp.
Qed.
Lemma bconcrete_ext : forall u f1 f2, (forall k, bfb k u -> f1 k = f2 k) ->
	bconcrete u f1 = bconcrete u f2.
Proof using.
	intros u; induction u as [x|k|u IHu v IHv|u IH]; intros f1 f2 Hf1f2.
	- exact eq_refl.
	- exact (Hf1f2 _ BFB_Var).
	- exact (f_equal2 _ (IHu _ _ (fun k Hk => Hf1f2 _ (BFB_App_l Hk))) (IHv _ _ (fun k Hk => Hf1f2 _ (BFB_App_r Hk)))).
	- refine (f_equal _ (IH _ _ _)); intros [|k] Hk; [exact eq_refl|exact (f_equal (fun a => incr_bound a O) (Hf1f2 _ (BFB_Abs Hk)))].
Qed.
Lemma babstract_bconcrete : forall u l n,
	bconcrete (babstract u l n) (fun k => if k <? n then BBound k else nth (map BVar l) (k - n) (BBound (k - length l))) = u.
Proof using.
	intros u; induction u as [x|k|u IHu v IHv|u IH]; intros l n.
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
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v.
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


Inductive beta : relation bterm :=
	| Beta : forall u v, beta <{ (^{u}) {v} }> (bsubstb u O v).
Inductive lbeta : relation lterm :=
	| LBeta : forall x u v, (forall y, lbv y u -> ~ lfv y v) -> lbeta {{ (^x, {u}) {v} }} (lsubst_full u x v).
Lemma beta_is_lbeta : is_arrow_of lbeta beta.
Proof using.
	unfold is_arrow_of, arrow.
	intros u v; split.
	- intros H.
	  rewrite over_bcontext_iff in H; destruct H as (c & u' & v' & H & equ & eqv).
	  remember (max (min_gt_vars u) (min_gt_vars v)) as n eqn:eq;
	    assert (Hnu : min_gt_vars u <= n) by (subst n; exact (le_max_l _ _));
	    assert (Hnv : min_gt_vars v <= n) by (subst n; exact (le_max_r _ _)); clear eq.
	  pose (l := O).
	  refine (match _ with ex_intro _ u' (ex_intro _ v' (conj H1 (conj H2 H3))) =>
	    ex_intro _ u' (ex_intro _ v' (conj
	      (proj2 (alpha_eq_iff _ _ (rev (map V_of_nat (seq n l)))) (eq_trans equ H1)) (conj
	      (proj2 (alpha_eq_iff _ _ (rev (map V_of_nat (seq n l)))) (eq_trans eqv H2)) H3))) end).
	  assert (Hnu' := le_trans _ _ _ (min_gt_bvars_le_vars _ []) Hnu); rewrite equ in Hnu'.
	  assert (Hnv' := le_trans _ _ _ (min_gt_bvars_le_vars _ []) Hnv); rewrite eqv in Hnv'.
	  assert (Hlu' := min_gt_fbound_of u [] : _ <= l); rewrite equ in Hlu'.
	  clear u v equ eqv Hnu Hnv.
	  generalize dependent l; rename u' into u, v' into v;
	    induction c as [|c IH v0|u0 c IH|c IH]; intros l Hlu'.
	  + cbn in Hnu', Hnv', Hlu' |- *.
	    inversion H as [u' v' eq1 eq2]; subst u v; rename u' into u, v' into v; clear H.
	    assert (Hnu := max_lub_l _ _ _ Hnu' : min_gt_bvars _ <= _);
	    assert (Hnv := max_lub_r _ _ _ Hnu' : min_gt_bvars _ <= _); clear Hnu'.
	    assert (Hlu := max_lub_l _ _ _ Hlu' : pred (min_gt_fbound _) <= _); apply le_pred_le_succ in Hlu;
	    assert (Hlv := max_lub_r _ _ _ Hlu' : min_gt_fbound _ <= _); clear Hlu'.
	    exists {{ (^(l + n)%nat, {of_bruijn u (l + S n)}) {of_bruijn v (l + n)} }}; cbn.
	    refine ((fun H1 H2 => ex_intro _ _ (conj H1 (conj _ (lctx_step (LBeta _ _ _ H2))))) _ _); swap 1 2.
	    * refine (f_equal2 (fun a b => BApp (BAbs a) b) _ _).
	      1: rewrite <-(rev_app_distr _ _ : rev (_ ++ [_]) = _ :: rev _),
	                 <-(map_app V_of_nat _ [l + n]%nat : map _ (_ ++ [_]) = map _ _ ++ _ _),
	                 (add_comm l n), <-seq_r.
	      1: rewrite add_comm, (plus_n_Sm _ _ : S n + _ = _)%nat; refine (eq_sym (bruijn_of_bruijn_eq u n (S l) Hnu Hlu)).
	      rewrite add_comm; refine (eq_sym (bruijn_of_bruijn_eq v n l Hnv Hlv)).
	    * refine (eq_trans _ (eq_sym (of_lsubst_is_bsubstb_of _ _ _ [] _ H2 ltac:(intros [])))).
	      cbn; injection H1 as equ eqv; f_equal; rewrite (eq_refl : rev_append _ [] = rev _); assumption.
	    * intros y H1 H2.
	      apply lbv_of_bruijn_inv in H1; destruct H1 as [k [-> Hk]].
	      apply lfv_of_bruijn_inv in H2.
	      clear Hlu Hnu Hnv' u.
	      rewrite <-plus_n_Sm in Hk.
	      rewrite (eq_refl : l = 0 + _)%nat in Hlv.
	      generalize dependent 0;
	        induction v as [x|b|u IHu v IHv|u IH]; intros o Hlv H2.
	      1: cbn in Hnv; rewrite (proj2 (onat_Some_iff _ _) (eq_sym H2)) in Hnv;
	           exact (lt_neq _ _ (le_lt_trans _ _ _ (le_trans _ _ _ (le_add_l _ (S _)) Hk) Hnv) eq_refl).
	      1: destruct H2 as [oleb eq]; apply V_inj in eq; subst.
	      1: refine (lt_neq _ _ (lt_le_trans _ _ _ Hk _) eq_refl).
	      1: apply le_sub_le_add_l; exact (add_le_mono _ _ _ _ (le_S _ _ oleb) (le_n _)).
	      1: destruct H2 as [H2|H2];
	           [exact (IHu (max_lub_l _ _ _ Hnv) _ (max_lub_l _ _ _ Hlv) H2)
	           |exact (IHv (max_lub_r _ _ _ Hnv) _ (max_lub_r _ _ _ Hlv) H2)].
	      exact (IH Hnv (S o) (proj1 (le_pred_le_succ _ _) Hlv) H2).
	  + specialize (IH (max_lub_l _ _ _ Hnu')
	                   (max_lub_l _ _ _ Hnv')
	                   _ (max_lub_l _ _ _ Hlu')) as (u' & v' & eq1 & eq2 & IH).
	    exists (LApp u' (of_bruijn v0 (n + l))), (LApp v' (of_bruijn v0 (n + l))).
	    split; [|split; [|exact (lctx_app_l IH)]].
	    1,2: cbn; f_equal.
	    1,3: assumption.
	    1,2: exact (eq_sym (bruijn_of_bruijn_eq _ _ _ (max_lub_r _ _ _ Hnu') (max_lub_r _ _ _ Hlu'))).
	  + specialize (IH (max_lub_r _ _ _ Hnu')
	                   (max_lub_r _ _ _ Hnv')
	                   _ (max_lub_r _ _ _ Hlu')) as (u' & v' & eq1 & eq2 & IH).
	    exists (LApp (of_bruijn u0 (n + l)) u'), (LApp (of_bruijn u0 (n + l)) v').
	    split; [|split; [|exact (lctx_app_r IH)]].
	    1,2: cbn; f_equal.
	    2,4: assumption.
	    1,2: exact (eq_sym (bruijn_of_bruijn_eq _ _ _ (max_lub_l _ _ _ Hnu') (max_lub_l _ _ _ Hlu'))).
	  + specialize (IH Hnu' Hnv' _ (proj1 (le_pred_le_succ _ _) Hlu')) as (u' & v' & eq1 & eq2 & IH).
	    exists (LAbs (n + l)%nat u'), (LAbs (n + l)%nat v').
	    rewrite seq_r, map_app, rev_app_distr in eq1, eq2; cbn in eq1, eq2.
	    split; [cbn; f_equal|split; [cbn; f_equal|exact (lctx_abs IH)]].
	    1,2: assumption.
	- intros (u' & v' & H1 & H2 & H3).
	  rewrite (proj1 (alpha_eq_iff _ _ []) H1), (proj1 (alpha_eq_iff _ _ []) H2); clear u v H1 H2;
	    rename u' into u, v' into v, H3 into H.
	  pose (l := @nil V); fold l.
	  generalize dependent l;
	    induction H as [u' v' H|u' v' w' H IH|u' v' w' H IH|x u' v' H IH]; intros l.
	  + refine (bctx_step _).
	    inversion H as [x u v H1]; subst; clear H; rename H1 into H.
	    refine (eq_ind _ (fun w => beta (bruijn_of (LApp (LAbs x u) v) l) w) (Beta _ _) _ _); fold bruijn_of.
	    exact (eq_sym (of_lsubst_is_bsubstb_of u x v [] l H ltac:(intros []))).
	  + exact (bctx_app_l (IH _)).
	  + exact (bctx_app_r (IH _)).
	  + refine (bctx_abs _); fold bruijn_of; exact (IH _).
Qed.

Lemma ctx_beta_Var_inv : forall x v, ~ (over_bcontext beta) (BVar x) v.
Proof using.
	intros x v H.
	apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & eqx & eqv)].
	destruct c as [| | |]; try discriminate eqx.
	cbn in eqx; subst u'; inversion H.
Qed.
Lemma ctx_beta_App_inv : forall u v w, over_bcontext beta <{ {u} {v} }> w ->
	(exists u', u = BAbs u' /\ w = bsubstb u' O v) \/
	(exists u', over_bcontext beta u u' /\ w = BApp u' v) \/ (exists v', over_bcontext beta v v' /\ w = BApp u v').
Proof using.
	intros u v w H; apply over_bcontext_iff in H;
	  destruct H as [c (u' & v' & H & equv & eqw)].
	destruct c as [|c v0|u0 c|]; try discriminate equv.
	- left; cbn in equv, eqw; subst u' v'.
	  destruct u as [| | |u]; inversion H as [a b c d]; subst; clear H.
	  exact (ex_intro _ _ (conj eq_refl eq_refl)).
	- right; left.
	  injection equv as equ eqv; subst; cbn.
	  refine (ex_intro _ _ (conj _ eq_refl)).
	  apply over_bcontext_iff; exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj H (conj eq_refl eq_refl))))).
	- right; right.
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

Lemma Beta_Var_inv : forall x v, ~ x -->_beta v.
Proof using.
	intros x v H; exact (ctx_beta_Var_inv _ _ H).
Qed.
Lemma Beta_App_inv : forall u v w, {{ {u} {v} }} -->_beta w ->
	(exists x u' v', (forall y, ~ (lfv y v' /\ lbv y u')) /\ alpha_eq u (LAbs x u') /\ alpha_eq v v' /\ alpha_eq w (lsubst_full u' x v')) \/
	(exists u' v', u -->_beta u' /\ alpha_eq v v' /\ w = u' v') \/ (exists u' v', alpha_eq u u' /\ v -->_beta v' /\ w = u' v').
Proof using.
	unfold arrow; cbn; intros u v w H;
	  destruct (ctx_beta_App_inv _ _ _ H) as [(u' & equ & eqw)|[(u' & Hu & eqw)|(v' & Hv & eqw)]].
	- left.
	  refine (match _ with ex_intro _ x (ex_intro _ u'' (conj H1 (conj H2 H3))) =>
	      ex_intro _ x (ex_intro _ u'' (ex_intro _ v (conj H1 (conj (proj2 (alpha_eq_iff _ _ []) H2)
	          (conj equiv_refl (proj2 (alpha_eq_iff _ _ []) H3)))))) end).
	  rewrite equ, eqw; cbn; exists (max (min_gt_vars u) (min_gt_vars v)), (of_bruijn u' (S (max (min_gt_vars u) (min_gt_vars v)))).
	  destruct u as [| |u]; try discriminate equ; injection equ as <-.
	  split; [|split].
	  1: intros y [Hy1 Hy2]; apply lbv_of_bruijn_inv in Hy2; destruct Hy2 as [k [-> Hk]].
	  1: exact (min_gt_vars_fv _ _ (le_trans _ _ _ (le_max_r _ _) (le_S_n _ _ (le_S _ _ Hk))) Hy1).
	  1: rewrite <-add_1_r; exact (f_equal BAbs (eq_sym
	          (bruijn_of_bruijn_eq _ _ 1
	             (le_trans _ _ _ (min_gt_bvars_le_vars _ _) (le_trans _ _ _ (le_max_r _ _) (le_max_l _ _)))
	             (min_gt_fbound_of _ [_])))).
	  refine (eq_trans _ (eq_sym (of_lsubst_is_bsubstb_of _ _ _ [] [] _ ltac:(intros [])))).
	  2: intros y Hy2 Hy1; apply lbv_of_bruijn_inv in Hy2; destruct Hy2 as [k [-> Hk]].
	  2: exact (min_gt_vars_fv _ _ (le_trans _ _ _ (le_max_r _ _) (le_S_n _ _ (le_S _ _ Hk))) Hy1).
	  refine (f_equal (fun a => bsubstb a O (bruijn_of v [])) _).
	  exact (bruijn_of_bruijn_of _ _ _ (le_trans _ _ _ (le_max_r _ _) (le_max_l _ _))).
	- right; left.
	  destruct w as [|w1 w2|]; try discriminate eqw; injection eqw as <- eqw.
	  exact (ex_intro _ _ (ex_intro _ _ (conj Hu (conj (proj2 (alpha_eq_iff _ _ []) (eq_sym eqw)) eq_refl)))).
	- right; right.
	  destruct w as [|w1 w2|]; try discriminate eqw; injection eqw as eqw <-.
	  exact (ex_intro _ _ (ex_intro _ _ (conj (proj2 (alpha_eq_iff _ _ []) (eq_sym eqw)) (conj Hv eq_refl)))).
Qed.
Lemma Beta_Abs_inv : forall x u v, (LAbs x u) -->_beta v ->
	exists y u' v', alpha_eq (LAbs x u) (LAbs y u') /\ u' -->_beta v' /\ alpha_eq (LAbs y v') v.
Proof using.
	intros x u v H; apply over_bcontext_iff in H; destruct H as ([| | |c] & u' & v' & H & equ & eqv);
	  try discriminate equ.
	1: cbn in equ; rewrite <-equ in H; inversion H.
	destruct v as [| |y v]; try discriminate eqv.
	injection equ as equ; injection eqv as eqv.
	pose (n := max (min_gt_vars u) (min_gt_vars v)).
	refine (ex_intro _ (V_of_nat n) (ex_intro _ _ (ex_intro _ _
	          (conj
	            (proj2 (alpha_eq_iff (LAbs _ _) (LAbs _ _) []) (f_equal BAbs (bruijn_of_bruijn_of u [x] n (le_max_l _ _))))
	          (conj _
	            (proj2 (alpha_eq_iff (LAbs _ _) (LAbs _ _) [])
	            (eq_sym (f_equal BAbs (bruijn_of_bruijn_of v [y] n (le_max_r _ _)))))))))).
	apply over_bcontext_iff; rewrite equ, eqv; cbn.
	assert (Hnu := le_trans _ _ n (min_gt_bvars_le_vars _ [x]) (le_max_l _ _)).
	assert (Hnv := le_trans _ _ n (min_gt_bvars_le_vars _ [y]) (le_max_r _ _)).
	rewrite equ in Hnu; rewrite eqv in Hnv; generalize dependent n; intros n Hnu Hnv.
	assert (tmp : forall u l, min_gt_fbound (bruijn_of u l) <= length l).
	{ clear; intros u; induction u as [x|u IHu v IHv|x u IH]; intros l.
	  - cbn; destruct (bruijn_of_var_eq x l 0) as [(l1 & l2 & eql & _ & eq)|[_ eq]]; rewrite eq.
	    2: exact (le_0_n _).
	    rewrite add_0_r, eql, length_app; cbn.
	    rewrite <-plus_n_Sm; exact (le_add_r _ _).
	  - exact (max_lub _ _ _ (IHu _) (IHv _)).
	  - cbn; specialize (IH (x :: l)); cbn in IH.
	    exact (proj2 (le_pred_le_succ _ _) IH). }
	assert (Hlu := eq_ind _ (fun a => min_gt_fbound a <= _) (tmp _ _) _ equ); cbn in Hlu.
	assert (Hlv := eq_ind _ (fun a => min_gt_fbound a <= _) (tmp _ _) _ eqv); cbn in Hlv.
	clear x y u v equ eqv tmp.
	rewrite !of_bruijn_csubst, !bruijn_of_lsubst, !app_nil_r.
	refine (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj _ (conj eq_refl eq_refl))))).
	rewrite lsubst_bctx_of, add_comm.
	assert (tmp : forall c u, min_gt_bvars u <= min_gt_bvars (subst_bcontext c u)).
	{ clear; intros c w; induction c as [|c IH v|u c IH|c IH].
	  - exact (le_n _).
	  - exact (le_trans _ _ _ IH (le_max_l _ _)).
	  - exact (le_trans _ _ _ IH (le_max_r _ _)).
	  - exact IH. }
	assert (Hnu' := le_trans _ _ _ (tmp _ _) Hnu);
	assert (Hnv' := le_trans _ _ _ (tmp _ _) Hnv); clear Hnu Hnv tmp.
	assert (tmp : forall c u, min_gt_fbound u <= offset_lcontext c + min_gt_fbound (subst_bcontext c u)).
	{ clear; intros c w; induction c as [|c IH v|u c IH|c IH].
	  - exact (le_n _).
	  - exact (le_trans _ _ _ IH (add_le_mono _ _ _ _ (le_n _) (le_max_l _ _))).
	  - exact (le_trans _ _ _ IH (add_le_mono _ _ _ _ (le_n _) (le_max_r _ _))).
	  - refine (le_trans _ _ _ IH (_ : _ <= S (offset_lcontext c + pred (min_gt_fbound (subst_bcontext _ _))))).
	  destruct (min_gt_fbound (subst_bcontext c w)) as [|k]; [exact (le_S _ _ (le_n _))|cbn; rewrite <-plus_n_Sm; exact (le_n _)]. }
	assert (Hlu' := le_trans _ _ _ (tmp _ _) (add_le_mono _ _ _ _ (le_n _) Hlu));
	assert (Hlv' := le_trans _ _ _ (tmp _ _) (add_le_mono _ _ _ _ (le_n _) Hlv)); clear Hlu Hlv tmp.
	remember (offset_lcontext c) as k eqn:eqk; clear c eqk.
	rewrite add_1_r in Hlu', Hlv'.
	assert (equ' := bruijn_of_bruijn_eq u' n (S k) Hnu' Hlu');
	assert (eqv' := bruijn_of_bruijn_eq v' n (S k) Hnv' Hlv').
	clear Hnv' Hlv' Hnu' Hlu'.
	simpl map in equ'; rewrite rev_cons in equ';
	simpl map in eqv'; rewrite rev_cons in eqv'.
	rewrite bruijn_of_app_r, <-plus_n_Sm, <-plus_Sn_m in equ', eqv'.
	rewrite length_rev, length_map, length_seq in equ', eqv'.
	rewrite <-(babstract_bconcrete (bruijn_of _ _) [V_of_nat n] k), equ' at 1.
	rewrite <-(babstract_bconcrete (bruijn_of _ _) [V_of_nat n] k), eqv'.
	match goal with |- beta (bconcrete _ ?f0) _ => pose (f := f0); fold f end.
	pose (f' := fun k' => if k' <? k then BBound k' else if k' =? k then BVar n else BBound (pred k')).
	assert (Hf : forall k', f k' = f' k').
	{ simpl map in f; simpl length in f; clear; intros k'; subst f f'; lazy beta.
	  remember (k' <? k) as tmp eqn:eq; destruct tmp; [exact eq_refl|].
	  apply eq_sym, ltb_ge, le_is_ex_add in eq; destruct eq as [m ->]; rewrite add_sub.
	  destruct m as [|m]; [rewrite eqb_refl; exact eq_refl|].
	  rewrite (proj2 (eqb_neq _ _) (fun H => lt_neq k (S _ + _) (le_n_S _ _ (le_add_l k m)) (eq_sym H))); cbn.
	  rewrite sub_0_r; destruct m; exact eq_refl. }
	rewrite !(bconcrete_ext _ _ f' (fun k _ => Hf _)); clear f Hf; subst f'.
	rewrite !bconcrete_bsubst; clear equ' eqv'.
	inversion H as [u v eq1 eq2]; clear H; subst.
	refine (eq_ind _ (fun a => beta (BApp (BAbs (bsubstb u (S k) (BVar n))) (bsubstb v k (BVar n))) a) (Beta _ _) _ _).
	pose (itern := fun A (f : A -> A) => fix inner n v := match n with O => v | S n => f (inner n v) end).
	pose (incr := fun v => incr_bound v O).
	rewrite (eq_refl : k = 0 + k)%nat at 1 3;
	  rewrite (eq_refl : bsubstb v k (BVar n) = itern _ incr 0 _);
	  rewrite (eq_refl : v = itern _ incr 0 _) at 2.
	generalize 0; intros d; generalize dependent d;
	  induction u as [x|m|u1 IH1 u2 IH2|u IH]; intros d.
	- exact eq_refl.
	- unfold bsubstb; fold bsubstb.
	  destruct (lt_ge_cases m d) as [mltd|dlem]; [rewrite (proj2 (ltb_lt _ _) mltd)|rewrite (proj2 (ltb_ge _ _) dlem)].
	  1: rewrite (proj2 (ltb_lt m (S (d + k))) (lt_trans _ _ _ mltd (le_add_r _ _))); unfold bsubstb.
	  1: rewrite (proj2 (ltb_lt m d) mltd), (proj2 (ltb_lt m (d + k)) (lt_le_trans _ _ _ mltd (le_add_r _ _))); exact eq_refl.
	  inversion dlem as [deqm|m' dlem' eqm]; subst m.
	  1: rewrite eqb_refl.
	  1: rewrite (proj2 (ltb_lt d (S (d + k))) (le_add_r _ _)); unfold bsubstb; fold bsubstb.
	  1: rewrite (proj2 (ltb_ge _ _) (le_n _)), eqb_refl.
	  all: swap 1 2.
	  1: rewrite (eqb_sym _ d), (proj2 (eqb_neq d (S m')) (lt_neq _ _ (le_n_S _ _ dlem'))); unfold bsubstb.
	  1: rewrite !pred_succ.
	  1: destruct (lt_ge_cases m' (d + k)) as [m'ltdk|dklem'].
	  1:{ rewrite (proj2 (ltb_lt _ _) m'ltdk), (proj2 (ltb_lt _ _) (le_n_S _ _ m'ltdk)).
	      rewrite (proj2 (ltb_ge _ _) dlem).
	      rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ dlem'))); exact eq_refl. }
	  1: rewrite (proj2 (ltb_ge _ _) dklem'), (proj2 (ltb_ge _ _) (le_n_S _ _ dklem')).
	  1: inversion dklem' as [dkeqm'|m dklem eqm']; subst m'.
	  1:{ rewrite !eqb_refl; exact eq_refl. }
	  1: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ (le_n_S _ _ dklem)))), (proj2 (ltb_ge _ _) dlem').
	  1: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_lt_trans _ _ _ (le_add_r _ _) (le_n_S _ _ dklem)))).
	  1: rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ dklem))).
	  1: exact eq_refl.
	  clear dlem; induction d as [|d IH]; [exact eq_refl|cbn; rewrite IH; generalize (itern _ incr d v); intros u; subst incr; clear itern IH v].
	  cbn; generalize (d + k)%nat; intros m; clear k d.
	  specialize (le_0_n _ : 0 <= m).
	  generalize 0; generalize dependent m; induction u as [x|k|u IHu v IHv|u IH]; intros m o olem.
	  + exact eq_refl.
	  + unfold bsubstb, incr_bound.
	    destruct (lt_ge_cases k m) as [kltm|mlek].
	    1: rewrite (proj2 (ltb_lt _ _) kltm).
	    1: destruct (o <=? k) as [|].
	    1: rewrite (proj2 (ltb_lt _ _) (le_n_S _ _ kltm)); exact eq_refl.
	    1: rewrite (proj2 (ltb_lt _ _) (le_S _ _ kltm)); exact eq_refl.
	    rewrite (proj2 (ltb_ge _ _) mlek), (proj2 (leb_le _ _) (le_trans _ _ _ olem mlek)), (proj2 (ltb_ge _ _) (le_n_S _ _ mlek)).
	    inversion mlek as [meqk|k' mlek' eqk]; subst k.
	    1: rewrite !eqb_refl; exact eq_refl.
	    rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ mlek'))).
	    rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ (le_n_S _ _ mlek')))).
	    unfold pred; rewrite (proj2 (leb_le _ _) (le_trans _ _ _ olem mlek')); exact eq_refl.
	  + exact (f_equal2 _ (IHu _ _ olem) (IHv _ _ olem)).
	  + exact (f_equal _ (IH _ _ (le_n_S _ _ olem))).
	- exact (f_equal2 _ (IH1 _) (IH2 _)).
	- exact (f_equal _ (IH (S _))).
Qed.

Definition normal_form := RewriteSystem.normal_form (arrow beta).
Definition normalizable := RewriteSystem.normalizable (arrow beta).
Definition strong_normalizable:= RewriteSystem.strong_normalizable (arrow beta).

Definition delta := {{ ^0, {0} {0} }}.
Definition Omega := delta delta.

Lemma alpha_delta_delta : forall v, alpha_eq delta v <-> exists x, v = LAbs x (x x).
Proof using.
	intros v; rewrite (alpha_eq_iff _ _ []); split.
	- intros H; simpl in H; rewrite if_dec_refl in H.
	  destruct v as [| |x v]; try discriminate H.
	  exists x; f_equal; injection H as H.
	  destruct v as [v0|[v1| |] [v2| |]|]; try discriminate H.
	  1: cbn in H; destruct (dec_V x v0); discriminate H.
	  injection H as eq1 eq2.
	  destruct (dec_V x v1) as [eq1'|ne]; [|discriminate eq1]; destruct (dec_V x v2) as [eq2'|ne]; [|discriminate eq2].
	  exact (f_equal2 (fun w1 w2 => (LVar w1) (LVar w2)) (eq_sym eq1') (eq_sym eq2')).
	- intros [x ->]; simpl; rewrite !if_dec_refl; exact eq_refl.
Qed.

Lemma beta_Omega_Omega : forall u v, alpha_eq u Omega -> u -->_beta v <-> alpha_eq v Omega.
Proof using.
	intros u v Hu.
	apply alpha_eq_sym, alpha_eq_App_inv in Hu; destruct Hu as (u1 & u2 & -> & H1 & H2).
	apply alpha_delta_delta in H1, H2; destruct H1 as (x & ->); destruct H2 as (y & ->).
	split.
	- intros H; apply Beta_App_inv in H; destruct H as [(z & u' & v' & H1 & H2 & H3 & H4)|[(u' & v' & H1 & H2 & ->)|(u' & v' & H1 & H2 & ->)]].
	  + destruct (proj1 (alpha_delta_delta _) (rt_trans (proj2 (alpha_delta_delta _) (ex_intro _ _ eq_refl)) H2)) as [x1 [= <- ->]];
	    destruct (proj1 (alpha_delta_delta _) (rt_trans (proj2 (alpha_delta_delta _) (ex_intro _ _ eq_refl)) H3)) as [x2 ->].
	    apply (rt_trans H4); clear; cbn; rewrite if_dec_refl.
	    apply alpha_eq_App; exact (alpha_eq_sym _ _ (proj2 (alpha_delta_delta _) (ex_intro _ _ eq_refl))).
	  + apply Beta_Abs_inv in H1; destruct H1 as (z & u'' & v'' & Ha1 & Hb & Ha2).
	    destruct (proj1 (alpha_delta_delta _) (rt_trans (proj2 (alpha_delta_delta _) (ex_intro _ _ eq_refl)) Ha1)) as [x' [= -> ->]].
	    apply Beta_App_inv in Hb; destruct Hb as [(? & ? & ? & ? & f & _)|[(? & ? & f & _)|(? & ? & _ & f & _)]].
	    1: apply alpha_eq_Var_inv in f; discriminate f.
	    1,2: contradiction (Beta_Var_inv _ _ f).
	  + apply Beta_Abs_inv in H2; destruct H2 as (z & u'' & v'' & Ha1 & Hb & Ha2).
	    destruct (proj1 (alpha_delta_delta _) (rt_trans (proj2 (alpha_delta_delta _) (ex_intro _ _ eq_refl)) Ha1)) as [x' [= -> ->]].
	    apply Beta_App_inv in Hb; destruct Hb as [(? & ? & ? & ? & f & _)|[(? & ? & f & _)|(? & ? & _ & f & _)]].
	    1: apply alpha_eq_Var_inv in f; discriminate f.
	    1,2: contradiction (Beta_Var_inv _ _ f).
	- intros H; apply alpha_eq_sym, alpha_eq_App_inv in H; destruct H as (u1 & u2 & -> & H1 & H2).
	  apply alpha_delta_delta in H1, H2; destruct H1 as [x' ->]; destruct H2 as [y' ->].
	  apply beta_is_lbeta; exists Omega, Omega; split; [|split; [|refine (lctx_step _)]].
	  1,2: rewrite (alpha_eq_iff _ _ []); cbn; rewrite !if_dec_refl; exact eq_refl.
	  assert (tmp := LBeta 0 {{ {0} {0} }} delta); fold delta Omega in tmp; cbn in tmp; rewrite if_dec_refl in tmp; refine (tmp _).
	  intros z H _; inversion H; subst; inversion H1.
Qed.

Goal ~normalizable Omega.
Proof using.
	intros [v [Hv1 Hv2]].
	assert (tmp : alpha_eq v Omega).
	{ clear Hv2.
	  pose (u := Omega); assert (tmp := rt_refl : alpha_eq u Omega); fold u in Hv1;
	    generalize dependent u; intros u H Hau; induction H as [u v H|u|u v w _ IH1 _ IH2].
	  1: exact (proj1 (beta_Omega_Omega _ _ Hau) H).
	  1: exact Hau.
	  1: exact (IH2 (IH1 Hau)). }
	clear Hv1; unfold RewriteSystem.normal_form in Hv2.
	assert (Hv := tmp).
	apply alpha_eq_sym, alpha_eq_App_inv in tmp; destruct tmp as (u1 & u2 & -> & H1 & H2).
	apply alpha_delta_delta in H1, H2; destruct H1 as [x ->]; destruct H2 as [y ->].
	refine (Hv2 Omega _).
	exact (proj2 (beta_Omega_Omega _ _ Hv) equiv_refl).
Qed.

Goal normalizable {{ (^0, {1}) {Omega} }} /\ ~ strong_normalizable {{ (^0, {1}) {Omega} }}.
Proof using.
	split.
	- exists 1; split; [|intros v H; contradiction (Beta_Var_inv _ _ H)].
	  refine (rt_step _).
	  unfold arrow; cbn; rewrite (if_dec_neq 0 1 _ _ ltac:(intros f; apply V_inj in f; discriminate f)), !if_dec_refl.
	  exact (bctx_step (Beta _ _)).
	- intros f; unfold strong_normalizable in f.
	  match type of f with RewriteSystem.strong_normalizable _ ?v =>
	    remember v as u eqn:equ; assert (Hu : alpha_eq v u) by (subst u; exact rt_refl) end.
	  clear equ; induction f as [u H IH].
	  refine (IH _ _ Hu).
	  apply alpha_eq_App_inv in Hu; destruct Hu as (u1 & u2 & -> & H1 & H2).
	  refine (bctx_app_r (proj2 (beta_Omega_Omega _ _ _) _)); exact (alpha_eq_sym _ _ H2).
Qed.

Inductive eta : relation bterm :=
	| Eta : forall u, eta (BAbs (BApp (incr_bound u O) (BBound O))) u.
Definition leta u v := exists x, ~ lfv x v /\ u = LAbs x (v x).

Lemma eta_is_leta : is_arrow_of leta eta.
Proof using.
	unfold is_arrow_of, arrow, leta.
	intros u v; split.
	- intros H.
	  apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & equ & eqv)].
	  assert (eqctx : forall u u' n, min_gt_vars u <= n -> bruijn_of u [] = subst_bcontext c u' -> bcontext_of (of_bcontext c n) [] = c).
	  { clear; intros u u' n equ Hn.
	    rewrite (eq_refl : [] = rev (map V_of_nat (seq n (length (@nil V))))); rewrite (eq_refl : n = length (@nil V) + n)%nat at 1.
	    generalize dependent (@nil V); generalize dependent u; generalize dependent u';
	      induction c as [|c IH v|u c IH|c IH]; intros u' w Hn l eq.
	    - exact eq_refl.
	    - destruct w as [x|w1 w2|]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      refine (f_equal2 BCApp_l (IH _ _ (max_lub_l _ _ _ Hn) _ eq1) _); fold bcontext_of of_bcontext.
	      subst v.
	      exact (eq_sym (bruijn_of_bruijn_of w2 l n (max_lub_r _ _ _ Hn))).
	    - destruct w as [x|w1 w2|]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      refine (f_equal2 BCApp_r _ (IH _ _ (max_lub_r _ _ _ Hn) _ eq2)); fold bcontext_of of_bcontext.
	      subst u.
	      exact (eq_sym (bruijn_of_bruijn_of w1 l n (max_lub_l _ _ _ Hn))).
	    - destruct w as [x|w1 w2|]; [cbn in eq|discriminate eq|injection eq as eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      refine (f_equal BCAbs _); fold bcontext_of of_bcontext.
	      specialize (IH u' w (max_lub_r _ _ _ Hn) (v :: l) eq); simpl length in IH; rewrite seq_r, map_app, rev_app_distr in IH.
	      rewrite add_comm at 2; exact IH. }
	  inversion H as [u0 eq1 eq2]; subst u' v'; clear H; rename u0 into v'.
	  pose (n := min_gt_vars u); specialize (eqctx _ _ n (le_n _) equ).
	  refine (match _ with ex_intro _ x (ex_intro _ v1 (conj H1 (conj H2 H3))) =>
	            ex_intro _ _ (ex_intro _ _ (conj (proj2 (alpha_eq_iff _ _ []) H1) (conj (proj2 (alpha_eq_iff _ _ []) H2)
	              (proj2 (over_lcontext_iff _ _ _) (ex_intro _ (of_bcontext c n)
	                        (ex_intro _ _ (ex_intro _ v1 (conj (ex_intro _ x (conj H3 eq_refl)) (conj eq_refl eq_refl))))))))) end).
	  rewrite equ, eqv.
	  refine (match _ with ex_intro _ x (ex_intro _ v1 (conj H1 (conj H2 H3))) =>
	            ex_intro _ x (ex_intro _ v1
	              (conj (eq_trans H1 (eq_sym (bruijn_of_lsubst _ _ _)))
	              (conj (eq_trans H2 (eq_sym (bruijn_of_lsubst _ _ _))) H3))) end).
	  rewrite eqctx, app_nil_r.
	  refine (match _ with ex_intro _ x (ex_intro _ v1 (conj H1 (conj H2 H3))) =>
	            ex_intro _ x (ex_intro _ v1
	              (conj (f_equal (fun a => subst_bcontext c a) H1)
	              (conj (f_equal (fun a => subst_bcontext c a) H2) H3))) end); cbn.
	  refine (match _ with ex_intro _ x (ex_intro _ v1 (conj H1 (conj H2 H3))) =>
	            ex_intro _ x (ex_intro _ v1
	              (conj (f_equal2 (fun a b => BAbs (BApp a b)) H1 (eq_sym (if_dec_refl _ _ _)))
	              (conj H2 H3))) end); cbn.
	  assert (tmp := f_equal (fun a => of_bruijn a n) eqv); cbn in tmp.
	  rewrite of_bruijn_csubst in tmp.
	  rewrite lsubst_bctx_of.
	  exists (n + offset_lcontext c)%nat, (of_bruijn v' (n + offset_lcontext c)); cbn.
	  assert (Hn : min_gt_bvars v' <= n).
	  { clear - equ; unfold n; generalize dependent u; generalize dependent (@nil V); induction c as [|c IH v|u' c IH|c IH]; intros l u eq n.
	    - destruct u as [x|u v|x u]; [cbn in eq|discriminate eq|injection eq as eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      destruct u as [y|u v|y u]; [cbn in eq; destruct (dec_V x y); [discriminate eq|]|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq y l 1) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      refine (le_trans _ _ _ _ (le_trans (min_gt_vars _) _ _ (le_max_l _ _) (le_max_r _ _))).
	      clear - eq1; generalize dependent (x :: l); generalize 0; clear; generalize dependent u;
	        induction v' as [y|n|u1 IH1 u2 IH2|u IH]; intros u0 o l eq.
	      + destruct u0 as [z| |]; [cbn in eq|discriminate eq|discriminate eq].
	      destruct (bruijn_of_var_eq z l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; [rewrite eq2 in eq; discriminate eq|].
	      rewrite eq2 in eq; injection eq as ->; exact (le_n _).
	      + exact (le_0_n _).
	      + destruct u0 as [z| |]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	        1: destruct (bruijn_of_var_eq z l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in eq; discriminate eq.
	        exact (max_lub _ _ _ (le_trans _ _ _ (IH1 _ _ _ eq1) (le_max_l _ _)) (le_trans _ _ _ (IH2 _ _ _ eq2) (le_max_r _ _))).
	      + destruct u0 as [z| |]; [cbn in eq|discriminate eq|injection eq as eq].
	        1: destruct (bruijn_of_var_eq z l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in eq; discriminate eq.
	        exact (le_trans _ _ _ (IH _ _ _ eq) (le_max_r _ _)).
	    - destruct u as [x|u1 u2|x u1]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      exact (le_trans _ _ _ (IH _ _ eq1) (le_max_l _ _)).
	    - destruct u as [x|u1 u2|x u1]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      exact (le_trans _ _ _ (IH _ _ eq2) (le_max_r _ _)).
	    - destruct u as [x|u1 u2|x u1]; [cbn in eq|discriminate eq|injection eq as eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      exact (le_trans _ _ _ (IH _ _ eq) (le_max_r _ _)). }
	  assert (Hc : min_gt_fbound v' <= offset_lcontext c).
	  { clear - eqv.
	    rewrite (eq_refl : offset_lcontext c = length (@nil V) + _)%nat; generalize dependent (@nil V);
	    generalize dependent v'; generalize dependent v;
	    induction c as [|c IH v'|u' c IH|c IH]; intros u u0 l eq.
	    - cbn in eq |- *; rewrite add_0_r, <-eq; clear.
	      generalize dependent l;
	        induction u as [x|u IHu v IHv|x u IH]; intros l.
	      + cbn; destruct (bruijn_of_var_eq x l 0) as [(l1 & l2 & eql & _ & eq)|[_ eq]]; rewrite eq; [cbn|exact (le_0_n _)].
	        rewrite add_0_r, eql, length_app, <-(plus_n_Sm _ _ : _ = _ + length (_ :: _))%nat; exact (le_add_r _ _).
	      + exact (max_lub _ _ _ (IHu _) (IHv _)).
	      + cbn; apply le_pred_le_succ; exact (IH (_ :: _)).
	    - destruct u as [x|u v|x u]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      exact (IH _ _ _ eq1).
	    - destruct u as [x|u v|x u]; [cbn in eq|injection eq as eq1 eq2|discriminate eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      exact (IH _ _ _ eq2).
	    - destruct u as [x|u v|x u]; [cbn in eq|discriminate eq|injection eq as eq].
	      1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq1)|[_ eq1]]; rewrite eq1 in eq; discriminate eq.
	      rewrite <-(plus_n_Sm _ _ : S _ + offset_lcontext c = _ + offset_lcontext (BCAbs _))%nat; exact (IH _ _ (_ :: _) eq). }
	  generalize dependent n; intros n eqctx tmp Hn.
	  refine ((fun H1 H2 => conj _ (conj H1 H2)) _ _).
	  + assert (tmp' := fun l => bruijn_of_app_nfv (of_bruijn v' (n + offset_lcontext c)) [] (n + offset_lcontext c)%nat l H2).
	    cbn in tmp'; rewrite tmp'; exact (f_equal (fun a => incr_bound a O) H1).
	  + exact (eq_sym (bruijn_of_bruijn_eq v' _ _ Hn Hc)).
	  + remember (offset_lcontext c) as k; clear - Hn Hc; intros f; apply lfv_of_bruijn_inv in f.
	    pose (o := O); fold o in f; rewrite (eq_refl : k = o + k)%nat in Hc; generalize dependent o;
	      induction v' as [x|b|u IHu v IHv|u IH]; intros o Ho f.
	    * cbn in Hn; rewrite (proj2 (onat_Some_iff _ _) (eq_sym f)) in Hn;
	        exact (lt_neq _ _ (le_n_S _ _ (le_trans _ _ _ Hn (le_add_r _ _))) eq_refl).
	    * cbn in Ho; destruct f as [oleb eq]; apply V_inj in eq.
	      apply le_is_ex_add in oleb; destruct oleb as [m ->].
	      rewrite (add_comm o _), (add_comm (S m) o : S (_ + _) = _), sub_add_distr, add_sub, sub_succ_r in eq.
	      refine (lt_neq _ _ _ (eq_sym eq)).
	      apply le_is_ex_add in Ho; destruct Ho as [p Hp].
	      destruct k as [|k]; [exfalso; rewrite add_0_r in Hp; refine (lt_neq _ _ (lt_le_trans _ _ _ (le_n_S _ _ (le_add_l _ _)) (le_add_l _ _)) Hp)|].
	      rewrite <-plus_n_Sm; generalize (n + k)%nat; clear.
	      destruct m as [|m]; [intros ?; exact (le_n _)|cbn].
	      intros n; apply le_pred_le_succ; cbn; apply le_pred_le_succ; exact (le_trans _ _ _ (le_sub_l _ _) (le_S _ _ (le_n _))).
	    * destruct f as [f|f]; [exact (IHu (max_lub_l _ _ _ Hn) _ (max_lub_l _ _ _ Ho) f)
	                           |exact (IHv (max_lub_r _ _ _ Hn) _ (max_lub_r _ _ _ Ho) f)].
	    * refine (IH Hn _ _ f); apply le_pred_le_succ; exact Ho.
	- intros (u' & v' & Hu & Hv & H); apply over_lcontext_iff in H; destruct H as [c (u'' & v'' & (x & lfvxv'' & ->) & -> & ->)].
	  rewrite (proj1 (alpha_eq_iff _ _ []) Hu), (proj1 (alpha_eq_iff _ _ []) Hv).
	  rewrite !bruijn_of_lsubst, app_nil_r.
	  apply over_bcontext_iff; refine (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj _ (conj eq_refl eq_refl))))).
	  cbn; rewrite if_dec_refl; refine (eq_ind _ (fun a => eta (BAbs (BApp a _)) _) (Eta (bruijn_of v'' (lsubst_bcontext c))) _ _).
	  exact (eq_sym (bruijn_of_app_nfv _ [] _ _ lfvxv'')).
Qed.

Inductive psubst_b : relation bterm :=
	| PS_Var : forall {x}, psubst_b (BVar x) (BVar x)
	| PS_Bound : forall {n}, psubst_b (BBound n) (BBound n)
	| PS_App : forall {u u' v v'}, psubst_b u u' -> psubst_b v v' -> psubst_b (BApp u v) (BApp u' v')
	| PS_Abs : forall {u u'}, psubst_b u u' -> psubst_b (BAbs u) (BAbs u')
	| PS_Beta : forall {u u' v v'}, psubst_b u u' -> psubst_b v v' -> psubst_b (BApp (BAbs u) v) (bsubstb u' O v').

Lemma psubst_b_refl : forall {u}, psubst_b u u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH].
	- exact PS_Var.
	- exact PS_Bound.
	- exact (PS_App IHu IHv).
	- exact (PS_Abs IH).
Qed.

Lemma incr_bound_comm : forall {u n1 n2}, n1 <= n2 -> incr_bound (incr_bound u n2) n1 = incr_bound (incr_bound u n1) (S n2).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n1 n2 Hn.
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
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v m nlem.
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
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v m mlen.
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
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v.
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
	intros u1; induction u1 as [x|k|u11 IH1 u12 IH2|u1 IH]; intros u2 u3 n1 n2 Hn.
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

Lemma psubst_b_bsubstb : forall {u1 u2 u1' u2' n}, psubst_b u1 u1' -> psubst_b u2 u2' -> psubst_b (bsubstb u1 n u2) (bsubstb u1' n u2').
Proof using.
	refine (fun u1 u2 u1' u2' n H1 => (_ : forall u2 u2' n, _) u2 u2' n); clear u2 u2' n.
	induction H1 as [x|k|u11 u11' u12 u12' H11 IH11 H12 IH12|u1 u1' H1 IH1|u11 u11' u12 u12' H11 IH11 H12 IH12];
	  intros u2 u2' n H2.
	- exact PS_Var.
	- unfold bsubstb; destruct (k <? n); [|destruct (k =? n); [exact H2|]]; exact PS_Bound.
	- exact (PS_App (IH11 _ _ _ H2) (IH12 _ _ _ H2)).
	- cbn; refine (PS_Abs (IH1 _ _ _ _)).
	  clear - H2; generalize 0; induction H2 as [x|k|u1 u1' u2 u2' H1 IH1 H2 IH2|u u' H IH|u1 u1' u2 u2' H1 IH1 H2 IH2];
	    intros n.
	  + exact PS_Var.
	  + exact psubst_b_refl.
	  + exact (PS_App (IH1 _) (IH2 _)).
	  + exact (PS_Abs (IH (S n))).
	  + rewrite (incr_bsubstb_le (le_0_n _)); cbn; exact (PS_Beta (IH1 _) (IH2 _)).
	- cbn.
	  rewrite (bsubstb_comm (le_0_n _)).
	  refine (PS_Beta (IH11 _ _ _ _) (IH12 _ _ _ H2)).
	  clear - H2; generalize 0; induction H2 as [x|k|u u' v v' Hu IHu Hv IHv|u u' H IH|u u' v v' Hu IHu Hv IHv]; intros n.
	  1: exact PS_Var.
	  1: exact PS_Bound.
	  1: exact (PS_App (IHu _) (IHv _)).
	  1: exact (PS_Abs (IH _)).
	  1: rewrite (incr_bsubstb_le (le_0_n _)); exact (PS_Beta (IHu _) (IHv _)).
Qed.

Lemma psubst_b_strong_confluence : RewriteSystem.strong_confluence eq psubst_b.
Proof using.
	unfold RewriteSystem.strong_confluence.
	refine (fun u u1 u2 H1 H2 => match _ with ex_intro _ u' (conj H1 H2) => ex_intro _ u' (conj (or_introl H1) (or_introl H2)) end).
	generalize dependent u2; generalize dependent u1; induction u as [x|n|u IHu v IHv|u IH]; intros u1 H1 u2 H2.
	1-4: inversion H1 as [x1 eqx1 eq1|n1 eqn1 eq1|u11 u11' u12 u12' H11 H12 eq11 eq1|u10 u1' H1' eq10 eq1|u11 u11' u12 u12' H11 H12 eq11 eq1];
	       subst; clear H1.
	1-5: inversion H2 as [x2 eqx2 eq2|n2 eqn2 eq2|u21 u21' u22 u22' H21 H22 eq21 eq2|u20 u2' H2' eq20 eq2|u21 u21' u22 u22' H21 H22 eq21 eq2];
	       subst; clear H2.
	- exists (BVar x); split; exact PS_Var.
	- exists (BBound n); split; exact PS_Bound.
	- specialize (IHu _ H11 _ H21) as [u1 [Hu11 Hu12]].
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (BApp u1 u2); split; refine (PS_App _ _); assumption.
	- inversion H11 as [| | |u10 u11 H0 eq10 eq1|]; subst; clear H11; rename H0 into H11.
	  specialize (IHu _ (PS_Abs H11) _ (PS_Abs H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11' as [| | |u10 u1 Hu11 eq10 eq1|]; clear Hu11'; subst.
	  inversion Hu12' as [| | |u10 u1' Hu12 eq10 eq1|]; clear Hu12'; subst.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (bsubstb u1 O u2); split.
	  2: exact (psubst_b_bsubstb Hu12 Hu22).
	  exact (PS_Beta Hu11 Hu21).
	- inversion H21 as [| | |u10 u21 H0 eq10 eq1|]; subst; clear H21; rename H0 into H21.
	  specialize (IHu _ (PS_Abs H11) _ (PS_Abs H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11' as [| | |u10 u1 Hu11 eq10 eq1|]; clear Hu11'; subst.
	  inversion Hu12' as [| | |u10 u1' Hu12 eq10 eq1|]; clear Hu12'; subst.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (bsubstb u1 O u2); split.
	  1: exact (psubst_b_bsubstb Hu11 Hu21).
	  exact (PS_Beta Hu12 Hu22).
	- specialize (IHu _ (PS_Abs H11) _ (PS_Abs H21)) as [u1' [Hu11' Hu12']].
	  inversion Hu11'; subst; clear Hu11'; rename H0 into Hu11, u' into u1.
	  inversion Hu12'; subst; clear Hu12'; rename H1 into Hu12.
	  specialize (IHv _ H12 _ H22) as [u2 [Hu21 Hu22]].
	  exists (bsubstb u1 0 u2).
	  split; refine (psubst_b_bsubstb _ _); assumption.
	- specialize (IH _ H1' _ H2') as [u' [IH1 IH2]].
	  exists (BAbs u'); split; refine (PS_Abs _); assumption.
Qed.

Lemma arrow_is_psubst_b : forall {u v}, over_bcontext beta u v -> psubst_b u v.
Proof using.
	intros u v H; apply over_bcontext_iff in H; destruct H as [c (u' & v' & H & -> & ->)].
	induction c as [|c IH v|u c IH|c IH].
	2: exact (PS_App IH psubst_b_refl).
	2: exact (PS_App psubst_b_refl IH).
	2: exact (PS_Abs IH).
	cbn; inversion H as [u v]; subst; clear H.
	exact (PS_Beta psubst_b_refl psubst_b_refl).
Qed.
Lemma psubst_b_is_arrows : forall {u v}, psubst_b u v -> (over_bcontext beta)^* u v.
Proof using.
	intros u v H; induction H as [x|n|u u' v v' _ IH1 _ IH2|u v _ IH|u u' v v' _ IH1 _ IH2].
	1,2: exact rt_refl.
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
	- refine (rt_trans (y:=BApp (BAbs u') v') (rt_trans (y:=BApp (BAbs u') v) _ _) (rt_step (bctx_step (Beta _ _)))).
	  1: clear - IH1; induction IH1 as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  4: clear - IH2; induction IH2 as [v v' H|v|v v' v'' _ IH1 _ IH2].
	  2,5: exact rt_refl.
	  2,4: exact (rt_trans IH1 IH2).
	  1: exact (rt_step (bctx_app_l (bctx_abs H))).
	  1: exact (rt_step (bctx_app_r H)).
Qed.

Lemma confluence_beta : RewriteSystem.confluence eq (over_bcontext beta).
Proof using.
	intros u v1 v2 H1 H2.
	apply (clos_refl_trans_ext (@arrow_is_psubst_b)) in H1, H2.
	specialize (RewriteSystem.strong_confluence_is_confluence _ _ psubst_b_strong_confluence _ _ _ H1 H2) as [w' [Hw1 Hw2]].
	apply or_comm, clos_rt_iff_eq_clos_t in Hw1, Hw2.
	clear u H1 H2; rename v1 into u1, v2 into u2, w' into v', Hw1 into Hv1, Hw2 into Hv2.
	apply (clos_refl_trans_ext (@psubst_b_is_arrows)) in Hv1, Hv2.
	assert (tmp : forall A R (x y : A), R^*^* x y -> R^* x y); [|apply tmp in Hv1, Hv2; clear tmp].
	{ clear; intros A R x y H; induction H as [x y H|x|x y z _ IH1 _ IH2].
	  1: exact H.
	  1: exact rt_refl.
	  1: exact (rt_trans IH1 IH2). }
	exists v'; split.
	1: exact (proj1 (or_comm _ _) (proj1 clos_rt_iff_eq_clos_t Hv1)).
	exact (proj1 (or_comm _ _) (proj1 clos_rt_iff_eq_clos_t Hv2)).
Qed.

Lemma confluence_arrow_beta : RewriteSystem.confluence alpha_eq (arrow beta).
Proof using.
	intros u v1 v2 H1 H2.
	apply (clos_rt_compose_swap (f:=fun a => bruijn_of a [])) in H1, H2.
	destruct (confluence_beta _ _ _ H1 H2) as [v' [Hv1 Hv2]].
	rewrite or_comm, <-clos_rt_iff_eq_clos_t in Hv1.
	rewrite or_comm, <-clos_rt_iff_eq_clos_t in Hv2.
	clear u H1 H2; rename v1 into u1, v2 into u2.
	assert (tmp : min_gt_fbound v' = 0).
	{ refine (proj1 (le_0_r _) _).
	  clear - Hv1.
	  rewrite (eq_refl : 0 = length (@nil V)); remember (bruijn_of u1 []) as u;
	    generalize dependent u1; generalize dependent (@nil V);
	    induction Hv1 as [u v H|u|u v w H1 IH1 H2 IH2]; intros l u' ->.
	  - remember (bruijn_of u' l) as u eqn:equ; generalize dependent l; generalize dependent u';
	    induction H as [u u' H|u u' v H IH|u v v' H IH|u v H IH]; intros u0 l eq.
	    2,3,4: destruct u0 as [x|u01 u02|x u0]; try discriminate eq; cbn in eq.
	    2,4,6: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in eq; discriminate eq.
	    2: injection eq as -> ->; exact (max_lub _ _ _ (IH _ _ eq_refl) (min_gt_fbound_of _ _)).
	    2: injection eq as -> ->; exact (max_lub _ _ _ (min_gt_fbound_of _ _) (IH _ _ eq_refl)).
	    2: injection eq as ->; apply le_pred_le_succ; exact (IH _ _ eq_refl).
	    inversion H as [u1 u2 equ equ']; subst; clear H.
	    destruct u0 as [x|u01 u02|x u0]; try discriminate equ; cbn in equ.
	    1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in equ; discriminate equ.
	    injection equ as eq ->.
	    destruct u01 as [x|u01 u012|x u0]; try discriminate eq; cbn in eq.
	    1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in eq; discriminate eq.
	    injection eq as ->.
	    assert (tmp := eq_refl : max (pred (length (x :: l))) (length l) = max (length l) (length l));
	      rewrite (max_id (length l)) in tmp; rewrite <-tmp; clear tmp.
	    specialize (le_n_S _ _ (le_0_n _) : 0 < length (x :: l)).
	    generalize (x :: l); clear x; generalize dependent l; generalize 0; generalize dependent u02;
	      induction u0 as [x|u1 IH1 u2 IH2|x u IH]; intros v n l2 l1 Hn.
	    + cbn; destruct (bruijn_of_var_eq x l1 0) as [(l11 & l12 & eql1 & _ & eq)|[_ eq]]; rewrite eq.
	      2: exact (le_0_n _).
	      rewrite add_0_r; clear eq; unfold bsubstb.
	      destruct (lt_ge_cases (length l11) n) as [ltn|nle].
	      1: rewrite (proj2 (ltb_lt _ _) ltn); cbn.
	      1: refine (lt_le_trans _ _ _ (le_trans _ _ _ ltn (le_S_n _ _ _)) (le_max_l _ _)).
	      1: destruct (length l1); [inversion Hn|exact Hn].
	      rewrite (proj2 (ltb_ge _ _) nle).
	      inversion nle as [neq|l' H eqlen].
	      1: rewrite eqb_refl; exact (le_trans _ _ _ (min_gt_fbound_of _ _) (le_max_r _ _)).
	      rewrite eql1, length_app, <-eqlen, eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))); cbn.
	      rewrite <-plus_n_Sm; exact (le_trans _ _ _ (le_add_r _ _) (le_max_l _ _)).
	    + cbn; exact (max_lub _ _ _ (IH1 _ _ _ _ Hn) (IH2 _ _ _ _ Hn)).
	    + cbn; apply le_pred_le_succ; rewrite succ_max_distr; specialize (IH v (S n) (V_of_nat (min_gt_vars v) :: l2) (x :: l1) (le_n_S _ _ Hn)).
	      refine (eq_ind _ (fun a => min_gt_fbound (bsubstb _ _ a) <= _) (eq_ind _ (fun a => _ <= max a _) IH _ _) _ _).
	      1: cbn; destruct (length l1); [inversion Hn|exact eq_refl].
	      exact (bruijn_of_app_nfv v [] (min_gt_vars v) l2 (min_gt_vars_fv _ _ (le_n _))).
	  - exact (min_gt_fbound_of _ _).
	  - specialize (IH1 _ _ eq_refl).
	    specialize (IH2 _ _ (eq_sym (bruijn_of_bruijn_eq _ _ _ (le_n _) (le_n _)))).
	    rewrite length_rev, length_map, length_seq in IH2.
	    exact (le_trans _ _ _ IH2 IH1). }
	rewrite <-(bruijn_of_bruijn_eq v' _ _ (le_n _) (le_n _)) in Hv1, Hv2.
	rewrite tmp, add_0_r in Hv1, Hv2; cbn in Hv1, Hv2; clear tmp.
	remember (of_bruijn v' (min_gt_bvars v')) as v eqn:eqw.
	exists v; refine ((fun H => conj (H u1 Hv1) (H u2 Hv2)) _).
	clear; intros u H; rewrite (alpha_eq_iff _ _ []).
	remember (bruijn_of u []) as u' eqn:equ; remember (bruijn_of v []) as v' eqn:eqv;
	  generalize dependent v; generalize dependent u; induction H as [u v H|u|u v w H1 IH1 _ IH2]; intros u' equ v' eqv.
	1: subst u v; left; exact (t_step H).
	1: right; exact eq_refl.
	subst u w; rename v' into w'.
	specialize (IH1 _ eq_refl); specialize (fun v' H => IH2 v' H _ eq_refl).
	assert (tmp : min_gt_fbound v = 0).
	{ refine (proj1 (le_0_r _) _).
	  clear - H1.
	  rewrite (eq_refl : 0 = length (@nil V)); remember (bruijn_of u' []) as u;
	    generalize dependent u'; generalize dependent (@nil V);
	    induction H1 as [u v H|u|u v w H1 IH1 H2 IH2]; intros l u' ->.
	  - remember (bruijn_of u' l) as u eqn:equ; generalize dependent l; generalize dependent u';
	    induction H as [u u' H|u u' v H IH|u v v' H IH|u v H IH]; intros u0 l eq.
	    2,3,4: destruct u0 as [x|u01 u02|x u0]; try discriminate eq; cbn in eq.
	    2,4,6: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in eq; discriminate eq.
	    2: injection eq as -> ->; exact (max_lub _ _ _ (IH _ _ eq_refl) (min_gt_fbound_of _ _)).
	    2: injection eq as -> ->; exact (max_lub _ _ _ (min_gt_fbound_of _ _) (IH _ _ eq_refl)).
	    2: injection eq as ->; apply le_pred_le_succ; exact (IH _ _ eq_refl).
	    inversion H as [u1 u2 equ equ']; subst; clear H.
	    destruct u0 as [x|u01 u02|x u0]; try discriminate equ; cbn in equ.
	    1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in equ; discriminate equ.
	    injection equ as eq ->.
	    destruct u01 as [x|u01 u012|x u0]; try discriminate eq; cbn in eq.
	    1: destruct (bruijn_of_var_eq x l 0) as [(? & ? & _ & _ & eq2)|[_ eq2]]; rewrite eq2 in eq; discriminate eq.
	    injection eq as ->.
	    assert (tmp := eq_refl : max (pred (length (x :: l))) (length l) = max (length l) (length l));
	      rewrite (max_id (length l)) in tmp; rewrite <-tmp; clear tmp.
	    specialize (le_n_S _ _ (le_0_n _) : 0 < length (x :: l)).
	    generalize (x :: l); clear x; generalize dependent l; generalize 0; generalize dependent u02;
	      induction u0 as [x|u1 IH1 u2 IH2|x u IH]; intros v n l2 l1 Hn.
	    + cbn; destruct (bruijn_of_var_eq x l1 0) as [(l11 & l12 & eql1 & _ & eq)|[_ eq]]; rewrite eq.
	      2: exact (le_0_n _).
	      rewrite add_0_r; clear eq; unfold bsubstb.
	      destruct (lt_ge_cases (length l11) n) as [ltn|nle].
	      1: rewrite (proj2 (ltb_lt _ _) ltn); cbn.
	      1: refine (lt_le_trans _ _ _ (le_trans _ _ _ ltn (le_S_n _ _ _)) (le_max_l _ _)).
	      1: destruct (length l1); [inversion Hn|exact Hn].
	      rewrite (proj2 (ltb_ge _ _) nle).
	      inversion nle as [neq|l' H eqlen].
	      1: rewrite eqb_refl; exact (le_trans _ _ _ (min_gt_fbound_of _ _) (le_max_r _ _)).
	      rewrite eql1, length_app, <-eqlen, eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H))); cbn.
	      rewrite <-plus_n_Sm; exact (le_trans _ _ _ (le_add_r _ _) (le_max_l _ _)).
	    + cbn; exact (max_lub _ _ _ (IH1 _ _ _ _ Hn) (IH2 _ _ _ _ Hn)).
	    + cbn; apply le_pred_le_succ; rewrite succ_max_distr; specialize (IH v (S n) (V_of_nat (min_gt_vars v) :: l2) (x :: l1) (le_n_S _ _ Hn)).
	      refine (eq_ind _ (fun a => min_gt_fbound (bsubstb _ _ a) <= _) (eq_ind _ (fun a => _ <= max a _) IH _ _) _ _).
	      1: cbn; destruct (length l1); [inversion Hn|exact eq_refl].
	      exact (bruijn_of_app_nfv v [] (min_gt_vars v) l2 (min_gt_vars_fv _ _ (le_n _))).
	  - exact (min_gt_fbound_of _ _).
	  - specialize (IH1 _ _ eq_refl).
	    specialize (IH2 _ _ (eq_sym (bruijn_of_bruijn_eq _ _ _ (le_n _) (le_n _)))).
	    rewrite length_rev, length_map, length_seq in IH2.
	    exact (le_trans _ _ _ IH2 IH1). }
	assert (tmp' := bruijn_of_bruijn_eq v _ 0 (le_n _) (eq_ind _ _ (le_n _) _ tmp)); clear tmp; cbn in tmp'.
	specialize (IH1 _ (eq_sym tmp')) as [IH1|IH1].
	1: specialize (IH2 _ (eq_sym tmp')) as [IH2|IH2].
	1: left; exact (t_trans IH1 IH2).
	1: left; refine (proj1 (Rplus_equiv equiv_refl (proj2 (alpha_eq_iff _ _ []) _)) IH1).
	1:   rewrite IH2; exact (bruijn_of_bruijn_eq _ _ _ (le_n _) (min_gt_fbound_of _ _)).
	rewrite IH1; exact (IH2 _ (eq_sym IH1)).
Qed.

Lemma normal_form_of_if : forall u u', bruijn_of u [] = u' -> (forall v', ~ over_bcontext beta u' v') -> normal_form u.
Proof using.
	intros u u' Hu' Hn v Hv; unfold arrow in Hv; rewrite Hu' in Hv; exact (Hn _ Hv).
Qed.

Lemma bsubstb_nfb : forall u n v, (forall k, n <= k -> ~ bfb k u) -> bsubstb u n v = u.
Proof using.
	intros u n v H.
	rewrite <-(incr_nfb u n H), bsubstb_incr, (incr_nfb u n H); exact eq_refl.
Qed.

Lemma bfv_incr_iff : forall x u n, bfv x (incr_bound u n) <-> bfv x u.
Proof using.
	intros x u n; split; generalize dependent n; induction u as [y|k|u IHu v IHv|u IH]; intros n H.
	- inversion H; exact BFV_Var.
	- inversion H.
	- inversion H; [exact (BFV_App_l (IHu _ H1))|exact (BFV_App_r (IHv _ H1))].
	- inversion H; exact (BFV_Abs (IH _ H1)).
	- inversion H; exact BFV_Var.
	- inversion H.
	- inversion H; [exact (BFV_App_l (IHu _ H1))|exact (BFV_App_r (IHv _ H1))].
	- inversion H; exact (BFV_Abs (IH _ H1)).
Qed.
Lemma bfb_incr_iff : forall k u n, bfb (if n <=? k then S k else k) (incr_bound u n) <-> bfb k u.
Proof using.
	intros k u n; split; generalize dependent n; generalize dependent k; induction u as [y|m|u IHu v IHv|u IH]; intros k n H.
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
	- inversion H; exact BFB_Var.
	- inversion H; [exact (BFB_App_l (IHu _ _ H2))|exact (BFB_App_r (IHv _ _ H2))].
	- inversion H; specialize (IH (S k) (S n)); rewrite (eq_refl : (S _ <=? S _) = (n <=? k)) in IH.
	  destruct (n <=? k); exact (BFB_Abs (IH H2)).
Qed.

Lemma bfb_incr_eq : forall u n, ~ bfb n (incr_bound u n).
Proof using.
	intros u; induction u as [y|m|u IHu v IHv|u IH]; intros n H.
	- inversion H.
	- inversion H; subst.
	  destruct (le_gt_cases n m) as [nlem|mltn].
	  1: rewrite (proj2 (leb_le _ _) nlem) in H2; subst; contradiction (lt_neq _ _ nlem eq_refl).
	  rewrite (proj2 (leb_gt _ _) mltn) in H2; subst; contradiction (lt_neq _ _ mltn eq_refl).
	- inversion H; [exact (IHu _ H2)|exact (IHv _ H2)].
	- inversion H; exact (IH _ H2).
Qed.

(* Fixpoint min_gt_vars u := match u with
	| LVar x => match onat_of_V x with None => O | Some n => S n end
	| LApp u v => max (min_gt_vars u) (min_gt_vars v)
	| LAbs x u => max (match onat_of_V x with None => O | Some n => S n end) (min_gt_vars u)
end.

Definition congruence (R : relation lterm) : relation lterm := (over_context R)^*.
Lemma cong_refl : forall R u v, u = v -> congruence R u v.
Proof using. intros R u ? <-; exact rt_refl. Qed.

Arguments ctx_step {R} {u v} _.
Arguments ctx_app_l {R} {u u'} [v] _.
Arguments ctx_app_r {R} [u] {v v'} _.
Arguments ctx_abs {R} [x] {u v} _.
Arguments cong_refl {R} {u v} _.

Lemma over_context_iff : forall R u v, over_context R u v <-> exists c u' v', R u' v' /\ u = subst_context c u' /\ v = subst_context c v'.
Proof using.
	intros R u v; split.
	- intros H;
	    induction H as [u v HR|u u' v H (c & u'1 & u'2 & HR & eq1 & eq2)
	                   |u v v' H (c & v'1 & v'2 & HR & eq1 & eq2)
	                   |x u v H (c & u' & v' & HR & eq1 & eq2)].
	  + exists CHole, u, v; split; [exact HR|split; exact eq_refl].
	  + exists (CApp_l c v), u'1, u'2; split; [exact HR|split; refine (f_equal (fun v => LApp v _) _); [exact eq1|exact eq2]].
	  + exists (CApp_r u c), v'1, v'2; split; [exact HR|split; refine (f_equal (fun v => LApp _ v) _); [exact eq1|exact eq2]].
	  + exists (CAbs x c), u', v'; split; [exact HR|split; refine (f_equal (fun v => LAbs x v) _); [exact eq1|exact eq2]].
	- intros (c & u' & v' & HR & equ & eqv).
	  generalize dependent v'; generalize dependent u'; generalize dependent v; generalize dependent u;
	    induction c as [|c IH v0|u0 c IH|x c IH];
	    intros u v u' equ v' HR eqv.
	  + simpl in equ, eqv; rewrite equ, eqv; exact (ctx_step HR).
	  + simpl in equ, eqv; rewrite equ, eqv; exact (ctx_app_l (IH _ _ _ eq_refl _ HR eq_refl)).
	  + simpl in equ, eqv; rewrite equ, eqv; exact (ctx_app_r (IH _ _ _ eq_refl _ HR eq_refl)).
	  + simpl in equ, eqv; rewrite equ, eqv; exact (ctx_abs (IH _ _ _ eq_refl _ HR eq_refl)).
Qed.

Lemma over_context_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (over_context R1) (over_context R2).
Proof using.
	intros R1 R2 HR u v; rewrite !over_context_iff; intros (c & u' & v' & HR1 & equ & eqv).
	exists c, u', v'; split; [exact (HR _ _ HR1)|split; assumption].
Qed.
Lemma congruence_ext : forall {R1 R2}, inclusion R1 R2 -> inclusion (congruence R1) (congruence R2).
Proof using.
	intros R1 R2 HR; exact (clos_refl_trans_ext (over_context_ext HR)).
Qed.

Lemma over_context_transp : forall {R u v}, over_context R u v -> over_context (transp R) v u.
Proof using.
	intros R u v H;
	  induction H as [u v HR|u u' v H IH|u v v' H IH|x u v H IH].
	- exact (ctx_step HR).
	- exact (ctx_app_l IH).
	- exact (ctx_app_r IH).
	- exact (ctx_abs IH).
Qed.
Lemma over_context_transp_comm : forall {R u v}, (over_context R)^t u v <-> over_context (R^t) u v.
Proof using.
	intros R u v; split; exact over_context_transp.
Qed.
Lemma congruence_transp : forall {R u v}, congruence R u v -> congruence (transp R) v u.
Proof using.
	intros R u v H; induction H as [u v H|u|u v w H1 IH1 H2 IH2].
	1: exact (rt_step (over_context_transp H)).
	1: exact rt_refl.
	exact (rt_trans IH2 IH1).
Qed.
Lemma congruence_transp_comm : forall {R u v}, (congruence R)^t u v <-> congruence (R^t) u v.
Proof using.
	intros R u v; split; exact congruence_transp.
Qed.

Inductive fv x | : lterm -> Prop :=
	| FV_Var : fv x
	| FV_App_l : forall u v, fv u -> fv (u v)
	| FV_App_r : forall u v, fv v -> fv (u v)
	| FV_Abs : forall y u, x <> y -> fv u -> fv {{ ^y, {u} }}.
Inductive bv x | : lterm -> Prop :=
	| BV_Bound : forall u, bv {{ ^x, {u} }}
	| BV_App_l : forall u v, bv u -> bv (u v)
	| BV_App_r : forall u v, bv v -> bv (u v)
	| BV_Abs : forall y u, bv u -> bv {{ ^y, {u} }}.

Lemma FV_Var_inv : forall x y, fv x y -> y = x.
Proof using. intros x y H; inversion H; exact eq_refl. Qed.
Lemma FV_App_inv : forall x u v, fv x (u v) -> (fv x u) \/ (fv x v).
Proof using. intros x u v H; inversion H; [left|right]; assumption. Qed.
Lemma FV_Abs_inv : forall x y u, fv x (LAbs y u) -> x <> y /\ fv x u.
Proof using. intros x y u H; inversion H; split; assumption. Qed.
Lemma BV_Var_inv : forall x y, ~ bv x y.
Proof using. intros x y H; inversion H. Qed.
Lemma BV_App_inv : forall x u v, bv x (u v) -> (bv x u) \/ (bv x v).
Proof using. intros x u v H; inversion H; [left|right]; assumption. Qed.
Lemma BV_Abs_inv : forall x y u, bv x (LAbs y u) -> x = y \/ bv x u.
Proof using. intros x y u H; inversion H; [left; exact eq_refl|right; assumption]. Qed.
Lemma FV_Var_iff : forall x y, fv x y <-> y = x.
Proof using. intros x y; split; [apply FV_Var_inv|intros ->; apply FV_Var]. Qed.
Lemma FV_App_iff : forall x u v, fv x (u v) <-> (fv x u) \/ (fv x v).
Proof using. intros x u v; split; [apply FV_App_inv|intros [H|H]; [apply FV_App_l|apply FV_App_r]; exact H]. Qed.
Lemma FV_Abs_iff : forall x y u, fv x (LAbs y u) <-> x <> y /\ fv x u.
Proof using. intros x y u; split; [apply FV_Abs_inv|intros [H1 H2]; apply FV_Abs; assumption]. Qed.
Lemma BV_Var_iff : forall x y, bv x y <-> False.
Proof using. intros x y; split; [apply BV_Var_inv|intros []]. Qed.
Lemma BV_App_iff : forall x u v, bv x (u v) <-> (bv x u) \/ (bv x v).
Proof using. intros x u v; split; [apply BV_App_inv|intros [H|H]; [apply BV_App_l|apply BV_App_r]; exact H]. Qed.
Lemma BV_Abs_iff : forall x y u, bv x (LAbs y u) <-> x = y \/ bv x u.
Proof using. intros x y u; split; [apply BV_Abs_inv|intros [<-|H]; [apply BV_Bound|apply BV_Abs, H]]. Qed.

Goal forall y, ~ fv y {{ ^0, {0} }}.
Proof using.
	intros y H; inversion H; subst; inversion H3; exact (H2 H1).
Qed.
Goal forall y, bv y {{ ^0, {0} }} <-> y = 0.
Proof using.
	intros y; split; intros H.
	- inversion H; [exact eq_refl|inversion H1].
	- subst; constructor.
Qed.

Lemma min_gt_vars_fv : forall u n, min_gt_vars u <= n -> ~ fv (V_of_nat n) u.
Proof using.
	intros u n Hn; induction u as [x|u IHu v IHv|x u IH].
	- simpl in Hn; rewrite FV_Var_iff.
	  remember (onat_of_V x) as o eqn:eqx; destruct o as [m|].
	  + apply eq_sym, onat_Some_iff in eqx; subst x; apply V_inf; intros ->.
	    contradiction (nle_succ_diag_l _ Hn).
	  + exact (onat_complete _ (eq_sym eqx) _).
	- simpl in Hn; rewrite FV_App_iff; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  intros [H|H]; [exact (IHu Hu H)|exact (IHv Hv H)].
	- simpl in Hn; rewrite FV_Abs_iff; assert (Hx := max_lub_l _ _ _ Hn); assert (Hu := max_lub_r _ _ _ Hn).
	  intros [H1 H2]; exact (IH Hu H2).
Qed.
Lemma min_gt_vars_bv : forall u n, min_gt_vars u <= n -> ~ bv (V_of_nat n) u.
Proof using.
	intros u n Hn; induction u as [x|u IHu v IHv|x u IH].
	- rewrite BV_Var_iff; intros [].
	- simpl in Hn; rewrite BV_App_iff; assert (Hu := max_lub_l _ _ _ Hn); assert (Hv := max_lub_r _ _ _ Hn).
	  intros [H|H]; [exact (IHu Hu H)|exact (IHv Hv H)].
	- simpl in Hn; rewrite BV_Abs_iff; assert (Hx := max_lub_l _ _ _ Hn); assert (Hu := max_lub_r _ _ _ Hn).
	  intros [H|H]; [|exact (IH Hu H)].
	  apply eq_sym, onat_Some_iff in H; rewrite H in Hx.
	  contradiction (nle_succ_diag_l _ Hx).
Qed.

Fixpoint subst (u : lterm) (x : V) (v : lterm) (H1 : ~ bv x u) (H2 : forall x, ~ (fv x v /\ bv x u)) {struct u} : lterm.
Proof using.
	destruct u as [y|u1 u2|y u].
	- destruct (dec_V x y) as [eq|ne]; [exact v|exact y].
	- refine ((subst u1 x v _ _) (subst u2 x v _ _)).
	  + intros H; exact (H1 (BV_App_l _ _ _ H)).
	  + intros y [Hfv Hbv]; exact (H2 y (conj Hfv (BV_App_l _ _ _ Hbv))).
	  + intros H; exact (H1 (BV_App_r _ _ _ H)).
	  + intros y [Hfv Hbv]; exact (H2 y (conj Hfv (BV_App_r _ _ _ Hbv))).
	- refine {{ ^y, {subst u x v _ _} }}.
	  + intros H; exact (H1 (BV_Abs _ _ _ H)).
	  + intros z [Hfv Hbv]; exact (H2 z (conj Hfv (BV_Abs _ _ _ Hbv))).
Defined.

Lemma subst_ext : forall {u x v H11 H21 H12 H22}, subst u x v H11 H21 = subst u x v H12 H22.
Proof using.
	intros u x v; induction u as [y|u1 IH1 u2 IH2|y u IH]; intros H11 H21 H12 H22.
	- exact eq_refl.
	- simpl; f_equal; [exact (IH1 _ _ _ _)|exact (IH2 _ _ _ _)].
	- simpl; f_equal; exact (IH _ _ _ _).
Qed.

Lemma subst_same : forall {u x H1 H2}, subst u x x H1 H2 = u.
Proof using.
	intros u x H1 H2; induction u as [y|u IHu v IHv|y u IH].
	- simpl; destruct (dec_V x y) as [eq|ne]; [exact (f_equal _ eq)|exact eq_refl].
	- simpl; f_equal; [exact (IHu _ _)|exact (IHv _ _)].
	- simpl; f_equal; exact (IH _ _).
Qed.

Lemma fv_is_fv_subst : forall u x v H1 H2 y, x <> y -> fv y u -> fv y (subst u x v H1 H2).
Proof using.
	intros u x v H1 H2 y; generalize dependent H2; generalize dependent H1;
	  induction u as [z|u1 IH1 u2 IH2|z u IH]; intros H1 H2 ne H.
	- simpl; apply FV_Var_inv in H; subst z; rewrite (if_dec_neq _ _ _ _ ne); exact (FV_Var _).
	- simpl; apply FV_App_inv in H; destruct H as [H|H]; [apply FV_App_l, IH1|apply FV_App_r, IH2]; assumption.
	- simpl; apply FV_Abs_inv in H; destruct H as [ne2 H]; apply FV_Abs, IH; assumption.
Qed.
Lemma fv_subst_is_fv : forall u x v H1 H2 y, fv y (subst u x v H1 H2) -> (x <> y /\ fv y u) \/ (fv y v /\ fv x u).
Proof using.
	intros u x v H1 H2 y; generalize dependent H2; generalize dependent H1;
	  induction u as [z|u1 IH1 u2 IH2|z u IH]; intros H1 H2 H.
	- simpl in H; destruct (dec_V x z) as [eq|ne].
	  + right; split; [exact H|exact (proj2 (FV_Var_iff _ _) (eq_sym eq))].
	  + left; split; [refine (eq_ind _ (fun w => x <> w) ne _ (FV_Var_inv _ _ H))|exact H].
	- simpl in H; apply FV_App_inv in H; destruct H as [H|H].
	  1: destruct (IH1 _ _ H) as [[Hl Hr]|[Hl Hr]].
	  3: destruct (IH2 _ _ H) as [[Hl Hr]|[Hl Hr]].
	  1,3: left; split.
	  5,6: right; split.
	  1,3,5,7: exact Hl.
	  1,3: constructor 2.
	  3,4: constructor 3.
	  1-4: exact Hr.
	- simpl in H; apply FV_Abs_inv in H; destruct H as [ne H].
	  destruct (IH _ _ H) as [[Hl Hr]|[Hl Hr]].
	  1: left; split.
	  3: right; split.
	  1,3: exact Hl.
	  1,2: constructor 4.
	  1: exact ne.
	  2: intros H0; exact (H1 (eq_ind _ (fun w => bv x (LAbs w u)) (BV_Bound _ _) _ H0)).
	  1,2: exact Hr.
Qed.
Lemma fv_subst_iff : forall u x v H1 H2 y, fv y (subst u x v H1 H2) <-> (x <> y /\ fv y u) \/ (fv y v /\ fv x u).
Proof using.
	intros u x v H1 H2 y; split; [apply fv_subst_is_fv|intros [[H1' H2']|[fvyv fvxu]]; [exact (fv_is_fv_subst _ _ _ _ _ _ H1' H2')|]].
	generalize dependent H2; generalize dependent H1;
	  induction u as [z|u1 IH1 u2 IH2|z u IH]; intros H1 H2.
	- simpl; apply FV_Var_inv in fvxu; symmetry in fvxu; rewrite (if_dec_eq _ _ _ _ fvxu); exact fvyv.
	- simpl; apply FV_App_inv in fvxu; destruct fvxu as [H|H]; [apply FV_App_l, IH1|apply FV_App_r, IH2]; exact H.
	- simpl; apply FV_Abs_inv in fvxu; destruct fvxu as [ne H]; apply FV_Abs; [|apply IH, H].
	  intros <-; apply (H2 y); split; [exact fvyv|exact (BV_Bound _ _)].
Qed.
Lemma bv_subst_iff : forall u x v H1 H2 y, bv y (subst u x v H1 H2) <-> bv y u \/ (bv y v /\ fv x u).
Proof using.
	intros u x v H1 H2 y; split; [|intros [H|H]; generalize dependent H]; generalize dependent H2; generalize dependent H1;
	  induction u as [z|u1 IH1 u2 IH2|z u IH]; intros H1 H2 H.
	7-9: destruct H as [Hbv Hfv].
	- simpl in H; destruct (dec_V x z) as [eq|ne];
	  [right; split; [exact H|exact (proj2 (FV_Var_iff _ _) (eq_sym eq))]|contradiction (BV_Var_inv _ _ H)].
	- simpl in H; apply BV_App_inv in H; destruct H as [H|H]; [clear IH2; rename IH1 into IH|clear IH1; rename IH2 into IH];
	  (destruct (IH _ _ H) as [IH'|[bv' IH']]; [left|right; split; [exact bv'|]]).
	  1: apply BV_App_l, IH'.
	  1: apply FV_App_l, IH'.
	  1: apply BV_App_r, IH'.
	  1: apply FV_App_r, IH'.
	- simpl in H; apply BV_Abs_inv in H; destruct H as [<-|H]; [left; exact (BV_Bound _ _)|];
	  destruct (IH _ _ H) as [IH'|[bv' IH']]; [left|right; split; [exact bv'|]].
	  1: apply BV_Abs, IH'.
	  1: apply FV_Abs; [|exact IH'].
	  intros <-; exact (H1 (BV_Bound _ _)).
	- contradiction (BV_Var_inv _ _ H).
	- simpl; apply BV_App_inv in H; destruct H as [H|H]; [constructor 2; clear IH2; rename IH1 into IH|constructor 3; clear IH1; rename IH2 into IH];
	    apply (IH _ _ H).
	- simpl; apply BV_Abs_inv in H; destruct H as [<-|H]; [constructor 1|constructor 4];
	    apply (IH _ _ H).
	- simpl; rewrite (if_dec_eq _ _ _ _ (eq_sym (FV_Var_inv _ _ Hfv))); exact Hbv.
	- simpl; apply FV_App_inv in Hfv; destruct Hfv as [Hfv|Hfv]; [constructor 2; clear IH2; rename IH1 into IH|constructor 3; clear IH1; rename IH2 into IH];
	    apply (IH _ _ (conj Hbv Hfv)).
	- simpl; apply FV_Abs_inv in Hfv; destruct Hfv as [ne Hfv]; constructor 4;
	    apply (IH _ _ (conj Hbv Hfv)).
Qed.

Lemma alpha_H2 : forall x u, ~ bv x u -> forall y, ~ (fv y x /\ bv y u).
Proof using.
	intros y u H2 z [H1' H2'].
	apply FV_Var_inv in H1'; subst z.
	exact (H2 H2').
Qed.
Inductive alpha : lterm -> lterm -> Prop :=
	| Alpha : forall x y u (H1 : ~ bv x u) (H2 : ~ bv y u) (H3 : ~ fv y u),
		alpha {{ ^x, {u} }} {{ ^y, {subst u x y H1 (alpha_H2 _ _ H2)} }}.
Definition alpha_eq : lterm -> lterm -> Prop := congruence alpha.

Notation "l  '-->_a'  r" := (over_context alpha l r) (at level 70, no associativity).
Notation "l  '===_a'  r" := (alpha_eq l r) (at level 70, no associativity).

Lemma alpha_sym : inclusion alpha alpha^t.
Proof using.
	intros u v H; inversion H; subst.
	match type of H with alpha _ (LAbs _ (subst _ _ _ _ ?H)) => remember H as H0 eqn:eq; clear eq end; clear H.
	rename u0 into u, H0 into H02, H1 into H01, H2 into H03, H3 into H04.
	unshelve refine (eq_ind _ (fun v => alpha _ (LAbs x v)) (Alpha y x (subst u x y H01 H02) _ _ _) _ _).
	- rewrite bv_subst_iff; intros [H'|[H' _]]; [exact (H03 H')|exact (BV_Var_inv _ _ H')].
	- rewrite bv_subst_iff; intros [H'|[H' _]]; [exact (H01 H')|exact (BV_Var_inv _ _ H')].
	- rewrite fv_subst_iff; intros [[H' _]|[xeqy fvxu]]; [exact (H' eq_refl)|].
	  apply FV_Var_inv in xeqy; subst y; exact (H04 fvxu).
	- match goal with |- subst _ _ _ ?Hl ?Hr = _ => remember Hl as H05 eqn:eql; remember Hr as H06 eqn:eqr; clear eql eqr end.
	  induction u as [z|u IHu v IHv|z u IH].
	  + simpl in *; destruct (dec_V x z) as [eq|ne]; simpl.
	    1: rewrite (if_dec_eq _ _ _ _ eq_refl); exact (f_equal _ eq).
	    rewrite FV_Var_iff in H04; exact (if_dec_neq _ _ _ _ (fun H => H04 (eq_sym H))).
	  + rewrite BV_App_iff in H03; rewrite FV_App_iff in H04; apply Decidable.not_or in H03, H04; destruct H03 as [H03u H03v], H04 as [H04u H04v].
	    simpl; f_equal; [apply IHu|apply IHv]; assumption.
	  + rewrite BV_Abs_iff in H03; rewrite FV_Abs_iff in H04; apply Decidable.not_or in H03; destruct H03 as [ynez H03].
	    assert (H04' := (fun H => H04 (conj ynez H)) : ~ _).
	    simpl; f_equal; apply IH; assumption.
Qed.
Lemma alpha_transp : same_relation alpha alpha^t.
Proof using.
	split; [exact alpha_sym|].
	intros u v; exact (alpha_sym v u).
Qed.
Lemma alpha_eq_sym : inclusion alpha_eq alpha_eq^t.
Proof using.
	unfold alpha_eq; intros u v H;
	  exact (congruence_ext (proj2 alpha_transp) _ _ (proj2 congruence_transp_comm H)).
Qed.
Lemma alpha_eq_transp : inclusion alpha_eq alpha_eq^t.
Proof using.
	unfold alpha_eq; intros u v H;
	  exact (congruence_ext (proj2 alpha_transp) _ _ (proj2 congruence_transp_comm H)).
Qed.

Lemma alpha_same_fv : forall {u v}, alpha u v -> forall x, fv x u <-> fv x v.
Proof using.
	intros u0 v H; inversion H as [x y u H1 H2 H3]; subst; clear H;
	  match goal with |- forall _, _ <-> fv _ (LAbs _ (subst _ _ _ _ ?H)) => remember H as H4 eqn:eq; clear eq end.
	intros z; rewrite !FV_Abs_iff; split; intros [ne H]; [split|].
	- intros eq; apply H3; rewrite <-eq; exact H.
	- apply fv_is_fv_subst; solve [auto].
	- apply fv_subst_is_fv in H; destruct H as [[xnez fvzu]|[zeqy _]].
	  + split; [symmetry; exact xnez|exact fvzu].
	  + apply FV_Var_inv in zeqy; contradiction (ne (eq_sym zeqy)).
Qed.

Lemma alpha_alpha : forall u v w, alpha u v -> alpha v w -> u = w \/ alpha u w.
Proof using.
	intros u0 v w H1 H2;
	  inversion H1 as [x y u H1' H2' H3']; subst;
	  inversion H2 as [x' z u' H1'' H2'' H3'']; subst.
	match type of H1'' with ~ bv _ (subst _ _ _ _ ?H) => remember H as H01 eqn:eq; clear eq end;
	  match goal with |- _ \/ alpha _ (LAbs _ (subst _ _ _ _ ?H)) => remember H as H02 eqn:eq; clear eq end.
	destruct (dec_V x z) as [<-|ne]; [left|right].
	1:{ clear - H3'; f_equal; generalize dependent H1'; generalize dependent H01;
	      induction u as [z|u1 IH1 u2 IH2|z u IH]; intros H02 H01 H03 H04.
	    - simpl in *; destruct (dec_V x z) as [<-|ne]; simpl; [rewrite (if_dec_eq _ _ _ _ eq_refl); exact eq_refl|].
	      rewrite FV_Var_iff in H3'; symmetry; exact (if_dec_neq _ _ _ _ ltac:(symmetry; exact H3')).
	    - simpl; f_equal; [apply IH1|apply IH2]; rewrite FV_App_iff in H3'; auto.
	    - simpl; f_equal; apply IH; intros H; apply H3', FV_Abs; [|exact H].
	      exact (fun H => H03 (eq_ind _ (fun w => bv y _) (BV_Bound _ _) _ H)). }
	unshelve refine (eq_ind _ (fun w => alpha (LAbs x u) (LAbs z w)) (Alpha _ _ _ H1' _ _) _ _).
	- clear - H2''; induction u as [a|u1 IH1 u2 IH2|a u].
	  + exact (BV_Var_inv _ _).
	  + simpl in H2''; assert (Hl := fun H => H2'' (BV_App_l _ _ _ H)); assert (Hr := fun H => H2'' (BV_App_r _ _ _ H));
	    clear - Hl Hr IH1 IH2.
	    intros H; apply BV_App_inv in H; destruct H as [H|H]; [exact (IH1 _ _ Hl H)|exact (IH2 _ _ Hr H)].
	  + intros H; apply BV_Abs_inv in H; destruct H as [H|H]; [subst a; apply H2'', BV_Bound|exact (IHu _ _ (fun H => H2'' (BV_Abs _ _ _ H)) H)].
	- refine (fun fvzu => H3'' (proj2 (FV_Abs_inv _ _ _ (proj1 (alpha_same_fv H1 z) (FV_Abs _ _ _ _ fvzu))))).
	  symmetry; exact ne.
	- match goal with |- subst _ _ _ _ ?H = _ => remember H as Hg1 eqn:eq; clear eq end;
	  match goal with |- _ = subst _ _ _ _ ?H => remember H as Hg2 eqn:eq; clear eq end;
	  match type of H1'' with ~ bv _ (subst _ _ _ _ ?H) => remember H as H2''' eqn:eq; clear eq end.
	  clear - H3'; rename H3' into nfvyu.
	  generalize dependent Hg1; generalize dependent Hg2; generalize dependent H2'''; generalize dependent H1'; induction u as [a|u IHu v IHv|a u IH];
	    intros H01 H02 H03 H04 H05.
	  + simpl in *; destruct (dec_V x a) as [eq|ne]; simpl; clear - nfvyu.
	    1: symmetry; exact (if_dec_eq _ _ _ _ eq_refl).
	    rewrite FV_Var_iff in nfvyu.
	    symmetry; exact (if_dec_neq _ _ _ _ ltac:(symmetry; exact nfvyu)).
	  + simpl in *;
	    match type of H03 with ~ bv _ (LApp (subst _ _ _ ?Hl ?Hr) _) => remember Hl as H06 eqn:eql; remember Hr as H07 eqn:eqr; clear eql eqr end;
	    match type of H03 with ~ bv _ (LApp _ (subst _ _ _ ?Hl ?Hr)) => remember Hl as H08 eqn:eql; remember Hr as H09 eqn:eqr; clear eql eqr end;
	    match goal with |- (LApp (subst _ _ _ _ ?Hr) _) = _ => remember Hr as H010 eqn:eqr; clear eqr end;
	    match goal with |- (LApp _ (subst _ _ _ _ ?Hr)) = _ => remember Hr as H011 eqn:eqr; clear eqr end;
	    match goal with |- _ = (LApp (subst _ _ _ ?Hl ?Hr) _) => remember Hl as H012 eqn:eql; remember Hr as H013 eqn:eqr; clear eql eqr end;
	    match goal with |- _ = (LApp _ (subst _ _ _ ?Hl ?Hr)) => remember Hl as H014 eqn:eql; remember Hr as H015 eqn:eqr; clear eql eqr end.
	    rewrite FV_App_iff in nfvyu; apply Decidable.not_or in nfvyu; f_equal; [destruct nfvyu as [nfvyu _]|destruct nfvyu as [_ nfvyu]];
	      clear - nfvyu.
	    2: rename v into u, H08 into H06, H09 into H07, H011 into H010, H014 into H012, H015 into H013.
	    1,2: generalize dependent H010; generalize dependent H07; generalize dependent H06;
	      induction u as [a|u1 IH1 u2 IH2|a u IH]; intros H01 H02 H03 H04 H05.
	    1,4: simpl in *; destruct (dec_V x a) as [eq|ne]; simpl; symmetry; [exact (if_dec_eq _ _ _ _ eq_refl)|refine (if_dec_neq _ _ _ _ _)].
	    1,2: rewrite FV_Var_iff in nfvyu; symmetry; exact nfvyu.
	    1,3: simpl; f_equal; [apply IH1|apply IH2]; intros H; apply nfvyu; [constructor 2|constructor 3]; exact H.
	    1,2: simpl; f_equal; apply IH; intros H; apply nfvyu; constructor 4; [intros H2; exact (H03 (eq_ind _ (fun w => bv _ _) (BV_Bound _ _) _ H2))|exact H].
	  + simpl in *;
	    match type of H03 with ~ bv _ (LAbs _ (subst _ _ _ ?Hl ?Hr)) => remember Hl as H06 eqn:eql; remember Hr as H07 eqn:eqr; clear eql eqr end;
	    match goal with |- (LAbs _ (subst _ _ _ _ ?Hr)) = _ => remember Hr as H08 eqn:eqr; clear eqr end;
	    match goal with |- _ = (LAbs _ (subst _ _ _ ?Hl ?Hr)) => remember Hl as H09 eqn:eql; remember Hr as H010 eqn:eqr; clear eql eqr end.
	    assert (nfvyu' := (fun H => nfvyu (FV_Abs _ _ _ (fun yeqa => H03 (eq_ind _ (fun w => bv _ _) (BV_Bound _ _) _ yeqa)) H)) : ~ _);
	      rewrite FV_Abs_iff in nfvyu; f_equal; clear - nfvyu'; rename nfvyu' into nfvyu.
	    generalize dependent H08; generalize dependent H07; generalize dependent H06;
	      induction u as [b|u1 IH1 u2 IH2|b u IH]; intros H01 H02 H03 H04 H05.
	    * simpl in *; destruct (dec_V x b) as [eq|ne]; simpl; symmetry; [exact (if_dec_eq _ _ _ _ eq_refl)|refine (if_dec_neq _ _ _ _ _)].
	      rewrite FV_Var_iff in nfvyu; symmetry; exact nfvyu.
	    * simpl; f_equal; [apply IH1|apply IH2]; intros H; apply nfvyu; [constructor 2|constructor 3]; exact H.
	    * simpl; f_equal; apply IH; intros H; apply nfvyu; constructor 4; [intros H2; exact (H03 (eq_ind _ (fun w => bv _ _) (BV_Bound _ _) _ H2))|exact H].
Qed.

Lemma AlphaEq_Var_inv : forall x u, alpha_eq x u -> u = x.
Proof using.
	intros x v H; remember (LVar x) as u eqn:equ; generalize dependent x;
	  refine (clos_refl_trans_l_ind (fun u v => _) _ _ _ _ H); clear u v H; [intros u|intros u v w H1 H2 IH];
	  intros x equ.
	1: exact eq_refl.
	rewrite equ in H1; inversion H1; subst; inversion H.
Qed.
Lemma AlphaEq_App_inv : forall u1 u2 v, alpha_eq (u1 u2) v -> exists u1' u2', v = u1' u2' /\ alpha_eq u1 u1' /\ alpha_eq u2 u2'.
Proof using.
	intros u1 u2 v H; remember (u1 u2) as u eqn:equ; generalize dependent u2; generalize dependent u1;
	  refine (clos_refl_trans_l_ind (fun u v => _) _ _ _ _ H); clear u v H; [intros u|intros u v w H1 H2 IH];
	  intros u1 u2 equ.
	1: exists u1, u2; split; [exact equ|split; exact rt_refl].
	subst; inversion H1; subst.
	- inversion H.
	- destruct (IH _ _ eq_refl) as (u1' & u2' & eqw & H1' & H2'); exists u1', u2'; split; [exact eqw|split].
	  1: exact (rt_trans (rt_step H4) H1').
	  exact H2'.
	- destruct (IH _ _ eq_refl) as (u1' & u2' & eqw & H1' & H2'); exists u1', u2'; split; [exact eqw|split].
	  2: exact (rt_trans (rt_step H4) H2').
	  exact H1'.
Qed.

Inductive lterm_bruijn :=
	| LBVar : V -> lterm_bruijn
	| LBBound : nat -> lterm_bruijn
	| LBApp : lterm_bruijn -> lterm_bruijn -> lterm_bruijn
	| LBAbs : lterm_bruijn -> lterm_bruijn.
Fixpoint bruijn_of_var x l n := match l with
	| [] => LBVar x
	| hd :: tl => if dec_V x hd then LBBound n else bruijn_of_var x tl (S n)
end.
Fixpoint bruijn_of u l := match u with
	| LVar x => bruijn_of_var x l O
	| LApp u v => LBApp (bruijn_of u l) (bruijn_of v l)
	| LAbs x u => LBAbs (bruijn_of u (x :: l))
end.
Fixpoint of_bruijn (u : lterm_bruijn) n := match u with
	| LBVar x => LVar x
	| LBBound i => LVar (Nat.sub n (S i))
	| LBApp u v => LApp (of_bruijn u n) (of_bruijn v n)
	| LBAbs u => LAbs n (of_bruijn u (S n))
end.
Fixpoint parallel_subst u m : lterm := match u with
	| LVar x => VarMap.find m x (LVar x)
	| LApp u v => (parallel_subst u m) (parallel_subst v m)
	| LAbs x u => LAbs x (parallel_subst u (VarMap.add m x x))
end.
Lemma parallel_subst_empty : forall u m,
	(forall x, VarMap.find m x (LVar x) = x) ->
	parallel_subst u m = u.
Proof using.
	intros u m Hm; generalize dependent m; induction u as [x|u IHu v IHv|x u IH]; intros m Hm.
	- exact (Hm _).
	- simpl; f_equal; [exact (IHu _ Hm)|exact (IHv _ Hm)].
	- simpl; f_equal; apply IH.
	  intros y; rewrite VarMap.find_add; destruct (VarMap.key_dec x y) as [eq|ne]; [exact (f_equal _ eq)|exact (Hm _)].
Qed.
Lemma parallel_subst_ext : forall u m1 m2,
	(forall y, fv y u -> VarMap.find m1 y (LVar y) = VarMap.find m2 y (LVar y)) -> parallel_subst u m1 = parallel_subst u m2.
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH]; intros m1 m2 H.
	- exact (H _ (FV_Var _)).
	- simpl; f_equal; [exact (IHu _ _ (fun y Hy => H y (FV_App_l _ _ _ Hy)))|exact (IHv _ _ (fun y Hy => H y (FV_App_r _ _ _ Hy)))].
	- simpl; f_equal; refine (IH _ _ _).
	  intros y Hy; rewrite !VarMap.find_add; destruct (VarMap.key_dec x y) as [_|ne];
	    [exact eq_refl|exact (H _ (FV_Abs _ _ _ (fun H => ne (eq_sym H)) Hy))].
Qed.

Lemma bruijn_of_Var_eq' : forall x l n,
	bruijn_of_var x l n = LBVar x /\ ~ In x l \/
	exists k, bruijn_of_var x l n = LBBound (k + n) /\ nth_error l k = Some x /\ forall k', k' < k -> nth_error l k' <> Some x.
Proof using.
	intros x l; induction l as [|hd tl IH]; intros n; simpl.
	1: left; split; [exact eq_refl|intros []].
	destruct (dec_V x hd) as [<-|xnehd].
	1: right; exists 0; split; [exact eq_refl|split; [exact eq_refl|intros ? f; contradiction (nlt_0_r _ f)]].
	specialize (IH (S n)) as [[IH1 IH2]|[k [IH1 [IH2 IH3]]]].
	1: left; split; [exact IH1|intros [H|H]; [exact (xnehd (eq_sym H))|exact (IH2 H)]].
	right; exists (S k); split; [rewrite <-plus_n_Sm in IH1; exact IH1|split; [exact IH2|]].
	intros [|k'] Hk'; [|exact (IH3 _ (le_S_n _ _ Hk'))].
	intros H; injection H as H; exact (xnehd (eq_sym H)).
Qed.

Lemma bruijn_of_Var_eq : forall x l,
	bruijn_of x l = LBVar x /\ ~ In x l \/
	exists k, bruijn_of x l = LBBound k /\ nth_error l k = Some x /\ forall k', k' < k -> nth_error l k' <> Some x.
Proof using.
	intros x l; simpl; specialize (bruijn_of_Var_eq' x l O) as [H|[k H]].
	1: left; exact H.
	rewrite add_0_r in H; right; exists k; exact H.
Qed.
Lemma bruijn_of_Var_var_iff : forall x l y, bruijn_of x l = LBVar y <-> x = y /\ ~ In x l.
Proof using.
	intros x l; specialize (bruijn_of_Var_eq x l) as [[H1 H2]|[k [H1 [H2 _]]]].
	1: split; intros H; [split; [rewrite H1 in H; injection H as H; exact H|exact H2]|destruct H as [<- _]; exact H1].
	apply nth_error_In in H2; split; intros f; [|contradiction (proj2 f H2)].
	rewrite H1 in f; discriminate f.
Qed.
Lemma bruijn_of_Var_bound_iff : forall x l k, bruijn_of x l = LBBound k <-> exists l1 l2, length l1 = k /\ l = l1 ++ x :: l2 /\ ~ In x l1.
Proof using.
	intros x l k; specialize (bruijn_of_Var_eq x l) as [[H1 H2]|[k' [H1 [H2 H3]]]].
	1: split; [intros f; rewrite H1 in f; discriminate f|intros (l1 & l2 & _ & -> & _)].
	1: contradiction (H2 (in_or_app _ (_ :: _) _ (or_intror (or_introl eq_refl)))).
	rewrite H1; split; [intros H; injection H as ->|].
	1: apply nth_error_split in H2; destruct H2 as (l1 & l2 & eql & Hl1); exists l1, l2; split; [|split].
	1,2: assumption.
	1: intros f; apply In_nth_error in f; destruct f as [k' Hk']; subst l k;
	     refine (H3 k' ltac:(rewrite <-nth_error_Some, Hk'; discriminate) _).
	1: rewrite <-Hk'; exact (nth_error_app1 _ _ ltac:(rewrite <-nth_error_Some, Hk'; discriminate)).
	intros (l1 & l2 & <- & -> & nin); f_equal; apply le_antisymm; apply le_ngt; intros f.
	1: refine (H3 _ f _); rewrite (nth_error_app2 _ _ (le_n _)), sub_diag; exact eq_refl.
	rewrite (nth_error_app1 _ _ f) in H2; exact (nin (nth_error_In _ _ H2)).
Qed.

Lemma psubst_psubst : forall u m1 m2,
	(forall x, bv x u -> VarMap.find m2 x (LVar x) = x) ->
	parallel_subst (parallel_subst u m1) m2 = parallel_subst u (VarMap.update (VarMap.map m1 (fun v => parallel_subst v m2)) m2).
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH]; intros m1 m2 Hm.
	- simpl; rewrite VarMap.find_update.
	  remember (VarMap.mem_dec m1 x) as tmp eqn:eqm; destruct tmp as [mem|nmem].
	  1,2: match goal with |- _ = (if ?H then _ else _) => destruct H as [H'|H'] end.
	  1,4: clear H'.
	  3,4: rewrite VarMap.mem_map in H'.
	  3: contradiction (H' mem).
	  3: contradiction (nmem H').
	  1: exact (eq_sym (eq_trans (VarMap.find_mem _ _ (proj2 (VarMap.mem_map _ _ _) mem) (LVar x) _) (VarMap.find_map_f _ _ _ (LVar x)))).
	  rewrite (VarMap.find_not_mem _ _ nmem); exact eq_refl.
	- simpl; f_equal; [exact (IHu _ _ (fun x Hx => Hm x (BV_App_l _ _ _ Hx)))|exact (IHv _ _ (fun x Hx => Hm x (BV_App_r _ _ _ Hx)))].
	- simpl; f_equal.
	  rewrite (IH _ (VarMap.add m2 x (LVar x))
	    (fun y Hy => ltac:(
	       rewrite VarMap.find_add; destruct (VarMap.key_dec x y) as [eq|ne];
	       [exact (f_equal _ eq)|exact (Hm _ (BV_Abs _ _ _ Hy))])));
	    clear IH; apply parallel_subst_ext.
	  intros y Hy; rewrite VarMap.find_update, VarMap.find_map_add, !VarMap.find_add, VarMap.find_update.
	  match goal with |- (if ?H then _ else _) = _ => destruct H as [mem|nmem] end.
	  1: destruct (VarMap.key_dec x y) as [_|ne]; [simpl; rewrite VarMap.find_add_key; exact eq_refl|].
	  1: rewrite VarMap.mem_map, VarMap.mem_add in mem; destruct mem as [H|mem]; [contradiction (ne H)|].
	  1: match goal with |- _ = (if ?H then _ else _) => destruct H as [_|nmem]; [|rewrite VarMap.mem_map in nmem; contradiction (nmem mem)] end.
	  1: f_equal; apply VarMap.map_ext; intros z; apply parallel_subst_ext; intros w Hw; rewrite VarMap.find_add.
	  1: destruct (VarMap.key_dec x w) as [<-|_]; [exact (eq_sym (Hm _ (BV_Bound _ _)))|exact eq_refl].
	  destruct (VarMap.key_dec x y); [exact eq_refl|].
	  match goal with |- _ = (if ?H then _ else _) => destruct H as [mem|_]; [|exact eq_refl] end.
	  rewrite VarMap.mem_map in nmem, mem; rewrite VarMap.mem_add in nmem; contradiction (nmem (or_intror mem)).
Qed.
Lemma congruence_Var : forall {R} x, congruence R x x.
Proof using. intros R x; exact rt_refl. Qed.
Lemma congruence_App : forall {R} {u u' v v'}, congruence R u u' -> congruence R v v' -> congruence R (u v) (u' v').
Proof using.
	intros R u u' v v' Hu Hv.
	refine (rt_trans (y:=(u' v)) _ _).
	1: induction Hu as [u u' H|u|u u' u'' _ IH1 _ IH2]; [exact (rt_step (ctx_app_l H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	1: induction Hv as [v v' H|v|v v' v'' _ IH1 _ IH2]; [exact (rt_step (ctx_app_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.
Lemma congruence_Abs : forall {R} x u u', congruence R u u' -> congruence R (LAbs x u) (LAbs x u').
Proof using.
	intros R x u u' H.
	induction H as [u u' H|u|u u' u'' _ IH1 _ IH2]; [exact (rt_step (ctx_abs H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.
Lemma bv_of_bruijn_inv : forall x (u : lterm_bruijn) n, bv x (of_bruijn u n) -> exists k, x = V_of_nat k /\ n <= k.
Proof using.
	intros x u n H; remember (of_bruijn u n) as u' eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u|u v H IH|u v H IH|y u H IH]; intros [k'|x'|u' v'|u'] n equ; try discriminate equ.
	1-4: injection equ as -> ->.
	- exists n; split; [exact eq_refl|exact (le_n _)].
	- exact (IH _ _ eq_refl).
	- exact (IH _ _ eq_refl).
	- specialize (IH _ _ eq_refl) as [k [eqx Hk]]; exists k; split; [exact eqx|exact (le_S_n _ _ (le_S _ _ Hk))].
Qed.
Lemma fv_of_bruijn_inv : forall x (u : lterm_bruijn) n,
	fv x (of_bruijn u n) -> (fix inner (u : lterm_bruijn) o := match u with
		| LBVar y => x = y
		| LBBound i => x = (Nat.sub (Nat.add o n) (S i))
		| LBApp u v => inner u o \/ inner v o
		| LBAbs u => inner u (S o)
	end) u O.
Proof using.
	intros x u n H; remember (of_bruijn u n) as u' eqn:equ; rewrite (eq_refl : n = Nat.add 0 n) in equ;
	  generalize dependent 0; generalize dependent u;
	  induction H as [|u v H IH|u v H IH|y u xney H IH]; intros [k'|x'|u' v'|u'] o equ; try discriminate equ.
	+ injection equ as equ; exact equ.
	+ injection equ as equ; exact equ.
	+ injection equ as -> _; left; exact (IH _ _ eq_refl).
	+ injection equ as _ ->; right; exact (IH _ _ eq_refl).
	+ injection equ as -> ->; specialize (IH _ (S _) eq_refl).
	  clear H; generalize dependent n; induction u' as [k|y|u IHu v IHv|u IH2]; intros n xney IH1.
	  1,2: exact IH1.
	  1: destruct IH1 as [IH1|IH1]; [left; exact (IHu _ xney IH1)|right; exact (IHv _ xney IH1)].
	  exact IH1.
Qed.
Lemma fv_of_bruijn_of_inv' : forall x u l n,
	fv x (of_bruijn (bruijn_of u l) n) -> fv x u /\ (forall k, n - length l <= k -> x <> k) /\ ~ In x l \/ exists k, n - (length l) <= k /\ x = k.
Proof using.
	intros x u l n H.
	generalize dependent n; generalize dependent l; induction u as [y|u IHu v IHv|y u IH]; intros l n H.
	- remember (onat_of_V x) as o eqn:eqo; destruct o as [o|]; [|left].
	  1: destruct (lt_ge_cases o (n - length l)) as [Ho|Ho]; [left|].
	  1: refine (match _ with conj H1 H2 => conj H1 (conj _ H2) end).
	  2: intros k Hk eqx; symmetry in eqo; apply onat_correct in eqo; subst x.
	  2: apply V_inj in eqx; subst o; exact (proj1 (lt_nge _ _) Ho Hk).
	  2: right; exists o; split; [exact Ho|exact (proj1 (onat_Some_iff _ _) (eq_sym eqo))].
	  1,2: specialize (bruijn_of_Var_eq y l) as [[eqy Hy]|(k & eqy & Hy & Hy2)]; rewrite eqy in H; simpl in H; [split; [exact H|]|].
	  2: rewrite (onat_correct _ _ (eq_sym eqo)) in *; apply FV_Var_inv, V_inj in H.
	  2: apply nth_error_split in Hy; destruct Hy as (l1 & l2 & -> & <-);
	       rewrite app_length, (eq_refl : length (_ :: _) = S (length _)), <-plus_n_Sm, (sub_add_distr _ (S _) _ : _ - (S (_ + _)) = _ - S _ - _) in Ho.
	  2: subst o; contradiction (lt_neq _ _ (lt_le_trans _ _ _ Ho (le_sub_l _ _)) eq_refl).
	  2: split.
	  1,3: rewrite (FV_Var_inv _ _ H) in Hy; exact Hy.
	  2: contradiction (onat_complete _ (eq_sym eqo) _ (eq_sym (FV_Var_inv _ _ H))).
	  intros k _; exact (onat_complete _ (eq_sym eqo) _).
	- apply FV_App_inv in H; destruct H as [H|H].
	  1: destruct (IHu _ _ H) as [IH|IH].
	  3: destruct (IHv _ _ H) as [IH|IH].
	  2,4: right; exact IH.
	  1: left; exact (conj (FV_App_l _ _ _ (proj1 IH)) (proj2 IH)).
	  1: left; exact (conj (FV_App_r _ _ _ (proj1 IH)) (proj2 IH)).
	- apply FV_Abs_inv in H; destruct H as [xnen H].
	  specialize (IH _ _ H) as [[IH1 [IH2 IH3]]|IH].
	  2: right; exact IH.
	  left; refine (conj (FV_Abs _ _ _ (fun eq => IH3 (or_introl (eq_sym eq))) IH1) (conj IH2 (fun H => IH3 (or_intror H)))).
Qed.
Inductive occ := OFun | OArg | OBdy.
Fixpoint fv_path x u (p : list occ) {struct u} : Prop := match u with
	| LVar y => match p with [] => y = x | _ => False end
	| LApp u v => match p with OFun :: p' => fv_path x u p' | OArg :: p' => fv_path x v p' | _ => False end
	| LAbs y u => match p with OBdy :: p' => x <> y /\ fv_path x u p' | _ => False end
end.
Lemma fv_path_iff : forall x u, fv x u <-> exists p, fv_path x u p.
Proof using.
	intros x u; split; induction u as [y|u IHu v IHv|y u IH]; intros H.
	4-6: destruct H as [p Hp].
	- exists []; exact (FV_Var_inv _ _ H).
	- apply FV_App_inv in H; destruct H as [H|H]; [specialize (IHu H) as [p Hp]|specialize (IHv H) as [p Hp]];
	    [exists (OFun :: p)|exists (OArg :: p)]; exact Hp.
	- apply FV_Abs_inv in H; destruct H as [H1 H2]; specialize (IH H2) as [p Hp];
	    exists (OBdy :: p); exact (conj H1 Hp).
	- destruct p as [|[] []]; try contradiction Hp; rewrite Hp; exact (FV_Var _).
	- destruct p as [|[] []]; try contradiction Hp.
	  1,2: simpl in Hp; exact (FV_App_l _ _ _ (IHu (ex_intro _ _ Hp))).
	  1,2: simpl in Hp; exact (FV_App_r _ _ _ (IHv (ex_intro _ _ Hp))).
	- destruct p as [|[] []]; try contradiction Hp.
	  1,2: simpl in Hp; destruct Hp as [xney Hp]; exact (FV_Abs _ _ _ xney (IH (ex_intro _ _ Hp))).
Qed.
Lemma fv_parallel_subst : forall x u m,
	fv x (parallel_subst u m) -> exists y, fv y u /\ fv x (VarMap.find m y (LVar y)).
Proof using.
	intros y u m H; apply fv_path_iff in H; destruct H as [p Hp].
	refine (match _ : exists y p1 p2, p = p1 ++ p2 /\ _ /\ _ with
	        | ex_intro _ y (ex_intro _ p1 (ex_intro _ p2 (conj _ (conj H1 H2)))) =>
	            ex_intro _ y (conj (proj2 (fv_path_iff _ _) (ex_intro _ p1 H1)) (proj2 (fv_path_iff _ _) (ex_intro _ p2 H2))) end).
	generalize dependent m; generalize dependent u; induction p as [|o p IH]; intros u m Hp.
	1,2: destruct u as [x|u v|x u].
	2,3: contradiction Hp.
	1,2: exists x, []; exact (ex_intro _ _ (conj eq_refl (conj eq_refl Hp))).
	1,2: destruct o; try contradiction Hp.
	1: specialize (IH u m Hp) as (z & p1 & p2 & eqp & IH1 & IH2).
	2: specialize (IH v m Hp) as (z & p1 & p2 & eqp & IH1 & IH2).
	1,2: refine (ex_intro _ z (ex_intro _ (_ :: p1) (ex_intro _ p2 (conj (f_equal _ eqp) (conj _ IH2))))); exact IH1.
	destruct Hp as [ynex Hp].
	unshelve refine (match IH u _ Hp with
	        | ex_intro _ z (ex_intro _ p1 (ex_intro _ p2 (conj eqp (conj H1 H2)))) =>
	            let H0 := _ : z <> x -> _ in
	            let znex := _ : z <> x in
	            ex_intro _ z (ex_intro _ (_ :: p1) (ex_intro _ p2
	              (conj (f_equal _ eqp) (conj (conj znex H1 : fv_path z (LAbs x u) (OBdy :: p1)) (H0 znex))))) end); swap 1 2.
	- clear H0; intros ->; subst p; clear - H1 Hp ynex; generalize dependent m; generalize dependent u;
	    induction p1 as [|o p1 IH]; intros u H1 m Hp.
	  1: destruct u; try exact H1.
	  1: rewrite H1 in *; simpl in *; rewrite VarMap.find_add_key in Hp; destruct p2; try exact Hp; exact (ynex (eq_sym Hp)).
	  1: destruct u; try exact H1; destruct o; try exact H1.
	  1-3: simpl in H1, Hp.
	  3: destruct H1 as [xnev H1]; destruct Hp as [ynev Hp].
	  1-2: eapply IH; eassumption.
	  refine (IH _ H1 (VarMap.add m v v) _).
	  rewrite (parallel_subst_ext _ _ (VarMap.add (VarMap.add m x x) v v)); [exact Hp|].
	  intros z Hz; rewrite !VarMap.find_add; destruct (VarMap.key_dec x z) as [xeqz|xnez]; destruct (VarMap.key_dec v z) as [veqz|vnez].
	  1: subst v z.
	  1-4: exact eq_refl.
	- intros znex; rewrite VarMap.find_add in H2; destruct (VarMap.key_dec x z) as [eq|ne]; [contradiction (znex (eq_sym eq))|exact H2].
Qed.
Lemma bv_parallel_subst_iff : forall x u m, bv x (parallel_subst u m) <-> bv x u \/ exists y, fv y u /\ bv x (VarMap.find m y y).
Proof using.
	intros x u m; split.
	1: intros H; remember (parallel_subst u m) as u' eqn:equ; generalize dependent u; generalize dependent m;
	  induction H as [u'|u' v' H IH|u' v' H IH|y' u' H IH].
	5: intros [H|[y [fvy bvx]]].
	5: generalize dependent m; induction H as [u'|u' v' H IH|u' v' H IH|y' u' H IH].
	9: rewrite fv_path_iff in fvy; destruct fvy as [p Hp]; generalize dependent u; generalize dependent m; induction p as [|o p IH];
	     intros m bvx u Hp; [|destruct o]; destruct u as [z|u v|z u]; try contradiction Hp.
	1-4: intros m [y|u v|y u] equ; try discriminate equ.
	1,3,5,7: right; exists y; split; [exact (FV_Var _)|simpl in equ |- *; rewrite <-equ].
	1: exact (BV_Bound _ _).
	1: exact (BV_App_l _ _ _ H).
	1: exact (BV_App_r _ _ _ H).
	1: exact (BV_Abs _ _ _ H).
	5-8: intros m.
	- injection equ as <- _; left; exact (BV_Bound _ _).
	- injection equ as equ' _; specialize (IH _ _ equ') as [IH|[y [Hy Hx]]].
	  1: left; exact (BV_App_l _ _ _ IH).
	  right; exists y; split; [exact (FV_App_l _ _ _ Hy)|exact Hx].
	- injection equ as _ eqv'; specialize (IH _ _ eqv') as [IH|[y [Hy Hx]]].
	  1: left; exact (BV_App_r _ _ _ IH).
	  right; exists y; split; [exact (FV_App_r _ _ _ Hy)|exact Hx].
	- injection equ as -> equ'; specialize (IH _ _ equ') as [IH|[z [Hz Hx]]].
	  1: left; exact (BV_Abs _ _ _ IH).
	  rewrite VarMap.find_add in Hx.
	  destruct (VarMap.key_dec y z) as [<-|ynez].
	  1: contradiction (BV_Var_inv _ _ Hx).
	  right; exists z; split; [exact (FV_Abs _ _ _ (fun H => ynez (eq_sym H)) Hz)|exact Hx].
	- exact (BV_Bound _ _).
	- simpl; exact (BV_App_l _ _ _ (IH _)).
	- simpl; exact (BV_App_r _ _ _ (IH _)).
	- simpl; exact (BV_Abs _ _ _ (IH _)).
	- simpl in Hp |- *; exact (eq_ind _ (fun w => bv _ (VarMap.find m w w)) bvx _ (eq_sym Hp)).
	- simpl in Hp |- *; exact (BV_App_l _ _ _ (IH _ bvx _ Hp)).
	- simpl in Hp |- *; exact (BV_App_r _ _ _ (IH _ bvx _ Hp)).
	- simpl in Hp |- *; destruct Hp as [ynez Hp].
	  specialize (IH (VarMap.add m z z)); rewrite (VarMap.find_add_other _ _ _ _ _ (fun H => ynez (eq_sym H))) in IH.
	  exact (BV_Abs _ _ _ (IH bvx _ Hp)).
Qed.

Lemma alpha_eq_of_bruijn_of : forall u n, min_gt_vars u <= n -> alpha_eq (of_bruijn (bruijn_of u []) n) u.
Proof using.
	clear; intros u n H.
	apply clos_refl_trans_iff.
	pose (renorm_steps := fix inner u n := match u with
	         | LVar _ => []
	         | LApp u v => map (fun v' => of_bruijn (bruijn_of u []) n v') (inner v n)
	                    ++ map (fun u' => u' v) (inner u n)
	         | LAbs x u => (LAbs x (of_bruijn (bruijn_of u []) (S n))) :: map (fun u' => LAbs x u') (inner u (S n)) end).
	exists (renorm_steps u n); simpl.
	generalize dependent n; induction u as [x|u IHu v IHv|x u IH]; intros n Hn.
	- simpl; exact eq_refl.
	- simpl renorm_steps; refine (proj2 (proj2 (rt_iff_app (y:=of_bruijn (bruijn_of u []) n v)) _)).
	  specialize (IHu _ (max_lub_l _ _ _ Hn)).
	  specialize (IHv _ (max_lub_r _ _ _ Hn)).
	  split.
	  + simpl.
	    remember (of_bruijn (bruijn_of v []) n) as v' eqn:eqv; clear - IHv.
	    generalize dependent v'; induction (renorm_steps v n) as [|hd tl IH]; intros v' H.
	    1: simpl; f_equal; exact H.
	    simpl in *; refine (conj (ctx_app_r (proj1 H)) (IH _ (proj2 H))).
	  + simpl.
	    remember (of_bruijn (bruijn_of u []) n) as u' eqn:equ; clear - IHu.
	    generalize dependent u'; induction (renorm_steps u n) as [|hd tl IH]; intros u' H.
	    1: simpl; f_equal; exact H.
	    simpl in *; refine (conj (ctx_app_l (proj1 H)) (IH _ (proj2 H))).
	- simpl renorm_steps; simpl.
	  specialize (IH _ (le_S _ _ (max_lub_r _ _ _ Hn))).
	  split; [apply ctx_step|].
	  + assert (tmp := Alpha n x (of_bruijn (bruijn_of u [x]) (S n))).
	    match type of tmp with ?h1 -> ?h2 -> ?h3 -> _ =>
	      assert (H1 : h1); [|assert (H2 : h2); [|assert (H3 : h3); [|specialize (tmp H1 H2 H3)]]] end.
	    4: match type of tmp with alpha _ (LAbs _ (subst _ _ _ _ ?h2)) =>
	      refine (eq_ind _ (fun w => alpha _ (LAbs _ w)) tmp _ _); remember h2 as H2' eqn:eq; clear eq tmp H2 H3 end.
	    * intros H; apply bv_of_bruijn_inv in H; destruct H as [k [eq Hk]].
	      exact (lt_neq _ _ Hk (V_inj _ _ eq)).
	    * intros H; apply bv_of_bruijn_inv in H; destruct H as [k [-> Hk]].
	      exact (min_gt_vars_bv _ _ (lt_le_incl _ _ (le_lt_trans _ _ _ Hn Hk)) (BV_Bound _ _)).
	    * intros H; apply fv_of_bruijn_inv in H.
	      pose (l := @nil V); rewrite (eq_refl : 0 = length l) in H; rewrite (eq_refl : [x] = l ++ [x]) in H.
	      clear - H Hn; simpl in Hn; assert (Hx := max_lub_l _ _ _ Hn); apply max_lub_r in Hn;
	        generalize dependent l; induction u as [y|u IHu v IHv|y u IH]; intros l H.
	      -- specialize (bruijn_of_Var_eq y (l ++ [x])) as [[eq H']|(k & eq & eqk & _)]; rewrite eq in H.
	         exact (H' (in_or_app _ [x] _ (or_intror (or_introl H)))).
	         rewrite <-plus_n_Sm in H; simpl in H; rewrite (proj2 (onat_Some_iff _ _) H) in Hx.
	         assert (tmp := proj1 (nth_error_Some (l ++ [x]) k) ltac:(rewrite eqk; discriminate)); rewrite app_length, add_comm in tmp.
	         rewrite (add_sub_swap _ _ _ (le_S_n _ _ tmp)) in Hx; clear tmp; exact (lt_neq _ _ (le_lt_trans _ _ _ (le_add_l _ _) Hx) eq_refl).
	      -- destruct H as [H|H]; [exact (IHu (max_lub_l _ _ _ Hn) _ H)|exact (IHv (max_lub_r _ _ _ Hn) _ H)].
	      -- simpl in H; refine (IH (max_lub_r _ _ _ Hn) (_ :: _) H).
	    * clear - Hn; apply max_lub_r in Hn.
	      remember [x] as tmp eqn:eqtmp; rewrite (eq_refl : [x] = [] ++ [x]) in eqtmp;
	        remember [] as l eqn:eql; rewrite eql in eqtmp at 2; subst tmp.
	      remember (S n) as tmp eqn:eqtmp;
	        rewrite (f_equal (fun w => length w + _)%nat (eq_sym eql) : S n = length l + S n)%nat in eqtmp; subst tmp.
	      clear eql; generalize dependent n; generalize dependent l; induction u as [y|u IHu v IHv|y u IH]; intros l n Hn H1 H2.
	      1:{ specialize (bruijn_of_Var_eq y l) as [[eq ynil]|(k & eq & _)]; rewrite eq;
	            remember (bruijn_of y (l ++ [x])) as tmp eqn:eqtmp.
	          1: destruct (dec_V x y) as [<-|xney].
	          1: rewrite (proj2 (bruijn_of_Var_bound_iff _ _ _) (ex_intro _ l (ex_intro _ [] (conj eq_refl (conj eq_refl ynil))))) in eqtmp;
	               subst tmp; simpl; rewrite add_comm, plus_Sn_m, plus_n_Sm, add_sub; exact (if_dec_refl _ _ _).
	          1: rewrite (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl
	                        (fun H => match in_app_or _ [_] _ H with
	                        | or_introl f => ynil f
	                        | or_intror (or_introl f) => xney f
	                        | or_intror (or_intror f) => f end))) in eqtmp;
	               subst tmp; simpl; refine (if_dec_neq _ _ _ _ _).
	          1: intros f; simpl in Hn; rewrite (proj2 (onat_Some_iff _ _) (eq_sym f)) in Hn; exact (lt_neq _ _ Hn eq_refl).
	          apply bruijn_of_Var_bound_iff in eq; destruct eq as (l1 & l2 & eqk & eql & ynil1).
	          assert (tmp' := fun a b c d e => proj2 (bruijn_of_Var_bound_iff y (l ++ [x]) k) (ex_intro _ a (ex_intro _ b (conj c (conj d e))))).
	          subst l; rewrite (tmp' l1 (l2 ++ [x]) eqk (eq_sym (app_assoc _ _ _)) ynil1) in eqtmp; subst tmp; simpl.
	          refine (if_dec_neq _ _ _ _ _); intros H; apply V_inj in H; contradict H.
	          rewrite app_length, (eq_refl : length (_ :: _) = S (length _)), <-(plus_n_Sm _ (length l2)), <-plus_Sn_m,
	                  <-add_assoc, add_comm, eqk, add_sub.
	          exact (lt_neq _ _ (le_add_l _ _)). }
	      1: simpl; f_equal; [exact (IHu _ _ (max_lub_l _ _ _ Hn) _ _)|exact (IHv _ _ (max_lub_r _ _ _ Hn) _ _)].
	      1: simpl; f_equal; exact (IH (y :: l) n (max_lub_r _ _ _ Hn) _ _).
	  + remember (of_bruijn (bruijn_of u []) (S n)) as u' eqn:equ; clear - IH.
	    generalize dependent u'; induction (renorm_steps u (S n)) as [|hd tl IH']; intros u' H.
	    1: simpl in *; f_equal; exact H.
	    simpl in *; refine (conj (ctx_abs (proj1 H)) (IH' _ (proj2 H))).
Qed.

Inductive fvb (x : V) | : lterm_bruijn -> Prop :=
	| FVB_Var : fvb (LBVar x)
	| FVB_App_l : forall u v : lterm_bruijn, fvb u -> fvb (LBApp u v)
	| FVB_App_r : forall u v : lterm_bruijn, fvb v -> fvb (LBApp u v)
	| FVB_Abs : forall u : lterm_bruijn, fvb u -> fvb (LBAbs u).
Fixpoint fvb_path x (u : lterm_bruijn) (p : list occ) {struct u} : Prop := match u with
	| LBVar y => match p with [] => y = x | _ => False end
	| LBBound _ => False
	| LBApp u v => match p with OFun :: p' => fvb_path x u p' | OArg :: p' => fvb_path x v p' | _ => False end
	| LBAbs u => match p with OBdy :: p' => fvb_path x u p' | _ => False end
end.
Fixpoint fbvb_path k (u : lterm_bruijn) (p : list occ) {struct u} : Prop := match u with
	| LBVar _ => False
	| LBBound k' => match p with [] => k' = k | _ => False end
	| LBApp u v => match p with OFun :: p' => fbvb_path k u p' | OArg :: p' => fbvb_path k v p' | _ => False end
	| LBAbs u => match p with OBdy :: p' => fbvb_path (S k) u p' | _ => False end
end.

Lemma FVB_Var_inv : forall x y, fvb x (LBVar y) -> y = x.
Proof using. intros x y H; inversion H; exact eq_refl. Qed.
Lemma FVB_Bound_inv : forall x k, ~ fvb x (LBBound k).
Proof using. intros x y H; inversion H. Qed.
Lemma FVB_App_inv : forall x (u v : lterm_bruijn), fvb x (LBApp u v) -> (fvb x u) \/ (fvb x v).
Proof using. intros x u v H; inversion H; [left|right]; assumption. Qed.
Lemma FVB_Abs_inv : forall x (u : lterm_bruijn), fvb x (LBAbs u) -> fvb x u.
Proof using. intros x u H; inversion H; assumption. Qed.
Lemma FVB_Var_iff : forall x y, fvb x (LBVar y) <-> y = x.
Proof using. intros x y; split; [apply FVB_Var_inv|intros ->; apply FVB_Var]. Qed.
Lemma FVB_Bound_iff : forall x k, fvb x (LBBound k) <-> False.
Proof using. intros x y; split; [apply FVB_Bound_inv|intros []]. Qed.
Lemma FVB_App_iff : forall x (u v : lterm_bruijn), fvb x (LBApp u v) <-> (fvb x u) \/ (fvb x v).
Proof using. intros x u v; split; [apply FVB_App_inv|intros [H|H]; [apply FVB_App_l|apply FVB_App_r]; exact H]. Qed.
Lemma FVB_Abs_iff : forall x (u : lterm_bruijn), fvb x (LBAbs u) <-> fvb x u.
Proof using. intros x u; split; [apply FVB_Abs_inv|exact (FVB_Abs _ _)]. Qed.

Lemma fvb_path_iff : forall x (u : lterm_bruijn), fvb x u <-> exists p, fvb_path x u p.
Proof using.
	intros x u; split; induction u as [y|k|u IHu v IHv|u IH]; intros H.
	5-8: destruct H as [p Hp].
	- exists []; exact (FVB_Var_inv _ _ H).
	- contradiction (FVB_Bound_inv _ _ H).
	- apply FVB_App_inv in H; destruct H as [H|H]; [specialize (IHu H) as [p Hp]|specialize (IHv H) as [p Hp]];
	    [exists (OFun :: p)|exists (OArg :: p)]; exact Hp.
	- apply FVB_Abs_inv in H; specialize (IH H) as [p Hp];
	    exists (OBdy :: p); exact Hp.
	- destruct p as [|[] []]; try contradiction Hp; rewrite Hp; exact (FVB_Var _).
	- contradiction Hp.
	- destruct p as [|[] []]; try contradiction Hp.
	  1,2: simpl in Hp; exact (FVB_App_l _ _ _ (IHu (ex_intro _ _ Hp))).
	  1,2: simpl in Hp; exact (FVB_App_r _ _ _ (IHv (ex_intro _ _ Hp))).
	- destruct p as [|[] []]; try contradiction Hp.
	  1,2: simpl in Hp; exact (FVB_Abs _ _ (IH (ex_intro _ _ Hp))).
Qed.

Lemma fv_iff_bruijn : forall x u l p, fv_path x u p /\ ~ In x l <-> fvb_path x (bruijn_of u l) p.
Proof using.
	intros x u l p; split; [intros [H1 H2]|]; generalize dependent l; generalize dependent p.
	- induction u as [y|u IHu v IHv|y u IH]; intros [|[] p] H; try contradiction H; intros l xnil.
	  + simpl in H; subst y; rewrite (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl xnil)); exact eq_refl.
	  + simpl in *; exact (IHu _ H _ xnil).
	  + simpl in *; exact (IHv _ H _ xnil).
	  + simpl in *; destruct H as [xney H]; exact (IH _ H (_ :: _) (fun H => match H with or_introl H => xney (eq_sym H) | or_intror H => xnil H end)).
	- induction u as [y|u IHu v IHv|y u IH]; intros [|[] p] l H; try contradiction H.
	  1-4: specialize (bruijn_of_Var_eq y l) as [[eqy ynil]|(k' & eqy & Hy & Hk)].
	  2-8: rewrite eqy in H; contradiction H.
	  + rewrite eqy in H; simpl in H; subst y; split; [exact eq_refl|exact ynil].
	  + simpl in *; exact (IHu _ _ H).
	  + simpl in *; exact (IHv _ _ H).
	  + simpl in *; destruct (IH _ _ H) as [H1 H2]; split; [split; [exact (fun H => H2 (or_introl (eq_sym H)))|exact H1]|exact (fun H => H2 (or_intror H))].
Qed.

Lemma fbvb_iff_bruijn : forall k u l p,
	(exists l1 x l2, fv_path x u p /\ length l1 = k /\ l = l1 ++ x :: l2 /\ ~ In x l1) <-> fbvb_path k (bruijn_of u l) p.
Proof using.
	intros k u l p; split; generalize dependent l; generalize dependent p; generalize dependent k.
	- induction u as [y|u IHu v IHv|y u IH]; intros k [|[] p] l (l1 & x & l2 & H1 & H2); try contradiction H1.
	  + simpl in H1; subst y; rewrite (proj2 (bruijn_of_Var_bound_iff _ _ _) (ex_intro _ _ (ex_intro _ _ H2))); exact eq_refl.
	  + simpl in *; exact (IHu _ _ _ (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj H1 H2))))).
	  + simpl in *; exact (IHv _ _ _ (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj H1 H2))))).
	  + simpl in *; destruct H1 as [xney H1]; destruct H2 as (eqk & eql & xnil1);
	      refine (IH _ _ _ (ex_intro _ (_ :: _) (ex_intro _ _ (ex_intro _ _
	                  (conj H1 (conj (f_equal S eqk)
	                   (conj (f_equal _ eql) (fun H => match H with or_introl H => xney (eq_sym H) | or_intror H => xnil1 H end)))))))).
	- induction u as [y|u IHu v IHv|y u IH]; intros k [|[] p] l H; try contradiction H.
	  1-4: specialize (bruijn_of_Var_eq y l) as [[eqy ynil]|(k' & eqy & _)].
	  1,3-8: rewrite eqy in H; contradiction H.
	  + rewrite eqy in H; simpl in H; subst k'.
	    apply bruijn_of_Var_bound_iff in eqy; destruct eqy as (l1 & l2 & H); exists l1, y, l2; split; [exact eq_refl|exact H].
	  + simpl in H; exact (IHu _ _ _ H).
	  + simpl in H; exact (IHv _ _ _ H).
	  + simpl in H; destruct (IH _ _ _ H) as ([|hd l1] & x & l2 & fvp & eqk & eqyl & xnil1);
	      [discriminate eqk|injection eqk as eqk; injection eqyl as <- eql].
	    exists l1, x, l2; split; [split; [|exact fvp]|split; [exact eqk|split; [exact eql|exact (fun H => xnil1 (or_intror H))]]].
	    exact (fun H => xnil1 (or_introl (eq_sym H))).
Qed.

Lemma bruijn_if_eq_if : forall u v lu1 lv1 lu2 lv2,
	(forall x, fv x u -> ~ In x lu2 -> ~ In x lv2) ->
	(forall lu21 x lu22, fv x u -> ~ In x lu1 -> lu2 = lu21 ++ x :: lu22 -> ~ In x lu21 ->
	 exists lv21 lv22, length lv21 = length lu21 /\ lv2 = lv21 ++ x :: lv22 /\ ~ In x lv21) ->
	(forall lu11 x lu12, fv x u -> lu1 = lu11 ++ x :: lu12 -> ~ In x lu11 ->
	 exists lv11 y lv12, lv1 = lv11 ++ y :: lv12 /\ length lv11 = length lu11 /\ ~ In y lv11 /\
	 (x <> y -> In x lu2) /\
	 (In x lu2 -> exists lu21 lu22 lv21 lv22, lu2 = lu21 ++ x :: lu22 /\ lv2 = lv21 ++ y :: lv22
	              /\ length lu21 = length lv21 /\ ~ In x lu21 /\ ~ In y lv21)) ->
	bruijn_of u lu1 = bruijn_of v lv1 -> bruijn_of u lu2 = bruijn_of v lv2.
Proof using.
	intros u; induction u as [x|u1 IH1 u2 IH2|x u IH]; intros v lu1 lv1 lu2 lv2 Hnin2 Hin2 Hl Hb.
	- specialize (bruijn_of_Var_eq x lu1) as [(eq1 & H1)|(k & eq1 & _)]; rewrite eq1 in *; destruct v as [y| |]; try discriminate Hb.
	  + apply eq_sym in Hb; rewrite ->bruijn_of_Var_var_iff in Hb; destruct Hb as [-> Hb].
	    specialize (bruijn_of_Var_eq x lu2) as [(eq2 & H2)|(k & eq2 & _)]; rewrite eq2 in *.
	    1: apply (Hnin2 _ (FV_Var _)) in H2; exact (eq_sym (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl H2))).
	    rewrite bruijn_of_Var_bound_iff in eq2; destruct eq2 as (lu21 & lu22 & <- & eqlu2 & Hlu21);
	      exact (eq_sym (proj2 (bruijn_of_Var_bound_iff _ _ _) (Hin2 _ _ _ (FV_Var _) H1 eqlu2 Hlu21))).
	  + apply eq_sym in Hb; rewrite ->bruijn_of_Var_bound_iff in eq1, Hb;
	      destruct eq1 as (lu11 & lu12 & eqlen1 & eqlu1 & Hlu11); destruct Hb as (lv11 & lv12 & <- & eqlv1 & Hlv11).
	    specialize (Hl _ _ _ (FV_Var _) eqlu1 Hlu11) as (lv11' & y' & lv12' & eqlv1' & eqlen1' & Hlv11' & Hnein & Hl).
	    assert (tmp :  y' = y).
	    { rewrite eqlen1 in eqlen1'; rewrite eqlv1 in eqlv1'; clear - eqlv1' eqlen1'.
	      generalize dependent lv11'; induction lv11 as [|hd tl IH]; intros [|hd' tl'] Heq Hl;
	      [injection Heq as eq _; exact (eq_sym eq)|discriminate Hl|discriminate Hl|injection Heq as _ eq; injection Hl as Hl; exact (IH _ eq Hl)]. }
	    subst y'.
	    specialize (in_dec dec_V x lu2) as [Hin|Hnin].
	    2: rewrite (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl Hnin)).
	    2: destruct (dec_V x y) as [<-|ne].
	    2: apply (Hnin2 _ (FV_Var _)) in Hnin; exact (eq_sym (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl Hnin))).
	    2: exfalso; refine (Hnin (Hnein (fun H => ne H))).
	    clear lv11' lv12' eqlv1' eqlen1' Hlv11' Hin2 Hnin2 lu1 eqlu1 lv1 eqlv1 lu11 lu12 Hlu11 eqlen1 lv11 lv12 Hlv11.
	    specialize (Hl Hin) as (lu21 & lu22 & lv21 & lv22 & eqlu2 & eqlv2 & eqlen2 & Hnin1 & Hnin2).
	    rewrite (proj2 (bruijn_of_Var_bound_iff x lu2 _) (ex_intro _ lu21 (ex_intro _ lu22 (conj eq_refl (conj eqlu2 Hnin1))))).
	    rewrite (proj2 (bruijn_of_Var_bound_iff y lv2 _) (ex_intro _ lv21 (ex_intro _ lv22 (conj eq_refl (conj eqlv2 Hnin2))))).
	    exact (f_equal _ eqlen2).
	- destruct v as [|v1 v2|];
	    [destruct (bruijn_of_Var_eq v lv1) as [(eq & _)|(? & eq & _)]; rewrite eq in Hb; discriminate Hb
	    |simpl; injection Hb as Hb1 Hb2; f_equal
	    |discriminate Hb].
	  1: exact (IH1 _ _ _ _ _ (fun x H => Hnin2 _ (FV_App_l _ _ _ H))
	                          (fun lu11 x lu12 H => Hin2 _ _ _ (FV_App_l _ _ _ H))
	                          (fun lu11 x lu12 H => Hl _ _ _ (FV_App_l _ _ _ H)) Hb1).
	  1: exact (IH2 _ _ _ _ _ (fun x H => Hnin2 _ (FV_App_r _ _ _ H))
	                          (fun lu11 x lu12 H => Hin2 _ _ _ (FV_App_r _ _ _ H))
	                          (fun lu11 x lu12 H => Hl _ _ _ (FV_App_r _ _ _ H)) Hb2).
	- destruct v as [| |y v];
	    [destruct (bruijn_of_Var_eq v lv1) as [(eq & _)|(? & eq & _)]; rewrite eq in Hb; discriminate Hb
	    |discriminate Hb
	    |simpl; injection Hb as Hb; f_equal].
	  refine (IH _ _ _ _ _ _ _ _ Hb).
	  + intros z fvzu ninzxlu2 Hz.
	    destruct (dec_V z x) as [zeqx|ynex].
	    1: exact (ninzxlu2 (or_introl (eq_sym zeqx))).
	    destruct Hz as [zeqy|zinlv2]; [subst z|].
	    2: exact (Hnin2 _ (FV_Abs _ _ _ ynex fvzu) (fun H => ninzxlu2 (or_intror H)) zinlv2).
	    assert (fvzu' := fvzu); apply fv_path_iff in fvzu'; destruct fvzu' as [p fvzu'].
	    destruct (in_dec dec_V y lu1) as [yin|ynin]; swap 1 2.
	    1: assert (tmp := conj fvzu' (fun H => match H with or_introl H' => ynex (eq_sym H') | or_intror H' => ynin H' end)
	                   : _ /\ ~ In _ (_ :: _)).
	    1: rewrite fv_iff_bruijn, Hb, <-fv_iff_bruijn in tmp.
	    1: exact (proj2 tmp (or_introl eq_refl)).
	    assert (tmp : exists lu11 lu12, lu1 = lu11 ++ y :: lu12 /\ ~ In y lu11).
	    { clear - yin; induction lu1 as [|hd tl IH]; [contradiction yin|].
	      destruct (dec_V hd y) as [eq|ne]; [|destruct yin as [eq|yin]; [contradiction (ne eq)|]].
	      1: exists [], tl; split; [exact (f_equal (fun w => w :: _) eq)|intros []].
	      specialize (IH yin) as (lu11 & lu12 & IH1 & IH2); exists (hd :: lu11), lu12; split; [exact (f_equal (cons hd) IH1)|].
	      intros [eq|Hin]; [exact (ne eq)|exact (IH2 Hin)]. }
	    destruct tmp as (lu11 & lu12 & eqlu1 & ynilu11).
	    specialize (Hl _ _ _ (FV_Abs _ _ _ ynex fvzu) eqlu1 ynilu11) as (lv11 & y' & lv12 & eqlv1 & eql & _ & H & _).
	    refine (ninzxlu2 (or_intror (H _))); intros <-; clear ninzxlu2 H.
	    assert (tmp := proj1 (fbvb_iff_bruijn _ _ (_ :: _) _)
	                    (ex_intro _ (_ :: _)
	                    (ex_intro _ _
	                    (ex_intro _ _
	                    (conj fvzu'
	                    (conj (eq_refl : _ = S (length _))
	                    (conj (f_equal _ eqlu1)
	                          (fun H => match H with or_introl H => ynex (eq_sym H) | or_intror H => ynilu11 H end)))))))).
	    rewrite Hb, <-fbvb_iff_bruijn in tmp; destruct tmp as ([|y'' lv11'] & y' & lv12' & fvp & eqlen & eqylv1 & y'nilv11);
	      [discriminate eqlen|injection eqlen as eqlen; injection eqylv1 as <- eqlv1'].
	    assert (tmp : y = y').
	    { rewrite <-eql in eqlen; rewrite eqlv1 in eqlv1'; clear - eqlen eqlv1'.
	      generalize dependent lv11'; induction lv11 as [|hd tl IH]; intros [|hd' tl'] Hl Hv.
	      2,3: discriminate Hl.
	      1: injection Hv as H _; exact H.
	      injection Hl as Hl; injection Hv as _ Hv; exact (IH _ Hl Hv). }
	    exact (y'nilv11 (or_introl tmp)).
	  + intros lu21 z lu22 fvzu ninz eqz znilu21.
	    destruct lu21 as [|x' lu21]; [injection eqz as xeqz _; contradiction (ninz (or_introl xeqz))|injection eqz as <- eqz].
	    specialize (Hin2 _ _ _ (FV_Abs _ _ _ (fun H => ninz (or_introl (eq_sym H))) fvzu)
	                 (fun H => ninz (or_intror H)) eqz (fun H => znilu21 (or_intror H))) as (lv21 & lv22 & Hle & eqlv2 & znilv21).
	    exists (y :: lv21), lv22; split; [exact (f_equal S Hle)|split; [exact (f_equal (cons y) eqlv2)|intros [<-|zin]]].
	    2: exact (znilv21 zin).
	    clear - Hb fvzu ninz.
	    apply fv_path_iff in fvzu; destruct fvzu as [p fvzu].
	    assert (tmp := proj1 (fv_iff_bruijn y (LAbs x u) lu1 (OBdy :: p))
	       (conj (conj (fun H => ninz (or_introl (eq_sym H))) fvzu) (fun H => ninz (or_intror H)))).
	    simpl in tmp; rewrite Hb, <-fv_iff_bruijn in tmp.
	    exact (proj2 tmp (or_introl eq_refl)).
	  + intros [|x' lu11] z lu12 fvzu eqxlu1 znilu11; injection eqxlu1 as <- eqlu1.
	    1: exists [], y, lv1; repeat split.
	    1: intros [].
	    1: intros _; left; exact eq_refl.
	    1: intros _; exists [], lu2, [], lv2; split; [exact eq_refl|split; [exact eq_refl|split; [exact eq_refl|split; intros []]]].
	    specialize (Hl lu11 z lu12 (FV_Abs _ _ _ (fun H => znilu11 (or_introl (eq_sym H))) fvzu) eqlu1 (fun H => znilu11 (or_intror H)))
	      as (lv11 & y' & lv12 & eqlv1 & eqlen & ynilv11 & H1 & H2).
	    assert (yney' : y <> y').
	    { apply fv_path_iff in fvzu; destruct fvzu as [p fvzu].
	      assert (tmp := proj1 (fbvb_iff_bruijn _ _ _ _)
	                (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (conj fvzu (conj eq_refl (conj (f_equal _ eqlu1) znilu11))))))).
	      rewrite Hb, <-fbvb_iff_bruijn in tmp; destruct tmp as ([|y0 l1] & y'' & l2 & fvyv & eqlen' & eqylv1 & Hni).
	      1: discriminate eqlen'.
	      injection eqlen' as eqlen'; injection eqylv1 as <- eqlv1'.
	      assert (y'' = y'); [|subst y''; exact (fun H => Hni (or_introl H))].
	      rewrite eqlv1' in eqlv1; rewrite <-eqlen' in eqlen; clear - eqlv1 eqlen;
	        generalize dependent lv11; induction l1 as [|hd tl IH]; intros [|hd1 tl1] H1 H2.
	      2,3: discriminate H2.
	      1: injection H1 as H1 _; exact H1.
	      injection H1 as _ H1; injection H2 as H2; exact (IH _ H1 H2). }
	    exists (y :: lv11), y', lv12; split; [exact (f_equal _ eqlv1)|split; [exact (f_equal _ eqlen)|split; [|split]]].
	    2: intros H; right; exact (H1 H).
	    1: intros [eq|H]; [exact (yney' eq)|exact (ynilv11 H)].
	    intros [eq|H]; [contradiction (znilu11 (or_introl eq))|].
	    specialize (H2 H) as (lu21 & lu22 & lv21 & lv22 & eq1 & eq2 & eq3 & H4 & H5).
	    exists (x :: lu21), lu22, (y :: lv21), lv22; repeat split; [exact (f_equal _ eq1)|exact (f_equal _ eq2)|exact (f_equal _ eq3)| |].
	    1: intros [eq|H']; [exact (znilu11 (or_introl eq))|exact (H4 H')].
	    intros [eq|H']; [exact (yney' eq)|exact (H5 H')].
Qed.
Corollary bruijn_if_eq_nil : forall u v lu lv,
	(forall lu1 x lu2, fv x u -> lu = lu1 ++ x :: lu2 -> ~ In x lu1 ->
	 exists lv1 y lv2, lv = lv1 ++ y :: lv2 /\ length lv1 = length lu1 /\ ~ In y lv1 /\ x = y) ->
	bruijn_of u lu = bruijn_of v lv -> bruijn_of u [] = bruijn_of v [].
Proof using.
	intros u v lu lv H; refine (bruijn_if_eq_if _ _ _ _ [] [] _ _ _).
	1: intros ? _ _ [].
	1: intros [|? ?] ? ? _ _ f; discriminate f.
	intros lu1 x lu2 fvxu eqlu xnilu1.
	specialize (H _ _ _ fvxu eqlu xnilu1) as (lv1 & y & lv2 & eqlv & eqlen & ynilv1 & xeqy).
	exists lv1, y, lv2; repeat split; try assumption.
	1: intros f; exact (f xeqy).
	intros [].
Qed.
Corollary bruijn_eq_eq_nil : forall u v l, bruijn_of u l = bruijn_of v l -> bruijn_of u [] = bruijn_of v [].
Proof using.
	intros u v l; refine (bruijn_if_eq_nil _ _ _ _ _).
	intros lu1 x lu2 fvxu eql xnilu1; exists lu1, x, lu2; repeat split; assumption.
Qed.

Lemma alpha_eq_iff : forall u v l, alpha_eq u v <-> bruijn_of u l = bruijn_of v l.
Proof using.
	intros u v l; split.
	1: intros H; generalize dependent l; induction H as [u v H|u|u v w Huv IHuv Hvw IHvw]; intros l.
	- generalize dependent l; induction H as [u v H|u u' v H IH|u v v' H IH|x u v H IH]; intros l.
	  + inversion H; subst; clear H; simpl.
	    f_equal; match goal with |- _ = bruijn_of (subst _ _ _ _ ?H) _ => remember H as H0 eqn:eq; clear eq end.
	    pose (l0 := @nil V); rewrite (eq_refl : x :: l = l0 ++ x :: l), (eq_refl : y :: l = l0 ++ y :: l).
	    assert (Hx := @in_nil _ _ : ~ In x l0);
	    assert (Hy := @in_nil _ _ : ~ In y l0).
	    generalize dependent l0; induction u0 as [z|u IHu v IHv|z u IH]; intros l0 Hx Hy.
	    * simpl; destruct (dec_V x z) as [<-|ne]; simpl.
	      1,2: unfold bruijn_of; generalize dependent 0;
	             induction l0 as [|w l0 IH]; intros n; simpl.
	      1: rewrite !(if_dec_eq _ _ _ _ eq_refl); exact eq_refl.
	      1: apply Decidable.not_or in Hx, Hy;
	         rewrite (if_dec_neq _ _ _ _ (fun H => proj1 Hx (eq_sym H))), (if_dec_neq _ _ _ _ (fun H => proj1 Hy (eq_sym H)));
	         exact (IH (proj2 Hx) (proj2 Hy) _).
	      1: rewrite (if_dec_neq _ _ _ _ (fun H => ne (eq_sym H))),
	                 (if_dec_neq _ _ _ _ (fun H => H3 (eq_ind _ (fun w => fv w _) (FV_Var _) _ H))); exact eq_refl.
	      apply Decidable.not_or in Hx, Hy;
	      destruct (dec_V z w); [exact eq_refl|exact (IH (proj2 Hx) (proj2 Hy) _)].
	    * rewrite BV_App_iff in H2; rewrite FV_App_iff in H3; apply Decidable.not_or in H2, H3.
	      simpl; f_equal; [exact (IHu _ (proj1 H2) (proj1 H3) _ _ Hx Hy)|exact (IHv _ (proj2 H2) (proj2 H3) _ _ Hx Hy)].
	    * rewrite BV_Abs_iff in H2; rewrite FV_Abs_iff in H3; apply Decidable.not_or in H2.
	      simpl; f_equal; refine (IH _ (proj2 H2) (fun H => H3 (conj (proj1 H2) H)) _ (_ :: _) _ _).
	      1,2: intros [->|H].
	      1: exact (H1 (BV_Bound _ _)).
	      1: exact (Hx H).
	      1: exact (proj1 H2 eq_refl).
	      1: exact (Hy H).
	  + simpl; exact (f_equal (fun w => LBApp w _) (IH _)).
	  + simpl; exact (f_equal (fun w => LBApp _ w) (IH _)).
	  + simpl; exact (f_equal (fun w => LBAbs w) (IH _)).
	- exact eq_refl.
	- exact (eq_trans (IHuv _) (IHvw _)).
	- intros H.
	  apply bruijn_eq_eq_nil in H.
	  refine (rt_trans (y:=of_bruijn (bruijn_of u []) (max (min_gt_vars u) (min_gt_vars v))) (alpha_eq_sym _ _ _) _).
	  2: rewrite H.
	  1,2: refine (alpha_eq_of_bruijn_of _ _ _).
	  1: exact (le_max_l _ _).
	  1: exact (le_max_r _ _).
Qed.

Lemma fvp_alpha : forall x u v p, alpha_eq u v -> fv_path x u p -> fv_path x v p.
Proof using.
	intros x u v p.
	rewrite (alpha_eq_iff _ _ []).
	intros Ha Hp.
	refine (proj1 (proj2 (fv_iff_bruijn _ _ [] _) (eq_ind _ (fun w => fvb_path _ w _) (proj1 (fv_iff_bruijn _ _ _ _) (conj Hp _)) _ Ha))).
	intros [].
Qed.

Lemma fv_alpha : forall x u v, alpha_eq u v -> fv x u -> fv x v.
Proof using.
	intros x u v H1 H2; rewrite fv_path_iff in *.
	destruct H2 as [p Hp]; exists p; exact (fvp_alpha _ _ _ _ H1 Hp).
Qed.

Lemma seq_r : forall s l : nat, seq s (S l) = seq s l ++ [s + l]%nat.
Proof using.
	intros s l; generalize dependent s; induction l as [|l IH]; intros s.
	1: exact (f_equal (fun w => [w]) (eq_sym (add_0_r _))).
	rewrite (eq_refl : seq _ (S (S _)) = _ :: seq _ (S _)), IH; exact (f_equal (fun w => _ :: _ ++ [w]) (plus_n_Sm _ _)).
Qed.

Lemma seq_add : forall s l1 l2, seq s (l1 + l2) = seq s l1 ++ seq (s + l1) l2.
Proof using.
	intros s l1 l2; rewrite (add_comm s l1); generalize dependent s; induction l1 as [|l1 IH]; intros s.
	1: exact eq_refl.
	rewrite (plus_Sn_m _ s), (plus_n_Sm _ s); exact (f_equal (fun w => s :: w) (IH (S s))).
Qed.

Lemma bruijn_of_bruijn_of : forall u l n, length l + min_gt_vars u <= n ->
	bruijn_of u l = bruijn_of (of_bruijn (bruijn_of u l) n) (rev (map V_of_nat (seq (n - length l) (length l)))).
Proof using.
	intros u; induction u as [x|u IHu v IHv|x u IH]; intros l n Hn; simpl.
	- rewrite (eq_refl : length l = 0 + length l)%nat in *; generalize dependent 0.
	  induction l as [|hd tl IH]; intros k Hn.
	  1: simpl in *; rewrite add_0_r in *.
	  1: generalize 0; generalize dependent n; induction k as [|k IH]; intros n Hn k'; [exact eq_refl|].
	  1: rewrite seq_r, map_app, rev_app_distr; simpl; refine (eq_trans (eq_sym (if_dec_neq _ _ _ _ _)) (f_equal (fun w => if dec_V _ _ then _ else w) _)).
	  1: intros H; rewrite (proj2 (onat_Some_iff _ _) H), plus_n_Sm, <-(add_sub_swap _ _ _ (le_trans _ _ _ (le_add_r _ _) Hn)), add_sub in Hn.
	  1: rewrite plus_Sn_m, add_comm in Hn; exact (lt_neq _ _ (le_trans _ _ _ (le_add_r (S _) _) Hn) eq_refl).
	  1: destruct n as [|n]; [contradiction (lt_neq _ _ (le_trans _ _ _ (le_n_S _ _ (le_0_n _)) Hn) eq_refl)|apply le_S_n in Hn; fold add in Hn].
	  1: exact (IH _ Hn (S k')).
	  simpl in Hn |- *; destruct (dec_V x hd) as [<-|xnehd].
	  2: specialize (IH (S k)); rewrite <-plus_n_Sm in Hn |- *; exact (IH Hn).
	  clear IH; simpl in *.
	  rewrite <-plus_n_Sm, <-plus_Sn_m, <-add_assoc in *.
	  rewrite add_assoc in *; remember (S k + length tl)%nat as l eqn:eql.
	  assert (Hk := eq_ind _ _ (le_add_r _ _) _ (eq_sym eql) : S k <= l).
	  assert (Hl := le_trans _ _ _ (le_add_r _ _) Hn); clear x Hn tl eql.
	  destruct l as [|l]; [inversion Hk|apply le_S_n in Hk].
	  destruct n as [|n]; [inversion Hl|apply le_S_n in Hl].
	  rewrite seq_r, map_app, rev_app_distr, <-(add_sub_swap _ _ _ Hl), add_sub; simpl.
	  rewrite (eq_refl : k = Nat.add 0 k) at 1.
	  generalize dependent 0; generalize dependent n; generalize dependent l; induction k as [|k IH]; intros l Hk n Hl o.
	  1: rewrite sub_0_r, add_0_r; exact (eq_sym (if_dec_refl _ _ _)).
	  destruct l as [|l]; [inversion Hk|apply le_S_n in Hk].
	  destruct n as [|n]; [inversion Hl|apply le_S_n in Hl].
	  rewrite <-plus_n_Sm, <-plus_Sn_m; unfold sub; fold sub.
	  rewrite (if_dec_neq _ _ _ _ (fun H => lt_neq _ _ (le_n_S _ _ (le_sub_l _ _)) (V_inj _ _ H))).
	  rewrite seq_r, map_app, rev_app_distr, <-(add_sub_swap _ _ _ Hl), add_sub; simpl.
	  exact (IH l Hk n Hl (S o)).
	- f_equal; [exact (IHu _ _ (le_trans _ _ _ (add_le_mono _ _ _ _ (le_n _) (le_max_l _ _)) Hn))
	           |exact (IHv _ _ (le_trans _ _ _ (add_le_mono _ _ _ _ (le_n _) (le_max_r _ _)) Hn))].
	- f_equal;
	  rewrite (IH (_ :: _) _ (le_n_S _ _ (le_trans _ _ _ (add_le_mono _ _ _ _ (le_n _) (le_max_r _ _)) Hn))) at 1; f_equal.
	  simpl length; simpl "-"; rewrite <-rev_unit, <-(map_app _ _ [_] : map _ (_ ++ [_]) = map _ _ ++ [_ _]), <-!map_rev; f_equal; f_equal.
	  rewrite (seq_r _ _).
	  exact (f_equal (fun w => seq (n - length l) (length l) ++ [w])
	                 (eq_trans (eq_sym (add_sub_swap _ _ _ (le_trans _ _ _ (le_add_r _ _) Hn))) (add_sub _ _))).
Qed.

Lemma AlphaEq_Abs_inv : forall x u v, alpha_eq (LAbs x u) v ->
	(exists v', alpha_eq u v' /\ v = LAbs x v') \/
	(exists y u' v' H1 H2, alpha_eq u u' /\ alpha_eq (subst u' x y H1 H2) v' /\ v = LAbs y v').
Proof using.
	intros x u' v H; destruct v as [| |y v'].
	1: apply alpha_eq_sym, AlphaEq_Var_inv in H; discriminate H.
	1: apply alpha_eq_sym, AlphaEq_App_inv in H; destruct H as (? & ? & f & _); discriminate f.
	destruct (dec_V x y) as [<-|xney].
	- left; exists v'; split; [|exact eq_refl].
	  apply (alpha_eq_iff _ _ []) in H; apply (alpha_eq_iff _ _ [x]).
	  simpl in H; injection H as H; exact H.
	- right; exists y, (of_bruijn (bruijn_of u' []) (max (min_gt_vars (LAbs x u')) (min_gt_vars (LAbs y v')))), v'.
	  match goal with |- exists (_ : ?h1) (_ : ?h2), _ => assert (H1 : h1); [|assert (H2 : h2); [|exists H1, H2; split]] end.
	  + intros H'; apply bv_of_bruijn_inv in H'; destruct H' as [k [-> Hk]].
	    exact (min_gt_vars_bv _ _ (max_lub_l _ _ _ Hk) (BV_Bound _ _)).
	  + intros z [Hz H']; apply FV_Var_inv in Hz; subst z.
	    apply bv_of_bruijn_inv in H'; destruct H' as [k [-> Hk]].
	    exact (min_gt_vars_bv _ _ (max_lub_r _ _ _ Hk) (BV_Bound _ _)).
	  + apply (alpha_eq_iff _ _ []).
	    assert (Hn : min_gt_vars u' <= max (min_gt_vars (LAbs x u')) (min_gt_vars (LAbs y v')))
	      by exact (le_trans _ _ _ (le_max_r _ _) (le_max_l _ _)).
	    generalize dependent Hn; generalize (max (min_gt_vars (LAbs x u')) (min_gt_vars (LAbs y v'))); clear.
	    induction u' as [x|u IHu v IHv|x u IH]; intros n Hn.
	    * exact eq_refl.
	    * simpl; rewrite (bruijn_of_bruijn_of _ [] _ (max_lub_l _ _ _ Hn)) at 1; f_equal.
	      exact (bruijn_of_bruijn_of _ [] _ (max_lub_r _ _ _ Hn)).
	    * simpl; refine (eq_ind _ (fun w => _ = LBAbs (bruijn_of _ w))
	        (f_equal (fun w => LBAbs w) (bruijn_of_bruijn_of _ [x] _ (le_n_S _ _ (max_lub_r _ _ _ Hn)))) _ _).
	      simpl; exact (f_equal (fun w => [V_of_nat w]) (sub_0_r _)).
	  + assert (Hyu0 : ~ fv y u')
	      by (intros Hfv; exact (proj1 (FV_Abs_inv _ _ _ (fv_alpha _ _ _ H (FV_Abs _ _ _ (fun H => xney (eq_sym H)) Hfv))) eq_refl)).
	    apply (alpha_eq_iff _ _ []) in H; rewrite (alpha_eq_iff _ _ [y]).
	    simpl in H; injection H as H; split; [rewrite <-H; clear H|exact eq_refl].
	    remember (max (min_gt_vars (LAbs x u')) (min_gt_vars (LAbs y v'))) as n eqn:eq;
	      assert (Hn := le_trans _ _ _ (le_max_r _ _) (le_trans _ _ _ (le_max_l _ _) (eq_ind _ (fun w => _ <= w) (le_n _) _ (eq_sym eq)))
	                 : min_gt_vars u' <= n);
	      assert (xlen := le_trans _ _ _ (le_max_l _ _) (le_trans _ _ _ (le_max_l _ _) (eq_ind _ (fun w => _ <= w) (le_n _) _ (eq_sym eq)))
	                 : _ <= n);
	      assert (ylen := le_trans _ _ _ (le_max_l _ _) (le_trans _ _ _ (le_max_r _ _) (eq_ind _ (fun w => _ <= w) (le_n _) _ (eq_sym eq)))
	                 : _ <= n).
	    assert (Hyu : fv y u' -> In y []) by (intros f; contradiction (Hyu0 f)); clear Hyu0.
	    rewrite (eq_refl : [y] = (map V_of_nat (rev (seq n (length (@nil V))))) ++ [y]), (eq_refl : [x] = [] ++ [x]);
	      remember (of_bruijn (bruijn_of u' []) n) as tmp eqn:eqtmp; rewrite (eq_refl : n = (length (@nil V) + n)%nat) in eqtmp; subst tmp;
	      remember [] as l eqn:eql; rewrite eql at 4 6.
	    clear eql eq v'.
	    generalize dependent H2; generalize dependent H1; generalize dependent l; induction u' as [z|u IHu v IHv|z u IH]; intros l Hyul H1 H2.
	    * specialize (bruijn_of_Var_eq z l) as [[eqz Hz]|(k & eqz & Hk & Hk')];
	        remember (bruijn_of (LVar z) l) as tmp eqn:eqtmp; rewrite eqz in eqtmp; subst tmp; simpl of_bruijn in *; simpl subst; clear H1 H2.
	      1:{ specialize (bruijn_of_Var_eq z (l ++ [x])) as [[eqz' Hz']|(k & eqz' & Hk & _)].
	          1: rewrite eqz'; clear Hz; rewrite (if_dec_neq _ _ _ _ (fun H => Hz' (in_or_app _ [x] _ (or_intror (or_introl H))))).
	          1: specialize (bruijn_of_Var_eq z (map V_of_nat (rev (seq n (length l))) ++ [y])) as [[eqz'' Hz'']|(k & _ & Hz & _)].
	          1: exact eqz''.
	          1: exfalso; refine ((_ : ~ In z (_ ++ [y])) (nth_error_In _ _ Hz)).
	          1: generalize (length l); clear - Hz' Hn Hyul; intros len f; apply in_app_or in f; destruct f as [f|[f|[]]].
	          2: subst z; exact (Hz' (in_or_app _ _ _ (or_introl (Hyul (FV_Var _))))).
	          1: induction len as [|len IH]; [exact f|rewrite seq_r, rev_app_distr in f; destruct f as [f|f]; [|exact (IH f)]].
	          1: simpl in Hn; rewrite (proj2 (onat_Some_iff _ _) (eq_sym f)) in Hn; exact (lt_neq _ _ (le_lt_trans _ _ _ (le_add_r _ _) Hn) eq_refl).
	          destruct (lt_ge_cases k (length l)) as [Hkl|Hkl].
	          1: rewrite (nth_error_app1 _ _ Hkl) in Hk; contradiction (Hz (nth_error_In _ _ Hk)).
	          rewrite (nth_error_app2 _ _ Hkl) in Hk; inversion Hkl; subst; clear Hkl.
	          2: rewrite (sub_succ_l _ _ H) in Hk; destruct (m - length l); discriminate Hk.
	          rewrite sub_diag in Hk; injection Hk as <-; rewrite (if_dec_refl _ _ _), eqz'; clear - ylen.
	          specialize (bruijn_of_Var_eq y (map V_of_nat (rev (seq n (length l))) ++ [y])) as [[_ f]|(k & eq & Hz & _)];
	            [contradiction (f (in_or_app _ [_] _ (or_intror (or_introl eq_refl))))|].
	          destruct (lt_ge_cases k (length (map V_of_nat (rev (seq n (length l)))))) as [Hkl|Hkl].
	          1: rewrite (nth_error_app1 _ _ Hkl) in Hz; apply nth_error_split in Hz; destruct Hz as (l1 & l2 & eq1 & <-).
	          1: exfalso; refine (lt_neq _ _ (lt_le_trans _ _ _ _ ylen) eq_refl); clear - eq1; generalize dependent l1;
	            induction (length l) as [|l' IH]; clear l; intros l1 H; [destruct l1; discriminate H|].
	          1: rewrite seq_r, rev_app_distr in H; simpl in H; destruct l1 as [|? l1].
	          1: injection H as eq _; rewrite (proj2 (onat_Some_iff _ _) (eq_sym eq)); exact (le_n_S _ _ (le_add_r _ _)).
	          1: injection H as _ H; exact (IH _ H).
	          rewrite (nth_error_app2 _ _ Hkl) in Hz; inversion Hkl; subst; [rewrite map_length, rev_length, seq_length in eq; exact eq|clear Hkl].
	          rewrite (sub_succ_l _ _ H) in Hz; destruct (m - length (map V_of_nat (rev (seq n (length l))))); discriminate Hz. }
	      clear eqtmp.
	      specialize (bruijn_of_Var_eq z (l ++ [x])) as [[_ Hz]|(k2 & eqz & Hk2 & Hk2')].
	      1: contradiction (Hz (in_or_app _ _ _ (or_introl (nth_error_In _ _ Hk)))).
	      rewrite eqz; rewrite <-Hk in Hk2'; rewrite <-Hk2 in Hk'.
	      apply nth_error_split in Hk; destruct Hk as [l1 [l2 [-> <-]]].
	      assert (Hk2l : k2 = length l1).
	      { apply le_antisymm.
	        1,2: rewrite le_ngt; intros f.
	        1: refine (Hk2' _ f _); rewrite <-app_assoc, !(nth_error_app2 _ _ (le_n _)), sub_diag; exact eq_refl.
	        1: refine (Hk' _ f _); rewrite <-app_assoc, !(nth_error_app1 _ _ f); exact eq_refl. }
	      subst k2; rewrite Hk2 in Hk'; clear Hk2 Hk2' eqz.
	      rewrite app_length; simpl length; rewrite <-plus_n_Sm, <-plus_Sn_m, <-add_assoc, add_comm, add_sub.
	      destruct (dec_V x (V_of_nat (length l2 + n))) as [eq|xne].
	      1: rewrite (proj2 (onat_Some_iff _ _) eq) in xlen; contradiction (lt_neq _ _ (le_lt_trans _ _ _ (le_add_l _ _) xlen) eq_refl).
	      1: rewrite plus_Sn_m, plus_n_Sm, (add_comm (length l1) (S (length l2))).
	      1: specialize (bruijn_of_Var_eq (length l2 + n)%nat (map V_of_nat (rev (seq n (S (length l2) + length l1))) ++ [y])) as [[_ f]|(k & eq & Hz & _)].
	      1: rewrite seq_add, seq_r, !rev_app_distr, !map_app, add_comm in f; simpl in f;
	           exfalso; apply f, in_or_app, or_introl, in_or_app, or_intror, or_introl; exact eq_refl.
	      rewrite eq; f_equal; clear - ylen Hz.
	      apply le_antisymm; rewrite le_ngt; intros f.
	      1: rewrite plus_Sn_m, plus_n_Sm, seq_add, rev_app_distr, map_app, <-app_assoc in Hz.
	      1: unfold "<" in f; rewrite <-(seq_length _ (n + length l2)), <-rev_length, <-(map_length V_of_nat) in f.
	      1: rewrite (nth_error_app2 _ _ f), map_length, rev_length, seq_length in *; clear f; generalize dependent (k - S (length l1));
	           rewrite (eq_refl : length l2 + n = 0 + length l2 + n)%nat; generalize 0; induction (length l2) as [|l IH]; intros o m H; clear l1 l2.
	      1: destruct m as [|[|]]; try discriminate H; injection H as eq; rewrite (proj2 (onat_Some_iff _ _) eq), add_0_r in ylen;
	           exact (lt_neq _ _ (lt_le_trans _ _ _ ylen (le_add_l _ _)) eq_refl).
	      1: rewrite seq_r, rev_app_distr, <-plus_n_Sm in H; destruct m as [|m]; [injection H as H|exact (IH (S _) _ H)].
	      1: apply V_inj in H; rewrite add_comm, <-add_assoc in H; exact (lt_neq _ _ (le_n_S _ _ (le_add_l _ o)) H).
	      1: rewrite <-(seq_length (length l1) (n + S (length l2))), <-rev_length, <-(map_length V_of_nat) in f.
	      1: rewrite seq_add, rev_app_distr, map_app, <-app_assoc, (nth_error_app1 _ _ f) in Hz; clear f; generalize dependent k;
	           rewrite (add_comm _ _ : n + S (length l2) = S 0 + (length l2 + n))%nat; generalize 0; generalize (length l2 + n)%nat; intros N;
	           induction (length l1) as [|l IH]; intros o m H; clear l1 l2.
	      1: destruct m as [|[|]]; try discriminate H; injection H as eq; rewrite (proj2 (onat_Some_iff _ _) eq), add_0_r in ylen;
	           exact (lt_neq _ _ (lt_le_trans _ _ _ ylen (le_add_l _ _)) eq_refl).
	      rewrite seq_r, rev_app_distr in H; destruct m as [|m]; [injection H as H|exact (IH _ _ H)].
	      apply V_inj in H; rewrite (add_comm _ N), <-add_assoc in H; exact (lt_neq _ _ (le_add_r _ _) (eq_sym H)).
	    * simpl; f_equal; [refine (IHu (max_lub_l _ _ _ Hn) _ (fun H => Hyul (FV_App_l _ _ _ H)) _ _)
	                      |refine (IHv (max_lub_r _ _ _ Hn) _ (fun H => Hyul (FV_App_r _ _ _ H)) _ _)].
	    * simpl; f_equal; rewrite (eq_refl : _ :: map _ _ ++ _ = map _ (rev [_] ++ _) ++ _), <-rev_app_distr;
	        rewrite (add_comm (length l) n) at 2; rewrite <-seq_r; refine (IH (max_lub_r _ _ _ Hn) (z :: l) _ _ _).
	      intros H; destruct (dec_V y z) as [eq|ne]; [left; exact (eq_sym eq)|right; exact (Hyul (FV_Abs _ _ _ ne H))].
Qed.

Goal alpha_eq {{ ^0, ^1, {0} {1} }} {{ ^1, ^0, {1} {0} }}.
Proof using.
	rewrite (alpha_eq_iff _ _ []); simpl; rewrite !if_dec_refl, !if_dec_neq.
	1: exact eq_refl.
	all: apply V_inf; discriminate.
Qed.

Lemma always_subst : forall u x v, exists u', alpha_eq u u' /\ ~ bv x u' /\ forall x, ~ (fv x v /\ bv x u').
Proof using.
	intros u x v; exists (of_bruijn (bruijn_of u []) (max (max (min_gt_vars u) (min_gt_vars v)) (min_gt_vars x))).
	split; [rewrite (alpha_eq_iff _ _ []); refine (bruijn_of_bruijn_of _ _ _ (le_trans _ _ _ (le_max_l _ _) (le_max_l _ _)))|split].
	1: intros H; apply bv_of_bruijn_inv in H; destruct H as [k [eqx Hk]]; simpl in Hk; rewrite (proj2 (onat_Some_iff _ _) eqx) in Hk.
	1: refine (lt_neq _ _ (lt_le_trans _ _ _ (le_max_r _ _) Hk) eq_refl).
	intros y [fvyv bvy]; apply bv_of_bruijn_inv in bvy; destruct bvy as [k [-> Hk]].
	exact (min_gt_vars_fv _ _ (le_trans _ _ _ (le_trans _ _ _ (le_max_r _ _) (le_max_l _ _)) Hk) fvyv).
Qed.

Lemma subst_alpha : forall u u' x v v', alpha_eq u u' -> alpha_eq v v' ->
	forall H1 H2 H1' H2', alpha_eq (subst u x v H1 H2) (subst u' x v' H1' H2').
Proof using.
	intros u u' x v v' Hau Hav H1 H2 H1' H2'; rewrite (alpha_eq_iff _ _ []) in Hau; rewrite (alpha_eq_iff _ _ []).
	pose (lu := @nil V); rewrite (eq_refl : bruijn_of u [] = bruijn_of u lu) in Hau;
	  rewrite (eq_refl : bruijn_of (subst u _ _ _ _) [] = bruijn_of (subst u _ _ _ _) lu).
	pose (lu' := @nil V); fold lu' in Hau |- *.
	assert (Hlu : forall x, In x lu -> ~ fv x v) by intros ? [].
	assert (Hlu' : forall x, In x lu' -> ~ fv x v') by intros ? [].
	assert (xnilu : ~ In x lu) by intros [].
	assert (xnilu' : ~ In x lu') by intros [].
	generalize dependent lu'; generalize dependent lu; generalize dependent u'; induction u as [y|u1 IHu u2 IHv|y u IH];
	  intros [y'|u1' u2'|y' u'] H1' H2' lu Hlu xnilu lu' Hau Hlu' xnilu'; try discriminate Hau.
	2,3: destruct (bruijn_of_Var_eq y lu) as [(eq & _)|(k & eq & _)]; rewrite eq in Hau; discriminate Hau.
	2,4: destruct (bruijn_of_Var_eq y' lu') as [(eq & _)|(k & eq & _)]; rewrite eq in Hau; discriminate Hau.
	- simpl.
	  destruct (dec_V x y) as [<-|xney]; [|destruct (dec_V x y') as [<-|xney']].
	  + rewrite (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl xnilu)) in Hau; symmetry in Hau; apply bruijn_of_Var_var_iff in Hau.
	    destruct Hau as [-> _]; rewrite if_dec_refl.
	    refine (bruijn_if_eq_if _ _ _ _ _ _ _ _ _ (proj1 (alpha_eq_iff _ _ []) Hav)).
	    intros y fvyv ynilu yinlu'; exact (Hlu' _ yinlu' (fv_alpha _ _ _ Hav fvyv)).
	    intros lu1 y lu2 fvyv _ -> _; contradiction (Hlu _ (in_or_app _ (_ :: _) _ (or_intror (or_introl eq_refl))) fvyv).
	    intros [|? ?] ? ? _ f; discriminate f.
	  + rewrite (proj2 (bruijn_of_Var_var_iff _ _ _) (conj eq_refl xnilu')) in Hau; apply bruijn_of_Var_var_iff in Hau.
	    contradiction (xney (eq_sym (proj1 Hau))).
	  + exact Hau.
	- simpl; injection Hau as Hau1 Hau2; f_equal;
	    [exact (IHu _ _ _ _ _ _ Hlu xnilu _ Hau1 Hlu' xnilu')|exact (IHv _ _ _ _ _ _ Hlu xnilu _ Hau2 Hlu' xnilu')].
	- simpl; injection Hau as Hau; f_equal.
	  refine (IH _ _ _ _ _ (_ :: _) _ _ _ Hau _ _).
	  1,3: intros z [<-|zinlu].
	  1: intros fvzv; exact (H2 _ (conj fvzv (BV_Bound _ _))).
	  1: exact (Hlu _ zinlu).
	  1: intros fvzv; exact (H2' _ (conj fvzv (BV_Bound _ _))).
	  1: exact (Hlu' _ zinlu).
	  1: intros [->|xinlu]; [exact (H1 (BV_Bound _ _))|exact (xnilu xinlu)].
	  1: intros [->|xinlu']; [exact (H1' (BV_Bound _ _))|exact (xnilu' xinlu')].
Qed.

Definition beta : relation lterm :=
	fun u v => exists C x u v H1 H2, u = subst_context C {{ (^x, {u}) {v} }} /\ v = subst_context C (subst u x v H1 H2).

Notation "l -->_ R r" := (over_context R l r) (at level 70, R at level 5, no associativity, format "l  -->_ R  r").
Notation "l ===_ R r" := (congruence R l r) (at level 70, R at level 5, no associativity, format "l  ===_ R  r").

Inductive beta : lterm -> lterm -> Prop :=
	| BetaStep : forall x u v H1 H2, beta {{ (^x, {u}) {v} }} (subst u x v H1 H2)
	| BetaAbs : forall x u u', beta u u' -> beta (LAbs x u) (LAbs x u')
	| BetaApp_l : forall u u' v, beta u u' -> beta (u v) (u' v)
	| BetaApp_r : forall u v v', beta v v' -> beta (u v) (u v')
	| BetaAlpha_l : forall u v v', alpha_eq u v -> beta v v' -> beta u v'
	| BetaAlpha_r : forall u u' v, beta u u' -> alpha_eq u' v -> beta u v.

Lemma Beta_Var_inv : forall x v, ~ beta x v.
Proof using.
	intros x v H; remember (LVar x) as u eqn:equ; induction H as [y u v H1 H2|y u u' H IH|u u' v H IH|u v v' H IH|u v v' Ha H IH|u u' v H IH Ha].
	1-4: discriminate equ.
	- subst u; apply AlphaEq_Var_inv in Ha; exact (IH Ha).
	- exact (IH equ).
Qed.
Lemma Beta_App_inv :
	forall u v w, beta (u v) w ->
		(exists x u' v' H1 H2, alpha_eq u (LAbs x u') /\ alpha_eq v v' /\ alpha_eq w (subst u' x v' H1 H2)) \/
		(exists u' v', beta u u' /\ alpha_eq v v' /\ w = u' v') \/ (exists u' v', alpha_eq u u' /\ beta v v' /\ w = u' v').
Proof using.
	intros u v w H; remember (u v) as u0 eqn:equ0;
	  generalize dependent v; generalize dependent u;
	  induction H as [x u v H1 H2|y u u' H IH|u u' v H IH|u v v' H IH|u v v' Ha H IH|u u' v H IH Ha];
	  intros u0 v0 equ0.
	2: discriminate equ0.
	- injection equ0 as <- <-; left; exists x, u, v, H1, H2; split; [|split]; apply cong_refl; exact eq_refl.
	- injection equ0 as <- <-; right; left; exists u', v; split; [exact H|split; [exact rt_refl|exact eq_refl]].
	- injection equ0 as <- <-; right; right; exists u, v'; split; [exact rt_refl|split; [exact H|exact eq_refl]].
	- subst u; rename u0 into u1, v0 into u2; apply AlphaEq_App_inv in Ha; destruct Ha as (v1 & v2 & -> & Ha1 & Ha2); rename v' into v.
	  specialize (IH _ _ eq_refl) as [(x & u' & v' & H1 & H2 & Hau & Hav & Haw)|[(u' & v' & Hu & Hv & eqv)|(u' & v' & Hu & Hv & eqv)]].
	  1: left; exists x, u', v', H1, H2; split; [|split; [|exact Haw]].
	  1: exact (congruence_trans Ha1 Hau).
	  1: exact (congruence_trans Ha2 Hav).
	  1,2: right. 1: left. 2: right. 1,2: exists u', v'; split; [|split; [|exact eqv]].
	  1: refine (BetaAlpha_l _ _ _ _ Hu).
	  2: refine (congruence_trans _ Hv).
	  3: refine (congruence_trans _ Hu).
	  4: refine (BetaAlpha_l _ _ _ _ Hv).
	  1-4: assumption.
	- subst u; rename u0 into u1, v0 into u2, v into w, u' into v.
	  specialize (IH _ _ eq_refl) as [(x & u' & v' & H1 & H2 & Hau & Hav & Haw)|[(u' & v' & Hu & Hv & ->)|(u' & v' & Hu & Hv & ->)]].
	  1: left; exists x, u', v', H1, H2; split; [|split; [|exact (congruence_trans (alpha_eq_sym _ _ Ha) Haw)]]; assumption.
	  1,2: right. 1: left. 2: right. 1,2: apply AlphaEq_App_inv in Ha; destruct Ha as (w1 & w2 & eqw & H1 & H2);
	       exists w1, w2; split; [|split; [|exact eqw]].
	  1: exact (BetaAlpha_r _ _ _ Hu H1).
	  1: exact (congruence_trans Hv H2).
	  1: exact (congruence_trans Hu H1).
	  1: exact (BetaAlpha_r _ _ _ Hv H2).
Qed.
Lemma Beta_Abs_inv : forall x u v, beta (LAbs x u) v -> exists y u' v', alpha_eq (LAbs x u) (LAbs y u') /\ beta u' v' /\ alpha_eq (LAbs y v') v.
Proof using.
	intros x u v H; remember (LAbs x u) as u0 eqn:equ0;
	  generalize dependent u; generalize dependent x;
	  induction H as [x0 u0 v H1 H2|x0 u0 u' H IH|u0 u' v H IH|u0 v v' H IH|u0 v v' Ha H IH|u0 u' v H IH Ha];
	  intros x u equ.
	1,3,4: discriminate equ.
	2,3: subst u0.
	- injection equ as -> ->; exists x, u, u'; split; [exact rt_refl|split; [exact H|exact rt_refl]].
	- destruct v as [| |y v].
	  1: apply alpha_eq_sym, AlphaEq_Var_inv in Ha; discriminate Ha.
	  1: apply alpha_eq_sym, AlphaEq_App_inv in Ha; destruct Ha as (? & ? & Ha & _); discriminate Ha.
	  specialize (IH _ _ eq_refl) as (z & v'' & w' & Hv & Hb & Hw).
	  exists z, v'', w'; split; [exact (congruence_trans Ha Hv)|split; [exact Hb|exact Hw]].
	- specialize (IH _ _ eq_refl) as (y & v' & w' & Hv & Hb & Hw).
	  exists y, v', w'; split; [exact Hv|split; [exact Hb|exact (congruence_trans Hw Ha)]].
Qed.

Lemma cong_beta : forall {u v}, congruence beta u v <-> exists l,
	let fix inner hd1 l := match l with [] => hd1 = v | hd2 :: tl => beta hd1 hd2 /\ inner hd2 tl end in inner u l.
Proof using.
	intros u v; split.
	- rewrite congruence_iff; intros [l Hl]; exists l; generalize dependent u; induction l as [|hd tl IH]; intros u H.
	  1: exact H.
	  split; [apply proj1 in H; clear - H|exact (IH _ (proj2 H))].
	  induction H as [u v H|u u' v H IH|u v v' H IH|x u v H IH].
	  1: exact H.
	  1: exact (BetaApp_l _ _ _ IH).
	  1: exact (BetaApp_r _ _ _ IH).
	  1: exact (BetaAbs _ _ _ IH).
	- intros [l Hl]; generalize dependent u; induction l as [|hd tl IH]; intros u Hl.
	  1: simpl in Hl; exact (cong_refl Hl).
	  destruct Hl as [Hu Hhd]; specialize (IH _ Hhd).
	  exact (cong_step (ctx_step Hu) IH).
Qed.

Definition normal_form := RewriteSystem.normal_form beta.
Definition normalizable := RewriteSystem.normalizable beta.
Definition strong_normalizable:= RewriteSystem.strong_normalizable beta.

Definition delta := {{ ^0, {0} {0} }}.
Definition Omega := delta delta.

Lemma alpha_delta_delta : forall v, alpha_eq delta v <-> exists x, v = LAbs x (x x).
Proof using.
	intros v; rewrite (alpha_eq_iff _ _ []); split.
	- intros H; simpl in H; rewrite if_dec_refl in H.
	  destruct v as [| |x v]; try discriminate H.
	  exists x; f_equal; injection H as H.
	  destruct v as [v0|v1 v2|]; try discriminate H.
	  1: simpl in H; destruct (dec_V v0 x); discriminate H.
	  injection H as eq1 eq2.
	  destruct v1 as [v1| |]; try discriminate eq1.
	  destruct v2 as [v2| |]; try discriminate eq2.
	  simpl in eq1, eq2; destruct (dec_V v1 x) as [eq1'|ne]; [|discriminate eq1]; destruct (dec_V v2 x) as [eq2'|ne]; [|discriminate eq2].
	  exact (f_equal2 (fun w1 w2 => (LVar w1) (LVar w2)) eq1' eq2').
	- intros [x ->]; simpl; rewrite !if_dec_refl; exact eq_refl.
Qed.

Lemma beta_Omega_Omega : forall v, beta Omega v <-> alpha_eq v Omega.
Proof using.
	intros v; split.
	- intros H; apply Beta_App_inv in H; destruct H as [(x & u' & v' & H1 & H2 & H3 & H4 & H5)|[(u' & v' & H1 & H2 & ->)|(u' & v' & H1 & H2 & ->)]].
	  + rewrite alpha_delta_delta in H3, H4; destruct H3 as [x1 eq1]; destruct H4 as [x2 ->]; injection eq1 as <- ->.
	    apply (congruence_trans H5); clear; simpl; rewrite if_dec_refl.
	    apply cong_App; exact (alpha_eq_sym _ _ (proj2 (alpha_delta_delta _) (ex_intro _ x2 eq_refl))).
	  + apply Beta_Abs_inv in H1; destruct H1 as (y & u'' & v'' & Ha1 & Hb & Ha2).
	    apply alpha_delta_delta in Ha1; destruct Ha1 as [x eq]; injection eq as -> ->.
	    apply Beta_App_inv in Hb; destruct Hb as [(? & ? & ? & ? & ? & f & _)|[(? & ? & f & _)|(? & ? & _ & f & _)]].
	    1: apply AlphaEq_Var_inv in f; discriminate f.
	    1,2: contradiction (Beta_Var_inv _ _ f).
	  + apply Beta_Abs_inv in H2; destruct H2 as (y & u'' & v'' & Ha1 & Hb & Ha2).
	    apply alpha_delta_delta in Ha1; destruct Ha1 as [x eq]; injection eq as -> ->.
	    apply Beta_App_inv in Hb; destruct Hb as [(? & ? & ? & ? & ? & f & _)|[(? & ? & f & _)|(? & ? & _ & f & _)]].
	    1: apply AlphaEq_Var_inv in f; discriminate f.
	    1,2: contradiction (Beta_Var_inv _ _ f).
	- intros H; apply alpha_eq_sym, AlphaEq_App_inv in H; destruct H as (u1 & u2 & -> & H1 & H2).
	  apply alpha_delta_delta in H1, H2; destruct H1 as [x ->]; destruct H2 as [y ->].
	  assert (tmp := BetaStep x (x x) (LAbs y (y y)) ltac:(intros f; inversion f; subst; inversion H0)); simpl in tmp.
	  rewrite if_dec_refl in tmp; refine (BetaAlpha_l _ _ _ _ (BetaAlpha_r _ _ _ (tmp _) _)); clear tmp.
	  1,3: rewrite (alpha_eq_iff _ _ []); simpl; rewrite !if_dec_refl; exact eq_refl.
	  intros z [_ H]; inversion H; subst; inversion H1.
Qed.

Goal ~normalizable Omega.
Proof using.
	intros [v [Hv1 Hv2]].
	apply cong_beta in Hv1; destruct Hv1 as [l Hl].
	pose (hd := Omega); fold hd in Hl.
	assert (Hhd := rt_refl : alpha_eq hd Omega).
	generalize dependent hd; induction l as [|hd2 tl IH]; intros hd1 Hl Hhd.
	- simpl in Hl; subst hd1; unfold normal_form in Hv2.
	  apply (Hv2 Omega); exact (BetaAlpha_l _ _ _ Hhd (proj2 (beta_Omega_Omega _) rt_refl)).
	- simpl in Hl; destruct Hl as [H1 H2].
	  exact (IH _ H2 (proj1 (beta_Omega_Omega _) (BetaAlpha_l _ _ _ (alpha_eq_sym _ _ Hhd) H1))).
Qed.

Definition eta u v := exists x, u = LAbs x (v x) /\ ~ fv x v. *)

End UntypedLambda.
