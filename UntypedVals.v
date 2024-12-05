Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Relations.
Require Import Untyped.

Open Scope nat.

Module Type UntypedValsT.
Declare Module Import UntypedL : UntypedLambdaT.
Module Export Vars := UntypedL.Vars.
Import UntypedBNotation.

Fixpoint code_nat_aux n := match n with
	| O => <{ <0> }>
	| S n => <{ <1> {code_nat_aux n} }>
end.
Definition code_nat n := <{ ^^ {code_nat_aux n} }>.

Fixpoint code_nat_funarg n f x := match n with
	| O => x
	| S n => <{ {f} {code_nat_funarg n f x} }>
end.
Fixpoint code_nat_funarg_r n f x : bterm := match n with
	| O => x
	| S n => code_nat_funarg_r n f <{ {f} {x} }>
end.

Definition code_S := <{ ^^^<1> (<2> <1> <0>) }>.

Definition code_add := <{ ^^^^<3> <1> (<2> <1> <0>) }>.

Definition code_mul := <{ ^^^<2> (<1> <0>) }>.

Definition code_exp := <{ ^^<1> <0> }>.

Definition code_true_aux := BBound 1.
Definition code_false_aux := BBound 0.
Definition code_bool_aux (b : bool) := if b then code_true_aux else code_false_aux.

Definition code_true := <{ ^^<1> }>.
Definition code_false := <{ ^^<0> }>.
Definition code_bool (b : bool) := if b then code_true else code_false.
Definition code_if b x y := <{ {b} {x} {y} }>.

Definition code_pair_imm u v := <{ ^<0> {incr_bound u O} {incr_bound v O} }>.
Definition code_pi1 := <{ ^<0> {code_true} }>.
Definition code_pi2 := <{ ^<0> {code_false} }>.

Definition code_pair_lt := <{ ^^^<0> <2> <1> }>.

Definition code_pred := <{
	^{code_pi2}
		(<0>
			(^{code_pair_imm <{ {code_S} ({code_pi1} <0> ) }> <{ {code_pi1} <0> }>})
			{code_pair_imm (code_nat O) (code_nat O)}) }>.

Definition code_intcase := <{ ^^^<2> (^<1> ({code_pred} <3>)) <1> }>.

Definition code_sub := <{ ^^<0> {code_pred} <1> }>.

Definition code_iszero := <{ ^<0> (^{code_false}) {code_true} }>.

Definition code_le := <{ ^^{code_iszero} ({code_sub} <1> <0>) }>.

Definition code_and := <{ ^^^^<3> (<2> <1> <0>) <0> }>.
Definition code_or := <{ ^^^^<3> <1> (<2> <1> <0>) }>.
Definition code_neg := <{ ^^^<2> <0> <1> }>.
Definition code_impl := <{ ^^^^<3> (<2> <1> <0>) <1> }>.
Definition code_impl' := <{ ^^{code_or} ({code_neg} <1>) <0> }>.

Definition code_eq_nat := <{ ^^{code_and} ({code_le} <1> <0>) ({code_le} <0> <1>) }>.

Definition code_G_maurey a b := <{
	^^ <1>
		(^^<0> <1>)
		(^{incr_bound (incr_bound (incr_bound a O) O) O})
		(<0> (^^<0> <1>) (^{incr_bound (incr_bound (incr_bound b O) O) O})) }>.

Definition Theta := <{ (^^<0> (<1> <1> <0>)) (^^<0> (<1> <1> <0>)) }>.

Fixpoint code_list_aux l := match l with
	| [] => <{ <0> }>
	| hd :: tl => <{ <1> {incr_bound (incr_bound hd O) O} {code_list_aux tl} }>
end.
Definition code_list l := <{ ^^ {code_list_aux l} }>.

Fixpoint code_list_funarg l f x := match l with
	| [] => x
	| hd :: tl => <{ {f} {hd} {code_list_funarg tl f x} }>
end.

Definition code_cons := <{ ^^^^<1> <3> (<2> <1> <0>) }>.

Definition code_hd := <{ ^<0> (^^<1>) {code_list []} }>.

Definition code_map := <{ ^^<0> (^^{code_cons} (<3> <1>) <0>) {code_list []} }>.

Definition code_tl :=
	<{ ^{code_pi2}
		(<0>
			(^^{code_pair_imm <{ {code_cons} <1> ({code_pi1} <0>)}> (code_pi1 (BBound 0))})
			{code_pair_imm (code_list []) (code_list [])}) }>.

Definition code_app :=
	<{ ^^<1> {code_cons} <0> }>.

Opaque code_nat
       code_S
       code_add
       code_mul
       code_exp
       code_true code_false
       code_pair_imm code_pi1 code_pi2
       code_pair_lt
       code_pred
       code_intcase
       code_sub
       code_iszero
       code_le
       code_and code_or code_neg code_impl
       code_impl'
       code_eq_nat
       code_G_maurey
       code_list
       code_cons
       code_hd
       code_map
       code_tl
       code_app.

Parameter code_nat_funarg_add : forall n1 n2 f x, code_nat_funarg (n1 + n2) f x = code_nat_funarg n1 f (code_nat_funarg n2 f x).
Parameter code_nat_funarg_ctx_r : forall {R} n f x1 x2, over_bcontext R x1 x2 -> over_bcontext R (code_nat_funarg n f x1) (code_nat_funarg n f x2).
Parameter code_nat_funarg_ctxstar_r : forall {R} n f x1 x2, (over_bcontext R)^* x1 x2 -> (over_bcontext R)^* (code_nat_funarg n f x1) (code_nat_funarg n f x2).
Parameter code_nat_funarg_ctxstar_l : forall {R} n f1 f2 x,
	(over_bcontext R)^* f1 f2 -> (over_bcontext R)^* (code_nat_funarg n f1 x) (code_nat_funarg n f2 x).
Parameter nfv_code_nat_aux : forall x n, ~ bfv x (code_nat_aux n).
Parameter nfb_code_nat_aux : forall k n, 2 <= k -> ~ bfb k (code_nat_aux n).
Parameter code_nat_funarg_eq_r : forall n f x, code_nat_funarg n f x = code_nat_funarg_r n f x.
Parameter code_nat_aux_eq : forall n, code_nat_aux n = code_nat_funarg n (BBound (S O)) (BBound O).
Parameter code_nat_eq : forall n, code_nat n = BAbs (BAbs (code_nat_funarg n (BBound (S O)) (BBound O))).
Parameter bsubstb_code_nat_funarg : forall n f x k v, bsubstb (code_nat_funarg n f x) k v = code_nat_funarg n (bsubstb f k v) (bsubstb x k v).
Parameter incr_code_nat_funarg : forall n f x k, incr_bound (code_nat_funarg n f x) k = code_nat_funarg n (incr_bound f k) (incr_bound x k).
Parameter beta_code_nat : forall n f x, (over_bcontext beta)^* (code_nat n f x) (code_nat_funarg n f x).
Parameter normal_code_nat : forall n v, ~ over_bcontext beta (code_nat n) v.
Parameter nfv_code_nat : forall n x, ~ bfv x (code_nat n).
Parameter nfb_code_nat : forall n k, ~ bfb k (code_nat n).
Parameter code_S_wd : forall n, (over_bcontext beta)^* (code_S (code_nat n)) (code_nat (S n)).
Parameter normal_code_S : forall u, ~ over_bcontext beta code_S u.
Parameter nfv_code_S : forall x, ~ bfv x code_S.
Parameter nfb_code_S : forall k, ~ bfb k code_S.
Parameter code_add_wd : forall m n, (over_bcontext beta)^* (code_add (code_nat m) (code_nat n)) (code_nat (m + n)).
Parameter normal_code_add : forall u, ~ over_bcontext beta code_add u.
Parameter nfv_code_add : forall x, ~ bfv x code_add.
Parameter nfb_code_add : forall k, ~ bfb k code_add.
Parameter code_mul_wd : forall m n, (over_bcontext beta)^* (code_mul (code_nat m) (code_nat n)) (code_nat (m * n)).
Parameter normal_code_mul : forall u, ~ over_bcontext beta code_mul u.
Parameter nfv_code_mul : forall x, ~ bfv x code_mul.
Parameter nfb_code_mul : forall k, ~ bfb k code_mul.
Parameter code_exp_wd : forall m n f x,
	(over_bcontext beta)^* (code_exp (code_nat m) (code_nat n) f x)
	                       (code_nat_funarg (Nat.pow n m) f x).
Parameter normal_code_exp : forall u, ~ over_bcontext beta code_exp u.
Parameter nfv_code_exp : forall x, ~ bfv x code_exp.
Parameter nfb_code_exp : forall k, ~ bfb k code_exp.
Parameter code_true_eq : code_true = BAbs (BAbs code_true_aux).
Parameter code_false_eq : code_false = BAbs (BAbs code_false_aux).
Parameter code_bool_eq : forall b, code_bool b = BAbs (BAbs (code_bool_aux b)).
Parameter normal_code_true : forall u, ~ over_bcontext beta code_true u.
Parameter normal_code_false : forall u, ~ over_bcontext beta code_false u.
Parameter normal_code_bool : forall b u, ~ over_bcontext beta (code_bool b) u.
Parameter nfv_code_true : forall x, ~ bfv x code_true.
Parameter nfb_code_true : forall k, ~ bfb k code_true.
Parameter nfv_code_false : forall x, ~ bfv x code_false.
Parameter nfb_code_false : forall k, ~ bfb k code_false.
Parameter nfv_code_bool : forall b x, ~ bfv x (code_bool b).
Parameter nfb_code_bool : forall b k, ~ bfb k (code_bool b).
Parameter code_true_wd : forall u v, (over_bcontext beta)^* (code_true u v) u.
Parameter code_false_wd : forall u v, (over_bcontext beta)^* (code_false u v) v.
Parameter code_bool_wd : forall b u v, (over_bcontext beta)^* ((code_bool b) u v) (if b then u else v).
Parameter code_if_true_wd : forall b u v, (over_bcontext beta)^* b code_true -> (over_bcontext beta)^* (code_if b u v) u.
Parameter code_if_false_wd : forall b u v, (over_bcontext beta)^* b code_false -> (over_bcontext beta)^* (code_if b u v) v.
Parameter code_if_wd : forall b u v b0, (over_bcontext beta)^* b (code_bool b0) -> (over_bcontext beta)^* (code_if b u v) (if b0 then u else v).
Parameter code_pi1_wd : forall u v, (over_bcontext beta)^* (code_pi1 (code_pair_imm u v)) u.
Parameter code_pi2_wd : forall u v, (over_bcontext beta)^* (code_pi2 (code_pair_imm u v)) v.
Parameter incr_code_pair_imm : forall u v n, incr_bound (code_pair_imm u v) n = code_pair_imm (incr_bound u n) (incr_bound v n).
Parameter bsubstb_code_pair_imm : forall u v n w, bsubstb (code_pair_imm u v) n w = code_pair_imm (bsubstb u n w) (bsubstb v n w).
Parameter bsubst_code_pair_imm : forall u v x w, bsubst (code_pair_imm u v) x w = code_pair_imm (bsubst u x w) (bsubst v x w).
Parameter bfv_code_pair_imm_iff : forall u v x, bfv x (code_pair_imm u v) <-> bfv x u \/ bfv x v.
Parameter bfb_code_pair_imm_iff : forall u v n, bfb n (code_pair_imm u v) <-> bfb n u \/ bfb n v.
Parameter nfv_code_pi1 : forall x, ~ bfv x code_pi1.
Parameter nfb_code_pi1 : forall k, ~ bfb k code_pi1.
Parameter nfv_code_pi2 : forall x, ~ bfv x code_pi2.
Parameter nfb_code_pi2 : forall k, ~ bfb k code_pi2.
Parameter code_pair_lt_wd : forall u v, (over_bcontext beta)^* (code_pair_lt u v) (code_pair_imm u v).
Parameter nfv_code_pair_lt : forall x, ~ bfv x code_pair_lt.
Parameter nfb_code_pair_lt : forall k, ~ bfb k code_pair_lt.
Parameter code_pred_wd : forall n, (over_bcontext beta)^* (code_pred (code_nat n)) (code_nat (pred n)).
Parameter nfv_code_pred : forall x, ~ bfv x code_pred.
Parameter nfb_code_pred : forall k, ~ bfb k code_pred.
Parameter code_intcase_wd : forall n u f, (over_bcontext beta)^* (code_intcase (code_nat n) u f) (match n with O => u | S n => f (code_nat n) end).
Parameter nfv_code_intcase : forall x, ~ bfv x code_intcase.
Parameter nfb_code_intcase : forall k, ~ bfb k code_intcase.
Parameter code_sub_wd : forall m n, (over_bcontext beta)^* (code_sub (code_nat m) (code_nat n)) (code_nat (m - n)).
Parameter nfv_code_sub : forall x, ~ bfv x code_sub.
Parameter nfb_code_sub : forall k, ~ bfb k code_sub.
Parameter code_iszero_wd : forall n, (over_bcontext beta)^* (code_iszero (code_nat n)) (code_bool (n =? O)).
Parameter nfv_code_iszero : forall x, ~ bfv x code_iszero.
Parameter nfb_code_iszero : forall k, ~ bfb k code_iszero.
Parameter code_le_wd : forall m n, (over_bcontext beta)^* (code_le (code_nat m) (code_nat n)) (code_bool (m <=? n)).
Parameter nfv_code_le : forall x, ~ bfv x code_le.
Parameter nfb_code_le : forall k, ~ bfb k code_le.
Parameter normal_code_and : forall u, ~ over_bcontext beta code_and u.
Parameter normal_code_or : forall u, ~ over_bcontext beta code_or u.
Parameter normal_code_neg : forall u, ~ over_bcontext beta code_neg u.
Parameter normal_code_impl : forall u, ~ over_bcontext beta code_impl u.
Parameter code_and_wd : forall b1 b2, (over_bcontext beta)^* (code_and (code_bool b1) (code_bool b2)) (code_bool (andb b1 b2)).
Parameter code_or_wd : forall b1 b2, (over_bcontext beta)^* (code_or (code_bool b1) (code_bool b2)) (code_bool (orb b1 b2)).
Parameter code_neg_wd : forall b, (over_bcontext beta)^* (code_neg (code_bool b)) (code_bool (negb b)).
Parameter code_impl_wd : forall b1 b2, (over_bcontext beta)^* (code_impl (code_bool b1) (code_bool b2)) (code_bool (orb (negb b1) b2)).
Parameter nfv_code_and : forall x, ~ bfv x code_and.
Parameter nfb_code_and : forall k, ~ bfb k code_and.
Parameter nfv_code_or : forall x, ~ bfv x code_or.
Parameter nfb_code_or : forall k, ~ bfb k code_or.
Parameter nfv_code_neg : forall x, ~ bfv x code_neg.
Parameter nfb_code_neg : forall k, ~ bfb k code_neg.
Parameter nfv_code_impl : forall x, ~ bfv x code_impl.
Parameter nfb_code_impl : forall k, ~ bfb k code_impl.
Parameter code_impl'_wd : (over_bcontext beta)^* code_impl' code_impl.
Parameter nfv_code_impl' : forall x, ~ bfv x code_impl'.
Parameter nfb_code_impl' : forall k, ~ bfb k code_impl'.
Parameter code_eq_nat_wd : forall m n, (over_bcontext beta)^* (code_eq_nat (code_nat m) (code_nat n)) (code_bool (m =? n)).
Parameter nfv_code_eq_nat : forall x, ~ bfv x code_eq_nat.
Parameter nfb_code_eq_nat : forall k, ~ bfb k code_eq_nat.
Parameter code_G_maurey_O_wd : forall a b m,
	(over_bcontext beta)^*
		(code_G_maurey a b (code_nat O) (code_nat m)) a.
Parameter code_G_maurey_S_wd : forall a b n m, exists u,
	(over_bcontext beta)^* (code_G_maurey a b (code_nat (S n)) (code_nat m)) u /\
	(over_bcontext beta)^* (code_G_maurey b a (code_nat m) (code_nat n)) u.
Parameter nfv_code_G_maurey_iff : forall a b x, bfv x (code_G_maurey a b) <-> bfv x a \/ bfv x b.
Parameter nfb_code_G_maurey_iff : forall a b k, bfb k (code_G_maurey a b) <-> bfb k a \/ bfb k b.
Parameter G_maurey_legt : forall m n,
	(over_bcontext beta)^* (code_G_maurey code_true code_false (code_nat m) (code_nat n)) (code_bool (m <=? n)) /\
	(over_bcontext beta)^* (code_G_maurey code_false code_true (code_nat m) (code_nat n)) (code_bool (n <? m)).
Parameter Theta_wd : forall f, (over_bcontext beta)^* (Theta f) (f (Theta f)).
Parameter nfv_Theta : forall x, ~ bfv x Theta.
Parameter nfb_Theta : forall k, ~ bfb k Theta.
Parameter code_list_funarg_app : forall l1 l2 f x, code_list_funarg (l1 ++ l2) f x = code_list_funarg l1 f (code_list_funarg l2 f x).
Parameter code_list_funarg_ctx_r : forall {R} l f x1 x2, over_bcontext R x1 x2 -> over_bcontext R (code_list_funarg l f x1) (code_list_funarg l f x2).
Parameter code_list_funarg_ctxstar_r : forall {R} l f x1 x2, (over_bcontext R)^* x1 x2 -> (over_bcontext R)^* (code_list_funarg l f x1) (code_list_funarg l f x2).
Parameter code_list_funarg_ctxstar_l : forall {R} l f1 f2 x,
	(over_bcontext R)^* f1 f2 -> (over_bcontext R)^* (code_list_funarg l f1 x) (code_list_funarg l f2 x).
Parameter incr_code_list : forall l k, incr_bound (code_list_aux l) (S (S k)) = code_list_aux (map (fun u => incr_bound u k) l).
Parameter bsubstb_code_list_gt : forall l k v,
	bsubstb (code_list_aux l) (S (S k)) (incr_bound (incr_bound v O) O) = code_list_aux (map (fun u => bsubstb u k v) l).
Parameter code_list_aux_eq : forall l,
	code_list_aux l = code_list_funarg (map (fun u => incr_bound (incr_bound u O) O) l) (BBound (S O)) (BBound O).
Parameter code_list_eq : forall l, code_list l = BAbs (BAbs (code_list_aux l)).
Parameter bsubstb_code_list_funarg : forall l f x k v, 
	bsubstb (code_list_funarg l f x) k v = code_list_funarg (map (fun u => bsubstb u k v) l) (bsubstb f k v) (bsubstb x k v).
Parameter incr_code_list_funarg : forall l f x k,
	incr_bound (code_list_funarg l f x) k = code_list_funarg (map (fun u => incr_bound u k) l) (incr_bound f k) (incr_bound x k).
Parameter beta_code_list : forall l f x, (over_bcontext beta)^* (code_list l f x) (code_list_funarg l f x).
Parameter bfv_code_list_iff : forall l x, bfv x (code_list l) <-> exists u, In u l /\ bfv x u.
Parameter bfb_code_list_iff : forall l k, bfb k (code_list l) <-> exists u, In u l /\ bfb k u.
Parameter code_cons_wd : forall hd tl, (over_bcontext beta)^* (code_cons hd (code_list tl)) (code_list (hd :: tl)).
Parameter normal_code_cons : forall u, ~ over_bcontext beta code_cons u.
Parameter nfv_code_cons : forall x, ~ bfv x code_cons.
Parameter nfb_code_cons : forall k, ~ bfb k code_cons.
Parameter code_hd_wd : forall l, (over_bcontext beta)^* (code_hd (code_list l)) (match l with hd :: _ => hd | [] => code_list [] end).
Parameter normal_code_hd : forall u, ~ over_bcontext beta code_hd u.
Parameter nfv_code_hd : forall x, ~ bfv x code_hd.
Parameter nfb_code_hd : forall k, ~ bfb k code_hd.
Parameter code_map_wd : forall f l, (over_bcontext beta)^* (code_map f (code_list l)) (code_list (map (fun u => BApp f u) l)).
Parameter nfv_code_map : forall x, ~ bfv x code_map.
Parameter nfb_code_map : forall k, ~ bfb k code_map.
Parameter code_tl_wd : forall l, (over_bcontext beta)^* (code_tl (code_list l)) (code_list (tl l)).
Parameter nfv_code_tl : forall x, ~ bfv x code_tl.
Parameter nfb_code_tl : forall k, ~ bfb k code_tl.
Parameter code_app_wd : forall l1 l2, (over_bcontext beta)^* (code_app (code_list l1) (code_list l2)) (code_list (l1 ++ l2)).
Parameter nfv_code_app : forall x, ~ bfv x code_app.
Parameter nfb_code_app : forall k, ~ bfb k code_app.

End UntypedValsT.

Module UntypedVals (UntypedL0 : UntypedLambdaT).
Module Import UntypedL := UntypedL0.
Module Export Vars := UntypedL.Vars.
Import UntypedBNotation.

Fixpoint code_nat_aux n := match n with
	| O => <{ <0> }>
	| S n => <{ <1> {code_nat_aux n} }>
end.
Definition code_nat n := <{ ^^ {code_nat_aux n} }>.
(* Fixpoint code_nat_aux_r n acc : bterm := match n with
	| O => acc (BBound O)
	| S n => code_nat_aux_r n (fun x => acc <{ <1> {x} }>)
end.
Definition code_nat_r n := <{ ^^ {code_nat_aux_r n (fun x => x)} }>. *)

Fixpoint code_nat_funarg n f x := match n with
	| O => x
	| S n => <{ {f} {code_nat_funarg n f x} }>
end.
Fixpoint code_nat_funarg_r n f x : bterm := match n with
	| O => x
	| S n => code_nat_funarg_r n f <{ {f} {x} }>
end.

Lemma code_nat_funarg_add : forall n1 n2 f x, code_nat_funarg (n1 + n2) f x = code_nat_funarg n1 f (code_nat_funarg n2 f x).
Proof using.
	intros n1 n2 f x; induction n1 as [|n1 IH]; [exact eq_refl|exact (f_equal _ IH)].
Qed.

Lemma code_nat_funarg_ctx_r : forall {R} n f x1 x2, over_bcontext R x1 x2 -> over_bcontext R (code_nat_funarg n f x1) (code_nat_funarg n f x2).
Proof using.
	intros R n f x1 x2 Hx; induction n as [|n IH]; [exact Hx|exact (bctx_app_r IH)].
Qed.
Lemma code_nat_funarg_ctxstar_r : forall {R} n f x1 x2, (over_bcontext R)^* x1 x2 -> (over_bcontext R)^* (code_nat_funarg n f x1) (code_nat_funarg n f x2).
Proof using.
	intros R n f x1 x2 H; induction H as [x1 x2 H|x|x1 x2 x3 _ IH1 _ IH2];
	  [exact (rt_step (code_nat_funarg_ctx_r _ _ _ _ H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.
Lemma code_nat_funarg_ctxstar_l : forall {R} n f1 f2 x,
	(over_bcontext R)^* f1 f2 -> (over_bcontext R)^* (code_nat_funarg n f1 x) (code_nat_funarg n f2 x).
Proof using.
	intros R n f1 f2 x Hf; induction n as [|n IH];
	  [exact rt_refl
	  |exact (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l BCHole _) Hf) (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) IH))].
Qed.

(* Lemma code_nat_aux_r_ext : forall n acc1 acc2, (forall v, acc1 v = acc2 v) -> code_nat_aux_r n acc1 = code_nat_aux_r n acc2.
Proof using.
	intros n; induction n as [|n IHn]; intros acc1 acc2 Hacc.
	1: exact (Hacc _).
	refine (IHn _ _ _); intros v; exact (Hacc _).
Qed. *)

Lemma nfv_code_nat_aux : forall x n, ~ bfv x (code_nat_aux n).
Proof using.
	intros x n H; induction n as [|n IH]; [inversion H|inversion H; [inversion H1|exact (IH H1)]].
Qed.
Lemma nfb_code_nat_aux : forall k n, 2 <= k -> ~ bfb k (code_nat_aux n).
Proof using.
	intros [|[|k]] n Hk H; [inversion Hk|inversion Hk; inversion H1|clear Hk].
	induction n as [|n IH]; [inversion H|inversion H; [inversion H2|exact (IH H2)]].
Qed.

Lemma code_nat_funarg_eq_r : forall n f x, code_nat_funarg n f x = code_nat_funarg_r n f x.
Proof using.
	intros n f x.
	pose (k := O).
	rewrite (eq_refl : x = code_nat_funarg k f x) at 2.
	rewrite (eq_refl : code_nat_funarg n f x = code_nat_funarg k f _).
	generalize dependent k; induction n as [|n IHn]; intros k; cbn.
	1: exact eq_refl.
	specialize (IHn (S k)); cbn in IHn.
	rewrite <-IHn; clear IHn.
	induction k as [|k IHk].
	1: exact eq_refl.
	exact (f_equal _ IHk).
Qed.
Lemma code_nat_aux_eq : forall n, code_nat_aux n = code_nat_funarg n (BBound (S O)) (BBound O).
Proof using.
	intros n.
	induction n as [|n IH]; [exact eq_refl|exact (f_equal _ IH)].
Qed.
Lemma code_nat_eq : forall n, code_nat n = BAbs (BAbs (code_nat_funarg n (BBound (S O)) (BBound O))).
Proof using.
	intros n; exact (f_equal (fun a => BAbs (BAbs a)) (code_nat_aux_eq _)).
Qed.
(* Lemma code_nat_eq_r : forall n, code_nat n = code_nat_r n.
Proof using.
	intros n; refine (f_equal (fun a => BAbs (BAbs a)) _).
	pose (k := O).
	rewrite (eq_refl : code_nat_aux n = code_nat_funarg k (BBound (S O)) _).
	pose (acc' := fun v => code_nat_funarg k (BBound (S O)) v).
	assert (tmp : forall v, (fun x => x) v = acc' v) by (intros v; exact eq_refl).
	rewrite (code_nat_aux_r_ext _ _ _ tmp); clear tmp; subst acc'.
	generalize dependent k; induction n as [|n IHn]; intros k; cbn.
	1: exact eq_refl.
	specialize (IHn (S k)); cbn in IHn.
	refine (eq_trans _ (eq_trans IHn _)).
	1: clear; induction k as [|k]; [exact eq_refl|exact (f_equal _ IHk)].
	refine (code_nat_aux_r_ext _ _ _ _).
	intros v; clear; induction k as [|k]; [exact eq_refl|exact (f_equal _ IHk)].
Qed. *)

Lemma bsubstb_code_nat_funarg : forall n f x k v, bsubstb (code_nat_funarg n f x) k v = code_nat_funarg n (bsubstb f k v) (bsubstb x k v).
Proof using.
	intros n f x k v.
	induction n as [|n IHn]; [exact eq_refl|exact (f_equal _ IHn)].
Qed.
Lemma incr_code_nat_funarg : forall n f x k, incr_bound (code_nat_funarg n f x) k = code_nat_funarg n (incr_bound f k) (incr_bound x k).
Proof using.
	intros n f x k.
	induction n as [|n IHn]; [exact eq_refl|exact (f_equal _ IHn)].
Qed.

Lemma beta_code_nat : forall n f x, (over_bcontext beta)^* (code_nat n f x) (code_nat_funarg n f x).
Proof using.
	intros n f x; rewrite code_nat_eq.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn; rewrite bsubstb_code_nat_funarg; cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); rewrite bsubstb_code_nat_funarg, bsubstb_incr; exact rt_refl.
Qed.

Lemma normal_code_nat : forall n v, ~ over_bcontext beta (code_nat n) v.
Proof using.
	intros n u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	generalize dependent u; induction n as [|n IHn]; intros u H.
	1: inversion H; inversion H0.
	inversion H; [inversion H0|inversion H3; inversion H4|exact (IHn _ H3)].
Qed.

Lemma nfv_code_nat : forall n x, ~ bfv x (code_nat n).
Proof using.
	intros n x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	induction n as [|n IH].
	1: inversion H.
	inversion H; [inversion H1|exact (IH H1)].
Qed.
Lemma nfb_code_nat : forall n k, ~ bfb k (code_nat n).
Proof using.
	intros n k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	induction n as [|n IH].
	1: inversion H.
	inversion H; [inversion H2|exact (IH H2)].
Qed.

Opaque code_nat.

Definition code_S := <{ ^^^<1> (<2> <1> <0>) }>.

Lemma code_S_wd : forall n, (over_bcontext beta)^* (code_S (code_nat n)) (code_nat (S n)).
Proof using.
	intros n.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCAbs (BCAbs (BCApp_r _ BCHole))) (beta_code_nat _ _ _)) _); cbn.
	rewrite code_nat_eq; exact rt_refl.
Qed.

Lemma normal_code_S : forall u, ~ over_bcontext beta code_S u.
Proof using.
	intros u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|inversion H3; inversion H4|clear u H u0 v H0 H2 H1; rename v' into u, H3 into H].
	inversion H; [inversion H0|clear u H u0 v H0 H2 H1; rename u' into u, H3 into H|inversion H3; inversion H4].
	inversion H; [inversion H0| |]; inversion H3; inversion H4.
Qed.

Lemma nfv_code_S : forall x, ~ bfv x code_S.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H; [inversion H1|clear - H1].
	inversion H1; [clear - H0|inversion H0].
	inversion H0; inversion H1.
Qed.
Lemma nfb_code_S : forall k, ~ bfb k code_S.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H; [inversion H2|clear - H2].
	inversion H2; inversion H1; inversion H6.
Qed.

Opaque code_S.

Definition code_add := <{ ^^^^<3> <1> (<2> <1> <0>) }>.

Lemma code_add_wd : forall m n, (over_bcontext beta)^* (code_add (code_nat m) (code_nat n)) (code_nat (m + n)).
Proof using.
	intros m n; unfold code_add.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)), !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCAbs (BCAbs (BCApp_r _ BCHole))) (beta_code_nat _ _ _)) _); cbn.
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) (beta_code_nat _ _ _)) _); cbn.
	rewrite code_nat_eq, code_nat_funarg_add; exact rt_refl.
Qed.

Lemma normal_code_add : forall u, ~ over_bcontext beta code_add u.
Proof using.
	intros u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|clear u H u0 v H0 H2 H1; rename u' into u, H3 into H|clear u H u0 v H0 H2 H1; rename v' into u, H3 into H].
	1: inversion H; [inversion H0| |]; inversion H3; inversion H4.
	inversion H; [inversion H0|clear u H u0 v H0 H2 H1; rename u' into u, H3 into H|inversion H3; inversion H4].
	inversion H; [inversion H0| |]; inversion H3; inversion H4.
Qed.

Lemma nfv_code_add : forall x, ~ bfv x code_add.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H; inversion H1; inversion H4; inversion H7.
Qed.
Lemma nfb_code_add : forall k, ~ bfb k code_add.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H; inversion H2; inversion H6; inversion H10.
Qed.

Opaque code_add.

Definition code_mul := <{ ^^^<2> (<1> <0>) }>.

Lemma code_mul_wd : forall m n, (over_bcontext beta)^* (code_mul (code_nat m) (code_nat n)) (code_nat (m * n)).
Proof using.
	intros m n; unfold code_mul.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)), (incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	rewrite !code_nat_eq.
	refine (rt_trans (rt_step (bctx_abs (bctx_app_r (bctx_step (Beta _ _))))) _); cbn; rewrite bsubstb_code_nat_funarg; cbn.
	refine (rt_trans (rt_step (bctx_abs (bctx_step (Beta _ _)))) _); cbn; rewrite bsubstb_code_nat_funarg, incr_code_nat_funarg; cbn.
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	induction m as [|m IHm]; [exact rt_refl|cbn].
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn; rewrite bsubstb_code_nat_funarg; cbn.
	rewrite code_nat_funarg_add.
	exact (code_nat_funarg_ctxstar_r _ _ _ _ IHm).
Qed.

Lemma normal_code_mul : forall u, ~ over_bcontext beta code_mul u.
Proof using.
	intros u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|inversion H3; inversion H4|clear u H u0 v H0 H2 H1; rename v' into u, H3 into H].
	inversion H; [inversion H0| |]; inversion H3; inversion H4.
Qed.

Lemma nfv_code_mul : forall x, ~ bfv x code_mul.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H; [inversion H1|clear - H1].
	inversion H1; [clear - H0|inversion H0].
	inversion H0; inversion H1.
Qed.
Lemma nfb_code_mul : forall k, ~ bfb k code_mul.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H; [inversion H2|clear - H2].
	inversion H2; inversion H1; inversion H6.
Qed.

Opaque code_mul.

Definition code_exp := <{ ^^<1> <0> }>.

Lemma code_exp_wd : forall m n f x,
	(over_bcontext beta)^* (code_exp (code_nat m) (code_nat n) f x)
	                       (code_nat_funarg (Nat.pow n m) f x).
Proof using.
	intros m n f x; unfold code_exp.
	refine (rt_trans (rt_step (bctx_app_l (bctx_app_l (bctx_app_l (bctx_step (Beta _ _)))))) _); cbn.
	rewrite (incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_app_l (bctx_app_l (bctx_step (Beta _ _))))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l BCHole _) (beta_code_nat _ _ _)) _); cbn.
	generalize dependent x; induction m as [|m IHm]; intros x.
	1: exact rt_refl.
	cbn; refine (rt_trans (beta_code_nat _ _ _) _).
	remember (n ^ m) as k eqn:eqk; clear eqk.
	remember (code_nat_funarg m (code_nat n) f) as u eqn:equ; clear equ.
	induction n as [|n IHn].
	1: exact rt_refl.
	cbn; rewrite code_nat_funarg_add; exact (rt_trans (IHm _) (code_nat_funarg_ctxstar_r _ _ _ _ IHn)).
Qed.

Lemma normal_code_exp : forall u, ~ over_bcontext beta code_exp u.
Proof using.
	intros u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0| |]; inversion H3; inversion H4.
Qed.

Lemma nfv_code_exp : forall x, ~ bfv x code_exp.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H; inversion H1.
Qed.
Lemma nfb_code_exp : forall k, ~ bfb k code_exp.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H; inversion H2.
Qed.

Opaque code_exp.

Definition code_true_aux := BBound 1.
Definition code_false_aux := BBound 0.
Definition code_bool_aux (b : bool) := if b then code_true_aux else code_false_aux.

Definition code_true := <{ ^^<1> }>.
Definition code_false := <{ ^^<0> }>.
Definition code_bool (b : bool) := if b then code_true else code_false.
Definition code_if b x y := <{ {b} {x} {y} }>.

Lemma code_true_eq : code_true = BAbs (BAbs code_true_aux).
Proof using.
	exact eq_refl.
Qed.
Lemma code_false_eq : code_false = BAbs (BAbs code_false_aux).
Proof using.
	exact eq_refl.
Qed.
Lemma code_bool_eq : forall b, code_bool b = BAbs (BAbs (code_bool_aux b)).
Proof using.
	intros [|]; exact eq_refl.
Qed.

Lemma normal_code_true : forall u, ~ over_bcontext beta code_true u.
Proof using.
	intros u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; inversion H0.
Qed.
Lemma normal_code_false : forall u, ~ over_bcontext beta code_false u.
Proof using.
	intros u H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; [inversion H0|].
	destruct u as [| | |u]; try discriminate H2; injection H2 as ->; clear u0 H0 H; rename H1 into H.
	inversion H; inversion H0.
Qed.
Lemma normal_code_bool : forall b u, ~ over_bcontext beta (code_bool b) u.
Proof using.
	intros [|]; [exact normal_code_true|exact normal_code_false].
Qed.

Lemma nfv_code_true : forall x, ~ bfv x code_true.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H.
Qed.
Lemma nfb_code_true : forall k, ~ bfb k code_true.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H.
Qed.
Lemma nfv_code_false : forall x, ~ bfv x code_false.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H.
Qed.
Lemma nfb_code_false : forall k, ~ bfb k code_false.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H.
Qed.
Lemma nfv_code_bool : forall b x, ~ bfv x (code_bool b).
Proof using.
	intros [|]; [exact nfv_code_true|exact nfv_code_false].
Qed.
Lemma nfb_code_bool : forall b k, ~ bfb k (code_bool b).
Proof using.
	intros [|]; [exact nfb_code_true|exact nfb_code_false].
Qed.

Lemma code_true_wd : forall u v, (over_bcontext beta)^* (code_true u v) u.
Proof using.
	intros u v.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	refine (eq_ind _ _ (rt_step (bctx_step (Beta _ _))) _ _).
	exact bsubstb_incr.
Qed.
Lemma code_false_wd : forall u v, (over_bcontext beta)^* (code_false u v) v.
Proof using.
	intros u v.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	exact (rt_step (bctx_step (Beta _ _))).
Qed.
Lemma code_bool_wd : forall b u v, (over_bcontext beta)^* ((code_bool b) u v) (if b then u else v).
Proof using.
	intros [|] u v; [exact (code_true_wd _ _)|exact (code_false_wd _ _)].
Qed.
Lemma code_if_true_wd : forall b u v, (over_bcontext beta)^* b code_true -> (over_bcontext beta)^* (code_if b u v) u.
Proof using.
	intros b u v Hb.
	refine (rt_trans _ (code_true_wd _ _)).
	exact (clos_rt_over_bcontext_ctx (BCApp_l (BCApp_l BCHole _) _) Hb).
Qed.
Lemma code_if_false_wd : forall b u v, (over_bcontext beta)^* b code_false -> (over_bcontext beta)^* (code_if b u v) v.
Proof using.
	intros b u v Hb.
	refine (rt_trans _ (code_false_wd _ _)).
	exact (clos_rt_over_bcontext_ctx (BCApp_l (BCApp_l BCHole _) _) Hb).
Qed.
Lemma code_if_wd : forall b u v b0, (over_bcontext beta)^* b (code_bool b0) -> (over_bcontext beta)^* (code_if b u v) (if b0 then u else v).
Proof using.
	intros b u v [|]; [exact (code_if_true_wd _ _ _)|exact (code_if_false_wd _ _ _)].
Qed.

Opaque code_true code_false.

Definition code_pair_imm u v := <{ ^<0> {incr_bound u O} {incr_bound v O} }>.
Definition code_pi1 := <{ ^<0> {code_true} }>.
Definition code_pi2 := <{ ^<0> {code_false} }>.

Lemma code_pi1_wd : forall u v, (over_bcontext beta)^* (code_pi1 (code_pair_imm u v)) u.
Proof using.
	intros u v.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_true _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn; rewrite !bsubstb_incr.
	exact (code_true_wd _ _).
Qed.
Lemma code_pi2_wd : forall u v, (over_bcontext beta)^* (code_pi2 (code_pair_imm u v)) v.
Proof using.
	intros u v.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_false _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn; rewrite !bsubstb_incr.
	exact (code_false_wd _ _).
Qed.

Lemma incr_code_pair_imm : forall u v n, incr_bound (code_pair_imm u v) n = code_pair_imm (incr_bound u n) (incr_bound v n).
Proof using.
	intros u v n; cbn;
	  exact (eq_sym (f_equal2 (fun a b => BAbs (BApp (BApp _ a) b)) (incr_bound_comm (le_0_n _)) (incr_bound_comm (le_0_n _)))).
Qed.
Lemma bsubstb_code_pair_imm : forall u v n w, bsubstb (code_pair_imm u v) n w = code_pair_imm (bsubstb u n w) (bsubstb v n w).
Proof using.
	intros u v n w; cbn; refine (f_equal2 (fun a b => BAbs (BApp (BApp _ a) b)) _ _).
	1,2: exact (eq_sym (incr_bsubstb_ge (le_0_n _))).
Qed.
Lemma bsubst_code_pair_imm : forall u v x w, bsubst (code_pair_imm u v) x w = code_pair_imm (bsubst u x w) (bsubst v x w).
Proof using.
	intros u v x w; cbn; refine (f_equal2 (fun a b => BAbs (BApp (BApp _ a) b)) _ _); [clear v|clear u; rename v into u].
	1,2: generalize 0; generalize dependent w; induction u as [y|k|u1 IH1 u2 IH2|u IH]; intros v n; cbn.
	1,5: destruct (dec_V x y); exact eq_refl.
	1,4: exact eq_refl.
	1,3: exact (f_equal2 _ (IH1 _ _) (IH2 _ _)).
	1,2: rewrite (incr_bound_comm (le_0_n _)); exact (f_equal _ (IH _ _)).
Qed.
Lemma bfv_code_pair_imm_iff : forall u v x, bfv x (code_pair_imm u v) <-> bfv x u \/ bfv x v.
Proof using.
	intros u v x; split; intros H.
	- inversion H as [| | |u' H' equ]; subst; clear H; rename H' into H.
	  inversion H as [|u' v' H' eq1|u' v' H' eq1|]; [|right; clear - H'].
	  1: subst; inversion H'; [inversion H1|left; clear - H1; rename H1 into H', u into v].
	  1,2: generalize dependent 0; induction v as [y|k|u IHu v IHv|u IH]; intros n H.
	  1,5: exact H.
	  1,4: inversion H.
	  2,4: inversion H; exact (BFV_Abs (IH _ H1)).
	  1,2: inversion H; [exact (BFV_App_l (IHu _ H1))|exact (BFV_App_r (IHv _ H1))].
	- destruct H as [H|H]; [refine (BFV_Abs (BFV_App_l (BFV_App_r _))); clear v|refine (BFV_Abs (BFV_App_r _)); clear u; rename v into u].
	  1,2: generalize 0; induction u as [y|k|u IHu v IHv|u IH]; intros n.
	  1,5: exact H.
	  1,4: inversion H.
	  2,4: inversion H; exact (BFV_Abs (IH H1 _)).
	  1,2: inversion H; [exact (BFV_App_l (IHu H1 _))|exact (BFV_App_r (IHv H1 _))].
Qed.
Lemma bfb_code_pair_imm_iff : forall u v n, bfb n (code_pair_imm u v) <-> bfb n u \/ bfb n v.
Proof using.
	intros u v n; split; intros H.
	- inversion H as [| | |n' u' H' equ]; subst; clear H; rename H' into H.
	  inversion H as [|n' u' v' H' eq1|n' u' v' H' eq1|]; [|right; clear - H'].
	  1: subst; inversion H'; [inversion H2|left; clear - H2; rename H2 into H', u into v].
	  1,2: rewrite (eq_refl : S n = 0 + S n) in H'; rewrite (eq_refl : n = 0 + n).
	  1,2: generalize dependent 0; induction v as [y|k|u IHu v IHv|u IH]; intros m H.
	  1,5: inversion H.
	  1,4: inversion H; subst; destruct (le_gt_cases m k) as [mlek|kltm];
	         [rewrite (proj2 (leb_le _ _) mlek) in H2|rewrite (proj2 (leb_gt _ _) kltm) in H2].
	  1,3: rewrite <-plus_n_Sm in H2; injection H2 as <-; exact BFB_Var.
	  1,2: subst k; rewrite <-plus_n_Sm in kltm; contradiction (lt_neq _ _ (lt_trans _ _ _ (le_add_r (S m) _) kltm) eq_refl).
	  1,3: inversion H; [exact (BFB_App_l (IHu _ H2))|exact (BFB_App_r (IHv _ H2))].
	  1,2: inversion H; subst; exact (BFB_Abs (IH (S _) H2)).
	- destruct H as [H|H]; [refine (BFB_Abs (BFB_App_l (BFB_App_r _))); clear v|refine (BFB_Abs (BFB_App_r _)); clear u; rename v into u].
	  1,2: rewrite (eq_refl : S n = 0 + S n); rewrite (eq_refl : n = 0 + n) in H.
	  1,2: generalize dependent 0; induction u as [y|k|u IHu v IHv|u IH]; intros m H.
	  1,5: inversion H.
	  1,4: inversion H; subst; cbn; rewrite (proj2 (leb_le _ _) (le_add_r _ _)), <-plus_n_Sm; exact BFB_Var.
	  1,3: inversion H; [exact (BFB_App_l (IHu _ H2))|exact (BFB_App_r (IHv _ H2))].
	  1,2: inversion H; exact (BFB_Abs (IH (S _) H2)).
Qed.
Lemma nfv_code_pi1 : forall x, ~ bfv x code_pi1.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' eq1|u v H' eq1|]; [inversion H'|exact (nfv_code_true _ H')].
Qed.
Lemma nfb_code_pi1 : forall k, ~ bfb k code_pi1.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' eq1|k' u v H' eq1|]; [inversion H'|subst].
	exact (nfb_code_true _ H').
Qed.
Lemma nfv_code_pi2 : forall x, ~ bfv x code_pi2.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' eq1|u v H' eq1|]; [inversion H'|exact (nfv_code_false _ H')].
Qed.
Lemma nfb_code_pi2 : forall k, ~ bfb k code_pi2.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' eq1|k' u v H' eq1|]; [inversion H'|subst].
	exact (nfb_code_false _ H').
Qed.

Opaque code_pair_imm code_pi1 code_pi2.

Definition code_pair_lt := <{ ^^^<0> <2> <1> }>.

Lemma code_pair_lt_wd : forall u v, (over_bcontext beta)^* (code_pair_lt u v) (code_pair_imm u v).
Proof using.
	intros u v.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn; rewrite (incr_bound_comm (le_n _)), bsubstb_incr.
	exact rt_refl.
Qed.

Lemma nfv_code_pair_lt : forall x, ~ bfv x code_pair_lt.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' eq1|u v H' eq1|]; inversion H'; inversion H2.
Qed.
Lemma nfb_code_pair_lt : forall k, ~ bfb k code_pair_lt.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' eqk equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' eq1|k' u v H' eq1|]; inversion H'; inversion H4.
Qed.

Opaque code_pair_lt.

Definition code_pred := <{
	^{code_pi2}
		(<0>
			(^{code_pair_imm <{ {code_S} ({code_pi1} <0> ) }> <{ {code_pi1} <0> }>})
			{code_pair_imm (code_nat O) (code_nat O)}) }>.

Lemma code_pred_wd : forall n, (over_bcontext beta)^* (code_pred (code_nat n)) (code_nat (pred n)).
Proof using.
	unfold code_pred; intros n.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi2 _)), !bsubstb_code_pair_imm; cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_S _)),
	        (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi1 _)),
	        (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (beta_code_nat _ _ _)) _); cbn.
	destruct n as [|n].
	1: exact (code_pi2_wd _ _).
	cbn.
	refine (rt_trans (rt_step (bctx_app_r (bctx_step (Beta _ _)))) _).
	rewrite bsubstb_code_pair_imm.
	refine (rt_trans (code_pi2_wd _ _) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi1 _)).
	induction n as [|n IHn].
	1: exact (code_pi1_wd _ _).
	cbn.
	refine (rt_trans (rt_step (bctx_app_r (bctx_step (Beta _ _)))) _).
	rewrite bsubstb_code_pair_imm.
	refine (rt_trans (code_pi1_wd _ _) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_S _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi1 _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) IHn) _); cbn.
	exact (code_S_wd _).
Qed.

Lemma nfv_code_pred : forall x, ~ bfv x code_pred.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [|clear H; rename H' into H].
	1: exact (nfv_code_pi2 _ H').
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|].
	2: rewrite bfv_code_pair_imm_iff in H'; clear H; destruct H' as [H|H].
	2: exact (nfv_code_nat _ _ H).
	2: exact (nfv_code_nat _ _ H).
	inversion H as [|u v H' equ|u v H' equ|]; subst; [|clear H; rename H' into H].
	1: inversion H'.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	rewrite bfv_code_pair_imm_iff in H; destruct H as [H|H].
	1: inversion H as [|u v H' equ|u v H' equ|]; subst; [|clear H; rename H' into H].
	1: exact (nfv_code_S _ H').
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; [|clear H; rename H' into H].
	1,3: exact (nfv_code_pi1 _ H').
	1,2: inversion H.
Qed.
Lemma nfb_code_pred : forall k, ~ bfb k code_pred.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [|clear H; rename H' into H].
	1: exact (nfb_code_pi2 _ H').
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|].
	2: rewrite bfb_code_pair_imm_iff in H'; clear H; destruct H' as [H|H].
	2: exact (nfb_code_nat _ _ H).
	2: exact (nfb_code_nat _ _ H).
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [|clear H; rename H' into H].
	1: inversion H'.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	rewrite bfb_code_pair_imm_iff in H; destruct H as [H|H].
	1: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [|clear H; rename H' into H].
	1: exact (nfb_code_S _ H').
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [|clear H; rename H' into H].
	1,3: exact (nfb_code_pi1 _ H').
	1,2: inversion H.
Qed.

Opaque code_pred.

Definition code_intcase := <{ ^^^<2> (^<1> ({code_pred} <3>)) <1> }>.

Lemma code_intcase_wd : forall n u f, (over_bcontext beta)^* (code_intcase (code_nat n) u f) (match n with O => u | S n => f (code_nat n) end).
Proof using.
	intros n u v; unfold code_intcase.
	refine (rt_trans (rt_step (bctx_app_l (bctx_app_l (bctx_step (Beta _ _))))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pred _)).
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pred _)), !(bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pred _)), !(bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	rewrite bsubstb_incr.
	refine (rt_trans (beta_code_nat _ _ _) _).
	destruct n as [|n].
	1: exact rt_refl.
	cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite bsubstb_incr.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pred _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	exact (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (code_pred_wd _)).
Qed.

Lemma nfv_code_intcase : forall x, ~ bfv x code_intcase.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	exact (nfv_code_pred _ H).
Qed.
Lemma nfb_code_intcase : forall k, ~ bfb k code_intcase.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	exact (nfb_code_pred _ H).
Qed.

Opaque code_intcase.

Definition code_sub := <{ ^^<0> {code_pred} <1> }>.

Lemma code_sub_wd : forall m n, (over_bcontext beta)^* (code_sub (code_nat m) (code_nat n)) (code_nat (m - n)).
Proof using.
	intros m n; unfold code_sub.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pred _)), (incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pred _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (beta_code_nat _ _ _) _).
	generalize dependent m; induction n as [|n IHn]; intros m.
	1: rewrite sub_0_r; exact rt_refl.
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (IHn _)) _); cbn.
	refine (eq_ind _ _ (code_pred_wd _) _ _); f_equal.
	clear IHn; exact (eq_sym (sub_succ_r _ _)).
Qed.

Lemma nfv_code_sub : forall x, ~ bfv x code_sub.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	exact (nfv_code_pred _ H).
Qed.
Lemma nfb_code_sub : forall k, ~ bfb k code_sub.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	exact (nfb_code_pred _ H).
Qed.

Opaque code_sub.

Definition code_iszero := <{ ^<0> (^{code_false}) {code_true} }>.

Lemma code_iszero_wd : forall n, (over_bcontext beta)^* (code_iszero (code_nat n)) (code_bool (n =? O)).
Proof using.
	intros n.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_false _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_true _)).
	refine (rt_trans (beta_code_nat _ _ _) _).
	destruct n as [|n]; cbn.
	1: exact rt_refl.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_false _)).
	exact rt_refl.
Qed.

Lemma nfv_code_iszero : forall x, ~ bfv x code_iszero.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	2: exact (nfv_code_true _ H).
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	exact (nfv_code_false _ H).
Qed.
Lemma nfb_code_iszero : forall k, ~ bfb k code_iszero.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	2: exact (nfb_code_true _ H).
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	exact (nfb_code_false _ H).
Qed.

Opaque code_iszero.

Definition code_le := <{ ^^{code_iszero} ({code_sub} <1> <0>) }>.

Lemma code_le_wd : forall m n, (over_bcontext beta)^* (code_le (code_nat m) (code_nat n)) (code_bool (m <=? n)).
Proof using.
	intros m n; unfold code_le.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_iszero _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_sub _)).
	rewrite (incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_iszero _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_sub _)).
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (code_sub_wd _ _)) _); cbn.
	refine (eq_ind _ _ (code_iszero_wd _) _ _); f_equal.
	generalize dependent n; induction m as [|m IHm]; intros n.
	1: exact eq_refl.
	destruct n as [|n]; [exact eq_refl|].
	exact (IHm n).
Qed.

Lemma nfv_code_le : forall x, ~ bfv x code_le.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfv_code_iszero _ H).
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	exact (nfv_code_sub _ H).
Qed.
Lemma nfb_code_le : forall k, ~ bfb k code_le.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfb_code_iszero _ H).
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	exact (nfb_code_sub _ H).
Qed.

Opaque code_le.

Definition code_and := <{ ^^^^<3> (<2> <1> <0>) <0> }>.
Definition code_or := <{ ^^^^<3> <1> (<2> <1> <0>) }>.
Definition code_neg := <{ ^^^<2> <0> <1> }>.
Definition code_impl := <{ ^^^^<3> (<2> <1> <0>) <1> }>.
Definition code_impl' := <{ ^^{code_or} ({code_neg} <1>) <0> }>.

Lemma normal_code_and : forall u, ~ over_bcontext beta code_and u.
Proof using.
	intros u H.
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1,2: inversion H as [u' v' H'| | |]; inversion H'.
Qed.
Lemma normal_code_or : forall u, ~ over_bcontext beta code_or u.
Proof using.
	intros u H.
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1: inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1,2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1,2: inversion H as [u' v' H'| | |]; inversion H'.
Qed.
Lemma normal_code_neg : forall u, ~ over_bcontext beta code_neg u.
Proof using.
	intros u H.
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1,2: inversion H as [u' v' H'| | |]; inversion H'.
Qed.
Lemma normal_code_impl : forall u, ~ over_bcontext beta code_impl u.
Proof using.
	intros u H.
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H']; [inversion H'|clear - H'; rename v' into u, H' into H].
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	2: inversion H as [u' v' H'| | |]; inversion H'.
	inversion H as [u' v' H'|u' u'' v' H'|u' u'' v' H'|]; [inversion H'|clear - H'; rename u'' into u, H' into H|clear - H'; rename v' into u, H' into H].
	1,2: inversion H as [u' v' H'| | |]; inversion H'.
Qed.

Lemma code_and_wd : forall b1 b2, (over_bcontext beta)^* (code_and (code_bool b1) (code_bool b2)) (code_bool (andb b1 b2)).
Proof using.
	intros b1 b2; unfold code_and.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_bool _ _)), !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	rewrite (code_bool_eq (andb _ _)).
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	refine (rt_trans (code_bool_wd _ _ _) _).
	destruct b1; cbn.
	2: exact rt_refl.
	exact (code_bool_wd _ _ _).
Qed.
Lemma code_or_wd : forall b1 b2, (over_bcontext beta)^* (code_or (code_bool b1) (code_bool b2)) (code_bool (orb b1 b2)).
Proof using.
	intros b1 b2; unfold code_or.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_bool _ _)), !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	rewrite (code_bool_eq (orb _ _)).
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	refine (rt_trans (code_bool_wd _ _ _) _).
	destruct b1; cbn.
	1: exact rt_refl.
	exact (code_bool_wd _ _ _).
Qed.
Lemma code_neg_wd : forall b, (over_bcontext beta)^* (code_neg (code_bool b)) (code_bool (negb b)).
Proof using.
	intros b; unfold code_neg.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	rewrite (code_bool_eq (negb _)).
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	destruct b; exact (code_bool_wd _ _ _).
Qed.
Lemma code_impl_wd : forall b1 b2, (over_bcontext beta)^* (code_impl (code_bool b1) (code_bool b2)) (code_bool (orb (negb b1) b2)).
Proof using.
	intros b1 b2; unfold code_impl.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_bool _ _)), !(incr_nfb _ _ (fun _ _ => nfb_code_bool _ _)).
	rewrite (code_bool_eq (orb _ _)).
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	refine (rt_trans (code_bool_wd _ _ _) _).
	destruct b1; cbn.
	2: exact rt_refl.
	exact (code_bool_wd _ _ _).
Qed.

Lemma nfv_code_and : forall x, ~ bfv x code_and.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; inversion H'.
Qed.
Lemma nfb_code_and : forall k, ~ bfb k code_and.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; inversion H'.
Qed.
Lemma nfv_code_or : forall x, ~ bfv x code_or.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|u v H' equ|u v H' equ|]; inversion H'.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; inversion H'.
Qed.
Lemma nfb_code_or : forall k, ~ bfb k code_or.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|k' u v H' equ|k' u v H' equ|]; inversion H'.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; inversion H'.
Qed.
Lemma nfv_code_neg : forall x, ~ bfv x code_neg.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; inversion H'.
Qed.
Lemma nfb_code_neg : forall k, ~ bfb k code_neg.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; inversion H'.
Qed.
Lemma nfv_code_impl : forall x, ~ bfv x code_impl.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; inversion H'.
Qed.
Lemma nfb_code_impl : forall k, ~ bfb k code_impl.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; inversion H'.
Qed.

Lemma code_impl'_wd : (over_bcontext beta)^* code_impl' code_impl.
Proof using.
	unfold code_impl', code_impl, code_or, code_neg.
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs BCHole)) _).
	refine (rt_trans (rt_step (bctx_app_l (bctx_app_l (bctx_step (Beta _ _))))) _); cbn.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	exact (rt_step (bctx_step (Beta _ _))).
Qed.

Opaque code_and code_or code_neg code_impl.

Lemma nfv_code_impl' : forall x, ~ bfv x code_impl'.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfv_code_or _ H).
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	exact (nfv_code_neg _ H).
Qed.
Lemma nfb_code_impl' : forall k, ~ bfb k code_impl'.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfb_code_or _ H).
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	exact (nfb_code_neg _ H).
Qed.

Opaque code_impl'.

Definition code_eq_nat := <{ ^^{code_and} ({code_le} <1> <0>) ({code_le} <0> <1>) }>.

Lemma code_eq_nat_wd : forall m n, (over_bcontext beta)^* (code_eq_nat (code_nat m) (code_nat n)) (code_bool (m =? n)).
Proof using.
	intros m n; unfold code_eq_nat.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_and _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_le _)).
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_and _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_le _)).
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (code_le_wd _ _)) _); cbn.
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l (BCApp_r _ BCHole) _) (code_le_wd _ _)) _); cbn.
	refine (eq_ind _ _ (code_and_wd _ _) _ _); f_equal.
	destruct (le_gt_cases m n) as [mlen|mgtn].
	2: rewrite (proj2 (leb_gt _ _) mgtn), eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ mgtn)); exact eq_refl.
	rewrite (proj2 (leb_le _ _) mlen); cbn.
	inversion mlen; subst.
	1: rewrite (proj2 (leb_le _ _) (le_n _)); exact (eq_sym (eqb_refl _)).
	rewrite (proj2 (leb_gt _ _) (le_n_S _ _ H)); exact (eq_sym (proj2 (eqb_neq _ _) (lt_neq _ _ (le_n_S _ _ H)))).
Qed.

Lemma nfv_code_eq_nat : forall x, ~ bfv x code_eq_nat.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfv_code_and _ H).
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: exact (nfv_code_le _ H).
Qed.
Lemma nfb_code_eq_nat : forall k, ~ bfb k code_eq_nat.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfb_code_and _ H).
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: exact (nfb_code_le _ H).
Qed.

Opaque code_eq_nat.

Definition code_G_maurey a b := <{
	^^ <1>
		(^^<0> <1>)
		(^{incr_bound (incr_bound (incr_bound a O) O) O})
		(<0> (^^<0> <1>) (^{incr_bound (incr_bound (incr_bound b O) O) O})) }>.

Lemma code_G_maurey_O_wd : forall a b m,
	(over_bcontext beta)^*
		(code_G_maurey a b (code_nat O) (code_nat m)) a.
Proof using.
	intros a b m; unfold code_G_maurey.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	rewrite (incr_bound_comm (u:=a) (le_n O)), (incr_bound_comm (le_S _ _ (le_n O))), bsubstb_incr at 1.
	rewrite (incr_bound_comm (u:=b) (le_n O)), (incr_bound_comm (le_S _ _ (le_n O))), bsubstb_incr at 1.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	rewrite (incr_bound_comm (u:=a) (le_n O)), bsubstb_incr at 1.
	rewrite (incr_bound_comm (u:=b) (le_n O)), bsubstb_incr at 1.
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l BCHole _) (beta_code_nat _ _ _)) _); cbn.
	exact (eq_ind _ _ (rt_step (bctx_step (Beta _ _))) _ bsubstb_incr).
Qed.
Lemma code_G_maurey_S_wd : forall a b n m, exists u,
	(over_bcontext beta)^* (code_G_maurey a b (code_nat (S n)) (code_nat m)) u /\
	(over_bcontext beta)^* (code_G_maurey b a (code_nat m) (code_nat n)) u.
Proof using.
	intros a b n m; unfold code_G_maurey;
	  exists <{ {code_nat m}
	               (^(^<0> <1>))
	               (^{incr_bound b 0})
	               {code_nat_funarg n <{ ^(^<0> <1>) }> <{ ^{incr_bound a 0} }>} }>; split.
	1:{ refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	    rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	    rewrite (incr_bound_comm (u:=a) (le_n O)), (incr_bound_comm (le_S _ _ (le_n O))), bsubstb_incr at 1.
	    rewrite (incr_bound_comm (u:=b) (le_n O)), (incr_bound_comm (le_S _ _ (le_n O))), bsubstb_incr at 1.
	    refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	    rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	    rewrite (incr_bound_comm (u:=a) (le_n O)), bsubstb_incr at 1.
	    rewrite (incr_bound_comm (u:=b) (le_n O)), bsubstb_incr at 1.
	    refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l BCHole _) (beta_code_nat _ _ _)) _); cbn.
	    refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	    rewrite incr_code_nat_funarg; cbn; rewrite <-(incr_bound_comm (le_n _)).
	    refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	    rewrite bsubstb_code_nat_funarg; cbn.
	    rewrite (incr_bound_comm (le_n _)), bsubstb_incr.
	    exact rt_refl. }
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)).
	rewrite (incr_bound_comm (u:=a) (le_n O)), (incr_bound_comm (le_S _ _ (le_n O))), bsubstb_incr at 1.
	rewrite (incr_bound_comm (u:=b) (le_n O)), (incr_bound_comm (le_S _ _ (le_n O))), bsubstb_incr at 1.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite !(incr_nfb _ _ (fun _ _ => nfb_code_nat _ _)), (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_nat _ _)).
	rewrite (incr_bound_comm (u:=a) (le_n O)), bsubstb_incr at 1.
	rewrite (incr_bound_comm (u:=b) (le_n O)), bsubstb_incr at 1.
	refine (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) _); cbn.
	exact (beta_code_nat _ _ _).
Qed.

Lemma nfv_code_G_maurey_iff : forall a b x, bfv x (code_G_maurey a b) <-> bfv x a \/ bfv x b.
Proof using.
	intros a b x; split.
	- intros H.
	  inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H; [left|right].
	  1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	  1,3: inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	  1,2: inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  1,2: inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  1,2: inversion H as [|u v H' equ|u v H' equ|]; inversion H'.
	  1,2: inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  1,2: rewrite !bfv_incr_iff in H; exact H.
	- intros [H|H].
	  1: refine (BFV_Abs (BFV_Abs (BFV_App_l (BFV_App_r (BFV_Abs _))))).
	  2: refine (BFV_Abs (BFV_Abs (BFV_App_r (BFV_App_r (BFV_Abs _))))).
	  1,2: rewrite !bfv_incr_iff; exact H.
Qed.
Lemma nfb_code_G_maurey_iff : forall a b k, bfb k (code_G_maurey a b) <-> bfb k a \/ bfb k b.
Proof using.
	intros a b k; split.
	- intros H.
	  inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H; [left|right].
	  1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	  1,3: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	  1,2: inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  1,2: inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; inversion H'.
	  1,2: inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  1,2: rewrite <-(bfb_incr_iff _ _ O), <-(bfb_incr_iff _ _ O), <-(bfb_incr_iff _ _ O); exact H.
	- intros [H|H].
	  1: refine (BFB_Abs (BFB_Abs (BFB_App_l (BFB_App_r (BFB_Abs _))))).
	  2: refine (BFB_Abs (BFB_Abs (BFB_App_r (BFB_App_r (BFB_Abs _))))).
	  1,2: rewrite (bfb_incr_iff (S (S k)) _ O), (bfb_incr_iff (S k) _ O), (bfb_incr_iff k _ O); exact H.
Qed.

Opaque code_G_maurey.

Lemma G_maurey_legt : forall m n,
	(over_bcontext beta)^* (code_G_maurey code_true code_false (code_nat m) (code_nat n)) (code_bool (m <=? n)) /\
	(over_bcontext beta)^* (code_G_maurey code_false code_true (code_nat m) (code_nat n)) (code_bool (n <? m)).
Proof using.
	intros m n; split; generalize dependent n; induction m as [|m IHm]; intros n.
	1,3: exact (code_G_maurey_O_wd _ _ _).
	1: destruct (code_G_maurey_S_wd code_true code_false m n) as [u [Hu1 Hu2]].
	2: destruct (code_G_maurey_S_wd code_false code_true m n) as [u [Hu1 Hu2]].
	1,2: refine (rt_trans Hu1 _).
	1,2: match type of Hu2 with clos_refl_trans _ ?u0 _ =>
	  assert (tmp : forall v2, (over_bcontext beta)^* u0 v2 ->
	                RewriteSystem.normal_form (over_bcontext beta) v2 -> (over_bcontext beta)^* u v2) end.
	1,3: intros v2 H1 H2.
	1,2: destruct (confluence_beta _ _ v2 Hu2 H1) as [w [Hw1 Hw2]].
	1,2: rewrite or_comm, <-clos_rt_iff_eq_clos_t in Hw1.
	1,2: destruct Hw2 as [f|<-]; [|exact Hw1].
	1,2: apply clos_trans_t1n in f; destruct f; contradiction (H2 _ H).
	1,2: refine (tmp _ _ (normal_code_bool _)); clear tmp Hu1 Hu2 u.
	1,2: destruct n as [|n].
	1,3: exact (code_G_maurey_O_wd _ _ _).
	1: destruct (code_G_maurey_S_wd code_false code_true n m) as [u [Hu1 Hu2]].
	2: destruct (code_G_maurey_S_wd code_true code_false n m) as [u [Hu1 Hu2]].
	1,2: refine (rt_trans Hu1 _).
	1,2: match type of Hu2 with clos_refl_trans _ ?u0 _ =>
	  assert (tmp : forall v2, (over_bcontext beta)^* u0 v2 ->
	                RewriteSystem.normal_form (over_bcontext beta) v2 -> (over_bcontext beta)^* u v2) end.
	1,3: intros v2 H1 H2.
	1,2: destruct (confluence_beta _ _ v2 Hu2 H1) as [w [Hw1 Hw2]].
	1,2: rewrite or_comm, <-clos_rt_iff_eq_clos_t in Hw1.
	1,2: destruct Hw2 as [f|<-]; [|exact Hw1].
	1,2: apply clos_trans_t1n in f; destruct f; contradiction (H2 _ H).
	1,2: refine (tmp _ _ (normal_code_bool _)); clear tmp Hu1 Hu2 u.
	1,2: exact (IHm _).
Qed.

Definition Theta := <{ (^^<0> (<1> <1> <0>)) (^^<0> (<1> <1> <0>)) }>.

Lemma Theta_wd : forall f, (over_bcontext beta)^* (Theta f) (f (Theta f)).
Proof using.
	intros f; unfold Theta.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	refine (rt_step (bctx_step (Beta _ _))).
Qed.

Lemma nfv_Theta : forall x, ~ bfv x Theta.
Proof using.
	intros x H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1,2: inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	1,2: inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; inversion H'.
Qed.
Lemma nfb_Theta : forall k, ~ bfb k Theta.
Proof using.
	intros k H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1,2: inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	1,2: inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; inversion H'.
Qed.

Fixpoint code_list_aux l := match l with
	| [] => <{ <0> }>
	| hd :: tl => <{ <1> {incr_bound (incr_bound hd O) O} {code_list_aux tl} }>
end.
Definition code_list l := <{ ^^ {code_list_aux l} }>.

Fixpoint code_list_funarg l f x := match l with
	| [] => x
	| hd :: tl => <{ {f} {hd} {code_list_funarg tl f x} }>
end.

Lemma code_list_funarg_app : forall l1 l2 f x, code_list_funarg (l1 ++ l2) f x = code_list_funarg l1 f (code_list_funarg l2 f x).
Proof using.
	intros l1 l2 f x; induction l1 as [|hd1 l1 IH]; [exact eq_refl|exact (f_equal _ IH)].
Qed.

Lemma code_list_funarg_ctx_r : forall {R} l f x1 x2, over_bcontext R x1 x2 -> over_bcontext R (code_list_funarg l f x1) (code_list_funarg l f x2).
Proof using.
	intros R l f x1 x2 Hx; induction l as [|hd l IH]; [exact Hx|exact (bctx_app_r IH)].
Qed.
Lemma code_list_funarg_ctxstar_r : forall {R} l f x1 x2, (over_bcontext R)^* x1 x2 -> (over_bcontext R)^* (code_list_funarg l f x1) (code_list_funarg l f x2).
Proof using.
	intros R l f x1 x2 H; induction H as [x1 x2 H|x|x1 x2 x3 _ IH1 _ IH2];
	  [exact (rt_step (code_list_funarg_ctx_r _ _ _ _ H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.
Lemma code_list_funarg_ctxstar_l : forall {R} l f1 f2 x,
	(over_bcontext R)^* f1 f2 -> (over_bcontext R)^* (code_list_funarg l f1 x) (code_list_funarg l f2 x).
Proof using.
	intros R l f1 f2 x Hf; induction l as [|hd l IH];
	  [exact rt_refl
	  |exact (rt_trans (clos_rt_over_bcontext_ctx (BCApp_l (BCApp_l BCHole _) _) Hf) (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) IH))].
Qed.

Lemma incr_code_list : forall l k, incr_bound (code_list_aux l) (S (S k)) = code_list_aux (map (fun u => incr_bound u k) l).
Proof using.
	intros l k; induction l as [|hd tl IH]; [exact eq_refl|cbn].
	refine (f_equal2 (fun a b => BApp (BApp _ a) b) _ IH).
	rewrite (incr_bound_comm (le_0_n k)), (incr_bound_comm (le_0_n (S k))); exact eq_refl.
Qed.
Lemma bsubstb_code_list_gt : forall l k v,
	bsubstb (code_list_aux l) (S (S k)) (incr_bound (incr_bound v O) O) = code_list_aux (map (fun u => bsubstb u k v) l).
Proof using.
	intros l k v; induction l as [|hd tl IH]; [exact eq_refl|cbn].
	refine (f_equal2 (fun a b => BApp (BApp _ a) b) _ IH).
	rewrite !(incr_bsubstb_ge (le_0_n _)); exact eq_refl.
Qed.

Lemma code_list_aux_eq : forall l,
	code_list_aux l = code_list_funarg (map (fun u => incr_bound (incr_bound u O) O) l) (BBound (S O)) (BBound O).
Proof using.
	intros l.
	induction l as [|hd tl IH]; [exact eq_refl|exact (f_equal _ IH)].
Qed.
Lemma code_list_eq : forall l, code_list l = BAbs (BAbs (code_list_aux l)).
Proof using.
	intros l; exact eq_refl.
Qed.

Lemma bsubstb_code_list_funarg : forall l f x k v, 
	bsubstb (code_list_funarg l f x) k v = code_list_funarg (map (fun u => bsubstb u k v) l) (bsubstb f k v) (bsubstb x k v).
Proof using.
	intros l f x k v.
	induction l as [|hd tl IHn]; [exact eq_refl|exact (f_equal _ IHn)].
Qed.
Lemma incr_code_list_funarg : forall l f x k,
	incr_bound (code_list_funarg l f x) k = code_list_funarg (map (fun u => incr_bound u k) l) (incr_bound f k) (incr_bound x k).
Proof using.
	intros l f x k.
	induction l as [|hd tl IHn]; [exact eq_refl|exact (f_equal _ IHn)].
Qed.

Lemma beta_code_list : forall l f x, (over_bcontext beta)^* (code_list l f x) (code_list_funarg l f x).
Proof using.
	intros l f x; rewrite code_list_eq, code_list_aux_eq.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn; rewrite bsubstb_code_list_funarg; cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _).
	rewrite bsubstb_code_list_funarg, bsubstb_incr; cbn.
	rewrite !map_map; refine (eq_ind _ _ rt_refl _ _); f_equal.
	induction l as [|hd tl IH]; [exact eq_refl|cbn; rewrite IH; f_equal].
	rewrite (incr_bound_comm (le_n _)), !bsubstb_incr; exact eq_refl.
Qed.

Lemma bfv_code_list_iff : forall l x, bfv x (code_list l) <-> exists u, In u l /\ bfv x u.
Proof using.
	intros l x; split.
	- intros H.
	  inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	  induction l as [|hd tl IH].
	  1: inversion H.
	  inversion H; [subst; clear H; rename H1 into H|specialize (IH H1) as [w [Hw1 Hw2]]; exists w; split; [right; exact Hw1|exact Hw2]].
	  inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	  rewrite !bfv_incr_iff in H.
	  exists hd; split; [left; exact eq_refl|exact H].
	- intros [u [Hu1 Hu2]].
	  refine (BFV_Abs (BFV_Abs _)).
	  induction l as [|hd tl IH].
	  1: inversion Hu1.
	  destruct Hu1 as [<-|Hu1]; [refine (BFV_App_l (BFV_App_r _))|exact (BFV_App_r (IH Hu1))].
	  rewrite !bfv_incr_iff; exact Hu2.
Qed.
Lemma bfb_code_list_iff : forall l k, bfb k (code_list l) <-> exists u, In u l /\ bfb k u.
Proof using.
	intros l k; split.
	- intros H.
	  inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	  induction l as [|hd tl IH].
	  1: inversion H.
	  inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	  2: specialize (IH H) as [u [Hu1 Hu2]]; exists u; split; [right; exact Hu1|exact Hu2].
	  inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	  rewrite (bfb_incr_iff (S k) _ O), (bfb_incr_iff k _ O) in H.
	  exists hd; split; [left; exact eq_refl|exact H].
	- intros [u [Hu1 Hu2]].
	  refine (BFB_Abs (BFB_Abs _)).
	  induction l as [|hd tl IH].
	  1: inversion Hu1.
	  destruct Hu1 as [<-|Hu1].
	  2: exact (BFB_App_r (IH Hu1)).
	  refine (BFB_App_l (BFB_App_r _)); rewrite (bfb_incr_iff (S k) _ O), (bfb_incr_iff k _ O); exact Hu2.
Qed.

Opaque code_list.

Definition code_cons := <{ ^^^^<1> <3> (<2> <1> <0>) }>.

Lemma code_cons_wd : forall hd tl, (over_bcontext beta)^* (code_cons hd (code_list tl)) (code_list (hd :: tl)).
Proof using.
	intros hd tl.
	rewrite !code_list_eq; cbn.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (incr_bound_comm (u:=hd) (le_n _)), (incr_bound_comm (le_0_n _)), bsubstb_incr, <-(incr_bound_comm (le_n O)).
	refine (clos_rt_over_bcontext_ctx (BCAbs (BCAbs (BCApp_r _ BCHole))) _).
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite !incr_code_list, map_map.
	refine (eq_ind _ _ (rt_step (bctx_step (Beta _ _))) _ _); cbn.
	clear hd; induction tl as [|hd tl IH].
	1: exact eq_refl.
	cbn; rewrite (incr_bound_comm (le_n _)), !bsubstb_incr; f_equal; exact IH.
Qed.

Lemma normal_code_cons : forall u, ~ over_bcontext beta code_cons u.
Proof using.
	intros u H.
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'|u' v' w' H'|u' w' v' H'|]; [inversion H'| |]; subst; clear H; rename v' into u, H' into H.
	2: inversion H as [u' v' H'|u' v' w' H'|u' w' v' H'|]; [inversion H'| |]; subst; clear H; rename v' into u, H' into H.
	3: inversion H as [u' v' H'| | |]; inversion H'.
	1,2: inversion H as [u' v' H'|u' v' w' H'|u' w' v' H'|]; [inversion H'| |]; subst; clear H; rename v' into u, H' into H.
	1,2,3,4: inversion H as [u' v' H'| | |]; inversion H'.
Qed.

Lemma nfv_code_cons : forall x, ~ bfv x code_cons.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	2: inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; inversion H'.
Qed.
Lemma nfb_code_cons : forall k, ~ bfb k code_cons.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; inversion H'.
Qed.

Opaque code_cons.

Definition code_hd := <{ ^<0> (^^<1>) {code_list []} }>.

Lemma code_hd_wd : forall l, (over_bcontext beta)^* (code_hd (code_list l)) (match l with hd :: _ => hd | [] => code_list [] end).
Proof using.
	intros l; unfold code_hd.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	refine (rt_trans (beta_code_list _ _ _) _).
	rewrite code_list_eq; cbn.
	destruct l as [|hd tl]; cbn.
	1: exact rt_refl.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite bsubstb_incr; exact rt_refl.
Qed.

Lemma normal_code_hd : forall u, ~ over_bcontext beta code_hd u.
Proof using.
	intros u H.
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'|u' v' w' H'|u' w' v' H'|]; [inversion H'| |]; subst; clear H; rename v' into u, H' into H.
	1: inversion H as [u' v' H'|u' v' w' H'|u' w' v' H'|]; [inversion H'| |]; subst; clear H; rename v' into u, H' into H.
	1: inversion H as [u' v' H'| | |]; inversion H'.
	1: inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	1: inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	1: inversion H as [u' v' H'| | |]; inversion H'.
	rewrite code_list_eq in H; cbn in H.
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |u' v' H' equ]; [inversion H'|subst; clear H; rename v' into u, H' into H].
	inversion H as [u' v' H'| | |]; inversion H'.
Qed.

Lemma nfv_code_hd : forall x, ~ bfv x code_hd.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	1: inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	1: inversion H as [| | |u H' equ]; subst; inversion H'.
	apply bfv_code_list_iff in H; destruct H as [u [[] Hu]].
Qed.
Lemma nfb_code_hd : forall k, ~ bfb k code_hd.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	1: inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	1: inversion H as [| | |k' u H' equ]; subst; inversion H'.
	apply bfb_code_list_iff in H; destruct H as [u [[] Hu]].
Qed.

Opaque code_hd.

Definition code_map := <{ ^^<0> (^^{code_cons} (<3> <1>) <0>) {code_list []} }>.

Lemma code_map_wd : forall f l, (over_bcontext beta)^* (code_map f (code_list l)) (code_list (map (fun u => BApp f u) l)).
Proof using.
	intros f l; unfold code_map.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (bsubstb_nfb (code_list []) _ _ ltac:(intros k _ Hk; rewrite bfb_code_list_iff in Hk; destruct Hk as [? [[] _]])).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (bsubstb_nfb (code_list []) _ _ ltac:(intros k _ Hk; rewrite bfb_code_list_iff in Hk; destruct Hk as [? [[] _]])).
	rewrite (incr_bound_comm (u:=f) (le_n _)), (incr_bound_comm (le_S _ _ (le_n _))), bsubstb_incr.
	refine (rt_trans (beta_code_list _ _ _) _).
	induction l as [|hd tl IH]; cbn.
	1: exact rt_refl.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (incr_bound_comm (le_n _)), bsubstb_incr, <-(incr_bound_comm (le_n _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite !bsubstb_incr.
	refine (rt_trans _ (code_cons_wd _ _)).
	exact (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) IH).
Qed.

Lemma nfv_code_map : forall x, ~ bfv x code_map.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	2: rewrite bfv_code_list_iff in H; destruct H as [u [[] Hu]].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfv_code_cons _ H).
	inversion H as [|u v H' equ|u v H' equ|]; subst; inversion H'.
Qed.
Lemma nfb_code_map : forall k, ~ bfb k code_map.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	2: rewrite bfb_code_list_iff in H; destruct H as [u [[] Hu]].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfb_code_cons _ H).
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; inversion H'.
Qed.

Opaque code_map.

Definition code_tl :=
	<{ ^{code_pi2}
		(<0>
			(^^{code_pair_imm <{ {code_cons} <1> ({code_pi1} <0>)}> (code_pi1 (BBound 0))})
			{code_pair_imm (code_list []) (code_list [])}) }>.

Lemma code_tl_wd : forall l, (over_bcontext beta)^* (code_tl (code_list l)) (code_list (tl l)).
Proof using.
	intros l; unfold code_tl.
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite !bsubstb_code_pair_imm; cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi1 _)).
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi2 _)).
	rewrite (bsubstb_nfb (code_list []) _ _ ltac:(intros k _ Hk; rewrite bfb_code_list_iff in Hk; destruct Hk as [? [[] _]])).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) (beta_code_list _ _ _)) _); cbn.
	destruct l as [|hd tl]; cbn.
	1: exact (code_pi2_wd _ _).
	refine (rt_trans (rt_step (bctx_app_r (bctx_app_l (bctx_step (Beta _ _))))) _); cbn.
	rewrite bsubstb_code_pair_imm; cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi1 _)).
	refine (rt_trans (rt_step (bctx_app_r (bctx_step (Beta _ _)))) _); cbn.
	rewrite bsubstb_code_pair_imm.
	refine (rt_trans (code_pi2_wd _ _) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_pi1 _)).
	clear hd; induction tl as [|hd tl IH]; cbn.
	1: exact (code_pi1_wd _ _).
	refine (rt_trans (rt_step (bctx_app_r (bctx_app_l (bctx_step (Beta _ _))))) _); cbn.
	rewrite bsubstb_code_pair_imm; cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (bsubstb_nfb code_pi1 1 (incr_bound hd 0) (fun _ _ => nfb_code_pi1 _)).
	refine (rt_trans (rt_step (bctx_app_r (bctx_step (Beta _ _)))) _); cbn.
	rewrite bsubstb_code_pair_imm.
	refine (rt_trans (code_pi1_wd _ _) _); cbn.
	rewrite !bsubstb_incr.
	rewrite (bsubstb_nfb code_cons _ _ (fun _ _ => nfb_code_cons _)).
	rewrite (bsubstb_nfb code_pi1 _ _ (fun _ _ => nfb_code_pi1 _)).
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) IH) _); cbn.
	exact (code_cons_wd _ _).
Qed.

Lemma nfv_code_tl : forall x, ~ bfv x code_tl.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfv_code_pi2 _ H).
	inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	2: rewrite bfv_code_pair_imm_iff in H; destruct H as [H|H].
	2,3: rewrite bfv_code_list_iff in H; destruct H as [u [[] H]].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	rewrite bfv_code_pair_imm_iff in H; destruct H as [H|H].
	1: inversion H as [|u v H' equ|u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1: exact (nfv_code_cons _ H).
	1,2: inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: exact (nfv_code_pi1 _ H).
Qed.
Lemma nfb_code_tl : forall k, ~ bfb k code_tl.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: exact (nfb_code_pi2 _ H).
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	2: rewrite bfb_code_pair_imm_iff in H; destruct H as [H|H].
	2,3: rewrite bfb_code_list_iff in H; destruct H as [u [[] Hu]].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	rewrite bfb_code_pair_imm_iff in H; destruct H as [H|H].
	1: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; clear H; rename H' into H.
	1: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1: exact (nfb_code_cons _ H).
	1,2: inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	1,2: exact (nfb_code_pi1 _ H).
Qed.

Opaque code_tl.

Definition code_app :=
	<{ ^^<1> {code_cons} <0> }>.

Lemma code_app_wd : forall l1 l2, (over_bcontext beta)^* (code_app (code_list l1) (code_list l2)) (code_list (l1 ++ l2)).
Proof using.
	intros l1 l2; unfold code_app.
	refine (rt_trans (rt_step (bctx_app_l (bctx_step (Beta _ _)))) _); cbn.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	refine (rt_trans (rt_step (bctx_step (Beta _ _))) _); cbn.
	rewrite bsubstb_incr.
	rewrite (bsubstb_nfb _ _ _ (fun _ _ => nfb_code_cons _)).
	refine (rt_trans (beta_code_list _ _ _) _).
	induction l1 as [|hd tl IH]; cbn.
	1: exact rt_refl.
	refine (rt_trans (clos_rt_over_bcontext_ctx (BCApp_r _ BCHole) IH) _); cbn.
	exact (code_cons_wd _ _).
Qed.

Lemma nfv_code_app : forall x, ~ bfv x code_app.
Proof using.
	intros x H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|u v H' equ|u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|u v H' equ|u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	exact (nfv_code_cons _ H).
Qed.
Lemma nfb_code_app : forall k, ~ bfb k code_app.
Proof using.
	intros k H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [| | |k' u H' equ]; subst; clear H; rename H' into H.
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [clear H; rename H' into H|inversion H'].
	inversion H as [|k' u v H' equ|k' u v H' equ|]; subst; [inversion H'|clear H; rename H' into H].
	exact (nfb_code_cons _ H).
Qed.

Opaque code_app.

End UntypedVals.
