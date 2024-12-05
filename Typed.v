Require Import Parametrization. Require Assoc FiniteSet. Require RewriteSystem.
Require Import Relations.
Require Import Untyped UntypedVals UntypedNorm.

Module Type SimpleType.
Parameter (B : Type).
Parameter B_dec : forall b1 b2 : B, { b1 = b2 } + { b1 <> b2 }.
End SimpleType.

Declare Custom Entry types.

Module TypedLambda (T0 : SimpleType) (UntypedVals0 : UntypedValsT).
Module Import UntypedVals := UntypedVals0.
Module Import UntypedL := UntypedVals.UntypedL.
Module Export Vars := UntypedL.Vars.
Module Export T := T0.
Import UntypedBNotation.

Inductive type :=
	| TSimple : B -> type
	| TArrow : type -> type -> type.

Module Import TypeNotations.
Notation ";{  F  };" := F (F custom types).
Notation "{ F }" := F (in custom types at level 0, F constr).
Notation "( F )" := F (in custom types at level 0, F custom types at level 1).
Notation "F => G" := (TArrow F G) (in custom types at level 1, right associativity, F custom types, G custom types).
End TypeNotations.

Definition vctx := VarMap.t type.
Definition ctx := list type.

Inductive typable : vctx -> ctx -> bterm -> type -> Prop :=
	| TPVar : forall Gv G x {F}, VarMap.find_opt Gv x = Some F -> typable Gv G (BVar x) F
	| TPBound : forall Gv G n {F}, nth_error G n = Some F -> typable Gv G (BBound n) F
	| TPApp : forall {Gv G u v F1 F2}, typable Gv G u ;{{F1} => {F2}}; -> typable Gv G v F1 -> typable Gv G (u v) F2
	| TPAbs : forall {Gv G u F1 F2}, typable Gv (F1 :: G) u F2 -> typable Gv G (BAbs u) ;{{F1} => {F2}};.

Module Import TypableNotations.
Notation "Gv  ;;  G  |-  u  :  F" := (typable Gv G u F) (at level 20, u custom bterms, F custom types, no associativity).
End TypableNotations.

Lemma typ_var_inv : forall Gv G x F, Gv ;; G |- {BVar x} : {F} -> VarMap.find_opt Gv x = Some F.
Proof using.
	intros Gv G x F H; inversion H; assumption.
Qed.
Lemma typ_bound_inv : forall Gv G n F, Gv ;; G |- {BBound n} : {F} -> nth_error G n = Some F.
Proof using.
	intros Gv G x F H; inversion H; assumption.
Qed.
Lemma typ_app_inv : forall Gv G u v F, Gv ;; G |- {u} {v} : {F} -> exists F1, Gv ;; G |- {u} : {F1} => {F} /\ Gv ;; G |- {v} : {F1}.
Proof using.
	intros Gv G u v F H; inversion H as [| |Gv' G' u' v' F1 F2 H1 H2|]; subst; exists F1; split; assumption.
Qed.
Lemma typ_abs_inv : forall Gv G u F, Gv ;; G |- {BAbs u} : {F} -> exists F1 F2, F = TArrow F1 F2 /\ Gv ;; (F1 :: G) |- {u} : {F2}.
Proof using.
	intros Gv G u F H; inversion H as [| | |Gv' G' u' F1 F2 H']; subst; exists F1, F2; split; [exact eq_refl|exact H'].
Qed.
Lemma typ_not_arrow_l : forall F1 F2, F1 <> TArrow F1 F2.
Proof using.
	intros F1; induction F1 as [b1|F11 IH F12 _]; intros F2 eq; [discriminate eq|injection eq as eq _; exact (IH _ eq)].
Qed.
Lemma typ_not_arrow_r : forall F1 F2, F2 <> TArrow F1 F2.
Proof using.
	intros F1 F2; generalize dependent F1; induction F2 as [b1|F21 _ F22 IH]; intros F1 eq; [discriminate eq|injection eq as _ eq; exact (IH _ eq)].
Qed.

Goal forall Gv F, Gv ;; [] |- ^<0> : {F} => {F}.
Proof using.
	intros Gv F; refine (TPAbs (TPBound _ [_] O eq_refl)).
Qed.
Goal forall Gv G F, ~ (Gv ;; G |- <0> <0> : {F}).
Proof using.
	intros Gv G F H.
	inversion H as [| |Gv' G' u v F1 F2 H1 H2|]; clear H; subst.
	apply typ_bound_inv in H1, H2.
	rewrite H2 in H1; injection H1 as eq; exact (typ_not_arrow_l _ _ eq).
Qed.

Lemma typable_incr : forall Gv G1 F1 G2 u F, Gv ;; (G1 ++ G2) |- {u} : {F} <-> Gv ;; (G1 ++ F1 :: G2) |- {incr_bound u (length G1)} : {F}.
Proof using.
	intros Gv G1 F0 G2 u F; split; intros H.
	- remember (G1 ++ G2) as G0 eqn:eqG; generalize dependent G1; induction H as [|Gv' G0 n F H|Gv' G0 u v F1 F2 H1 IH1 H2 IH2|Gv' G0 u F1 F2 H IH]; intros G1 ->.
	  + refine (TPVar _ _ _ H).
	  + refine (TPBound _ _ _ _); rewrite <-H; clear F H; generalize dependent G1; induction n as [|n IHn]; intros [|F1 G1].
	    1-3: exact eq_refl.
	    specialize (IHn G1); cbn; destruct (length G1 <=? n); exact IHn.
	  + exact (TPApp (IH1 _ eq_refl) (IH2 _ eq_refl)).
	  + exact (TPAbs (IH (_ :: _) eq_refl)).
	- generalize dependent F; generalize dependent G1; induction u as [x|n|u IHu v IHv|u IH]; intros G1 F H.
	  + exact (TPVar _ _ _ (typ_var_inv _ _ _ _ H)).
	  + apply typ_bound_inv in H; refine (TPBound _ _ _ (eq_trans _ H)); cbn; clear F H.
	    generalize dependent n; induction G1 as [|F1 G1 IHG]; intros n.
	    1: exact eq_refl.
	    destruct n as [|n]; [exact eq_refl|specialize (IHG n); cbn; destruct (length G1 <=? n); exact IHG].
	  + cbn in H; apply typ_app_inv in H; destruct H as [F' [Hu Hv]]; exact (TPApp (IHu _ _ Hu) (IHv _ _ Hv)).
	  + cbn in H; apply typ_abs_inv in H; destruct H as [F1 [F2 [-> H]]]; exact (TPAbs (IH (_ :: _) _ H)).
Qed.
Lemma typable_subst : forall Gv G1 F1 G2 u v F, Gv ;; (G1 ++ F1 :: G2) |- {u} : {F} -> Gv ;; (G1 ++ G2) |- {v} : {F1} -> Gv ;; (G1 ++ G2) |- {bsubstb u (length G1) v} : {F}.
Proof using.
	intros Gv G1 F0 G2 u v F Hu Hv.
	remember (G1 ++ F0 :: G2) as G0 eqn:eqG; generalize dependent G1; generalize dependent v;
	  induction Hu as [Gv' G0 x F H|Gv' G0 n F H|Gv' G0 u1 u2 F1 F2 H1 IH1 H2 IH2|Gv' G0 u F1 F2 H IH]; intros v G1 -> Hv.
	- unfold bsubstb; exact (TPVar _ _ _ H).
	- unfold bsubstb.
	  destruct (lt_ge_cases n (length G1)) as [nltG1|G1len].
	  1: rewrite (proj2 (ltb_lt _ _) nltG1); refine (TPBound _ _ _ _); clear - H nltG1.
	  1: generalize dependent G1; induction n as [|n IHn]; intros [|F1 G1] H1 H2;
	       [inversion H2|exact H1|inversion H2|exact (IHn _ H1 (le_S_n _ _ H2))].
	  rewrite (proj2 (ltb_ge _ _) G1len).
	  apply le_is_ex_add in G1len; destruct G1len as [n' ->]; rename n' into n.
	  assert (H' : nth_error (F0 :: G2) n = Some F)
	    by (clear - H; rewrite add_comm in H; induction G1 as [|F1 G1 IH]; [exact H|exact (IH H)]).
	  clear H; rename H' into H.
	  destruct n as [|n].
	  1: rewrite eqb_refl; injection H as ->; exact Hv.
	  rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (add_le_mono (S O) _ _ _ (le_n_S _ _ (le_0_n _)) (le_n _)))); cbn.
	  refine (TPBound _ _ _ _); rewrite add_comm.
	  clear - H; induction G1 as [|F1 G1 IH1]; [exact H|exact IH1].
	- exact (TPApp (IH1 _ _ eq_refl Hv) (IH2 _ _ eq_refl Hv)).
	- exact (TPAbs (IH _ (_ :: _) eq_refl (proj1 (typable_incr _ [] _ _ _ _) Hv))).
Qed.

Definition type_nat (F : type) := ;{ ({F} => {F}) => {F} => {F} };.

Lemma type_nat_wd : forall Gv G n F, Gv ;; G |- {code_nat n} : {type_nat F}.
Proof using.
	intros Gv G n F; rewrite code_nat_eq; refine (TPAbs (TPAbs _)).
	induction n as [|n IHn]; [refine (TPBound _ (_ :: _) O eq_refl)|refine (TPApp (TPBound _ (_ :: _ :: _) (S O) eq_refl) IHn)].
Qed.

Definition type_S (F : type) := TArrow (type_nat F) (type_nat F).

Lemma type_S_wd : forall Gv G F, Gv ;; G |- {code_S} : {type_S F}.
Proof using.
	intros Gv G F; refine (TPAbs (TPAbs (TPAbs (TPApp (TPBound _ (_ :: _ :: _) (S O) eq_refl) _)))).
	exact (TPApp (TPApp (TPBound _ (_ :: _ :: _ :: _) (S (S O)) eq_refl) (TPBound _ (_ :: _ :: _) (S O) eq_refl)) (TPBound _ (_ :: _) O eq_refl)).
Qed.

Definition type_add (F : type) := TArrow (type_nat F) (TArrow (type_nat F) (type_nat F)).

Lemma type_add_wd : forall Gv G F, Gv ;; G |- {code_add} : {type_add F}.
Proof using.
	intros Gv G F; repeat eapply TPAbs; repeat eapply TPApp; apply TPBound; exact eq_refl.
Qed.

Definition type_mul (F : type) := TArrow (type_nat F) (TArrow (type_nat F) (type_nat F)).

Lemma type_mul_wd : forall Gv G F, Gv ;; G |- {code_mul} : {type_mul F}.
Proof using.
	intros Gv G F; repeat eapply TPAbs; repeat eapply TPApp; apply TPBound; exact eq_refl.
Qed.

Definition type_exp (F : type) := TArrow (type_nat (TArrow F F)) (TArrow (type_nat F) (type_nat F)).

Lemma type_exp_wd : forall Gv G F, Gv ;; G |- {code_exp} : {type_exp F}.
Proof using.
	intros Gv G F; repeat eapply TPAbs; repeat eapply TPApp; apply TPBound; exact eq_refl.
Qed.
Lemma not_type_exp : forall Gv G F, ~ Gv ;; G |- {code_exp} : {type_nat F} => {type_nat F} => {type_nat F}.
Proof using.
	intros Gv G F H.
	repeat (apply typ_abs_inv in H; destruct H as [F1 [F2 [[=<- <-] H]]]).
	apply typ_app_inv in H; destruct H as [F1 [H1 H2]].
	apply typ_bound_inv in H1; injection H1 as _ H _; clear G F1 H2.
	exact (typ_not_arrow_l _ _ H).
Qed.

Definition type_pair (F1 F2 F : type) := ;{ ({F1} => {F2} => {F}) => {F} };.
Definition type_pi1 (F1 F2 : type) := TArrow (type_pair F1 F2 F1) F1.
Definition type_pi2 (F1 F2 : type) := TArrow (type_pair F1 F2 F2) F2.

Lemma type_pair_wd : forall Gv G u v F1 F2 F, Gv ;; G |- {u} : {F1} -> Gv ;; G |- {v} : {F2} -> Gv ;; G |- {code_pair_imm u v} : {type_pair F1 F2 F}.
Proof using.
	intros Gv G u v F1 F2 F Hu Hv; repeat eapply TPAbs; repeat eapply TPApp; [apply TPBound; exact eq_refl| |].
	1,2: apply (typable_incr _ []); assumption.
Qed.
Lemma type_pi1_wd : forall Gv G F1 F2, Gv ;; G |- {code_pi1} : {type_pi1 F1 F2}.
Proof using.
	intros Gv G F1 F2; repeat eapply TPAbs; repeat eapply TPApp; [apply TPBound; exact eq_refl|].
	repeat eapply TPAbs; apply TPBound; exact eq_refl.
Qed.
Lemma type_pi2_wd : forall Gv G F1 F2, Gv ;; G |- {code_pi2} : {type_pi2 F1 F2}.
Proof using.
	intros Gv G F1 F2; repeat eapply TPAbs; repeat eapply TPApp; [apply TPBound; exact eq_refl|].
	repeat eapply TPAbs; apply TPBound; exact eq_refl.
Qed.

Definition type_bool (F : type) := ;{ {F} => {F} => {F} };.
Lemma type_true_wd : forall Gv G F, Gv ;; G |- {code_true} : {type_bool F}.
Proof using.
	intros Gv G F; repeat eapply TPAbs; apply TPBound; exact eq_refl.
Qed.
Lemma type_false_wd : forall Gv G F, Gv ;; G |- {code_false} : {type_bool F}.
Proof using.
	intros Gv G F; repeat eapply TPAbs; apply TPBound; exact eq_refl.
Qed.
Lemma type_bool_wd : forall Gv G b F, Gv ;; G |- {code_bool b} : {type_bool F}.
Proof using.
	unfold code_bool.
	intros Gv G [|] F; [exact (type_true_wd _ _ _)|exact (type_false_wd _ _ _)].
Qed.

Lemma type_pred_wd : forall Gv G F, Gv ;; G |- {code_pred} : {type_nat (type_pair (type_nat F) (type_nat F) (type_nat F))} => {type_nat F}.
Proof using.
	intros Gv G F; apply TPAbs; eapply TPApp; [exact (type_pi2_wd _ _ (type_nat F) _)|].
	eapply TPApp; [|exact (type_pair_wd _ _ _ _ _ _ (type_nat F) (type_nat_wd _ _ _ F) (type_nat_wd _ _ _ F))].
	eapply TPApp; [apply TPBound; exact eq_refl|].
	apply TPAbs.
	apply type_pair_wd.
	1: refine (TPApp (type_S_wd _ _ _) _).
	1,2: exact (TPApp (type_pi1_wd _ _ _ _) (TPBound _ (_ :: _) O eq_refl)).
Qed.

Definition type_G_maurey Fnf Fng Fnx Fa Fmf Fmg Fmx Fb Fm3 Fn4 :=
	;{(({Fnf} => ({Fnf} => {Fng}) => {Fng}) => ({Fnx} => {Fa}) => {Fm3} => {Fn4})
	  => (({Fmf} => ({Fmf} => {Fmg}) => {Fmg}) => ({Fmx} => {Fb}) => {Fm3})
	  => {Fn4}};.

Lemma type_G_maurey_wd : forall Gv G a b Fnf Fng Fnx Fa Fmf Fmg Fmx Fb Fm3 Fn4,
	Gv ;; G |- {a} : {Fa} -> Gv ;; G |- {b} : {Fb} -> Gv ;; G |- {code_G_maurey a b} : {type_G_maurey Fnf Fng Fnx Fa Fmf Fmg Fmx Fb Fm3 Fn4}.
Proof using.
	intros Gv G a b F1 F2 f3 F4 F5 F6 F7 F8 F9 F10 Ha Hb.
	refine (TPAbs (TPAbs (TPApp _ _))).
	1,2: refine (TPApp (TPApp (TPBound _ _ _ _) (TPAbs (TPAbs _))) (TPAbs _)); [exact eq_refl| |].
	1,3: refine (TPApp (TPBound _ (_ :: _) O eq_refl) (TPBound _ (_ :: _ :: _) (S O) eq_refl)).
	1,2: do 3 apply (typable_incr _ []); assumption.
Qed.

Lemma autored_beta : forall Gv G u v F, Gv ;; G |- {u} : {F} -> over_bcontext beta u v -> Gv ;; G |- {v} : {F}.
Proof using.
	intros Gv G u v F Hu Huv; generalize dependent F; generalize dependent G;
	  induction Huv as [u v H|u u' v Huv IH|u v v' Huv IH|u v H IH]; intros G F Hu.
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp (IH _ _ Hu) Hv).
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp Hu (IH _ _ Hv)).
	2: apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [-> Hu]]]; exact (TPAbs (IH _ _ Hu)).
	inversion H as [u1 u2 equ eqv]; subst u v; clear H; rename u1 into u, u2 into v.
	apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [[= -> ->] Hu]]]; exact (typable_subst _ [] _ _ _ _ _ Hu Hv).
Qed.

Lemma autored_eta : forall Gv G u v F, Gv ;; G |- {u} : {F} -> over_bcontext eta u v -> Gv ;; G |- {v} : {F}.
Proof using.
	intros Gv G u v F Hu Huv; generalize dependent F; generalize dependent G;
	  induction Huv as [u v H|u u' v Huv IH|u v v' Huv IH|u v H IH]; intros G F Hu.
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp (IH _ _ Hu) Hv).
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp Hu (IH _ _ Hv)).
	2: apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [-> Hu]]]; exact (TPAbs (IH _ _ Hu)).
	inversion H as [u' equ eqv]; subst u v; clear H; rename u' into u.
	apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [-> Hu]]].
	apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	apply typ_bound_inv in Hv; injection Hv as <-.
	exact (proj2 (typable_incr _ [] _ _ _ _) Hu).
Qed.

Lemma typable_is_bfv : forall Gv G u F, Gv ;; G |- {u} : {F} -> forall x, bfv x u -> VarMap.mem Gv x.
Proof using.
	intros Gv G u F H x; induction H as [Gv G y F H|Gv G n F H|Gv G u v F1 F2 H1 IH1 H2 IH2|Gv G u F1 F2 H IH].
	1: intros f; inversion f; refine (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H)).
	1: intros f; inversion f.
	1: intros f; inversion f; [apply IH1|apply IH2]; assumption.
	1: intros f; inversion f; apply IH; assumption.
Qed.
Lemma typable_is_bfb_lt : forall Gv G u F, Gv ;; G |- {u} : {F} -> forall n, bfb n u -> n < length G.
Proof using.
	intros Gv G u F H; induction H as [Gv G x F H|Gv G k F H|Gv G u v F1 F2 H1 IH1 H2 IH2|Gv G u F1 F2 H IH]; intros n Hn.
	1: inversion Hn.
	2: inversion Hn; subst; [exact (IH1 _ H3)|exact (IH2 _ H3)].
	2: inversion Hn; subst; refine (le_S_n _ _ (IH _ H2)).
	inversion Hn; subst; clear Hn.
	generalize dependent G; induction k as [|k IHk]; intros [|hd l] H.
	1,3: discriminate H.
	1: exact (le_n_S _ _ (le_0_n _)).
	exact (le_n_S _ _ (IHk _ H)).
Qed.

Section ReductibilityCandidates.

Implicit Types u v : bterm.

Definition SN : bterm -> Prop := RewriteSystem.strong_normalizable (over_bcontext (union _ beta eta)).
Fixpoint RED F : bterm -> Prop := match F with
	| TSimple b => SN
	| TArrow F1 F2 => fun u => forall v, RED F1 v -> RED F2 (BApp u v)
end.

Definition neutral u := match u with BAbs _ => False | _ => True end.

Definition CR1 (P : bterm -> Prop) : Prop := forall u, P u -> SN u.
Definition CR2 (P : bterm -> Prop) : Prop := forall u u', P u -> (over_bcontext (union _ beta eta)) u u' -> P u'.
Definition CR3 (P : bterm -> Prop) : Prop := forall u, neutral u -> (forall u', (over_bcontext (union _ beta eta)) u u' -> P u') -> P u.
Definition CR P := CR1 P /\ CR2 P /\ CR3 P.

Lemma SN_is_CR : CR SN.
Proof using.
	split; [exact (fun _ H => H)|split; [unfold CR2|unfold CR3]].
	- intros u u' H1 H2; inversion H1 as [H]; exact (H _ H2).
	- intros u Hu H; constructor.
	  intros u' Hu'; exact (H _ Hu').
Qed.

Lemma RED_is_CR : forall F, CR (RED F).
Proof using.
	unfold CR, CR1, CR2, CR3; intros F; induction F as [b|F1 [IH11 [IH12 IH13]] F2 [IH21 [IH22 IH23]]].
	1: exact SN_is_CR.
	cbn; split; [|split].
	- intros u Hu.
	  pose (v := BVar O).
	  assert (Hv : RED F1 v)
	    by (refine (IH13 v I _); intros v' Hv'; inversion Hv'; destruct H as [H|H]; inversion H).
	  specialize (IH21 _ (Hu _ Hv)); remember (BApp u v) as uv eqn:equv.
	  clear Hu Hv IH11 IH12 IH13 IH22 IH23.
	  generalize dependent u; induction IH21 as [uv H IH]; intros u ->; constructor.
	  intros u' Hu'; exact (IH (BApp u' v) (bctx_app_l Hu') _ eq_refl).
	- intros u u' H1 H2 v Hv.
	  exact (IH22 _ _ (H1 _ Hv) (bctx_app_l H2)).
	- intros u H1 H2 v Hv.
	  specialize (IH11 _ Hv); induction IH11 as [v Hvv' IHv].
	  refine (IH23 (BApp _ _) I _).
	  intros u' Hu'; inversion Hu' as [uv' u'' [H|H] eq1 eq2|u0 v1 v2 H eq1 eq2|u1 v' v2 H eq1 eq2|]; subst.
	  1: inversion H; subst u; contradiction H1.
	  1: inversion H.
	  1: exact (H2 _ H _ Hv).
	  exact (IHv _ H (IH12 _ _ Hv H)).
Qed.

Lemma RED_var : forall F x, RED F (BVar x).
Proof using.
	intros F x; pose (l := @nil bterm);
	  assert (Hl : forall v, In v l -> exists Fv, RED Fv v) by (intros ? []);
	  rewrite (eq_refl : BVar x = (fix inner l := match l with [] => BVar x | hd :: tl => BApp (inner tl) hd end) l);
	  generalize dependent l.
	induction F as [b|F1 IH1 F2 IH2]; intros l Hl.
	2: intros v Hv; refine (IH2 (v :: l) (fun v' Hv' => match Hv' with or_introl veq => _ | or_intror H => Hl _ H end)).
	2: subst v'; exists F1; exact Hv.
	cbn.
	assert (Hl2 := fun v Hv => match Hl v Hv with ex_intro _ _ H => proj1 (RED_is_CR _) _ H end); clear b Hl; rename Hl2 into Hl.
	remember (length l) as n eqn:eqlen; generalize dependent l.
	induction n as [|n IHn]; intros [|v l] Hl eq; try discriminate eq.
	1: refine (Acc_intro _ _); intros v Hv; inversion Hv; subst; destruct H as [H|H]; inversion H.
	injection eq as eqlen.
	assert (Hv := Hl _ (or_introl eq_refl)); cbn in Hl; specialize (fun v Hv => Hl v (or_intror Hv)).
	assert (Hu := IHn _ Hl eqlen).
	match type of Hu with SN ?u0 => remember u0 as u eqn:equ end;
	  generalize dependent v; generalize dependent l; induction Hu as [u Hu IHu]; intros l Hl eqlen -> v Hv.
	induction Hv as [v Hv IHv].
	refine (Acc_intro _ _); intros u' Hu'.
	inversion Hu' as [u'' v' [H|H] eq1 eq2|u1' v1 u2' H eq1 eq2|u1' u2' v2 H eq1 eq2|]; subst.
	1: destruct l; inversion H.
	1: inversion H.
	2: exact (IHv _ H).
	refine (match _
	        with ex_intro _ l' (conj H1 (conj H2 H3)) =>
	            IHu _ H l' H1 H2 H3 _ (Acc_intro _ Hv) end).
	clear Hu' IHn IHu v Hv IHv Hu; rename v1 into v.
	match type of H with over_bcontext _ ?u0 _ => remember u0 as u eqn:equ end;
	  generalize dependent l; induction H as [u v [H|H]|u u' v H IH|u v v' H IH|u v H IH]; intros l Hl equ.
	1: subst; destruct l as [|? [|? ?]]; inversion H.
	1: subst; destruct l; inversion H.
	1,2: destruct l as [|v'' l]; [discriminate equ|injection equ as equ <-].
	1:{ specialize (IH _ (fun _ Hv => Hl _ (or_intror Hv)) equ) as (l' & H1 & H2 & H3); exists (v :: l').
	    split; [intros v' [eq|Hv]; [exact (Hl _ (or_introl eq))|exact (H1 _ Hv)]
	           |split; [exact (f_equal _ H2)|exact (f_equal (fun a => BApp a v) H3)]]. }
	1:{ exists (v' :: l); split; [|split; [exact eq_refl|exact (f_equal (fun a => BApp a v') equ)]].
	    intros v'' [->|Hv]; [exact (Acc_inv (Hl _ (or_introl eq_refl)) _ H)|exact (Hl _ (or_intror Hv))]. }
	destruct l; discriminate equ.
Qed.
Lemma RED_bound : forall F n, RED F (BBound n).
Proof using.
	intros F n; pose (l := @nil bterm);
	  assert (Hl : forall v, In v l -> exists Fv, RED Fv v) by (intros ? []);
	  rewrite (eq_refl : BBound n = (fix inner l := match l with [] => BBound n | hd :: tl => BApp (inner tl) hd end) l);
	  generalize dependent l.
	induction F as [b|F1 IH1 F2 IH2]; intros l Hl.
	2: intros v Hv; refine (IH2 (v :: l) (fun v' Hv' => match Hv' with or_introl veq => _ | or_intror H => Hl _ H end)).
	2: subst v'; exists F1; exact Hv.
	cbn.
	assert (Hl2 := fun v Hv => match Hl v Hv with ex_intro _ _ H => proj1 (RED_is_CR _) _ H end); clear b Hl; rename Hl2 into Hl.
	remember (length l) as k eqn:eqlen; generalize dependent l.
	induction k as [|k IHk]; intros [|v l] Hl eq; try discriminate eq.
	1: refine (Acc_intro _ _); intros v Hv; inversion Hv; subst; destruct H as [H|H]; inversion H.
	injection eq as eqlen.
	assert (Hv := Hl _ (or_introl eq_refl)); cbn in Hl; specialize (fun v Hv => Hl v (or_intror Hv)).
	assert (Hu := IHk _ Hl eqlen).
	match type of Hu with SN ?u0 => remember u0 as u eqn:equ end;
	  generalize dependent v; generalize dependent l; induction Hu as [u Hu IHu]; intros l Hl eqlen -> v Hv.
	induction Hv as [v Hv IHv].
	refine (Acc_intro _ _); intros u' Hu'.
	inversion Hu' as [u'' v' [H|H] eq1 eq2|u1' v1 u2' H eq1 eq2|u1' u2' v2 H eq1 eq2|]; subst.
	1: destruct l; inversion H.
	1: inversion H.
	2: exact (IHv _ H).
	refine (match _
	        with ex_intro _ l' (conj H1 (conj H2 H3)) =>
	            IHu _ H l' H1 H2 H3 _ (Acc_intro _ Hv) end).
	clear Hu' IHk IHu v Hv IHv Hu; rename v1 into v.
	match type of H with over_bcontext _ ?u0 _ => remember u0 as u eqn:equ end;
	  generalize dependent l; induction H as [u v [H|H]|u u' v H IH|u v v' H IH|u v H IH]; intros l Hl equ.
	1: subst; destruct l as [|? [|? ?]]; inversion H.
	1: subst; destruct l; inversion H.
	1,2: destruct l as [|v'' l]; [discriminate equ|injection equ as equ <-].
	1:{ specialize (IH _ (fun _ Hv => Hl _ (or_intror Hv)) equ) as (l' & H1 & H2 & H3); exists (v :: l').
	    split; [intros v' [eq|Hv]; [exact (Hl _ (or_introl eq))|exact (H1 _ Hv)]
	           |split; [exact (f_equal _ H2)|exact (f_equal (fun a => BApp a v) H3)]]. }
	1:{ exists (v' :: l); split; [|split; [exact eq_refl|exact (f_equal (fun a => BApp a v') equ)]].
	    intros v'' [->|Hv]; [exact (Acc_inv (Hl _ (or_introl eq_refl)) _ H)|exact (Hl _ (or_intror Hv))]. }
	destruct l; discriminate equ.
Qed.

Lemma RED_bsubstb : forall F1 F2 u, (forall v, RED F1 v -> RED F2 (bsubstb u O v)) -> RED (TArrow F1 F2) (BAbs u).
Proof using.
	intros F1 F2 u Hu v Hv.
	assert (SNu : SN u).
	{ clear v Hv; unfold SN.
	  pose (v := BVar O).
	  assert (Hv : RED F1 v) by (exact (RED_var _ _)).
	  specialize (Hu _ Hv); apply RED_is_CR in Hu; clear F1 F2 Hv; subst v.
	  pose (n := O); rewrite (eq_refl : bsubstb u O _ = bsubstb u n (BVar 0)) in Hu.
	  remember (bsubstb u n (BVar 0)) as u' eqn:equ; generalize dependent n; generalize dependent u.
	  unfold RewriteSystem.strong_normalizable.
	  induction Hu as [u' Hu IHu]; intros u n ->.
	  clear Hu; specialize (fun u n H => IHu _ H u n eq_refl).
	  constructor; intros v Hv.
	  refine (IHu _ n _); clear IHu; unfold transp in *.
	  generalize dependent n; induction Hv as [u v [H|H]|u u' v H IH|u v v' H IH|u v H IH]; intros n.
	  1: refine (bctx_step (or_introl _)).
	  2: refine (bctx_step (or_intror _)).
	  1,2: inversion H; subst.
	  1: rewrite (bsubstb_comm (le_0_n _)); exact (Beta _ _).
	  1: cbn; rewrite <-(incr_bsubstb_ge (v:=BVar 0) (le_0_n _)); exact (Eta _).
	  1: exact (bctx_app_l (IH _)).
	  1: exact (bctx_app_r (IH _)).
	  exact (bctx_abs (IH _)). }
	assert (SNv : SN v) by (exact (proj1 (RED_is_CR _) _ Hv)).
	generalize dependent v; induction SNu as [u SNu IHu]; intros v Hv SNv.
	induction SNv as [v SNv IHv].
	refine (proj2 (proj2 (RED_is_CR _)) (BApp _ _) I _); intros u' Hu'.
	inversion Hu' as [luv u'' [H|H] eq1 eq2|lu u1 v' H eq1 eq2|lu v' u2 H eq1 eq2|]; subst.
	- inversion H; subst; exact (Hu _ Hv).
	- inversion H.
	- inversion H; subst; [destruct H0 as [H0|H0]; inversion H0; subst|].
	  1: cbn in Hu; specialize (Hu _ Hv); rewrite bsubstb_incr in Hu; exact Hu.
	  refine (IHu _ H1 _ _ Hv (Acc_intro _ SNv)); clear - Hu H1.
	  intros v Hv; specialize (Hu _ Hv); clear F1 Hv; rename v0 into u', H1 into Huu'.
	  refine (proj1 (proj2 (RED_is_CR _)) _ _ Hu _); clear F2 Hu.
	  generalize dependent v; generalize O; induction Huu' as [u u' [H|H]|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH]; intros n v.
	  1: inversion H; subst; refine (bctx_step (or_introl _)); cbn; rewrite (bsubstb_comm (le_0_n _)); exact (Beta _ _).
	  1: inversion H; subst; refine (bctx_step (or_intror _)); cbn; rewrite <-(incr_bsubstb_ge (le_0_n _)); exact (Eta _).
	  1: exact (bctx_app_l (IH _ _)).
	  1: exact (bctx_app_r (IH _ _)).
	  exact (bctx_abs (IH _ _)).
	- exact (IHv _ H (proj1 (proj2 (RED_is_CR _)) _ _ Hv H)).
Qed.

Fixpoint pbsubstb u f := match u with
	| BVar x => BVar x
	| BBound n => f n
	| BApp u v => BApp (pbsubstb u f) (pbsubstb v f)
	| BAbs u => BAbs (pbsubstb u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
end.

Lemma pbsubstb_ext : forall u f1 f2, (forall n, f1 n = f2 n) -> pbsubstb u f1 = pbsubstb u f2.
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros f1 f2 Hf.
	- exact eq_refl.
	- exact (Hf _).
	- exact (f_equal2 _ (IH1 _ _ Hf) (IH2 _ _ Hf)).
	- refine (f_equal _ (IH _ _ _)); intros [|n]; [exact eq_refl|exact (f_equal (fun a => incr_bound a _) (Hf _))].
Qed.

Lemma bsubstb_is_pbsubstb : forall u n v, bsubstb u n v = pbsubstb u (fun k => if k <? n then BBound k else if k =? n then v else BBound (pred k)).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _) (IH2 _ _)).
	- refine (f_equal BAbs (eq_trans (IH _ _) (pbsubstb_ext _ _ _ _))).
	  intros [|[|k]]; [exact eq_refl| |rewrite (eq_refl : (S _ <? S _) = (_ <? n)), (eq_refl : (S _ =? S _) = (_ =? n))].
	  1: cbn; destruct n as [|n]; exact eq_refl.
	  destruct (S k <? n); [|destruct (S k =? n)]; exact eq_refl.
Qed.

Lemma over_beta_incr :
	forall u n v, over_bcontext (union _ beta eta) (incr_bound u n) v ->
	exists w, over_bcontext (union _ beta eta) u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u' eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u' v' H|u'1 u'2 v' H IH|u' v'1 v'2 H IH|u'1 u'2 H IH]; intros u n equ.
	- destruct H as [H|H]; inversion H; clear H; subst; rename H0 into H.
	  1,2: destruct u as [| |[| | |u1] u2|[| |u1 [|[|k2]| |]|]]; try discriminate H.
	  3: injection H as _ H; destruct (n <=? k2); discriminate H.
	  1: injection H as -> ->; rewrite <-(incr_bsubstb_le (le_0_n _)).
	  1: exact (ex_intro _ _ (conj (bctx_step (or_introl (Beta _ _))) eq_refl)).
	  injection H as H.
	  refine (match _ with ex_intro _ w (conj H1 H2) => ex_intro _ w (conj
	            (bctx_step (or_intror (eq_ind _ (fun a => eta (BAbs (BApp a (BBound O))) w) (Eta _) _ H1))) H2) end).
	  rename v' into v, u1 into u, n into l.
	  assert (Hn := le_0_n l); generalize dependent l; generalize dependent O; generalize dependent v.
	  induction u as [x|m|u1 IH1 u2 IH2|u IH]; intros [y|n|v1 v2|v] k l Heq klel; try discriminate Heq.
	  1: exists (BVar x); split; [exact eq_refl|exact Heq].
	  2: injection Heq as H1 H2; specialize (IH1 _ _ _ H1 klel) as [w1 [<- ->]]; specialize (IH2 _ _ _ H2 klel) as [w2 [<- ->]].
	  2: exists (BApp w1 w2); split; exact eq_refl.
	  2: injection Heq as Heq; specialize (IH _ _ _ Heq (le_n_S _ _ klel)) as [w [<- ->]].
	  2: exists (BAbs w); split; exact eq_refl.
	  unfold incr_bound in Heq.
	  destruct m as [|m]; injection Heq as Heq.
	  1: destruct n as [|n]; [|destruct (k <=? S n); discriminate Heq].
	  1: destruct k as [|k]; [discriminate Heq|destruct l as [|l]; [inversion klel|]].
	  1: exists (BBound O); split; exact eq_refl.
	  exists (BBound (if l <=? m then m else n)); cbn.
	  destruct (le_gt_cases l m) as [llem|mltl].
	  1: rewrite !(proj2 (leb_le _ _) llem), (proj2 (leb_le _ _) (le_trans _ _ _ klel llem)) in *; split; [exact eq_refl|].
	  1: destruct (le_gt_cases k n) as [klen|nltk]; [rewrite (proj2 (leb_le _ _) klen) in Heq; injection Heq as ->; exact eq_refl|].
	  1: rewrite (proj2 (leb_gt _ _) nltk) in Heq; subst n;
	       contradiction (lt_neq _ _ (le_trans _ _ _ nltk (le_trans _ _ _ klel (le_S _ _ (le_S _ _ llem)))) eq_refl).
	  rewrite (proj2 (leb_gt _ _) mltl) in *.
	  destruct (le_gt_cases l n) as [llen|nltl]; [rewrite (proj2 (leb_le _ _) llen)|rewrite (proj2 (leb_gt _ _) nltl)].
	  1: rewrite (proj2 (leb_le _ _) (le_trans _ _ _ klel llen)) in Heq; injection Heq as <-;
	       contradiction (lt_neq _ _ (le_trans _ _ _ mltl llen) eq_refl).
	  rewrite Heq; split; exact eq_refl.
	- destruct u as [| |u1 u2|]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BApp w u2); split; [exact (bctx_app_l Hw)|exact eq_refl].
	- destruct u as [| |u1 u2|]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BApp u1 w); split; [exact (bctx_app_r Hw)|exact eq_refl].
	- destruct u as [| | |u]; try discriminate equ.
	  injection equ as ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BAbs w); split; [exact (bctx_abs Hw)|exact eq_refl].
Qed.
Lemma over_beta_t_incr :
	forall u n v, (over_bcontext (union _ beta eta))^+ (incr_bound u n) v ->
	exists w, (over_bcontext (union _ beta eta))^+ u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u0 eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u0 v0 H|u0 v0 w0 _ IH1 _ IH2]; intros u n equ.
	1: subst; destruct (over_beta_incr _ _ _ H) as [v [Hv1 Hv2]]; exists v; split; [exact (t_step Hv1)|exact Hv2].
	specialize (IH1 _ _ equ) as [v [Hv1 Hv2]].
	specialize (IH2 _ _ Hv2) as [w [Hw1 Hw2]].
	exists w; split; [exact (t_trans Hv1 Hw1)|exact Hw2].
Qed.
Lemma over_beta_rt_incr :
	forall u n v, (over_bcontext (union _ beta eta))^* (incr_bound u n) v ->
	exists w, (over_bcontext (union _ beta eta))^* u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u0 eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u0 v0 H|u0|u0 v0 w0 _ IH1 _ IH2]; intros u n equ.
	1: subst; destruct (over_beta_incr _ _ _ H) as [v [Hv1 Hv2]]; exists v; split; [exact (rt_step Hv1)|exact Hv2].
	1: subst; refine (ex_intro _ _ (conj rt_refl eq_refl)).
	specialize (IH1 _ _ equ) as [v [Hv1 Hv2]].
	specialize (IH2 _ _ Hv2) as [w [Hw1 Hw2]].
	exists w; split; [exact (rt_trans Hv1 Hw1)|exact Hw2].
Qed.

Lemma betaeta_bsubstb_l :
	forall u u' n v, (over_bcontext (union _ beta eta))^* u u' ->
	(over_bcontext (union _ beta eta))^* (bsubstb u n v) (bsubstb u' n v).
Proof using.
	intros u u' n v H; induction H as [u u' H|u|u1 u2 u3 _ IH1 _ IH2].
	2: exact rt_refl.
	2: exact (rt_trans IH1 IH2).
	refine (rt_step _).
	generalize dependent v; generalize dependent n;
	  induction H as [u u' H|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH]; intros n v.
	- destruct H as [H|H].
	  1: inversion H; subst; cbn.
	  1: rewrite (bsubstb_comm (le_0_n _)).
	  1: exact (bctx_step (or_introl (Beta _ _))).
	  inversion H; subst; cbn.
	  rewrite <-(incr_bsubstb_ge (le_0_n _)).
	  exact (bctx_step (or_intror (Eta _))).
	- exact (bctx_app_l (IH _ _)).
	- exact (bctx_app_r (IH _ _)).
	- exact (bctx_abs (IH _ _)).
Qed.
Lemma betastar_bsubstb_r :
	forall u n v v', (over_bcontext (union _ beta eta))^* v v' ->
	(over_bcontext (union _ beta eta))^* (bsubstb u n v) (bsubstb u n v').
Proof using.
	assert (tmp : forall u u' n, (over_bcontext (union _ beta eta))^* u u' -> (over_bcontext (union _ beta eta))^* (incr_bound u n) (incr_bound u' n)).
	{ intros u u' n H; induction H as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  2: exact rt_refl.
	  2: exact (rt_trans IH1 IH2).
	  refine (rt_step _).
	  generalize dependent n; induction H as [u u' [H|H]|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH]; intros n.
	  - inversion H; subst; cbn; rewrite (incr_bsubstb_le (le_0_n _)); exact (bctx_step (or_introl (Beta _ _))).
	  - inversion H; subst; cbn; rewrite <-(incr_bound_comm (le_0_n _)); exact (bctx_step (or_intror (Eta _))).
	  - exact (bctx_app_l (IH _)).
	  - exact (bctx_app_r (IH _)).
	  - exact (bctx_abs (IH _)). }
	intros u;
	  induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v v' Hv.
	1: exact rt_refl.
	1: unfold bsubstb; destruct (k <? n); [exact rt_refl|destruct (k =? n); [exact Hv|exact rt_refl]].
	1: cbn; specialize (IH1 n _ _ Hv); specialize (IH2 n _ _ Hv);
	     match goal with |- clos_refl_trans _ (BApp ?u ?v) (BApp ?u' ?v') =>
	       remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv' end.
	1: refine (rt_trans (y:=BApp u0' v0) _ _); [rename IH1 into H|rename IH2 into H]; clear - H.
	3: cbn; specialize (IH (S n) _ _ (tmp _ _ O Hv)); rename IH into H.
	3: match goal with |- clos_refl_trans _ (BAbs ?u) (BAbs ?u') =>
	     remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv'; clear - H end.
	1,2,3: induction H as [u v H|u|u v w _ IH1 _ IH2]; [refine (rt_step _)|exact rt_refl|exact (rt_trans IH1 IH2)].
	1: exact (bctx_app_l H).
	1: exact (bctx_app_r H).
	1: exact (bctx_abs H).
Qed.

Lemma bsubstb_pbsubstb : forall u n v f,
	bsubstb (pbsubstb u f) n v = pbsubstb u (fun k => bsubstb (f k) n v).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v f.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _ _) (IH2 _ _ _)).
	- cbn; f_equal; rewrite IH; apply pbsubstb_ext.
	  intros [|k]; [exact eq_refl|exact (eq_sym (incr_bsubstb_ge (le_0_n _)))].
Qed.

Lemma pbsubstb_id : forall u, pbsubstb u (fun n => BBound n) = u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH].
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ IHu IHv).
	- refine (f_equal _ (eq_trans (pbsubstb_ext _ _ _ _) IH)); intros [|n]; exact eq_refl.
Qed.

Lemma typable_is_red : forall Gv G u F f, Gv ;; G |- {u} : {F} ->
	(forall n Fn, nth_error G n = Some Fn -> RED Fn (f n)) ->
	RED F (pbsubstb u f).
Proof using.
	intros Gv G u F f Hu Hf.
	generalize dependent f; induction Hu as [Gv G x F H|Gv G n F H|Gv G u1 u2 F1 F2 H1 IH1 H2 IH2|Gv G u F1 F2 H IH]; intros f Hf.
	- exact (RED_var _ _).
	- exact (Hf _ _ H).
	- exact (IH1 _ Hf _ (IH2 _ Hf)).
	- simpl pbsubstb; refine (RED_bsubstb _ _ _ _); intros v Hv; rewrite bsubstb_pbsubstb; refine (IH _ _).
	  intros [|n] Fn HFn; [injection HFn as <-; exact Hv|rewrite bsubstb_incr; exact (Hf _ _ HFn)].
Qed.
Corollary typable_is_sn : forall Gv G u F, Gv ;; G |- {u} : {F} -> SN u.
Proof using.
	intros Gv G u F Hu.
	rewrite <-pbsubstb_id; refine (proj1 (RED_is_CR _) _ (typable_is_red _ _ _ _ _ Hu _)).
	intros n Fn _; exact (RED_bound _ _).
Qed.
End ReductibilityCandidates.

Module TypeReqs <: FiniteSet.SetReqs.
Definition val := type.
Definition val_dec : forall v1 v2 : val, { v1 = v2 } + { v1 <> v2 }.
Proof using.
	intros v1; induction v1 as [b1|f11 IH1 f12 IH2]; intros [b2|f21 f22].
	1: destruct (B_dec b1 b2) as [Hb|Hb]; [left; f_equal; exact Hb|right; intros [=H]; exact (Hb H)].
	1,2: right; discriminate.
	specialize (IH1 f21) as [IH1|IH1]; [|right; intros [=H _]; exact (IH1 H)].
	specialize (IH2 f22) as [IH2|IH2]; [|right; intros [=_ H]; exact (IH2 H)].
	left; exact (f_equal2 _ IH1 IH2).
Qed.
End TypeReqs.
Module FiniteTypes := FiniteSet.Make TypeReqs.

Inductive NJm : list type -> type -> Prop :=
	| Ax : forall {ctx F}, In F ctx -> NJm ctx F
	| ArrowE : forall {ctx F1 F2}, NJm ctx (TArrow F1 F2) -> NJm ctx F1 -> NJm ctx F2
	| ArrowI : forall {ctx F1 F2}, NJm (F1 :: ctx) F2 -> NJm ctx (TArrow F1 F2).

Lemma NJm_iff : forall ctx F, NJm ctx F <-> exists u, VarMap.empty ;; ctx |- {u} : {F}.
Proof using.
	intros ctx F; split.
	- intros H; induction H as [ctx F H|ctx F1 F2 H1 [u1 Hu1] H2 [u2 Hu2]|ctx F1 F2 H [u Hu]].
	  + induction ctx as [|F1 ctx IH]; [contradiction H|cbn in H; destruct H as [<-|H]].
	    1: exists (BBound O); exact (TPBound _ (_ :: _) O eq_refl).
	    specialize (IH H) as [u Hu]; exact (ex_intro _ _ (proj1 (typable_incr _ [] _ _ _ _) Hu)).
	  + exact (ex_intro _ _ (TPApp Hu1 Hu2)).
	  + exact (ex_intro _ _ (TPAbs Hu)).
	- intros [u Hu]; remember VarMap.empty as vctx eqn:eqvctx;
	    induction Hu as [vctx ctx x F H|vctx ctx n F H|vctx ctx u v F1 F2 H1 IH1 H2 IH2|vctx ctx u F1 F2 H IH]; subst vctx.
	  + contradiction (VarMap.mem_empty _ (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H))).
	  + refine (Ax _); generalize dependent ctx; induction n as [|n IHn]; (intros [|F1 ctx]; [discriminate 1|intros H]).
	    1: left; injection H as H; exact (eq_sym H).
	    right; exact (IHn _ H).
	  + exact (ArrowE (IH1 eq_refl) (IH2 eq_refl)).
	  + exact (ArrowI (IH eq_refl)).
Qed.

Corollary NJm_coherent : B -> exists F, ~ NJm [] F.
Proof using.
	intros b; exists (TSimple b); rewrite NJm_iff; intros [u Hu].
	assert (tmp := fun H2 => RewriteSystem.strong_normalizable_is_normalizable
	          eq _ (Hr:=Build_Respects _ eq _ (over_bcontext (union _ beta eta)) ltac:(intros ? ? ? ? <- <-; split; exact (fun H => H)))
	          H2 _ (typable_is_sn _ _ _ _ Hu)).
	match type of tmp with ?h -> _ => assert (tmp1 : h); [|specialize (tmp tmp1); clear tmp1] end.
	1:{ clear; intros u; induction u as [x|n|u IHu v IHv|u IH].
	    1,2: left; intros v Hv; inversion Hv; destruct H as [H|H]; inversion H.
	    1: destruct IHu as [IHu|[u' IHu]]; [|right; refine (ex_intro _ _ (bctx_app_l IHu))].
	    1: destruct IHv as [IHv|[v' IHv]]; [|right; refine (ex_intro _ _ (bctx_app_r IHv))].
	    1: destruct u as [x|n|u1 u2|u]; [| | |right; refine (ex_intro _ _ (bctx_step (or_introl (Beta _ _))))].
	    1-3: left; intros uv' Huv'; inversion Huv'; [destruct H as [H|H]; inversion H|exact (IHu _ H2)|exact (IHv _ H2)].
	    destruct IH as [IH|[u' IH]]; [|right; refine (ex_intro _ _ (bctx_abs IH))].
	    assert (tmp : (forall y, ~ eta (BAbs u) y) -> RewriteSystem.normal_form (over_bcontext (union _ beta eta)) (BAbs u))
	      by (intros H y Hy; inversion Hy; [destruct H0 as [H0|H0]; [inversion H0|exact (H _ H0)]|exact (IH _ H1)]).
	    refine (match _ with
	            | or_introl H => or_introl (tmp H)
	            | or_intror (ex_intro _ u' Hu') =>
	                or_intror (ex_intro _ u'
	                  (eq_ind _ (fun a => over_bcontext _ (BAbs a) _) (bctx_step (or_intror (Eta _))) u (eq_sym Hu'))) end); clear IH tmp.
	    assert (tmp : forall y, u <> BApp (incr_bound y O) (BBound O) -> ~ eta (BAbs u) y)
	      by (intros y Hy H; inversion H; subst; exact (Hy eq_refl)).
	    refine (match _ with or_introl H => or_introl (fun y => tmp y (H y)) | or_intror H => or_intror H end); clear tmp.
	    destruct u as [x|n|u1 u2|u].
	    1,2,4: left; intros u'; discriminate.
	    destruct u2 as [x|[|n]|u21 u22|u2].
	    1,3,4,5: left; intros u'; discriminate.
	    refine (match (_ : (forall u', u1 <> incr_bound u' O) \/ _) with
	            | or_introl H => ltac:(left; intros u' [=f]; exact (H _ f))
	            | or_intror (ex_intro _ u' H) => or_intror (ex_intro _ u' (f_equal (fun a => BApp a _) H)) end).
	    generalize O.
	    induction u1 as [x|k|u1 IH1 u2 IH2|u IH]; intros n.
	    1: right; exists (BVar x); exact eq_refl.
	    1: remember (n <=? k) as tmp eqn:eqtmp; symmetry in eqtmp; destruct tmp as [|].
	    1: apply leb_le in eqtmp; inversion eqtmp; subst.
	    1: clear eqtmp; left; intros [| | |]; try discriminate; intros [=f]; remember (k <=? n) as tmp eqn:eqtmp; destruct tmp.
	    1: subst; apply eq_sym, leb_le in eqtmp; exact (lt_neq _ _ eqtmp eq_refl).
	    1: subst; apply eq_sym, leb_gt in eqtmp; exact (lt_neq _ _ eqtmp eq_refl).
	    1: right; exists (BBound m); cbn; rewrite (proj2 (leb_le _ _) H); exact eq_refl.
	    1: right; exists (BBound k); cbn; rewrite eqtmp; exact eq_refl.
	    1: specialize (IH1 n) as [IH1|[u1' ->]].
	    1: left; intros [| | |]; try discriminate; intros [=f _]; exact (IH1 _ f).
	    1: specialize (IH2 n) as [IH2|[u2' ->]].
	    1: left; intros [| | |]; try discriminate; intros [=_ f]; exact (IH2 _ f).
	    1: right; exact (ex_intro _ (BApp u1' u2') eq_refl).
	    specialize (IH (S n)) as [IH|[u' ->]].
	    1: left; intros [| | |]; try discriminate; intros [=f]; exact (IH _ f).
	    right; exact (ex_intro _ (BAbs u') eq_refl). }
	destruct tmp as [u' [Rsuu' Hu']].
	assert (Tu' : VarMap.empty ;; [] |- {u'} : {TSimple b}).
	{ clear Hu'; induction Rsuu' as [u v H|u|u v w _ IH1 _ IH2]; [|exact Hu|exact (IH2 (IH1 Hu))].
	  apply over_bcontext_union in H; destruct H as [H|H]; [exact (autored_beta _ _ _ _ _ Hu H)|exact (autored_eta _ _ _ _ _ Hu H)]. }
	clear u Hu Rsuu'; rename u' into u, Hu' into Hnu, Tu' into Hu.
	inversion Hu as [vctx ctx x F H eq1 eq2 eq3|vctx ctx n F H eq1 eq2 eq3|vctx ctx u1 u2 F1 F2 H1 H2 eq1 eq2 eq3|]; subst.
	1: contradiction (VarMap.mem_empty _ (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H))).
	1: destruct n; discriminate H.
	remember (TSimple b) as F2 eqn:eqF2; clear b eqF2 Hu.
	remember (TArrow F1 F2) as F1F2 eqn:eqF.
	remember (@nil type) as ctx eqn:eqctx.
	generalize dependent F2; generalize dependent F1; generalize dependent u2;
	  remember VarMap.empty as vctx;
	  induction H1 as [vctx ctx x F H|vctx ctx n F H|vctx ctx u11 u12 F11 F12 H11 IH1 H12 IH2|vctx ctx u1 F11 F12 H IH];
	  intros u2 Hnu F1 H2 F2 eq; subst.
	1: contradiction (VarMap.mem_empty _ (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H))).
	1: destruct n; discriminate H.
	2: exact (Hnu _ (bctx_step (or_introl (Beta _ _)))).
	exact (IH1 eq_refl eq_refl _ (fun y Hy => Hnu _ (bctx_app_l Hy)) _ H12 _ eq_refl).
Qed.

Fixpoint eval_type f F : bool := match F with
	| TSimple b => f b
	| TArrow F1 F2 => orb (negb (eval_type f F1)) (eval_type f F2)
end.
Lemma NJm_eval_type : forall ctx F, NJm ctx F -> forall f, (forall Fi, In Fi ctx -> eval_type f Fi = true) -> eval_type f F = true.
Proof using.
	intros ctx F HF f Hctx; induction HF as [ctx b H|ctx F1 F2 H1 IH1 H2 IH2|ctx F1 F H IH].
	- exact (Hctx _ H).
	- specialize (IH1 Hctx); specialize (IH2 Hctx); cbn in IH1; rewrite IH2 in IH1; exact IH1.
	- specialize (fun H => IH (fun Fi HFi => match HFi with
	                            | or_introl H' => eq_ind _ _ H _ (eq_sym H') | or_intror H => Hctx _ H end)); cbn in IH.
	  cbn; destruct (eval_type f F1); [exact (IH eq_refl)|exact eq_refl].
Qed.
Corollary NJm_coherent' : B -> exists F, ~ NJm [] F.
Proof using.
	intros b; exists (TSimple b); intros H; discriminate (NJm_eval_type _ _ H (fun _ => false) ltac:(intros _ [])).
Qed.
(* 
Lemma typ_app_inv_rect : forall Gv G u v F, Gv ;; G |- {u} {v} : {F} -> { F1 | Gv ;; G |- {u} : {F1} => {F} /\ Gv ;; G |- {v} : {F1} }.
Proof using.
	intros Gv G u v F H; inversion H as [| |Gv' G' u' v' F1 F2 H1 H2|]; subst; exists F1; split; assumption.
Qed.
Lemma typ_abs_inv_rect : forall Gv G u F, Gv ;; G |- {BAbs u} : {F} -> { F1 & { F2 & (F = TArrow F1 F2) * Gv ;; (F1 :: G) |- {u} : {F2} }%type }.
Proof using.
	intros Gv G u F H; destruct F as [b|F1 F2]; [exfalso; inversion H|].
	exists F1, F2; split; [exact eq_refl|].
	inversion H; exact H4.
Qed.

Module UNorm := UntypedNorm.UntypedNorm UntypedL.
Definition eta_long Gv G u F : Gv ;; G |- {u} : {F} -> RewriteSystem.normal_form (over_bcontext beta) u -> bterm.
Proof using.
	(* intros H Hnorm; apply UNorm.normal_form_iff in Hnorm; destruct Hnorm as [Hnhf Hnargs].
	unfold UNorm.normal_head_form in Hnhf. *)
	(* generalize dependent F; generalize dependent G; induction u as [x|n|u IHu v IHv|u IH]; intros Gv G F H Hnorm. *)
	generalize dependent F; generalize dependent G;
	  refine ((fun from_b => UNorm.bterm_head_rect (fun u => _) _ (fun n G F _ _ => from_b n F) _ u) _); clear u; swap 2 3.
	- intros x _ F _ _.
	  refine (let args := _ in UNorm.of_head_form (length args) (BVar x) args).
	  induction F as [b|F1 _ F2 IH2].
	  1: exact [].
	  exact (List.map (fun v => incr_bound v O) IH2 ++ [from_b O F1]).
	- intros n F.
	  refine (let args := _ in UNorm.of_head_form (length args) (BBound (length args + n)) args).
	  clear n; induction F as [b|F1 IH1 F2 IH2].
	  1: exact [].
	  exact (List.map (fun v => incr_bound v O) IH2 ++ [UNorm.of_head_form (length IH1) (BBound (length IH1)) IH1]).
	- intros u Hhd Hargs G F Hu Hnorm.
	  specialize (UNorm.of_head_form_head_form u).
	  apply UNorm.normal_form_iff in Hnorm; destruct Hnorm as [Hnhd Hntl].
	  unfold UNorm.normal_head_form, UNorm.of_head_form in Hnhd.
	  remember (UNorm.nlambdas u) as nl eqn:eql;
	  remember (UNorm.skip_apps (UNorm.skip_lambdas u)) as hd eqn:eqh;
	  remember (UNorm.acc_apps (UNorm.skip_lambdas u)) as ar eqn:eqa;
	  clear eql eqh eqa; intros <-.
	  assert (tmp : { G' & { F' | Gv ;; G' ++ G |- {hd} : {F'} } }).
	  { unfold UNorm.of_head_form in Hu.
	  generalize dependent G; generalize dependent F; induction nl as [|nl IH]; intros F G Hu.
	  2: apply typ_abs_inv_rect in Hu.
	  2: destruct Hu as [F1 [F2 [-> Hu]]]; specialize (IH _ _ Hu) as [G' [F' IH]]; refine (existT _ (G' ++ [F1]) (exist _ F' _)).
	  2: rewrite app_assoc; exact IH.
	  unfold UNorm.add_lambdas in Hu.
	  generalize dependent F; induction ar as [|atl ar IH]; intros F Hu.
	  2: apply typ_abs_inv_rect in Hu.
	  2: destruct Hu as [F1 [F2 [-> Hu]]]; specialize (IH _ _ Hu) as [G' [F' IH]]; refine (existT _ (G' ++ [F1]) (exist _ F' _)).
	  2: rewrite app_assoc; exact IH.
	  unfold UNorm.add_lambdas in Hu.
	  }
Defined.
Fixpoint eta_long G u0 args := match F with
	| TSimple _ => (O, u0, args)
	| TArrow F1 F2 => match args with
		| hd :: tl => let (nls, u0, tl) := eta_long F2 u0 tl in (S nls, u0, (hd :: tl))
		| [] => let (nls, u0, args) := eta_long F2 u0 [] in (S nls, incr_bound u0 O, (eta_long F1 (BBound O) [] :: List.map (fun v => incr_bound v O) args))
	end
end.

Lemma eta_long_wd : forall u F, (over_bcontext eta)^* (eta_long u F) u.
Proof using.
	intros u F; generalize dependent u; induction F as [b|F1 _ F2 IH2]; intros u.
	1: exact rt_refl.
	destruct u as [x|n|u v|u]; cbn.
	4: exact (clos_rt_over_bcontext_ctx (BCAbs BCHole) (IH2 _)).
	1-3: refine (rt_trans (clos_rt_over_bcontext_ctx (BCAbs (BCApp_l BCHole _)) _) (rt_step (bctx_step (Eta _)))).
	1-3: exact (IH2 _).
Qed.

Lemma eta_long_typable : forall Gv G u F, Gv ;; G |- {u} : {F} -> Gv ;; G |- {eta_long u F} : {F}.
Proof using.
	intros Gv G u F; generalize dependent G.
Qed. *)

End TypedLambda.

Require Import UntypedFelleisen.

Module TypedLambdaC (T0 : SimpleType) (UntypedF0 : UntypedLambdaFT).
Module Import UntypedL := UntypedF0.
Module Export Vars := UntypedL.Vars.
Module Export T := T0.
Import UntypedBNotation.

Inductive type :=
	| TBot : type
	| TSimple : B -> type
	| TArrow : type -> type -> type.

Module Import TypeNotations.
Notation ";{  F  };" := F (F custom types).
Notation "_|_" := TBot (in custom types at level 0).
Notation "{ F }" := F (in custom types at level 0, F constr).
Notation "( F )" := F (in custom types at level 0, F custom types at level 2).
Notation "~ F" := (TArrow F TBot) (in custom types at level 1, F custom types at level 1).
Notation "F => G" := (TArrow F G) (in custom types at level 2, right associativity, F custom types, G custom types).
End TypeNotations.

Definition nabla u := BApp BCFelleisen (BAbs (incr_bound u O)).

Declare Module VarMapReqs : Assoc.AssocReqs
	with Definition key := V
	with Definition key_dec := dec_V.
Module VarMap := Assoc.Make(VarMapReqs).
Definition vctx := VarMap.t type.
Definition ctx := list type.

Inductive typable : vctx -> ctx -> bterm -> type -> Prop :=
	| TPC : forall {Gv G F}, typable Gv G BCFelleisen ;{ ~ ~ {F} => {F} };
	| TPVar : forall {Gv} G x {F}, VarMap.find_opt Gv x = Some F -> typable Gv G (BVar x) F
	| TPBound : forall {Gv} G n {F}, nth_error G n = Some F -> typable Gv G (BBound n) F
	| TPApp : forall {Gv G u v F1 F2}, typable Gv G u ;{{F1} => {F2}}; -> typable Gv G v F1 -> typable Gv G (u v) F2
	| TPAbs : forall {Gv G u F1 F2}, typable Gv (F1 :: G) u F2 -> typable Gv G (BAbs u) ;{{F1} => {F2}};.

Module Import TypableNotations.
Notation "Gv  ;;  G  |-  u  :  F" := (typable Gv G u F) (at level 20, u custom bterms, F custom types, no associativity).
End TypableNotations.

Lemma typ_C_inv : forall Gv G F, Gv ;; G |- C; : {F} -> exists F', F = ;{ ~ ~ {F'} => {F'} };.
Proof using.
	intros Gv G F H; inversion H as [Gv' G' F' eq| | | |]; refine (ex_intro _ _ eq_refl).
Qed.
Lemma typ_var_inv : forall Gv G x F, Gv ;; G |- {BVar x} : {F} -> VarMap.find_opt Gv x = Some F.
Proof using.
	intros Gv G x F H; inversion H; assumption.
Qed.
Lemma typ_bound_inv : forall Gv G n F, Gv ;; G |- {BBound n} : {F} -> nth_error G n = Some F.
Proof using.
	intros Gv G x F H; inversion H; assumption.
Qed.
Lemma typ_app_inv : forall Gv G u v F, Gv ;; G |- {u} {v} : {F} -> exists F1, Gv ;; G |- {u} : {F1} => {F} /\ Gv ;; G |- {v} : {F1}.
Proof using.
	intros Gv G u v F H; inversion H as [| | |Gv' G' u' v' F1 F2 H1 H2|]; subst; exists F1; split; assumption.
Qed.
Lemma typ_abs_inv : forall Gv G u F, Gv ;; G |- {BAbs u} : {F} -> exists F1 F2, F = TArrow F1 F2 /\ Gv ;; (F1 :: G) |- {u} : {F2}.
Proof using.
	intros Gv G u F H; inversion H as [| | | |Gv' G' u' F1 F2 H']; subst; exists F1, F2; split; [exact eq_refl|exact H'].
Qed.
Lemma typ_not_arrow_l : forall F1 F2, F1 <> TArrow F1 F2.
Proof using.
	intros F1; induction F1 as [|b1|F11 IH F12 _]; intros F2 eq; [discriminate eq|discriminate eq|injection eq as eq _; exact (IH _ eq)].
Qed.
Lemma typ_not_arrow_r : forall F1 F2, F2 <> TArrow F1 F2.
Proof using.
	intros F1 F2; generalize dependent F1; induction F2 as [|b1|F21 _ F22 IH]; intros F1 eq;
	  [discriminate eq|discriminate eq|injection eq as _ eq; exact (IH _ eq)].
Qed.

Lemma typable_incr : forall Gv G1 F1 G2 u F, Gv ;; (G1 ++ G2) |- {u} : {F} <-> Gv ;; (G1 ++ F1 :: G2) |- {incr_bound u (length G1)} : {F}.
Proof using.
	intros Gv G1 F0 G2 u F; split; intros H.
	- remember (G1 ++ G2) as G0 eqn:eqG; generalize dependent G1;
	    induction H as [Gv G0 F|Gv G0 x F H|Gv G0 n F H|Gv G0 u v F1 F2 H1 IH1 H2 IH2|Gv G0 u F1 F2 H IH]; intros G1 ->.
	  + exact TPC.
	  + exact (TPVar _ _ H).
	  + refine (TPBound _ _ _); rewrite <-H; clear F H; generalize dependent G1; induction n as [|n IHn]; intros [|F1 G1].
	    1-3: exact eq_refl.
	    specialize (IHn G1); cbn; destruct (length G1 <=? n); exact IHn.
	  + exact (TPApp (IH1 _ eq_refl) (IH2 _ eq_refl)).
	  + exact (TPAbs (IH (_ :: _) eq_refl)).
	- generalize dependent F; generalize dependent G1; induction u as [|x|n|u IHu v IHv|u IH]; intros G1 F H.
	  + apply typ_C_inv in H; destruct H as [F' ->]; exact TPC.
	  + exact (TPVar _ _ (typ_var_inv _ _ _ _ H)).
	  + apply typ_bound_inv in H; refine (TPBound _ _ (eq_trans _ H)); cbn; clear F H.
	    generalize dependent n; induction G1 as [|F1 G1 IHG]; intros n.
	    1: exact eq_refl.
	    destruct n as [|n]; [exact eq_refl|specialize (IHG n); cbn; destruct (length G1 <=? n); exact IHG].
	  + cbn in H; apply typ_app_inv in H; destruct H as [F' [Hu Hv]]; exact (TPApp (IHu _ _ Hu) (IHv _ _ Hv)).
	  + cbn in H; apply typ_abs_inv in H; destruct H as [F1 [F2 [-> H]]]; exact (TPAbs (IH (_ :: _) _ H)).
Qed.
Lemma typable_subst : forall Gv G1 F1 G2 u v F,
	Gv ;; (G1 ++ F1 :: G2) |- {u} : {F} ->
	Gv ;; (G1 ++ G2) |- {v} : {F1} ->
	Gv ;; (G1 ++ G2) |- {bsubstb u (length G1) v} : {F}.
Proof using.
	intros Gv G1 F0 G2 u v F Hu Hv.
	remember (G1 ++ F0 :: G2) as G0 eqn:eqG; generalize dependent G1; generalize dependent v;
	  induction Hu as [Gv G0 F|Gv G0 x F H|Gv G0 n F H|Gv G0 u1 u2 F1 F2 H1 IH1 H2 IH2|Gv G0 u F1 F2 H IH]; intros v G1 -> Hv.
	- exact TPC.
	- exact (TPVar _ _ H).
	- unfold bsubstb.
	  destruct (lt_ge_cases n (length G1)) as [nltG1|G1len].
	  1: rewrite (proj2 (ltb_lt _ _) nltG1); refine (TPBound _ _ _); clear - H nltG1.
	  1: generalize dependent G1; induction n as [|n IHn]; intros [|F1 G1] H1 H2;
	       [inversion H2|exact H1|inversion H2|exact (IHn _ H1 (le_S_n _ _ H2))].
	  rewrite (proj2 (ltb_ge _ _) G1len).
	  apply le_is_ex_add in G1len; destruct G1len as [n' ->]; rename n' into n.
	  assert (H' : nth_error (F0 :: G2) n = Some F)
	    by (clear - H; rewrite add_comm in H; induction G1 as [|F1 G1 IH]; [exact H|exact (IH H)]).
	  clear H; rename H' into H.
	  destruct n as [|n].
	  1: rewrite eqb_refl; injection H as ->; exact Hv.
	  rewrite eqb_sym, (proj2 (eqb_neq _ _) (lt_neq _ _ (add_le_mono (S O) _ _ _ (le_n_S _ _ (le_0_n _)) (le_n _)))); cbn.
	  refine (TPBound _ _ _); rewrite add_comm.
	  clear - H; induction G1 as [|F1 G1 IH1]; [exact H|exact IH1].
	- exact (TPApp (IH1 _ _ eq_refl Hv) (IH2 _ _ eq_refl Hv)).
	- exact (TPAbs (IH _ (_ :: _) eq_refl (proj1 (typable_incr _ [] _ _ _ _) Hv))).
Qed.

Lemma typ_nabla : forall Gv G u F, Gv ;; G |- {u} : _|_ -> Gv ;; G |- {nabla u} : {F}.
Proof using.
	intros Gv G u F Hu; refine (TPApp TPC (TPAbs (proj1 (typable_incr _ [] _ _ _ _) Hu))).
Qed.

Goal forall Gv F, Gv ;; [] |- ^<0> : {F} => {F}.
Proof using.
	intros Gv F; refine (TPAbs (TPBound [_] O eq_refl)).
Qed.
Goal forall Gv G F, ~ (Gv ;; G |- <0> <0> : {F}).
Proof using.
	intros Gv G F H.
	inversion H as [| | |Gv' G' u v F1 F2 H1 H2|]; clear H; subst.
	apply typ_bound_inv in H1, H2.
	rewrite H2 in H1; injection H1 as eq; exact (typ_not_arrow_l _ _ eq).
Qed.

Lemma autored_beta : forall Gv G u v F, Gv ;; G |- {u} : {F} -> over_bcontext beta u v -> Gv ;; G |- {v} : {F}.
Proof using.
	intros Gv G u v F Hu Huv; generalize dependent F; generalize dependent G;
	  induction Huv as [u v H|u u' v Huv IH|u v v' Huv IH|u v H IH]; intros G F Hu.
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp (IH _ _ Hu) Hv).
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp Hu (IH _ _ Hv)).
	2: apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [-> Hu]]]; exact (TPAbs (IH _ _ Hu)).
	inversion H as [u1 u2 H' equ eqv|u1 u2 equ eqv|u1 u2 H' equ eqv]; subst u v; clear H; rename u1 into u, u2 into v.
	- apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	  apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [[= -> ->] Hu]]]; exact (typable_subst _ [] _ _ _ _ _ Hu Hv).
	- apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	  apply typ_app_inv in Hu; destruct Hu as [Fu' [HC Hu]].
	  apply typ_C_inv in HC; destruct HC as [Fu'' [= -> <-]].
	  refine (TPApp TPC (TPAbs (TPApp (proj1 (typable_incr _ [] _ _ _ _) Hu) _))).
	  refine (TPAbs (TPApp (TPBound (_ :: _ :: _) (S O) eq_refl) _)).
	  refine (TPApp (TPBound (_ :: _) O eq_refl) _).
	  exact (proj1 (typable_incr _ [] _ _ _ _) (proj1 (typable_incr _ [] _ _ _ _) Hv)).
	- apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	  apply typ_app_inv in Hv; destruct Hv as [Fv [HC Hv]].
	  apply typ_C_inv in HC; destruct HC as [F' [= -> <-]].
	  refine (TPApp TPC (TPAbs (TPApp (proj1 (typable_incr _ [] _ _ _ _) Hv) _))).
	  refine (TPAbs (TPApp (TPBound (_ :: _ :: _) (S O) eq_refl) _)).
	  refine (TPApp _ (TPBound (_ :: _) O eq_refl)).
	  exact (proj1 (typable_incr _ [] _ _ _ _) (proj1 (typable_incr _ [] _ _ _ _) Hu)).
Qed.

Lemma autored_eta : forall Gv G u v F, Gv ;; G |- {u} : {F} -> over_bcontext eta u v -> Gv ;; G |- {v} : {F}.
Proof using.
	intros Gv G u v F Hu Huv; generalize dependent F; generalize dependent G;
	  induction Huv as [u v H|u u' v Huv IH|u v v' Huv IH|u v H IH]; intros G F Hu.
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp (IH _ _ Hu) Hv).
	2: apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]]; exact (TPApp Hu (IH _ _ Hv)).
	2: apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [-> Hu]]]; exact (TPAbs (IH _ _ Hu)).
	inversion H as [u' equ eqv|u' equ eqv]; subst u v; clear H; rename u' into u.
	- apply typ_abs_inv in Hu; destruct Hu as [F1 [F2 [-> Hu]]].
	  apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	  apply typ_bound_inv in Hv; injection Hv as <-.
	  exact (proj2 (typable_incr _ [] _ _ _ _) Hu).
	- apply typ_app_inv in Hu; destruct Hu as [Fu [Hu Hv]].
	  apply typ_C_inv in Hu; destruct Hu as [f' [= -> <-]].
	  apply typ_abs_inv in Hv; destruct Hv as [F1 [F2 [[= <- <-] Hu]]].
	  apply typ_app_inv in Hu; destruct Hu as [F1 [Hu Hv]].
	  apply typ_bound_inv in Hu; injection Hu as <-.
	  exact (proj2 (typable_incr _ [] _ _ _ _) Hv).
Qed.

Lemma typable_is_bfv : forall Gv G u F, Gv ;; G |- {u} : {F} -> forall x, bfv x u -> VarMap.mem Gv x.
Proof using.
	intros Gv G u F H x; induction H as [Gv G F|Gv G y F H|Gv G n F H|Gv G u v F1 F2 H1 IH1 H2 IH2|Gv G u F1 F2 H IH].
	1: intros f; inversion f.
	1: intros f; inversion f; refine (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H)).
	1: intros f; inversion f.
	1: intros f; inversion f; [apply IH1|apply IH2]; assumption.
	1: intros f; inversion f; apply IH; assumption.
Qed.
Lemma typable_is_bfb_lt : forall Gv G u F, Gv ;; G |- {u} : {F} -> forall n, bfb n u -> n < length G.
Proof using.
	intros Gv G u F H; induction H as [Gv G F|Gv G x F H|Gv G k F H|Gv G u v F1 F2 H1 IH1 H2 IH2|Gv G u F1 F2 H IH]; intros n Hn.
	1: inversion Hn.
	1: inversion Hn.
	2: inversion Hn; subst; [exact (IH1 _ H3)|exact (IH2 _ H3)].
	2: inversion Hn; subst; refine (le_S_n _ _ (IH _ H2)).
	inversion Hn; subst; clear Hn.
	generalize dependent G; induction k as [|k IHk]; intros [|hd l] H.
	1,3: discriminate H.
	1: exact (le_n_S _ _ (le_0_n _)).
	exact (le_n_S _ _ (IHk _ H)).
Qed.

Section ReductibilityCandidates.

Implicit Types u v : bterm.

Definition SN : bterm -> Prop := RewriteSystem.strong_normalizable (over_bcontext (union _ beta eta)).
Fixpoint RED F : bterm -> Prop := match F with
	| TBot => SN
	| TSimple b => SN
	| TArrow F1 F2 => fun u => forall v, RED F1 v -> RED F2 (BApp u v)
end.

(* Definition neutral u := match u with BAbs _ => False | BCFelleisen => False | BApp BCFelleisen _ => False | _ => True end.

Definition CR1 (P : bterm -> Prop) : Prop := forall u, P u -> SN u.
Definition CR2 (P : bterm -> Prop) : Prop := forall u u', P u -> (over_bcontext (union _ beta eta)) u u' -> P u'.
Definition CR3 (P : bterm -> Prop) : Prop := forall u, neutral u -> (forall u', (over_bcontext (union _ beta eta)) u u' -> P u') -> P u.
Definition CR P := CR1 P /\ CR2 P /\ CR3 P.

Lemma SN_is_CR : CR SN.
Proof using.
	split; [exact (fun _ H => H)|split; [unfold CR2|unfold CR3]].
	- intros u u' H1 H2; inversion H1 as [H]; exact (H _ H2).
	- intros u Hu H; constructor.
	  intros u' Hu'; exact (H _ Hu').
Qed.

Lemma RED_is_CR : forall F, CR (RED F).
Proof using.
	unfold CR, CR1, CR2, CR3; intros F; induction F as [|b|F1 [IH11 [IH12 IH13]] F2 [IH21 [IH22 IH23]]].
	1,2: exact SN_is_CR.
	cbn; split; [|split].
	- intros u Hu.
	  pose (v := BVar O).
	  assert (Hv : RED F1 v)
	    by (refine (IH13 v I _); intros v' Hv'; inversion Hv'; destruct H as [H|H]; inversion H).
	  specialize (IH21 _ (Hu _ Hv)); remember (BApp u v) as uv eqn:equv.
	  clear Hu Hv IH11 IH12 IH13 IH22 IH23.
	  generalize dependent u; induction IH21 as [uv H IH]; intros u ->; constructor.
	  intros u' Hu'; exact (IH (BApp u' v) (bctx_app_l Hu') _ eq_refl).
	- intros u u' H1 H2 v Hv.
	  exact (IH22 _ _ (H1 _ Hv) (bctx_app_l H2)).
	- intros u H1 H2 v Hv.
	  specialize (IH11 _ Hv); induction IH11 as [v Hvv' IHv].
	  refine (IH23 (BApp u _) ltac:(destruct u; try exact H1; exact I) _).
	  intros u' Hu'; inversion Hu' as [uv' u'' [H|H] eq1 eq2|u0 v1 v2 H eq1 eq2|u1 v' v2 H eq1 eq2|]; subst.
	  1: inversion H; subst u; [contradiction H1|contradiction H1|].
	  2: inversion H.
	  2: subst u; contradiction H1.
	  2: exact (H2 _ H _ Hv).
	  2: exact (IHv _ H (IH12 _ _ Hv H)).
	  subst.
	  refine (H2 _ _ _ _).
Qed.

Lemma RED_var : forall F x, RED F (BVar x).
Proof using.
	intros F x; pose (l := @nil bterm);
	  assert (Hl : forall v, In v l -> exists Fv, RED Fv v) by (intros ? []);
	  rewrite (eq_refl : BVar x = (fix inner l := match l with [] => BVar x | hd :: tl => BApp (inner tl) hd end) l);
	  generalize dependent l.
	induction F as [b|F1 IH1 F2 IH2]; intros l Hl.
	2: intros v Hv; refine (IH2 (v :: l) (fun v' Hv' => match Hv' with or_introl veq => _ | or_intror H => Hl _ H end)).
	2: subst v'; exists F1; exact Hv.
	cbn.
	assert (Hl2 := fun v Hv => match Hl v Hv with ex_intro _ _ H => proj1 (RED_is_CR _) _ H end); clear b Hl; rename Hl2 into Hl.
	remember (length l) as n eqn:eqlen; generalize dependent l.
	induction n as [|n IHn]; intros [|v l] Hl eq; try discriminate eq.
	1: refine (Acc_intro _ _); intros v Hv; inversion Hv; subst; destruct H as [H|H]; inversion H.
	injection eq as eqlen.
	assert (Hv := Hl _ (or_introl eq_refl)); cbn in Hl; specialize (fun v Hv => Hl v (or_intror Hv)).
	assert (Hu := IHn _ Hl eqlen).
	match type of Hu with SN ?u0 => remember u0 as u eqn:equ end;
	  generalize dependent v; generalize dependent l; induction Hu as [u Hu IHu]; intros l Hl eqlen -> v Hv.
	induction Hv as [v Hv IHv].
	refine (Acc_intro _ _); intros u' Hu'.
	inversion Hu' as [u'' v' [H|H] eq1 eq2|u1' v1 u2' H eq1 eq2|u1' u2' v2 H eq1 eq2|]; subst.
	1: destruct l; inversion H.
	1: inversion H.
	2: exact (IHv _ H).
	refine (match _
	        with ex_intro _ l' (conj H1 (conj H2 H3)) =>
	            IHu _ H l' H1 H2 H3 _ (Acc_intro _ Hv) end).
	clear Hu' IHn IHu v Hv IHv Hu; rename v1 into v.
	match type of H with over_bcontext _ ?u0 _ => remember u0 as u eqn:equ end;
	  generalize dependent l; induction H as [u v [H|H]|u u' v H IH|u v v' H IH|u v H IH]; intros l Hl equ.
	1: subst; destruct l as [|? [|? ?]]; inversion H.
	1: subst; destruct l; inversion H.
	1,2: destruct l as [|v'' l]; [discriminate equ|injection equ as equ <-].
	1:{ specialize (IH _ (fun _ Hv => Hl _ (or_intror Hv)) equ) as (l' & H1 & H2 & H3); exists (v :: l').
	    split; [intros v' [eq|Hv]; [exact (Hl _ (or_introl eq))|exact (H1 _ Hv)]
	           |split; [exact (f_equal _ H2)|exact (f_equal (fun a => BApp a v) H3)]]. }
	1:{ exists (v' :: l); split; [|split; [exact eq_refl|exact (f_equal (fun a => BApp a v') equ)]].
	    intros v'' [->|Hv]; [exact (Acc_inv (Hl _ (or_introl eq_refl)) _ H)|exact (Hl _ (or_intror Hv))]. }
	destruct l; discriminate equ.
Qed.
Lemma RED_bound : forall F n, RED F (BBound n).
Proof using.
	intros F n; pose (l := @nil bterm);
	  assert (Hl : forall v, In v l -> exists Fv, RED Fv v) by (intros ? []);
	  rewrite (eq_refl : BBound n = (fix inner l := match l with [] => BBound n | hd :: tl => BApp (inner tl) hd end) l);
	  generalize dependent l.
	induction F as [b|F1 IH1 F2 IH2]; intros l Hl.
	2: intros v Hv; refine (IH2 (v :: l) (fun v' Hv' => match Hv' with or_introl veq => _ | or_intror H => Hl _ H end)).
	2: subst v'; exists F1; exact Hv.
	cbn.
	assert (Hl2 := fun v Hv => match Hl v Hv with ex_intro _ _ H => proj1 (RED_is_CR _) _ H end); clear b Hl; rename Hl2 into Hl.
	remember (length l) as k eqn:eqlen; generalize dependent l.
	induction k as [|k IHk]; intros [|v l] Hl eq; try discriminate eq.
	1: refine (Acc_intro _ _); intros v Hv; inversion Hv; subst; destruct H as [H|H]; inversion H.
	injection eq as eqlen.
	assert (Hv := Hl _ (or_introl eq_refl)); cbn in Hl; specialize (fun v Hv => Hl v (or_intror Hv)).
	assert (Hu := IHk _ Hl eqlen).
	match type of Hu with SN ?u0 => remember u0 as u eqn:equ end;
	  generalize dependent v; generalize dependent l; induction Hu as [u Hu IHu]; intros l Hl eqlen -> v Hv.
	induction Hv as [v Hv IHv].
	refine (Acc_intro _ _); intros u' Hu'.
	inversion Hu' as [u'' v' [H|H] eq1 eq2|u1' v1 u2' H eq1 eq2|u1' u2' v2 H eq1 eq2|]; subst.
	1: destruct l; inversion H.
	1: inversion H.
	2: exact (IHv _ H).
	refine (match _
	        with ex_intro _ l' (conj H1 (conj H2 H3)) =>
	            IHu _ H l' H1 H2 H3 _ (Acc_intro _ Hv) end).
	clear Hu' IHk IHu v Hv IHv Hu; rename v1 into v.
	match type of H with over_bcontext _ ?u0 _ => remember u0 as u eqn:equ end;
	  generalize dependent l; induction H as [u v [H|H]|u u' v H IH|u v v' H IH|u v H IH]; intros l Hl equ.
	1: subst; destruct l as [|? [|? ?]]; inversion H.
	1: subst; destruct l; inversion H.
	1,2: destruct l as [|v'' l]; [discriminate equ|injection equ as equ <-].
	1:{ specialize (IH _ (fun _ Hv => Hl _ (or_intror Hv)) equ) as (l' & H1 & H2 & H3); exists (v :: l').
	    split; [intros v' [eq|Hv]; [exact (Hl _ (or_introl eq))|exact (H1 _ Hv)]
	           |split; [exact (f_equal _ H2)|exact (f_equal (fun a => BApp a v) H3)]]. }
	1:{ exists (v' :: l); split; [|split; [exact eq_refl|exact (f_equal (fun a => BApp a v') equ)]].
	    intros v'' [->|Hv]; [exact (Acc_inv (Hl _ (or_introl eq_refl)) _ H)|exact (Hl _ (or_intror Hv))]. }
	destruct l; discriminate equ.
Qed.

Lemma RED_bsubstb : forall F1 F2 u, (forall v, RED F1 v -> RED F2 (bsubstb u O v)) -> RED (TArrow F1 F2) (BAbs u).
Proof using.
	intros F1 F2 u Hu v Hv.
	assert (SNu : SN u).
	{ clear v Hv; unfold SN.
	  pose (v := BVar O).
	  assert (Hv : RED F1 v) by (exact (RED_var _ _)).
	  specialize (Hu _ Hv); apply RED_is_CR in Hu; clear F1 F2 Hv; subst v.
	  pose (n := O); rewrite (eq_refl : bsubstb u O _ = bsubstb u n (BVar 0)) in Hu.
	  remember (bsubstb u n (BVar 0)) as u' eqn:equ; generalize dependent n; generalize dependent u.
	  unfold RewriteSystem.strong_normalizable.
	  induction Hu as [u' Hu IHu]; intros u n ->.
	  clear Hu; specialize (fun u n H => IHu _ H u n eq_refl).
	  constructor; intros v Hv.
	  refine (IHu _ n _); clear IHu; unfold transp in *.
	  generalize dependent n; induction Hv as [u v [H|H]|u u' v H IH|u v v' H IH|u v H IH]; intros n.
	  1: refine (bctx_step (or_introl _)).
	  2: refine (bctx_step (or_intror _)).
	  1,2: inversion H; subst.
	  1: rewrite (bsubstb_comm (le_0_n _)); exact (Beta _ _).
	  1: cbn; rewrite <-(incr_bsubstb_ge (v:=BVar 0) (le_0_n _)); exact (Eta _).
	  1: exact (bctx_app_l (IH _)).
	  1: exact (bctx_app_r (IH _)).
	  exact (bctx_abs (IH _)). }
	assert (SNv : SN v) by (exact (proj1 (RED_is_CR _) _ Hv)).
	generalize dependent v; induction SNu as [u SNu IHu]; intros v Hv SNv.
	induction SNv as [v SNv IHv].
	refine (proj2 (proj2 (RED_is_CR _)) (BApp _ _) I _); intros u' Hu'.
	inversion Hu' as [luv u'' [H|H] eq1 eq2|lu u1 v' H eq1 eq2|lu v' u2 H eq1 eq2|]; subst.
	- inversion H; subst; exact (Hu _ Hv).
	- inversion H.
	- inversion H; subst; [destruct H0 as [H0|H0]; inversion H0; subst|].
	  1: cbn in Hu; specialize (Hu _ Hv); rewrite bsubstb_incr in Hu; exact Hu.
	  refine (IHu _ H1 _ _ Hv (Acc_intro _ SNv)); clear - Hu H1.
	  intros v Hv; specialize (Hu _ Hv); clear F1 Hv; rename v0 into u', H1 into Huu'.
	  refine (proj1 (proj2 (RED_is_CR _)) _ _ Hu _); clear F2 Hu.
	  generalize dependent v; generalize O; induction Huu' as [u u' [H|H]|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH]; intros n v.
	  1: inversion H; subst; refine (bctx_step (or_introl _)); cbn; rewrite (bsubstb_comm (le_0_n _)); exact (Beta _ _).
	  1: inversion H; subst; refine (bctx_step (or_intror _)); cbn; rewrite <-(incr_bsubstb_ge (le_0_n _)); exact (Eta _).
	  1: exact (bctx_app_l (IH _ _)).
	  1: exact (bctx_app_r (IH _ _)).
	  exact (bctx_abs (IH _ _)).
	- exact (IHv _ H (proj1 (proj2 (RED_is_CR _)) _ _ Hv H)).
Qed.

Fixpoint pbsubstb u f := match u with
	| BVar x => BVar x
	| BBound n => f n
	| BApp u v => BApp (pbsubstb u f) (pbsubstb v f)
	| BAbs u => BAbs (pbsubstb u (fun n => match n with O => BBound O | S n => incr_bound (f n) O end))
end.

Lemma pbsubstb_ext : forall u f1 f2, (forall n, f1 n = f2 n) -> pbsubstb u f1 = pbsubstb u f2.
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros f1 f2 Hf.
	- exact eq_refl.
	- exact (Hf _).
	- exact (f_equal2 _ (IH1 _ _ Hf) (IH2 _ _ Hf)).
	- refine (f_equal _ (IH _ _ _)); intros [|n]; [exact eq_refl|exact (f_equal (fun a => incr_bound a _) (Hf _))].
Qed.

Lemma bsubstb_is_pbsubstb : forall u n v, bsubstb u n v = pbsubstb u (fun k => if k <? n then BBound k else if k =? n then v else BBound (pred k)).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _) (IH2 _ _)).
	- refine (f_equal BAbs (eq_trans (IH _ _) (pbsubstb_ext _ _ _ _))).
	  intros [|[|k]]; [exact eq_refl| |rewrite (eq_refl : (S _ <? S _) = (_ <? n)), (eq_refl : (S _ =? S _) = (_ =? n))].
	  1: cbn; destruct n as [|n]; exact eq_refl.
	  destruct (S k <? n); [|destruct (S k =? n)]; exact eq_refl.
Qed.

Lemma over_beta_incr :
	forall u n v, over_bcontext (union _ beta eta) (incr_bound u n) v ->
	exists w, over_bcontext (union _ beta eta) u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u' eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u' v' H|u'1 u'2 v' H IH|u' v'1 v'2 H IH|u'1 u'2 H IH]; intros u n equ.
	- destruct H as [H|H]; inversion H; clear H; subst; rename H0 into H.
	  1,2: destruct u as [| |[| | |u1] u2|[| |u1 [|[|k2]| |]|]]; try discriminate H.
	  3: injection H as _ H; destruct (n <=? k2); discriminate H.
	  1: injection H as -> ->; rewrite <-(incr_bsubstb_le (le_0_n _)).
	  1: exact (ex_intro _ _ (conj (bctx_step (or_introl (Beta _ _))) eq_refl)).
	  injection H as H.
	  refine (match _ with ex_intro _ w (conj H1 H2) => ex_intro _ w (conj
	            (bctx_step (or_intror (eq_ind _ (fun a => eta (BAbs (BApp a (BBound O))) w) (Eta _) _ H1))) H2) end).
	  rename v' into v, u1 into u, n into l.
	  assert (Hn := le_0_n l); generalize dependent l; generalize dependent O; generalize dependent v.
	  induction u as [x|m|u1 IH1 u2 IH2|u IH]; intros [y|n|v1 v2|v] k l Heq klel; try discriminate Heq.
	  1: exists (BVar x); split; [exact eq_refl|exact Heq].
	  2: injection Heq as H1 H2; specialize (IH1 _ _ _ H1 klel) as [w1 [<- ->]]; specialize (IH2 _ _ _ H2 klel) as [w2 [<- ->]].
	  2: exists (BApp w1 w2); split; exact eq_refl.
	  2: injection Heq as Heq; specialize (IH _ _ _ Heq (le_n_S _ _ klel)) as [w [<- ->]].
	  2: exists (BAbs w); split; exact eq_refl.
	  unfold incr_bound in Heq.
	  destruct m as [|m]; injection Heq as Heq.
	  1: destruct n as [|n]; [|destruct (k <=? S n); discriminate Heq].
	  1: destruct k as [|k]; [discriminate Heq|destruct l as [|l]; [inversion klel|]].
	  1: exists (BBound O); split; exact eq_refl.
	  exists (BBound (if l <=? m then m else n)); cbn.
	  destruct (le_gt_cases l m) as [llem|mltl].
	  1: rewrite !(proj2 (leb_le _ _) llem), (proj2 (leb_le _ _) (le_trans _ _ _ klel llem)) in *; split; [exact eq_refl|].
	  1: destruct (le_gt_cases k n) as [klen|nltk]; [rewrite (proj2 (leb_le _ _) klen) in Heq; injection Heq as ->; exact eq_refl|].
	  1: rewrite (proj2 (leb_gt _ _) nltk) in Heq; subst n;
	       contradiction (lt_neq _ _ (le_trans _ _ _ nltk (le_trans _ _ _ klel (le_S _ _ (le_S _ _ llem)))) eq_refl).
	  rewrite (proj2 (leb_gt _ _) mltl) in *.
	  destruct (le_gt_cases l n) as [llen|nltl]; [rewrite (proj2 (leb_le _ _) llen)|rewrite (proj2 (leb_gt _ _) nltl)].
	  1: rewrite (proj2 (leb_le _ _) (le_trans _ _ _ klel llen)) in Heq; injection Heq as <-;
	       contradiction (lt_neq _ _ (le_trans _ _ _ mltl llen) eq_refl).
	  rewrite Heq; split; exact eq_refl.
	- destruct u as [| |u1 u2|]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BApp w u2); split; [exact (bctx_app_l Hw)|exact eq_refl].
	- destruct u as [| |u1 u2|]; try discriminate equ.
	  injection equ as -> ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BApp u1 w); split; [exact (bctx_app_r Hw)|exact eq_refl].
	- destruct u as [| | |u]; try discriminate equ.
	  injection equ as ->.
	  specialize (IH _ _ eq_refl) as [w [Hw ->]].
	  exists (BAbs w); split; [exact (bctx_abs Hw)|exact eq_refl].
Qed.
Lemma over_beta_t_incr :
	forall u n v, (over_bcontext (union _ beta eta))^+ (incr_bound u n) v ->
	exists w, (over_bcontext (union _ beta eta))^+ u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u0 eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u0 v0 H|u0 v0 w0 _ IH1 _ IH2]; intros u n equ.
	1: subst; destruct (over_beta_incr _ _ _ H) as [v [Hv1 Hv2]]; exists v; split; [exact (t_step Hv1)|exact Hv2].
	specialize (IH1 _ _ equ) as [v [Hv1 Hv2]].
	specialize (IH2 _ _ Hv2) as [w [Hw1 Hw2]].
	exists w; split; [exact (t_trans Hv1 Hw1)|exact Hw2].
Qed.
Lemma over_beta_rt_incr :
	forall u n v, (over_bcontext (union _ beta eta))^* (incr_bound u n) v ->
	exists w, (over_bcontext (union _ beta eta))^* u w /\ v = incr_bound w n.
Proof using.
	intros u n v H; remember (incr_bound u n) as u0 eqn:equ; generalize dependent n; generalize dependent u;
	  induction H as [u0 v0 H|u0|u0 v0 w0 _ IH1 _ IH2]; intros u n equ.
	1: subst; destruct (over_beta_incr _ _ _ H) as [v [Hv1 Hv2]]; exists v; split; [exact (rt_step Hv1)|exact Hv2].
	1: subst; refine (ex_intro _ _ (conj rt_refl eq_refl)).
	specialize (IH1 _ _ equ) as [v [Hv1 Hv2]].
	specialize (IH2 _ _ Hv2) as [w [Hw1 Hw2]].
	exists w; split; [exact (rt_trans Hv1 Hw1)|exact Hw2].
Qed.

Lemma betaeta_bsubstb_l :
	forall u u' n v, (over_bcontext (union _ beta eta))^* u u' ->
	(over_bcontext (union _ beta eta))^* (bsubstb u n v) (bsubstb u' n v).
Proof using.
	intros u u' n v H; induction H as [u u' H|u|u1 u2 u3 _ IH1 _ IH2].
	2: exact rt_refl.
	2: exact (rt_trans IH1 IH2).
	refine (rt_step _).
	generalize dependent v; generalize dependent n;
	  induction H as [u u' H|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH]; intros n v.
	- destruct H as [H|H].
	  1: inversion H; subst; cbn.
	  1: rewrite (bsubstb_comm (le_0_n _)).
	  1: exact (bctx_step (or_introl (Beta _ _))).
	  inversion H; subst; cbn.
	  rewrite <-(incr_bsubstb_ge (le_0_n _)).
	  exact (bctx_step (or_intror (Eta _))).
	- exact (bctx_app_l (IH _ _)).
	- exact (bctx_app_r (IH _ _)).
	- exact (bctx_abs (IH _ _)).
Qed.
Lemma betastar_bsubstb_r :
	forall u n v v', (over_bcontext (union _ beta eta))^* v v' ->
	(over_bcontext (union _ beta eta))^* (bsubstb u n v) (bsubstb u n v').
Proof using.
	assert (tmp : forall u u' n, (over_bcontext (union _ beta eta))^* u u' -> (over_bcontext (union _ beta eta))^* (incr_bound u n) (incr_bound u' n)).
	{ intros u u' n H; induction H as [u u' H|u|u u' u'' _ IH1 _ IH2].
	  2: exact rt_refl.
	  2: exact (rt_trans IH1 IH2).
	  refine (rt_step _).
	  generalize dependent n; induction H as [u u' [H|H]|u1 u1' u2 H IH|u1 u2 u2' H IH|u u' H IH]; intros n.
	  - inversion H; subst; cbn; rewrite (incr_bsubstb_le (le_0_n _)); exact (bctx_step (or_introl (Beta _ _))).
	  - inversion H; subst; cbn; rewrite <-(incr_bound_comm (le_0_n _)); exact (bctx_step (or_intror (Eta _))).
	  - exact (bctx_app_l (IH _)).
	  - exact (bctx_app_r (IH _)).
	  - exact (bctx_abs (IH _)). }
	intros u;
	  induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v v' Hv.
	1: exact rt_refl.
	1: unfold bsubstb; destruct (k <? n); [exact rt_refl|destruct (k =? n); [exact Hv|exact rt_refl]].
	1: cbn; specialize (IH1 n _ _ Hv); specialize (IH2 n _ _ Hv);
	     match goal with |- clos_refl_trans _ (BApp ?u ?v) (BApp ?u' ?v') =>
	       remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv' end.
	1: refine (rt_trans (y:=BApp u0' v0) _ _); [rename IH1 into H|rename IH2 into H]; clear - H.
	3: cbn; specialize (IH (S n) _ _ (tmp _ _ O Hv)); rename IH into H.
	3: match goal with |- clos_refl_trans _ (BAbs ?u) (BAbs ?u') =>
	     remember u as u0 eqn:equ; remember v as v0 eqn:eqv; remember u' as u0' eqn:equ'; remember v' as v0' eqn:eqv'; clear - H end.
	1,2,3: induction H as [u v H|u|u v w _ IH1 _ IH2]; [refine (rt_step _)|exact rt_refl|exact (rt_trans IH1 IH2)].
	1: exact (bctx_app_l H).
	1: exact (bctx_app_r H).
	1: exact (bctx_abs H).
Qed.

Lemma bsubstb_pbsubstb : forall u n v f,
	bsubstb (pbsubstb u f) n v = pbsubstb u (fun k => bsubstb (f k) n v).
Proof using.
	intros u; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros n v f.
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ (IH1 _ _ _) (IH2 _ _ _)).
	- cbn; f_equal; rewrite IH; apply pbsubstb_ext.
	  intros [|k]; [exact eq_refl|exact (eq_sym (incr_bsubstb_ge (le_0_n _)))].
Qed.

Lemma pbsubstb_id : forall u, pbsubstb u (fun n => BBound n) = u.
Proof using.
	intros u; induction u as [x|n|u IHu v IHv|u IH].
	- exact eq_refl.
	- exact eq_refl.
	- exact (f_equal2 _ IHu IHv).
	- refine (f_equal _ (eq_trans (pbsubstb_ext _ _ _ _) IH)); intros [|n]; exact eq_refl.
Qed.

Lemma typable_is_red : forall Gv G u F f, Gv ;; G |- {u} : {F} ->
	(forall n Fn, nth_error G n = Some Fn -> RED Fn (f n)) ->
	RED F (pbsubstb u f).
Proof using.
	intros Gv G u F f Hu Hf.
	generalize dependent f; induction Hu as [Gv G x F H|Gv G n F H|Gv G u1 u2 F1 F2 H1 IH1 H2 IH2|Gv G u F1 F2 H IH]; intros f Hf.
	- exact (RED_var _ _).
	- exact (Hf _ _ H).
	- exact (IH1 _ Hf _ (IH2 _ Hf)).
	- simpl pbsubstb; refine (RED_bsubstb _ _ _ _); intros v Hv; rewrite bsubstb_pbsubstb; refine (IH _ _).
	  intros [|n] Fn HFn; [injection HFn as <-; exact Hv|rewrite bsubstb_incr; exact (Hf _ _ HFn)].
Qed.
Corollary typable_is_sn : forall Gv G u F, Gv ;; G |- {u} : {F} -> SN u.
Proof using.
	intros Gv G u F Hu.
	rewrite <-pbsubstb_id; refine (proj1 (RED_is_CR _) _ (typable_is_red _ _ _ _ _ Hu _)).
	intros n Fn _; exact (RED_bound _ _).
Qed. *)
End ReductibilityCandidates.

(* Module TypeReqs <: FiniteSet.SetReqs.
Definition val := type.
Definition val_dec : forall v1 v2 : val, { v1 = v2 } + { v1 <> v2 }.
Proof using.
	intros v1; induction v1 as [b1|f11 IH1 f12 IH2]; intros [b2|f21 f22].
	1: destruct (B_dec b1 b2) as [Hb|Hb]; [left; f_equal; exact Hb|right; intros [=H]; exact (Hb H)].
	1,2: right; discriminate.
	specialize (IH1 f21) as [IH1|IH1]; [|right; intros [=H _]; exact (IH1 H)].
	specialize (IH2 f22) as [IH2|IH2]; [|right; intros [=_ H]; exact (IH2 H)].
	left; exact (f_equal2 _ IH1 IH2).
Qed.
End TypeReqs.
Module FiniteTypes := FiniteSet.Make TypeReqs.

Inductive NJm : list type -> type -> Prop :=
	| Ax : forall {ctx F}, In F ctx -> NJm ctx F
	| ArrowE : forall {ctx F1 F2}, NJm ctx (TArrow F1 F2) -> NJm ctx F1 -> NJm ctx F2
	| ArrowI : forall {ctx F1 F2}, NJm (F1 :: ctx) F2 -> NJm ctx (TArrow F1 F2).

Lemma NJm_iff : forall ctx F, NJm ctx F <-> exists u, VarMap.empty ;; ctx |- {u} : {F}.
Proof using.
	intros ctx F; split.
	- intros H; induction H as [ctx F H|ctx F1 F2 H1 [u1 Hu1] H2 [u2 Hu2]|ctx F1 F2 H [u Hu]].
	  + induction ctx as [|F1 ctx IH]; [contradiction H|cbn in H; destruct H as [<-|H]].
	    1: exists (BBound O); exact (TPBound _ (_ :: _) O eq_refl).
	    specialize (IH H) as [u Hu]; exact (ex_intro _ _ (proj1 (typable_incr _ [] _ _ _ _) Hu)).
	  + exact (ex_intro _ _ (TPApp Hu1 Hu2)).
	  + exact (ex_intro _ _ (TPAbs Hu)).
	- intros [u Hu]; remember VarMap.empty as vctx eqn:eqvctx;
	    induction Hu as [vctx ctx x F H|vctx ctx n F H|vctx ctx u v F1 F2 H1 IH1 H2 IH2|vctx ctx u F1 F2 H IH]; subst vctx.
	  + contradiction (VarMap.mem_empty _ (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H))).
	  + refine (Ax _); generalize dependent ctx; induction n as [|n IHn]; (intros [|F1 ctx]; [discriminate 1|intros H]).
	    1: left; injection H as H; exact (eq_sym H).
	    right; exact (IHn _ H).
	  + exact (ArrowE (IH1 eq_refl) (IH2 eq_refl)).
	  + exact (ArrowI (IH eq_refl)).
Qed.

Corollary NJm_coherent : B -> exists F, ~ NJm [] F.
Proof using.
	intros b; exists (TSimple b); rewrite NJm_iff; intros [u Hu].
	assert (tmp := fun H2 => RewriteSystem.strong_normalizable_is_normalizable
	          eq _ (Hr:=Build_Respects _ eq _ (over_bcontext (union _ beta eta)) ltac:(intros ? ? ? ? <- <-; split; exact (fun H => H)))
	          H2 _ (typable_is_sn _ _ _ _ Hu)).
	match type of tmp with ?h -> _ => assert (tmp1 : h); [|specialize (tmp tmp1); clear tmp1] end.
	1:{ clear; intros u; induction u as [x|n|u IHu v IHv|u IH].
	    1,2: left; intros v Hv; inversion Hv; destruct H as [H|H]; inversion H.
	    1: destruct IHu as [IHu|[u' IHu]]; [|right; refine (ex_intro _ _ (bctx_app_l IHu))].
	    1: destruct IHv as [IHv|[v' IHv]]; [|right; refine (ex_intro _ _ (bctx_app_r IHv))].
	    1: destruct u as [x|n|u1 u2|u]; [| | |right; refine (ex_intro _ _ (bctx_step (or_introl (Beta _ _))))].
	    1-3: left; intros uv' Huv'; inversion Huv'; [destruct H as [H|H]; inversion H|exact (IHu _ H2)|exact (IHv _ H2)].
	    destruct IH as [IH|[u' IH]]; [|right; refine (ex_intro _ _ (bctx_abs IH))].
	    assert (tmp : (forall y, ~ eta (BAbs u) y) -> RewriteSystem.normal_form (over_bcontext (union _ beta eta)) (BAbs u))
	      by (intros H y Hy; inversion Hy; [destruct H0 as [H0|H0]; [inversion H0|exact (H _ H0)]|exact (IH _ H1)]).
	    refine (match _ with
	            | or_introl H => or_introl (tmp H)
	            | or_intror (ex_intro _ u' Hu') =>
	                or_intror (ex_intro _ u'
	                  (eq_ind _ (fun a => over_bcontext _ (BAbs a) _) (bctx_step (or_intror (Eta _))) u (eq_sym Hu'))) end); clear IH tmp.
	    assert (tmp : forall y, u <> BApp (incr_bound y O) (BBound O) -> ~ eta (BAbs u) y)
	      by (intros y Hy H; inversion H; subst; exact (Hy eq_refl)).
	    refine (match _ with or_introl H => or_introl (fun y => tmp y (H y)) | or_intror H => or_intror H end); clear tmp.
	    destruct u as [x|n|u1 u2|u].
	    1,2,4: left; intros u'; discriminate.
	    destruct u2 as [x|[|n]|u21 u22|u2].
	    1,3,4,5: left; intros u'; discriminate.
	    refine (match (_ : (forall u', u1 <> incr_bound u' O) \/ _) with
	            | or_introl H => ltac:(left; intros u' [=f]; exact (H _ f))
	            | or_intror (ex_intro _ u' H) => or_intror (ex_intro _ u' (f_equal (fun a => BApp a _) H)) end).
	    generalize O.
	    induction u1 as [x|k|u1 IH1 u2 IH2|u IH]; intros n.
	    1: right; exists (BVar x); exact eq_refl.
	    1: remember (n <=? k) as tmp eqn:eqtmp; symmetry in eqtmp; destruct tmp as [|].
	    1: apply leb_le in eqtmp; inversion eqtmp; subst.
	    1: clear eqtmp; left; intros [| | |]; try discriminate; intros [=f]; remember (k <=? n) as tmp eqn:eqtmp; destruct tmp.
	    1: subst; apply eq_sym, leb_le in eqtmp; exact (lt_neq _ _ eqtmp eq_refl).
	    1: subst; apply eq_sym, leb_gt in eqtmp; exact (lt_neq _ _ eqtmp eq_refl).
	    1: right; exists (BBound m); cbn; rewrite (proj2 (leb_le _ _) H); exact eq_refl.
	    1: right; exists (BBound k); cbn; rewrite eqtmp; exact eq_refl.
	    1: specialize (IH1 n) as [IH1|[u1' ->]].
	    1: left; intros [| | |]; try discriminate; intros [=f _]; exact (IH1 _ f).
	    1: specialize (IH2 n) as [IH2|[u2' ->]].
	    1: left; intros [| | |]; try discriminate; intros [=_ f]; exact (IH2 _ f).
	    1: right; exact (ex_intro _ (BApp u1' u2') eq_refl).
	    specialize (IH (S n)) as [IH|[u' ->]].
	    1: left; intros [| | |]; try discriminate; intros [=f]; exact (IH _ f).
	    right; exact (ex_intro _ (BAbs u') eq_refl). }
	destruct tmp as [u' [Rsuu' Hu']].
	assert (Tu' : VarMap.empty ;; [] |- {u'} : {TSimple b}).
	{ clear Hu'; induction Rsuu' as [u v H|u|u v w _ IH1 _ IH2]; [|exact Hu|exact (IH2 (IH1 Hu))].
	  apply over_bcontext_union in H; destruct H as [H|H]; [exact (autored_beta _ _ _ _ _ Hu H)|exact (autored_eta _ _ _ _ _ Hu H)]. }
	clear u Hu Rsuu'; rename u' into u, Hu' into Hnu, Tu' into Hu.
	inversion Hu as [vctx ctx x F H eq1 eq2 eq3|vctx ctx n F H eq1 eq2 eq3|vctx ctx u1 u2 F1 F2 H1 H2 eq1 eq2 eq3|]; subst.
	1: contradiction (VarMap.mem_empty _ (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H))).
	1: destruct n; discriminate H.
	remember (TSimple b) as F2 eqn:eqF2; clear b eqF2 Hu.
	remember (TArrow F1 F2) as F1F2 eqn:eqF.
	remember (@nil type) as ctx eqn:eqctx.
	generalize dependent F2; generalize dependent F1; generalize dependent u2;
	  remember VarMap.empty as vctx;
	  induction H1 as [vctx ctx x F H|vctx ctx n F H|vctx ctx u11 u12 F11 F12 H11 IH1 H12 IH2|vctx ctx u1 F11 F12 H IH];
	  intros u2 Hnu F1 H2 F2 eq; subst.
	1: contradiction (VarMap.mem_empty _ (proj1 (proj1 (VarMap.find_opt_Some _ _ _) H))).
	1: destruct n; discriminate H.
	2: exact (Hnu _ (bctx_step (or_introl (Beta _ _)))).
	exact (IH1 eq_refl eq_refl _ (fun y Hy => Hnu _ (bctx_app_l Hy)) _ H12 _ eq_refl).
Qed.

Fixpoint eval_type f F : bool := match F with
	| TSimple b => f b
	| TArrow F1 F2 => orb (negb (eval_type f F1)) (eval_type f F2)
end.
Lemma NJm_eval_type : forall ctx F, NJm ctx F -> forall f, (forall Fi, In Fi ctx -> eval_type f Fi = true) -> eval_type f F = true.
Proof using.
	intros ctx F HF f Hctx; induction HF as [ctx b H|ctx F1 F2 H1 IH1 H2 IH2|ctx F1 F H IH].
	- exact (Hctx _ H).
	- specialize (IH1 Hctx); specialize (IH2 Hctx); cbn in IH1; rewrite IH2 in IH1; exact IH1.
	- specialize (fun H => IH (fun Fi HFi => match HFi with
	                            | or_introl H' => eq_ind _ _ H _ (eq_sym H') | or_intror H => Hctx _ H end)); cbn in IH.
	  cbn; destruct (eval_type f F1); [exact (IH eq_refl)|exact eq_refl].
Qed.
Corollary NJm_coherent' : B -> exists F, ~ NJm [] F.
Proof using.
	intros b; exists (TSimple b); intros H; discriminate (NJm_eval_type _ _ H (fun _ => false) ltac:(intros _ [])).
Qed. *)
(* 
Lemma typ_app_inv_rect : forall Gv G u v F, Gv ;; G |- {u} {v} : {F} -> { F1 | Gv ;; G |- {u} : {F1} => {F} /\ Gv ;; G |- {v} : {F1} }.
Proof using.
	intros Gv G u v F H; inversion H as [| |Gv' G' u' v' F1 F2 H1 H2|]; subst; exists F1; split; assumption.
Qed.
Lemma typ_abs_inv_rect : forall Gv G u F, Gv ;; G |- {BAbs u} : {F} -> { F1 & { F2 & (F = TArrow F1 F2) * Gv ;; (F1 :: G) |- {u} : {F2} }%type }.
Proof using.
	intros Gv G u F H; destruct F as [b|F1 F2]; [exfalso; inversion H|].
	exists F1, F2; split; [exact eq_refl|].
	inversion H; exact H4.
Qed.

Module UNorm := UntypedNorm.UntypedNorm UntypedL.
Definition eta_long Gv G u F : Gv ;; G |- {u} : {F} -> RewriteSystem.normal_form (over_bcontext beta) u -> bterm.
Proof using.
	(* intros H Hnorm; apply UNorm.normal_form_iff in Hnorm; destruct Hnorm as [Hnhf Hnargs].
	unfold UNorm.normal_head_form in Hnhf. *)
	(* generalize dependent F; generalize dependent G; induction u as [x|n|u IHu v IHv|u IH]; intros Gv G F H Hnorm. *)
	generalize dependent F; generalize dependent G;
	  refine ((fun from_b => UNorm.bterm_head_rect (fun u => _) _ (fun n G F _ _ => from_b n F) _ u) _); clear u; swap 2 3.
	- intros x _ F _ _.
	  refine (let args := _ in UNorm.of_head_form (length args) (BVar x) args).
	  induction F as [b|F1 _ F2 IH2].
	  1: exact [].
	  exact (List.map (fun v => incr_bound v O) IH2 ++ [from_b O F1]).
	- intros n F.
	  refine (let args := _ in UNorm.of_head_form (length args) (BBound (length args + n)) args).
	  clear n; induction F as [b|F1 IH1 F2 IH2].
	  1: exact [].
	  exact (List.map (fun v => incr_bound v O) IH2 ++ [UNorm.of_head_form (length IH1) (BBound (length IH1)) IH1]).
	- intros u Hhd Hargs G F Hu Hnorm.
	  specialize (UNorm.of_head_form_head_form u).
	  apply UNorm.normal_form_iff in Hnorm; destruct Hnorm as [Hnhd Hntl].
	  unfold UNorm.normal_head_form, UNorm.of_head_form in Hnhd.
	  remember (UNorm.nlambdas u) as nl eqn:eql;
	  remember (UNorm.skip_apps (UNorm.skip_lambdas u)) as hd eqn:eqh;
	  remember (UNorm.acc_apps (UNorm.skip_lambdas u)) as ar eqn:eqa;
	  clear eql eqh eqa; intros <-.
	  assert (tmp : { G' & { F' | Gv ;; G' ++ G |- {hd} : {F'} } }).
	  { unfold UNorm.of_head_form in Hu.
	  generalize dependent G; generalize dependent F; induction nl as [|nl IH]; intros F G Hu.
	  2: apply typ_abs_inv_rect in Hu.
	  2: destruct Hu as [F1 [F2 [-> Hu]]]; specialize (IH _ _ Hu) as [G' [F' IH]]; refine (existT _ (G' ++ [F1]) (exist _ F' _)).
	  2: rewrite app_assoc; exact IH.
	  unfold UNorm.add_lambdas in Hu.
	  generalize dependent F; induction ar as [|atl ar IH]; intros F Hu.
	  2: apply typ_abs_inv_rect in Hu.
	  2: destruct Hu as [F1 [F2 [-> Hu]]]; specialize (IH _ _ Hu) as [G' [F' IH]]; refine (existT _ (G' ++ [F1]) (exist _ F' _)).
	  2: rewrite app_assoc; exact IH.
	  unfold UNorm.add_lambdas in Hu.
	  }
Defined.
Fixpoint eta_long G u0 args := match F with
	| TSimple _ => (O, u0, args)
	| TArrow F1 F2 => match args with
		| hd :: tl => let (nls, u0, tl) := eta_long F2 u0 tl in (S nls, u0, (hd :: tl))
		| [] => let (nls, u0, args) := eta_long F2 u0 [] in (S nls, incr_bound u0 O, (eta_long F1 (BBound O) [] :: List.map (fun v => incr_bound v O) args))
	end
end.

Lemma eta_long_wd : forall u F, (over_bcontext eta)^* (eta_long u F) u.
Proof using.
	intros u F; generalize dependent u; induction F as [b|F1 _ F2 IH2]; intros u.
	1: exact rt_refl.
	destruct u as [x|n|u v|u]; cbn.
	4: exact (clos_rt_over_bcontext_ctx (BCAbs BCHole) (IH2 _)).
	1-3: refine (rt_trans (clos_rt_over_bcontext_ctx (BCAbs (BCApp_l BCHole _)) _) (rt_step (bctx_step (Eta _)))).
	1-3: exact (IH2 _).
Qed.

Lemma eta_long_typable : forall Gv G u F, Gv ;; G |- {u} : {F} -> Gv ;; G |- {eta_long u F} : {F}.
Proof using.
	intros Gv G u F; generalize dependent G.
Qed. *)

End TypedLambdaC.
