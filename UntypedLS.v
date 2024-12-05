Require Import Parametrization. Require Assoc. Require RewriteSystem.
Require Import Relations.
Require Import Untyped.
Require Streams.

Declare Custom Entry bstack.

Module UntypedLambdaSigma (UntypedL : UntypedLambdaT).
Module U := UntypedL.
Module Export Vars := U.Vars.
Module VarMapReqs <: Assoc.AssocReqs.
Definition key := V.
Definition key_dec := dec_V.
End VarMapReqs.
Module VarMap := Assoc.Make(VarMapReqs).

Unset Elimination Schemes.
Inductive bterm : Type :=
	| BVar : V -> bterm
	| BZero : bterm
	| BApp : bterm -> bterm -> bterm
	| BAbs : bterm -> bterm
	| BSubst : bterm -> bstack -> bterm
with bstack : Type :=
	| Sid : bstack
	| Sdot : bterm -> bstack -> bstack
	| Sshift : bstack
	| Scomp : bstack -> bstack -> bstack.
Scheme bterm_ind := Induction for bterm Sort Prop
  with bstack_ind := Induction for bstack Sort Prop.
Scheme bterm_ind0 := Induction for bterm Sort Prop.
Scheme bstack_ind0 := Induction for bstack Sort Prop.
Combined Scheme bval_mutind from bterm_ind,bstack_ind.

Fixpoint nat_to_bound_aux n := match n with
	| O => Sshift
	| S n => Scomp Sshift (nat_to_bound_aux n)
end.
Definition nat_to_bound n := match n with
	| O => BZero
	| S n => BSubst BZero (nat_to_bound_aux n)
end.

Module Import UntypedBNotation.
Notation "<{  b  }>" := b (b custom bterms at level 3).
Notation "<[  s  ]>" := s (s custom bstack at level 2).

Notation "{ v }" := v (in custom bterms at level 0, v constr).
Notation "( v )" := v (in custom bterms at level 0, v custom bterms at level 3).
Notation "'O'" := (BZero) (in custom bterms at level 0).
Notation "< n >" := (nat_to_bound n) (in custom bterms at level 0, n constr at level 1, format "< n >").
Notation "<! n >" := (BSubst BZero (nat_to_bound_aux n)) (in custom bterms at level 0, n constr at level 1, format "<! n >").
Notation "\ M" := (BAbs M) (in custom bterms at level 3, M custom bterms, format "\ M").
Notation "M N" := (BApp M N) (in custom bterms at level 2, M custom bterms, N custom bterms, left associativity).
Notation "M [ S ]" := (BSubst M S) (in custom bterms at level 1, M custom bterms, S custom bstack at level 2, format "M [ S ]").

Notation "/ v \" := v (in custom bstack at level 0, v constr, only parsing).
Notation "{ v }" := v (in custom bstack at level 0, v constr, only printing).
Notation "[ v ]" := v (in custom bstack at level 0, v custom bstack at level 2, only parsing).
Notation "( v )" := v (in custom bstack at level 0, v custom bstack at level 2, only printing).
Notation "'id'" := Sid (in custom bstack at level 0).
Notation "^" := Sshift (in custom bstack at level 0).
Notation "M  :  S" := (Sdot M S) (in custom bstack at level 1, M custom bterms at level 0, S custom bstack).
Notation "S  @  T" := (Scomp S T) (in custom bstack at level 2, S custom bstack, T custom bstack, right associativity).
End UntypedBNotation.

Unset Elimination Schemes.
Inductive tcontext : Type :=
	| TCHole
	| TCApp_l : tcontext -> bterm -> tcontext
	| TCApp_r : bterm -> tcontext -> tcontext
	| TCAbs : tcontext -> tcontext
	| TCSubst_l : tcontext -> bstack -> tcontext
	| TCSubst_r : bterm -> tscontext -> tcontext
with tscontext : Type :=
	| TSCdot_l : tcontext -> bstack -> tscontext
	| TSCdot_r : bterm -> tscontext -> tscontext
	| TSCcomp_l : tscontext -> bstack -> tscontext
	| TSCcomp_r : bstack -> tscontext -> tscontext.
Scheme tcontext_ind := Induction for tcontext Sort Prop
  with tscontext_ind := Induction for tscontext Sort Prop.
Scheme tcontext_ind0 := Induction for tcontext Sort Prop.
Scheme tscontext_ind0 := Induction for tscontext Sort Prop.
Combined Scheme tcontext_mutind from tcontext_ind,tscontext_ind.

Inductive stcontext : Type :=
	| STCApp_l : stcontext -> bterm -> stcontext
	| STCApp_r : bterm -> stcontext -> stcontext
	| STCAbs : stcontext -> stcontext
	| STCSubst_l : stcontext -> bstack -> stcontext
	| STCSubst_r : bterm -> scontext -> stcontext
with scontext : Type :=
	| SCHole
	| SCdot_l : stcontext -> bstack -> scontext
	| SCdot_r : bterm -> scontext -> scontext
	| SCcomp_l : scontext -> bstack -> scontext
	| SCcomp_r : bstack -> scontext -> scontext.
Scheme stcontext_ind := Induction for stcontext Sort Prop
  with sstcontext_ind := Induction for scontext Sort Prop.
Scheme stcontext_ind0 := Induction for stcontext Sort Prop.
Scheme sstcontext_ind0 := Induction for scontext Sort Prop.
Combined Scheme scontext_mutind from stcontext_ind,sstcontext_ind.
Set Elimination Schemes.

Fixpoint subst_tcontext (c : tcontext) (t : bterm) := match c with
	| TCHole => t
	| TCApp_l c v => BApp (subst_tcontext c t) v
	| TCApp_r u c => BApp u (subst_tcontext c t)
	| TCAbs c => BAbs (subst_tcontext c t)
	| TCSubst_l c s => BSubst (subst_tcontext c t) s
	| TCSubst_r u c => BSubst u (subst_tscontext c t)
end with subst_tscontext (c : tscontext) (t : bterm) := match c with
	| TSCdot_l c s => Sdot (subst_tcontext c t) s
	| TSCdot_r u c => Sdot u (subst_tscontext c t)
	| TSCcomp_l c s => Scomp (subst_tscontext c t) s
	| TSCcomp_r s c => Scomp s (subst_tscontext c t)
end.
Fixpoint subst_stcontext (c : stcontext) (t : bstack) := match c with
	| STCApp_l c v => BApp (subst_stcontext c t) v
	| STCApp_r u c => BApp u (subst_stcontext c t)
	| STCAbs c => BAbs (subst_stcontext c t)
	| STCSubst_l c s => BSubst (subst_stcontext c t) s
	| STCSubst_r u c => BSubst u (subst_scontext c t)
end with subst_scontext (c : scontext) (t : bstack) := match c with
	| SCHole => t
	| SCdot_l c s => Sdot (subst_stcontext c t) s
	| SCdot_r u c => Sdot u (subst_scontext c t)
	| SCcomp_l c s => Scomp (subst_scontext c t) s
	| SCcomp_r s c => Scomp s (subst_scontext c t)
end.

Fixpoint csubst_tcontext (c : tcontext) (t : tcontext) := match c with
	| TCHole => t
	| TCApp_l c v => TCApp_l (csubst_tcontext c t) v
	| TCApp_r u c => TCApp_r u (csubst_tcontext c t)
	| TCAbs c => TCAbs (csubst_tcontext c t)
	| TCSubst_l c s => TCSubst_l (csubst_tcontext c t) s
	| TCSubst_r u c => TCSubst_r u (csubst_tscontext c t)
end with csubst_tscontext (c : tscontext) (t : tcontext) := match c with
	| TSCdot_l c s => TSCdot_l (csubst_tcontext c t) s
	| TSCdot_r u c => TSCdot_r u (csubst_tscontext c t)
	| TSCcomp_l c s => TSCcomp_l (csubst_tscontext c t) s
	| TSCcomp_r s c => TSCcomp_r s (csubst_tscontext c t)
end.
Fixpoint csubst_stcontext (c : stcontext) (t : scontext) := match c with
	| STCApp_l c v => STCApp_l (csubst_stcontext c t) v
	| STCApp_r u c => STCApp_r u (csubst_stcontext c t)
	| STCAbs c => STCAbs (csubst_stcontext c t)
	| STCSubst_l c s => STCSubst_l (csubst_stcontext c t) s
	| STCSubst_r u c => STCSubst_r u (csubst_scontext c t)
end with csubst_scontext (c : scontext) (t : scontext) := match c with
	| SCHole => t
	| SCdot_l c s => SCdot_l (csubst_stcontext c t) s
	| SCdot_r u c => SCdot_r u (csubst_scontext c t)
	| SCcomp_l c s => SCcomp_l (csubst_scontext c t) s
	| SCcomp_r s c => SCcomp_r s (csubst_scontext c t)
end.

Unset Elimination Schemes.
Inductive over_tcontext {Rt : relation bterm} {Rs : relation bstack} | : relation bterm :=
	| tc_step : forall {u v}, Rt u v -> over_tcontext u v
	| tc_app_l : forall {u u'} [v], over_tcontext u u' -> over_tcontext (BApp u v) (BApp u' v)
	| tc_app_r : forall [u] {v v'}, over_tcontext v v' -> over_tcontext (BApp u v) (BApp u v')
	| tc_abs : forall {u u'}, over_tcontext u u' -> over_tcontext (BAbs u) (BAbs u')
	| tc_subst_l : forall {u u'} [s], over_tcontext u u' -> over_tcontext (BSubst u s) (BSubst u' s)
	| tc_subst_r : forall [u] {s s'}, over_scontext s s' -> over_tcontext (BSubst u s) (BSubst u s')
with over_scontext {Rt : relation bterm} {Rs : relation bstack} | : relation bstack :=
	| sc_step : forall {s t}, Rs s t -> over_scontext s t
	| sc_dot_l : forall {u u'} [s], over_tcontext u u' -> over_scontext (Sdot u s) (Sdot u' s)
	| sc_dot_r : forall [u] {s s'}, over_scontext s s' -> over_scontext (Sdot u s) (Sdot u s')
	| sc_comp_l : forall {s s'} [t], over_scontext s s' -> over_scontext (Scomp s t) (Scomp s' t)
	| sc_comp_r : forall [s] {t t'}, over_scontext t t' -> over_scontext (Scomp s t) (Scomp s t').
Arguments over_tcontext Rt Rs : clear implicits.
Arguments over_scontext Rt Rs : clear implicits.
Scheme over_tcontext_ind := Induction for over_tcontext Sort Prop
  with over_scontext_ind := Induction for over_scontext Sort Prop.
Scheme over_tcontext_ind0 := Induction for over_tcontext Sort Prop.
Scheme over_scontext_ind0 := Induction for over_scontext Sort Prop.
Combined Scheme over_context_mutind from over_tcontext_ind,over_scontext_ind.
Set Elimination Schemes.

Lemma over_tcontext_iff : forall Rt Rs,
	(forall u v, over_tcontext Rt Rs u v <->
		(exists c u' v', u = subst_tcontext c u' /\ v = subst_tcontext c v' /\ Rt u' v') \/
		(exists c s' t', u = subst_stcontext c s' /\ v = subst_stcontext c t' /\ Rs s' t')) /\
	(forall s t, over_scontext Rt Rs s t <->
		(exists c u' v', s = subst_tscontext c u' /\ t = subst_tscontext c v' /\ Rt u' v') \/
		(exists c s' t', s = subst_scontext c s' /\ t = subst_scontext c t' /\ Rs s' t')).
Proof using.
	intros Rt Rs;
	  refine (match _ with conj H1 H2 =>
	            conj (fun u v => conj (proj1 H1 u v) (proj1 H2 u v)) (fun s t => conj (proj2 H1 s t) (proj2 H2 s t)) end); split.
	- refine (over_context_mutind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
	  + intros u v Ruv; left; exact (ex_intro _ TCHole (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl Ruv))))).
	  + intros u1 u2 v _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TCApp_l c v) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (STCApp_l c v) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u v1 v2 _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TCApp_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (STCApp_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u v _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TCAbs c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (STCAbs c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u1 u2 s _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TCSubst_l c s) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (STCSubst_l c s) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u s1 s2 _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TCSubst_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (STCSubst_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros s t Rst; right; exact (ex_intro _ SCHole (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl Rst))))).
	  + intros u1 u2 s _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TSCdot_l c s) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (SCdot_l c s) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u s1 s2 _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TSCdot_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (SCdot_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u1 u2 s _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TSCcomp_l c s) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (SCcomp_l c s) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	  + intros u s1 s2 _ [(c & u' & v' & -> & -> & IH)|(c & s' & t' & -> & -> & IH)]; [left|right].
	    1: exact (ex_intro _ (TSCcomp_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	    1: exact (ex_intro _ (SCcomp_r u c) (ex_intro _ _ (ex_intro _ _ (conj eq_refl (conj eq_refl IH))))).
	- assert (tmp : forall A B C R f (u v : C) (H : C -> C -> Prop), (forall (c : A) (u' v' : B), R u' v' -> H (f c u') (f c v')) ->
	                          (exists c u' v', u = f c u' /\ v = f c v' /\ R u' v') -> H u v)
	      by (intros A B C R f u v H H1 (c & u' & v' & -> & -> & H2); exact (H1 _ _ _ H2)).
	  refine (match _ with conj H1 H2 =>
	      conj (fun u v => or_ind (tmp _ _ _ _ _ _ _ _ (proj1 H1)) (tmp _ _ _ _ _ _ _ _ (proj1 H2)))
	           (fun s t => or_ind (tmp _ _ _ _ _ _ _ _ (proj2 H1)) (tmp _ _ _ _ _ _ _ _ (proj2 H2))) end); clear tmp.
	  split; [refine (tcontext_mutind _ _ _ _ _ _ _ _ _ _ _ _)|refine (scontext_mutind _ _ _ _ _ _ _ _ _ _ _ _)].
	  + intros u v Ruv; exact (tc_step Ruv).
	  + intros c IH v u1 u2 Ru; exact (tc_app_l (IH _ _ Ru)).
	  + intros u c IH v1 v2 Rv; exact (tc_app_r (IH _ _ Rv)).
	  + intros c IH u v Ruv; exact (tc_abs (IH _ _ Ruv)).
	  + intros c IH s u1 u2 Ru; exact (tc_subst_l (IH _ _ Ru)).
	  + intros u c IH s1 s2 Rss; exact (tc_subst_r (IH _ _ Rss)).
	  + intros c IH s u1 u2 Ru; exact (sc_dot_l (IH _ _ Ru)).
	  + intros u c IH s1 s2 Rss; exact (sc_dot_r (IH _ _ Rss)).
	  + intros c IH t s1 s2 Rss; exact (sc_comp_l (IH _ _ Rss)).
	  + intros s c IH t1 t2 Rtt; exact (sc_comp_r (IH _ _ Rtt)).
	  + intros c IH v u1 u2 Ru; exact (tc_app_l (IH _ _ Ru)).
	  + intros u c IH v1 v2 Rv; exact (tc_app_r (IH _ _ Rv)).
	  + intros c IH u v Ruv; exact (tc_abs (IH _ _ Ruv)).
	  + intros c IH s u1 u2 Ru; exact (tc_subst_l (IH _ _ Ru)).
	  + intros u c IH s1 s2 Rss; exact (tc_subst_r (IH _ _ Rss)).
	  + intros s t Rst; exact (sc_step Rst).
	  + intros c IH s u1 u2 Ru; exact (sc_dot_l (IH _ _ Ru)).
	  + intros u c IH s1 s2 Rss; exact (sc_dot_r (IH _ _ Rss)).
	  + intros c IH t s1 s2 Rss; exact (sc_comp_l (IH _ _ Rss)).
	  + intros s c IH t1 t2 Rtt; exact (sc_comp_r (IH _ _ Rtt)).
Qed.

Inductive sigma_stack : bstack -> bstack -> Prop :=
	| Sshapp : forall N S, sigma_stack <[ ^ @ [{N} : /S\] ]> S
	| Sdotcomp : forall N S S', sigma_stack <[ [{N} : /S\] @ /S'\ ]> <[ {N}[/S'\] : [/S\ @ /S'\] ]>
	| Scompcomp : forall S1 S2 S3, sigma_stack (Scomp (Scomp S1 S2) S3) (Scomp S1 (Scomp S2 S3))
	| Sidl : forall S, sigma_stack <[ id @ /S\ ]> S
	| Sidr : forall S, sigma_stack <[ /S\ @ id ]> S
	| Szerosh : sigma_stack <[ O : ^ ]> <[id]>
	| Ssubstsh : forall S, sigma_stack <[ O[/S\] : [^ @ /S\] ]> S.
Inductive sigma : bterm -> bterm -> Prop :=
	| SEval : forall N S, sigma (BSubst BZero (Sdot N S)) N
	| SApp : forall M N S, sigma (BSubst (BApp M N) S) (BApp (BSubst M S) (BSubst N S))
	| SAbs : forall M S, sigma (BSubst (BAbs M) S) (BAbs (BSubst M (Sdot BZero (Scomp S Sshift))))
	| SSubst2 : forall M S1 S2, sigma (BSubst (BSubst M S1) S2) (BSubst M (Scomp S1 S2))
	| SSubstId : forall M, sigma (BSubst M Sid) M.
Inductive beta : bterm -> bterm -> Prop :=
	| SBeta : forall M N, beta (BApp (BAbs M) N) (BSubst M <[{N} : id]>).

Lemma local_confluence_sigma_csigma :
	forall u u1 u2, sigma u u1 -> over_tcontext sigma sigma_stack u u2 ->
	exists w, ((over_tcontext sigma sigma_stack)^+ u1 w \/ u1 = w) /\ ((over_tcontext sigma sigma_stack)^+ u2 w \/ u2 = w).
Proof using.
	intros u u1 u2 H1 H2; inversion H1 as [m s|m n s|m s|m s1 s2|m]; subst.
	- inversion H2; clear H2; subst.
	  1: inversion H; subst; exists u2; split; right; exact eq_refl.
	  1: inversion H4; inversion H.
	  inversion H4; clear H4; subst.
	  1: inversion H; clear H; subst.
	  1: exists BZero; split; [right; exact eq_refl|left; exact (t_step (tc_step (SSubstId _)))].
	  1: exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1: exists u'; split; left; [exact (t_step H3)|exact (t_step (tc_step (SEval _ _)))].
	  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_step (tc_step (SEval _ _)))))).
	- inversion H2; clear H2; subst.
	  1: inversion H; clear H; subst;
	       [exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl)))|].
	  1:  refine (ex_intro _ _ (conj (or_introl (t_trans (t_step _) (t_step _))) (or_intror eq_refl))).
	  1:   exact (tc_app_l (tc_step (SSubstId _))).
	  1:  exact (tc_app_r (tc_step (SSubstId _))).
	  1: inversion H4; clear H4; subst.
	  1:   inversion H.
	  1:  refine (ex_intro _ _ (conj (or_introl (t_step (tc_app_l (tc_subst_l H3)))) _)).
	  1:   exact (or_introl (t_step (tc_step (SApp _ _ _)))).
	  1:  refine (ex_intro _ _ (conj (or_introl (t_step (tc_app_r (tc_subst_l H3)))) _)).
	  1:   exact (or_introl (t_step (tc_step (SApp _ _ _)))).
	  refine (ex_intro _ _ (conj _ (or_introl (t_step (tc_step (SApp _ _ _)))))).
	  left; refine (t_trans (t_step (tc_app_l _)) (t_step (tc_app_r _))).
	  1,2: exact (tc_subst_r H4).
	- inversion H2; clear H2; subst.
	  1: inversion H; [exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl)))|clear H; subst].
	  1:  refine (ex_intro _ _ (conj (or_introl _) (or_intror eq_refl))).
	  1:  refine (t_trans (t_step (tc_abs (tc_subst_r (sc_dot_r (sc_step (Sidl _)))))) _).
	  1:  refine (t_trans (t_step (tc_abs (tc_subst_r (sc_step Szerosh)))) _).
	  1:  exact (t_step (tc_abs (tc_step (SSubstId _)))).
	  1: inversion H4; [inversion H|clear H4; subst].
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step (tc_abs (tc_subst_l H0)))) (or_introl (t_step (tc_step (SAbs _ _)))))).
	  exact (ex_intro _ _ (conj (or_introl (t_step (tc_abs (tc_subst_r (sc_dot_r (sc_comp_l H4))))))
	                            (or_introl (t_step (tc_step (SAbs _ _)))))).
	- inversion H2; clear H2; subst.
	  1: inversion H; [exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl)))|].
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step (tc_subst_r (sc_step (Sidr _))))) (or_intror eq_refl))).
	  1: inversion H4; clear H4; subst.
	  1:   inversion H; clear H; subst.
	  1:       refine (ex_intro _ _ (conj (or_introl _) (or_intror eq_refl))).
	  1:       refine (t_trans (t_step (tc_subst_r (sc_step (Sdotcomp _ _ _)))) _).
	  1:       exact (t_step (tc_step (SEval _ _))).
	  1:      refine (ex_intro _ _ (conj (or_introl (t_step (tc_step (SApp _ _ _)))) (or_introl _))).
	  1:      refine (t_trans (t_step (tc_step (SApp _ _ _))) _).
	  1:      refine (t_trans (t_step (tc_app_l (tc_step (SSubst2 _ _ _)))) _).
	  1:      exact (t_step (tc_app_r (tc_step (SSubst2 _ _ _)))).
	  1:     refine (ex_intro _ _ (conj (or_introl _) (or_introl _))).
	  1:     exact (t_trans (t_step (tc_step (SAbs _ _))) (t_step (tc_abs (tc_subst_r (sc_dot_r (sc_step (Scompcomp _ _ _))))))).
	  1:     refine (t_trans (t_step (tc_step (SAbs _ _))) _).
	  1:     refine (t_trans (t_step (tc_abs (tc_step (SSubst2 _ _ _)))) _).
	  1:     refine (t_trans (t_step (tc_abs (tc_subst_r (sc_step (Sdotcomp _ _ _))))) _).
	  1:     refine (t_trans (t_step (tc_abs (tc_subst_r (sc_dot_l (tc_step (SEval _ _)))))) _).
	  1:     refine (t_trans (t_step (tc_abs (tc_subst_r (sc_dot_r (sc_step (Scompcomp _ _ _)))))) _).
	  1:     exact (t_step (tc_abs (tc_subst_r (sc_dot_r (sc_comp_r (sc_step (Sshapp _ _))))))).
	  1:    refine (ex_intro _ _ (conj (or_introl (t_step (tc_step (SSubst2 _ _ _)))) (or_introl _))).
	  1:    refine (t_trans (t_step (tc_step (SSubst2 _ _ _))) _).
	  1:    exact (t_step (tc_subst_r (sc_step (Scompcomp _ _ _)))).
	  1:   refine (ex_intro _ _ (conj (or_introl _) (or_intror eq_refl))).
	  1:   exact (t_step (tc_subst_r (sc_step (Sidl _)))).
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step (tc_subst_l H3))) (or_introl (t_step (tc_step (SSubst2 _ _ _)))))).
	  1: exact (ex_intro _ _ (conj (or_introl (t_step (tc_subst_r (sc_comp_l H3)))) (or_introl (t_step (tc_step (SSubst2 _ _ _)))))).
	  exact (ex_intro _ _ (conj (or_introl (t_step (tc_subst_r (sc_comp_r H4)))) (or_introl (t_step (tc_step (SSubst2 _ _ _)))))).
	- inversion H2; clear H2; subst.
	  1: inversion H; clear H; subst.
	  1:     refine (ex_intro _ _ (conj (or_intror eq_refl) (or_introl _))).
	  1:     exact (t_trans (t_step (tc_app_l (tc_step (SSubstId _)))) (t_step (tc_app_r (tc_step (SSubstId _))))).
	  1:    refine (ex_intro _ _ (conj (or_intror eq_refl) (or_introl _))).
	  1:    refine (t_trans (t_step (tc_abs (tc_subst_r (sc_dot_r (sc_step (Sidl _)))))) _).
	  1:    exact (t_trans (t_step (tc_abs (tc_subst_r (sc_step Szerosh)))) (t_step (tc_abs (tc_step (SSubstId _))))).
	  1:   refine (ex_intro _ _ (conj (or_intror eq_refl) (or_introl _))).
	  1:   exact (t_step (tc_subst_r (sc_step (Sidr _)))).
	  1:  refine (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1: refine (ex_intro _ _ (conj (or_introl (t_step H4)) (or_introl (t_step (tc_step (SSubstId _)))))).
	  inversion H4; inversion H.
Qed.
Lemma local_confluence_sigma_stack_csigma :
	forall s s1 s2, sigma_stack s s1 -> over_scontext sigma sigma_stack s s2 ->
	exists w, ((over_scontext sigma sigma_stack)^+ s1 w \/ s1 = w) /\ ((over_scontext sigma sigma_stack)^+ s2 w \/ s2 = w).
Proof using.
	intros t t1 t2 H1 H2; inversion H1 as [m s|m s1 s2|s1 s2 s3|s|s| |s]; clear H1; subst.
	- inversion H2; clear H2; subst.
	  1: inversion H; exists t2; split; right; exact eq_refl.
	  1: inversion H3; inversion H.
	  inversion H3; clear H3; subst.
	  1: inversion H; clear H; subst.
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_step (sc_step (Sidr _)))))).
	  1:  exists (Scomp Sshift t'); split; right; exact eq_refl.
	  1: exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_step (sc_step (Sshapp _ _)))))).
	  exact (ex_intro _ _ (conj (or_introl (t_step H2)) (or_introl (t_step (sc_step (Sshapp _ _)))))).
	- inversion H2; clear H2; subst.
	  1: inversion H; clear H; subst;
	       [exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl)))|].
	  1:  refine (ex_intro _ _ (conj (or_introl (t_trans (t_step _) (t_step _))) (or_intror eq_refl))).
	  1:   exact (sc_dot_l (tc_step (SSubstId _))).
	  1:   exact (sc_dot_r (sc_step (Sidr _))).
	  1: inversion H3; clear H3; subst.
	  1:  inversion H; clear H; subst.
	  1:   exact (ex_intro _ _ (conj (or_introl (t_step (sc_step (Ssubstsh _)))) (or_introl (t_step (sc_step (Sidl _)))))).
	  1:   refine (ex_intro _ _ (conj (or_introl (t_trans _ (t_step (sc_step (Ssubstsh _))))) (or_intror eq_refl))).
	  1:    refine (t_trans (t_step (sc_dot_l (tc_step (SSubst2 _ _ _)))) _).
	  1:    exact (t_step (sc_dot_r (sc_step (Scompcomp _ _ _)))).
	  1:  refine (ex_intro _ _ (conj (or_introl (t_step (sc_dot_l (tc_subst_l H2)))) _)).
	  1:   exact (or_introl (t_step (sc_step (Sdotcomp _ _ _)))).
	  1:  refine (ex_intro _ _ (conj (or_introl (t_step (sc_dot_r (sc_comp_l H2)))) _)).
	  1:   exact (or_introl (t_step (sc_step (Sdotcomp _ _ _)))).
	  refine (ex_intro _ _ (conj _ (or_introl (t_step (sc_step (Sdotcomp _ _ _)))))).
	  left; exact (t_trans (t_step (sc_dot_l (tc_subst_r H3))) (t_step (sc_dot_r (sc_comp_r H3)))).
	- inversion H2; clear H2; subst.
	  1: inversion H; [exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl)))|clear H; subst].
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step (sc_comp_r (sc_step (Sidr _))))) (or_intror eq_refl))).
	  1: inversion H3; clear H3; subst.
	  1:  inversion H; clear H; subst.
	  1:   refine (ex_intro _ _ (conj (or_introl _) (or_intror eq_refl))).
	  1:    refine (t_trans (t_step (sc_comp_r (sc_step (Sdotcomp _ _ _)))) _).
	  1:    exact (t_step (sc_step (Sshapp _ _))).
	  1:   refine (ex_intro _ _ (conj (or_introl (t_step (sc_step (Sdotcomp _ _ _)))) (or_introl _))).
	  1:    refine (t_trans (t_step (sc_step (Sdotcomp _ _ _))) _).
	  1:    refine (t_trans (t_step (sc_dot_l (tc_step (SSubst2 _ _ _)))) _).
	  1:    exact (t_step (sc_dot_r (sc_step (Scompcomp _ _ _)))).
	  1:   refine (ex_intro _ _ (conj (or_introl (t_step (sc_step (Scompcomp _ _ _)))) (or_introl _))).
	  1:    refine (t_trans (t_step (sc_step (Scompcomp _ _ _))) _).
	  1:    exact (t_step (sc_comp_r (sc_step (Scompcomp _ _ _)))).
	  1:   exact (ex_intro _ _ (conj (or_introl (t_step (sc_step (Sidl _)))) (or_intror eq_refl))).
	  1:   exact (ex_intro _ _ (conj (or_introl (t_step (sc_comp_r (sc_step (Sidl _))))) (or_intror eq_refl))).
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step (sc_comp_l H2))) (or_introl (t_step (sc_step (Scompcomp _ _ _)))))).
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step (sc_comp_r (sc_comp_l H2)))) (or_introl (t_step (sc_step (Scompcomp _ _ _)))))).
	  exact (ex_intro _ _ (conj (or_introl (t_step (sc_comp_r (sc_comp_r H3)))) (or_introl (t_step (sc_step (Scompcomp _ _ _)))))).
	- inversion H2; clear H2; subst.
	  1: inversion H; exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1: inversion H3; inversion H.
	  exact (ex_intro _ _ (conj (or_introl (t_step H3)) (or_introl (t_step (sc_step (Sidl _)))))).
	- inversion H2; clear H2; subst.
	  1: inversion H; clear H; subst.
	  1:  refine (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_trans (t_step _) (t_step _))))).
	  1:   exact (sc_dot_l (tc_step (SSubstId _))).
	  1:   exact (sc_dot_r (sc_step (Sidr _))).
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_step (sc_comp_r (sc_step (Sidr _))))))).
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1: exact (ex_intro _ _ (conj (or_introl (t_step H3)) (or_introl (t_step (sc_step (Sidr _)))))).
	  inversion H3; inversion H.
	- inversion H2; clear H2; subst.
	  1: inversion H; clear H; subst.
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1: inversion H3; inversion H.
	  inversion H3; inversion H.
	- inversion H2; clear H2; subst.
	  1: inversion H; exact (ex_intro _ _ (conj (or_intror eq_refl) (or_intror eq_refl))).
	  1: inversion H3; clear H3; subst.
	  1:  inversion H; clear H; subst.
	  1:   exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_step (sc_dot_r (sc_step (Sshapp _ _))))))).
	  1:   exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_trans (t_step (sc_dot_r (sc_step (Sidr _)))) (t_step (sc_step Szerosh)))))).
	  1:  inversion H2; inversion H.
	  1:  exact (ex_intro _ _ (conj (or_introl (t_step H2)) (or_introl (t_trans (t_step (sc_dot_r (sc_comp_r H2))) (t_step (sc_step (Ssubstsh _))))))).
	  inversion H3; clear H3; subst.
	  1: inversion H; clear H; subst.
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_step (sc_dot_l (tc_step (SEval _ _))))))).
	  1:  exact (ex_intro _ _ (conj (or_intror eq_refl) (or_introl (t_trans (t_step (sc_dot_l (tc_step (SSubstId _)))) (t_step (sc_step Szerosh)))))).
	  1: inversion H2; inversion H.
	  exact (ex_intro _ _ (conj (or_introl (t_step H2)) (or_introl (t_trans (t_step (sc_dot_l (tc_subst_r H2))) (t_step (sc_step (Ssubstsh _))))))).
Qed.

Lemma local_confluence_sigma :
	RewriteSystem.local_confluence eq (over_tcontext sigma sigma_stack) /\ RewriteSystem.local_confluence eq (over_scontext sigma sigma_stack).
Proof using.
	refine (match _ with conj H1 H2 => conj (fun u u1 u2 H => H1 u u1 H u2) (fun u u1 u2 H => H2 u u1 H u2) end).
	refine (over_context_mutind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
	- intros u v1 H1 v2; exact (local_confluence_sigma_csigma _ _ _ H1).
	- intros u u' v1 H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_csigma _ _ _ H (tc_app_l H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (BApp w v1); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [u v H|u v w _ IH1 _ IH2]; [exact (t_step (tc_app_l H))|exact (t_trans IH1 IH2)].
	  exists (BApp u' v'); split; left; [exact (t_step (tc_app_r H4))|exact (t_step (tc_app_l H1))].
	- intros u u' v1 H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_csigma _ _ _ H (tc_app_r H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: exists (BApp u'0 v1); split; left; [exact (t_step (tc_app_l H4))|exact (t_step (tc_app_r H1))].
	  specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (BApp u w); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [? v H|? v w _ IH1 _ IH2]; [exact (t_step (tc_app_r H))|exact (t_trans IH1 IH2)].
	- intros u u' H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_csigma _ _ _ H (tc_abs H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  specialize (IH1 _ H0) as [w [Hw1 Hw2]]; exists (BAbs w); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [? v H|? v w _ IH1 _ IH2]; [exact (t_step (tc_abs H))|exact (t_trans IH1 IH2)].
	- intros u u' v1 H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_csigma _ _ _ H (tc_subst_l H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (BSubst w v1); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [u v H|u v w _ IH1 _ IH2]; [exact (t_step (tc_subst_l H))|exact (t_trans IH1 IH2)].
	  exists (BSubst u' s'); split; left; [exact (t_step (tc_subst_r H4))|exact (t_step (tc_subst_l H1))].
	- intros u s s' H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_csigma _ _ _ H (tc_subst_r H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: exists (BSubst u' s'); split; left; [exact (t_step (tc_subst_l H4))|exact (t_step (tc_subst_r H1))].
	  specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (BSubst u w); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [? v H|? v w _ IH1 _ IH2]; [exact (t_step (tc_subst_r H))|exact (t_trans IH1 IH2)].
	- intros s t1 H1 t2; exact (local_confluence_sigma_stack_csigma _ _ _ H1).
	- intros u u' v1 H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_stack_csigma _ _ _ H (sc_dot_l H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (Sdot w v1); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [u v H|u v w _ IH1 _ IH2]; [exact (t_step (sc_dot_l H))|exact (t_trans IH1 IH2)].
	  exists (Sdot u' s'); split; left; [exact (t_step (sc_dot_r H4))|exact (t_step (sc_dot_l H1))].
	- intros u u' v1 H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_stack_csigma _ _ _ H (sc_dot_r H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: exists (Sdot u'0 v1); split; left; [exact (t_step (sc_dot_l H4))|exact (t_step (sc_dot_r H1))].
	  specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (Sdot u w); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [? v H|? v w _ IH1 _ IH2]; [exact (t_step (sc_dot_r H))|exact (t_trans IH1 IH2)].
	- intros u u' v1 H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_stack_csigma _ _ _ H (sc_comp_l H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (Scomp w v1); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [u v H|u v w _ IH1 _ IH2]; [exact (t_step (sc_comp_l H))|exact (t_trans IH1 IH2)].
	  exists (Scomp u' t'); split; left; [exact (t_step (sc_comp_r H4))|exact (t_step (sc_comp_l H1))].
	- intros u s s' H1 IH1 v2 H2; inversion H2; subst.
	  1: specialize (local_confluence_sigma_stack_csigma _ _ _ H (sc_comp_r H1)) as [w [Hw1 Hw2]]; exists w; split; assumption.
	  1: exists (Scomp s'0 s'); split; left; [exact (t_step (sc_comp_l H4))|exact (t_step (sc_comp_r H1))].
	  specialize (IH1 _ H4) as [w [Hw1 Hw2]]; exists (Scomp u w); split.
	  1:  destruct Hw1 as [Hw1|<-]; [left; clear - Hw1; rename Hw1 into H|right; exact eq_refl].
	  2:  destruct Hw2 as [Hw2|<-]; [left; clear - Hw2; rename Hw2 into H|right; exact eq_refl].
	  1,2: induction H as [? v H|? v w _ IH1 _ IH2]; [exact (t_step (sc_comp_r H))|exact (t_trans IH1 IH2)].
Qed.

Goal forall N, (over_tcontext (union _ beta sigma) sigma_stack)^+ <{ (\<1>) {N} }> <{ O }>.
Proof using.
	intros N; unfold nat_to_bound, nat_to_bound_aux.
	refine (t_trans (t_step (tc_step (or_introl (SBeta _ _)))) _).
	refine (t_trans (t_step (tc_step (or_intror (SSubst2 _ _ _)))) _).
	refine (t_trans (t_step (tc_subst_r (sc_step (Sshapp _ _)))) _).
	exact (t_step (tc_step (or_intror (SSubstId _)))).
Qed.

Fixpoint of_bterm_aux u n := match u with
	| U.BVar x => match n with O => BVar x | S n => BSubst (BVar x) (nat_to_bound_aux n) end
	| U.BBound n => nat_to_bound n
	| U.BApp u v => BApp (of_bterm_aux u n) (of_bterm_aux v n)
	| U.BAbs u => BAbs (of_bterm_aux u (S n))
end.
Definition of_bterm u := of_bterm_aux u O.

Inductive bunified :=
	| UVar : V -> bunified
	| UZero : bunified
	| UAbs : bunified -> bunified
	| Uid : bunified
	| Udot : bunified -> bunified -> bunified
	| Ushift : bunified
	| Ucomp : bunified -> bunified -> bunified.

Fixpoint bunified_of_bterm u := match u with
	| BVar x => UVar x
	| BZero => UZero
	| BApp u v => Udot (bunified_of_bterm u) (bunified_of_bterm v)
	| BAbs u => UAbs (bunified_of_bterm u)
	| BSubst u s => Ucomp (bunified_of_bterm u) (bunified_of_bstack s)
end with bunified_of_bstack s := match s with
	| Sid => Uid
	| Sdot u s => Udot (bunified_of_bterm u) (bunified_of_bstack s)
	| Sshift => Ushift
	| Scomp s t => Ucomp (bunified_of_bstack s) (bunified_of_bstack t)
end.
Inductive bunified_wd_term : bunified -> Prop :=
	| UWTVar : forall x, bunified_wd_term (UVar x)
	| UWTZero : bunified_wd_term UZero
	| UWTApp : forall u v, bunified_wd_term u -> bunified_wd_term v -> bunified_wd_term (Udot u v)
	| UWTAbs : forall u, bunified_wd_term u -> bunified_wd_term (UAbs u)
	| UWTSubst : forall u s, bunified_wd_term u -> bunified_wd_stack s -> bunified_wd_term (Ucomp u s)
with bunified_wd_stack : bunified -> Prop :=
	| UWSid : bunified_wd_stack Uid
	| UWSdot : forall u s, bunified_wd_term u -> bunified_wd_stack s -> bunified_wd_stack (Udot u s)
	| UWSshift : bunified_wd_stack Ushift
	| UWScomp : forall s t, bunified_wd_stack s -> bunified_wd_stack t -> bunified_wd_stack (Ucomp s t).
Fixpoint bterm_of_bunified u (H : bunified_wd_term u) : bterm
with bstack_of_bunified u (H : bunified_wd_stack u) : bstack.
Proof using.
	- destruct u as [x| |u| |u v| |u s].
	  4,6: exfalso; inversion H.
	  1: exact (BVar x).
	  1: exact BZero.
	  1: refine (BAbs (bterm_of_bunified u _)); inversion H; assumption.
	  1: refine (BApp (bterm_of_bunified u _) (bterm_of_bunified v _)); inversion H; assumption.
	  1: refine (BSubst (bterm_of_bunified u _) (bstack_of_bunified s _)); inversion H; assumption.
	- destruct u as [| | | |u s| |s t].
	  1,2,3: exfalso; inversion H.
	  1: exact Sid.
	  1: refine (Sdot (bterm_of_bunified u _) (bstack_of_bunified s _)); inversion H; assumption.
	  1: exact Sshift.
	  1: refine (Scomp (bstack_of_bunified s _) (bstack_of_bunified t _)); inversion H; assumption.
Defined.

Lemma bunified_of_wd : (forall u, bunified_wd_term (bunified_of_bterm u)) /\ (forall s, bunified_wd_stack (bunified_of_bstack s)).
Proof using.
	refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	1-9: intros; constructor; assumption.
Qed.
Lemma bterm_of_unified_ext : forall u,
	(forall H1 H2, bterm_of_bunified u H1 = bterm_of_bunified u H2) /\
	(forall H1 H2, bstack_of_bunified u H1 = bstack_of_bunified u H2).
Proof using.
	intros u; induction u as [x| |u [IH1 IH2]| |u [IHu1 IHu2] v [IHv1 IHv2]| |u [IHu1 IHu2] s [IHs1 IHs2]];
	  split; intros H1 H2.
	1,3,8,12: exact eq_refl.
	1,2,4,5,8: inversion H1.
	1: exact (f_equal BAbs (IH1 _ _)).
	1: exact (f_equal2 BApp (IHu1 _ _) (IHv1 _ _)).
	1: exact (f_equal2 Sdot (IHu1 _ _) (IHv2 _ _)).
	1: exact (f_equal2 BSubst (IHu1 _ _) (IHs2 _ _)).
	exact (f_equal2 Scomp (IHu2 _ _) (IHs2 _ _)).
Qed.
Lemma bval_of_unified_of_bval :
	(forall u H, bterm_of_bunified (bunified_of_bterm u) H = u) /\
	(forall u H, bstack_of_bunified (bunified_of_bstack u) H = u).
Proof using.
	refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	1,2,6,8: intros; exact eq_refl.
	- intros u IHu v IHv H; exact (f_equal2 BApp (IHu _) (IHv _)).
	- intros u IH H; exact (f_equal BAbs (IH _)).
	- intros u IHu s IHs H; exact (f_equal2 BSubst (IHu _) (IHs _)).
	- intros u IHu s IHs H; exact (f_equal2 Sdot (IHu _) (IHs _)).
	- intros s IHs t IHt H; exact (f_equal2 Scomp (IHs _) (IHt _)).
Qed.
Lemma bunified_of_val_of_bunified : forall u,
	(forall H, bunified_of_bterm (bterm_of_bunified u H) = u) /\
	(forall H, bunified_of_bstack (bstack_of_bunified u H) = u).
Proof using.
	intros u; induction u as [x| |u [IH1 IH2]| |u [IHu1 IHu2] v [IHv1 IHv2]| |u [IHu1 IHu2] v [IHv1 IHv2]]; split; intros H.
	2,4,6,7,11: inversion H.
	1,2,4,7: exact eq_refl.
	- exact (f_equal UAbs (IH1 _)).
	- exact (f_equal2 Udot (IHu1 _) (IHv1 _)).
	- exact (f_equal2 Udot (IHu1 _) (IHv2 _)).
	- exact (f_equal2 Ucomp (IHu1 _) (IHv2 _)).
	- exact (f_equal2 Ucomp (IHu2 _) (IHv2 _)).
Qed.

Inductive usigma : relation bunified :=
	| USidr : forall {u}, usigma (Ucomp u Uid) u
	| USidl : forall {u}, usigma (Ucomp Uid u) u
	| UScomp : forall {u v w}, usigma (Ucomp (Ucomp u v) w) (Ucomp u (Ucomp v w))
	| USzero : forall {u v}, usigma (Ucomp UZero (Udot u v)) u
	| USshift : forall {u v}, usigma (Ucomp Ushift (Udot u v)) v
	| USdot : forall {u v w}, usigma (Ucomp (Udot u v) w) (Udot (Ucomp u w) (Ucomp v w))
	| USAbs : forall {u v}, usigma (Ucomp (UAbs u) v) (UAbs (Ucomp u (Udot UZero (Ucomp v Ushift))))
	| USetadot : usigma (Udot UZero Ushift) Uid
	| USetacomp : forall {u}, usigma (Udot (Ucomp UZero u) (Ucomp Ushift u)) u.

Lemma bunified_of_bval_neq : forall u s, bunified_of_bterm u <> bunified_of_bstack s.
Proof using.
	refine (bterm_ind _ (fun s => forall u, bunified_of_bterm u <> bunified_of_bstack s) _ _ _ _ _ _ _ _ _).
	- intros x s; destruct s; discriminate.
	- intros s; destruct s; discriminate.
	- intros u IHu v IHv s; destruct s; try discriminate; intros [=H1 H2]; exact (IHv _ H2).
	- intros u IH s; destruct s; discriminate.
	- intros u IHu t IHt s; destruct s; try discriminate; intros [=H1 H2]; exact (IHu _ H1).
	- intros u; destruct u; discriminate.
	- intros v IHv s IHs u; destruct u; try discriminate; intros [=H1 H2]; exact (IHs _ H2).
	- intros u; destruct u; discriminate.
	- intros s IHs t IHt u; destruct u; try discriminate; intros [=H1 H2]; exact (IHs _ H1).
Qed.

Lemma bterm_of_bunified_eq : forall {u v}, u = v -> forall Hu Hv, bterm_of_bunified u Hu = bterm_of_bunified v Hv.
Proof using.
	intros u v <- Hu Hv; exact (proj1 (bterm_of_unified_ext _) _ _).
Qed.
Lemma bstack_of_bunified_eq : forall {u v}, u = v -> forall Hu Hv, bstack_of_bunified u Hu = bstack_of_bunified v Hv.
Proof using.
	intros u v <- Hu Hv; exact (proj2 (bterm_of_unified_ext _) _ _).
Qed.

Lemma bunified_of_bterm_inj : forall u v, bunified_of_bterm u = bunified_of_bterm v -> u = v.
Proof using.
	intros u v H;
	  rewrite <-(proj1 bval_of_unified_of_bval _ (proj1 bunified_of_wd u)),
	          <-(proj1 bval_of_unified_of_bval _ (proj1 bunified_of_wd v)).
	exact (bterm_of_bunified_eq H _ _).
Qed.
Lemma bunified_of_bstack_inj : forall s t, bunified_of_bstack s = bunified_of_bstack t -> s = t.
Proof using.
	intros s t H;
	  rewrite <-(proj2 bval_of_unified_of_bval _ (proj2 bunified_of_wd s)),
	          <-(proj2 bval_of_unified_of_bval _ (proj2 bunified_of_wd t)).
	exact (bstack_of_bunified_eq H _ _).
Qed.

Lemma usigma_iff :
	(forall u v, usigma (bunified_of_bterm u) (bunified_of_bterm v) <-> sigma u v) /\
	(forall u v, usigma (bunified_of_bstack u) (bunified_of_bstack v) <-> sigma_stack u v).
Proof using.
	refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	- intros x v; split; intros H; inversion H.
	- intros v; split; intros H; inversion H.
	- intros u1 IH1 u2 IH2 v; split; intros H; inversion H.
	  1: destruct u2; discriminate H2.
	  subst.
	  destruct u1; try discriminate H1; injection H1 as H11 H12.
	  contradiction (bunified_of_bval_neq _ _ H12).
	- intros u IH v; split; intros H; inversion H.
	- intros u IHu s IHs v; split; intros H; inversion H; clear H; subst.
	  1: destruct s; try discriminate H2; clear H2.
	  1:  apply bunified_of_bterm_inj in H3; subst.
	  1:  constructor.
	  1: contradiction (bunified_of_bval_neq _ _ (eq_sym H3)).
	  1: destruct u; try discriminate H1; injection H1 as -> ->.
	  1:  destruct v; try discriminate H3; injection H3 as H1 H2.
	  1:  apply bunified_of_bterm_inj in H1; subst.
	  1:  destruct b0; try discriminate H2; injection H2 as H1 H2.
	  1:  apply bunified_of_bstack_inj in H1, H2; subst.
	  1:  constructor.
	  1: destruct u; try discriminate H1; clear H1.
	  1:  destruct s; try discriminate H2; injection H2 as H ->.
	  1:  apply bunified_of_bterm_inj in H; subst.
	  1:  constructor.
	  1: destruct u; discriminate H1.
	  1: destruct u; try discriminate H1; injection H1 as -> ->.
	  1:  destruct v; try discriminate H3; injection H3 as H1 H2.
	  1:  destruct v1; try discriminate H1; injection H1 as H11 H12.
	  1:  destruct v2; try discriminate H2; injection H2 as H21 H22.
	  1:  apply bunified_of_bterm_inj in H11, H21; apply bunified_of_bstack_inj in H12, H22; subst.
	  1:  constructor.
	  1: destruct u; try discriminate H1; injection H1 as ->.
	  1:  destruct v; try discriminate H3; injection H3 as H.
	  1:  destruct v; try discriminate H; injection H as H1 H2.
	  1:  destruct b; try discriminate H2; injection H2 as H2 H3.
	  1:  destruct b; try discriminate H2; clear H2.
	  1:  destruct b0; try discriminate H3; injection H3 as H2 H3.
	  1:  destruct b0_2; try discriminate H3; clear H3.
	  1:  apply bunified_of_bterm_inj in H1; apply bunified_of_bstack_inj in H2; subst.
	  1:  constructor.
	  1-5: constructor.
	- intros v; split; intros H; inversion H.
	- intros u IHu s IHs v; split; intros H; inversion H.
	  1: destruct u; try discriminate H1; clear H1.
	  1:  destruct s; try discriminate H2; clear H2.
	  1:  destruct v; try discriminate H3; clear H3.
	  1:  constructor.
	  1: destruct u; try discriminate H1; injection H1 as H11 ->.
	  1:  destruct u; try discriminate H11; clear H11.
	  1:  destruct s; try discriminate H2; injection H2 as H1 H2.
	  1:  destruct s1; try discriminate H1; clear H1.
	  1:  apply bunified_of_bstack_inj in H0, H2; subst.
	  1:  constructor.
	  1-2: constructor.
	- intros v; split; intros H; inversion H.
	- intros s IHs t IHt v; split; intros H; inversion H; subst.
	  1: destruct t; try discriminate H2; clear H2.
	  1:  apply bunified_of_bstack_inj in H3; subst.
	  1:  constructor.
	  1: destruct s; try discriminate H1; clear H1.
	  1:  apply bunified_of_bstack_inj in H3; subst.
	  1:  constructor.
	  1: destruct s; try discriminate H1; injection H1 as -> ->.
	  1:  destruct v; try discriminate H3; injection H3 as H1 H2.
	  1:  destruct v2; try discriminate H2; injection H2 as H2 H3.
	  1:  apply bunified_of_bstack_inj in H1, H2, H3; subst.
	  1:  constructor.
	  1: destruct s; discriminate H1.
	  1: destruct s; try discriminate H1; clear H1.
	  1:  destruct t; try discriminate H2; injection H2 as -> H2.
	  1:  apply bunified_of_bstack_inj in H2; subst.
	  1:  constructor.
	  1: destruct s; try discriminate H1; injection H1 as -> ->.
	  1:  destruct v; try discriminate H3; injection H3 as H1 H2.
	  1:  destruct b0; try discriminate H1; injection H1 as H11 H12.
	  1:  destruct v; try discriminate H2; injection H2 as H2 H3.
	  1:  apply bunified_of_bterm_inj in H11; apply bunified_of_bstack_inj in H12, H2, H3; subst.
	  1:  constructor.
	  1: destruct s; discriminate H1.
	  1-5: constructor.
Qed.

Fixpoint bterm_of_aux u st := match u with
	| BVar x => U.BVar x
	| BZero => match st with (hd :: _, _) => hd | ([], n) => U.BBound n end
	| BApp u v => U.BApp (bterm_of_aux u st) (bterm_of_aux v st)
	| BAbs u => U.BAbs (bterm_of_aux u (U.BBound O :: List.map (fun u => U.incr_bound u O) (fst st), S (snd st)))
	| BSubst u s => bterm_of_aux u (bterm_of_st_aux s st)
end with bterm_of_st_aux s st := match s with
	| Sid => st
	| Sdot u s => (bterm_of_aux u st :: fst (bterm_of_st_aux s st), snd (bterm_of_st_aux s st))
	| Sshift => match fst st with _ :: tl => (tl, snd st) | [] => ([], S (snd st)) end
	| Scomp s t => bterm_of_st_aux s (bterm_of_st_aux t st)
end.
Definition bterm_of u := bterm_of_aux u ([], O).

Fixpoint same_st_aux' l1 := match l1 with
	| [] => fix inner n l2 m := match l2 with [] => n = m | hd2 :: tl2 => U.BBound n = hd2 /\ inner (S n) tl2 m end
	| hd1 :: tl1 => fun n l2 m => match l2 with
		| [] => hd1 = U.BBound m /\ same_st_aux' tl1 n [] (S m)
		| hd2 :: tl2 => hd1 = hd2 /\ same_st_aux' tl1 n tl2 m end
end.
Definition same_st_aux st1 st2 := same_st_aux' (fst st1) (snd st1) (fst st2) (snd st2).
Lemma same_st_aux_bound_S : forall l n, same_st_aux (l ++ [U.BBound n], S n) (l, n).
Proof using.
	intros l n; induction l as [|hd tl IH]; [split; exact eq_refl|split; [exact eq_refl|exact IH]].
Qed.
Lemma bterm_of_aux_same_st :
	(forall u st1 st2, same_st_aux st1 st2 -> bterm_of_aux u st1 = bterm_of_aux u st2) /\
	(forall s st1 st2, same_st_aux st1 st2 -> same_st_aux (bterm_of_st_aux s st1) (bterm_of_st_aux s st2)).
Proof using.
	refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	- intros x st1 st2 H; exact eq_refl.
	- intros [[|hd1 tl1] n1] [[|hd2 tl2] n2] H; try exact (proj1 H); exact (f_equal _ H).
	- intros u IHu v IHv st1 st2 H; exact (f_equal2 U.BApp (IHu _ _ H) (IHv _ _ H)).
	- intros u IH st1 st2 H; refine (f_equal U.BAbs (IH _ _ _)); split; [exact eq_refl|clear u IH].
	  destruct st1 as [l1 n1]; destruct st2 as [l2 n2]; cbn in H |- *.
	  generalize dependent n2; generalize dependent l2; generalize dependent n1; induction l1 as [|hd1 tl1 IH1];
	    intros n1 l2 n2 H.
	  1: cbn in H |- *; generalize dependent n2; generalize dependent n1; induction l2 as [|hd2 tl2 IH2];
	    intros n1 n2 H.
	  3: destruct l2 as [|hd2 tl2].
	  1: exact (f_equal _ H).
	  1-3: split; destruct H as [H1 H2].
	  1,3,5: exact (f_equal (fun u => U.incr_bound u O) H1).
	  1: exact (IH2 _ _ H2).
	  1,2: exact (IH1 _ _ _ H2).
	- intros u IHu s IHs st1 st2 H; exact (IHu _ _ (IHs _ _ H)).
	- intros st1 st2 H; exact H.
	- intros u IHu s IHs st1 st2 H; exact (conj (IHu _ _ H) (IHs _ _ H)).
	- intros [[|hd1 tl1] n1] [[|hd2 tl2] n2] H; try exact (proj2 H); exact (f_equal _ H).
	- intros s IHs t IHt st1 st2 H; exact (IHs _ _ (IHt _ _ H)).
Qed.

Definition nshifts n := match n with O => Sid | S n => nat_to_bound_aux n end.
Fixpoint dshift n s := match n with O => s | S n => Sdot BZero (Scomp (dshift n s) Sshift) end.
Lemma dshift_add : forall m n s, dshift (m + n) s = dshift m (dshift n s).
Proof using.
	intros m n s; induction m as [|m IHm]; [exact eq_refl|exact (f_equal (fun s => Sdot BZero (Scomp s Sshift)) IHm)].
Qed.
Lemma dshift_rev : forall n s, dshift n s = match n with O => s | S n => dshift n (Sdot BZero (Scomp s Sshift)) end.
Proof using.
	intros [|n] s; [exact eq_refl|rewrite <-add_1_r; exact (dshift_add _ _ _)].
Qed.
Fixpoint nshifts_comp n s := match n with O => s | S n => Scomp Sshift (nshifts_comp n s) end.
Lemma nshifts_eq_comp : forall n, nshifts (S n) = nshifts_comp n Sshift.
Proof using.
	intros n; induction n as [|n IHn].
	1: exact eq_refl.
	exact (f_equal (Scomp _) IHn).
Qed.
Lemma nshifts_comp_wd : forall n s, (over_scontext sigma sigma_stack)^* (Scomp (nshifts n) s) (nshifts_comp n s).
Proof using.
	intros [|n] s; [exact (rt_step (sc_step (Sidl _)))|cbn].
	induction n as [|n IHn].
	1: exact rt_refl.
	cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _).
	match type of IHn with clos_refl_trans _ ?l ?r =>
	  remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHn; induction IHn as [u v H|u|u v w _ IH1 _ IH2];
	  [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)] end.
Qed.
Lemma nshifts_comp_add : forall m n s, nshifts_comp (m + n) s = nshifts_comp m (nshifts_comp n s).
Proof using.
	intros m n s; induction m as [|m IHm].
	1: exact eq_refl.
	exact (f_equal (Scomp Sshift) IHm).
Qed.
Lemma nshifts_comp_rev : forall n s, nshifts_comp n s = match n with O => s | S n => nshifts_comp n (Scomp Sshift s) end.
Proof using.
	intros [|n] s; [exact eq_refl|rewrite <-add_1_r; exact (nshifts_comp_add _ _ _)].
Qed.
Lemma nshifts_comp_over_scontext : forall {Rt Rs} [n] {s1 s2},
	over_scontext Rt Rs s1 s2 -> over_scontext Rt Rs (nshifts_comp n s1) (nshifts_comp n s2).
Proof using.
	intros Rt Rs n s1 s2 H; induction n as [|n IHn].
	1: exact H.
	exact (sc_comp_r IHn).
Qed.
Lemma nshifts_comp_over_scontext_t : forall {Rt Rs} [n] {s1 s2},
	(over_scontext Rt Rs)^+ s1 s2 -> (over_scontext Rt Rs)^+ (nshifts_comp n s1) (nshifts_comp n s2).
Proof using.
	intros Rt Rs n s1 s2 H; induction H as [s1 s2 H|s1 s2 s3 _ IH1 _ IH2].
	1: exact (t_step (nshifts_comp_over_scontext H)).
	exact (t_trans IH1 IH2).
Qed.
Lemma nshifts_comp_over_scontext_rt : forall {Rt Rs} [n] {s1 s2},
	(over_scontext Rt Rs)^* s1 s2 -> (over_scontext Rt Rs)^* (nshifts_comp n s1) (nshifts_comp n s2).
Proof using.
	intros Rt Rs n s1 s2 H; induction H as [s1 s2 H|s|s1 s2 s3 _ IH1 _ IH2].
	1: exact (rt_step (nshifts_comp_over_scontext H)).
	1: exact rt_refl.
	exact (rt_trans IH1 IH2).
Qed.

Lemma shift_dshift : forall s, sigma_stack (Scomp Sshift (dshift (S O) s)) (Scomp s Sshift).
Proof using.
	intros s; exact (Sshapp _ _).
Qed.
Lemma nshifts_dshift : forall n s,
	(over_scontext sigma sigma_stack)^* (nshifts_comp n (dshift n s)) (match n with O => s | S n => Scomp s (nshifts (S n)) end).
Proof using.
	intros [|n] s; [exact rt_refl|rewrite nshifts_comp_rev].
	cbn; refine (rt_trans (rt_step (nshifts_comp_over_scontext (sc_step (shift_dshift _)))) _).
	pose (r := O);
	  rewrite (eq_refl : Sshift = nat_to_bound_aux r),
	          (eq_refl : nat_to_bound_aux n = nat_to_bound_aux (r + n)).
	generalize dependent r; induction n as [|n IHn]; intros r.
	1: rewrite add_0_r; exact rt_refl.
	rewrite nshifts_comp_rev, <-plus_n_Sm, <-plus_Sn_m; cbn;
	  refine (rt_trans (nshifts_comp_over_scontext_rt _) (IHn (S _))); cbn.
	refine (rt_trans (rt_step (sc_comp_r (sc_step (Sdotcomp _ _ _)))) _).
	exact (rt_trans (rt_step (sc_step (Sshapp _ _))) (rt_step (sc_step (Scompcomp _ _ _)))).
Qed.
Lemma nat_dshift : forall n s,
	(over_tcontext sigma sigma_stack)^*
		(BSubst (nat_to_bound n) (dshift n s))
		(match n with O => BSubst BZero s | S n => BSubst BZero (Scomp s (nshifts (S n))) end).
Proof using.
	intros [|n] s; [exact rt_refl|refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _)].
	assert (tmp := rt_trans (nshifts_comp_wd (S _) _) (nshifts_dshift (S n) s)); unfold nshifts in tmp |- *.
	match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	  remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	  [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)] end.
Qed.
Lemma nat_aux_add_dshift : forall q i s,
	(over_scontext sigma sigma_stack)^* (nshifts_comp (S q + i) (dshift (S q) s)) (nshifts_comp i (Scomp s (nshifts (S q)))).
Proof using.
	intros q i s.
	rewrite add_comm, nshifts_comp_add.
	exact (nshifts_comp_over_scontext_rt (nshifts_dshift _ _)).
Qed.
Lemma nat_addS_dshift : forall q i s,
	(over_tcontext sigma sigma_stack)^* (BSubst (nat_to_bound ((S q) + i)) (dshift (S q) s))
	  (BSubst BZero (nshifts_comp i (Scomp s (nshifts (S q))))).
Proof using.
	intros q i s; cbn; refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	assert (tmp := rt_trans (nshifts_comp_wd (S _) _) (nat_aux_add_dshift q i s)); cbn in tmp; fold add in tmp.
	match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	  remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	  [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)] end.
Qed.
Lemma nat_addO_dshift : forall i s,
	(over_tcontext sigma sigma_stack)^* (BSubst (nat_to_bound i) s)
	  (BSubst BZero (nshifts_comp i s)).
Proof using.
	intros [|i] s; [exact rt_refl|refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _)].
	assert (tmp := nshifts_comp_wd (S i) s); cbn in tmp |- *.
	match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	  remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	  [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)] end.
Qed.
Lemma nat_add_dshift : forall q i s,
	(over_tcontext sigma sigma_stack)^* (BSubst (nat_to_bound (q + i)) (dshift q s))
	  (BSubst BZero (nshifts_comp i (match q with O => s | S q => Scomp s (nshifts (S q)) end))).
Proof using.
	intros [|q] i s; [exact (nat_addO_dshift _ _)|exact (nat_addS_dshift _ _ _)].
Qed.
Lemma nat_le_dshift : forall q i s,
	(over_tcontext sigma sigma_stack)^* (BSubst (nat_to_bound i) (dshift (i + S q) s)) (nat_to_bound i).
Proof using.
	intros q [|i] s; cbn.
	1: exact (rt_step (tc_step (SEval _ _))).
	refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	refine (rt_trans _ (rt_step (tc_step (SEval _ (Scomp (Scomp (dshift q s) Sshift) (nat_to_bound_aux i)))))).
	match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) => assert (tmp : (over_scontext sigma sigma_stack)^* l r);
	  [|remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	    [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)]] end.
	refine (rt_trans (nshifts_comp_wd (S i) (dshift (S i + S q) s)) _).
	rewrite dshift_add.
	refine (rt_trans (nshifts_dshift _ _) _); cbn.
	exact (rt_step (sc_step (Sdotcomp _ _ _))).
Qed.

Fixpoint nincrs k u n := match k with O => u | S k => U.incr_bound (nincrs k u n) n end.
Lemma nincrs_var : forall p x q, nincrs p (U.BVar x) q = U.BVar x.
Proof using.
	intros p x q; induction p as [|p IHp]; [exact eq_refl|cbn; rewrite IHp; exact eq_refl].
Qed.
Lemma nincrs_bound : forall p k q, nincrs p (U.BBound k) q = U.BBound (if k <? q then k else k + p).
Proof using.
	intros p k q; specialize (lt_ge_cases k q) as [kltq|qlek].
	1:  rewrite (proj2 (ltb_lt _ _) kltq).
	2:  rewrite (proj2 (ltb_ge _ _) qlek).
	1,2: induction p as [|p IHp]; [try rewrite add_0_r; exact eq_refl|cbn; rewrite IHp; unfold U.incr_bound].
	1:  rewrite (proj2 (leb_gt _ _) kltq); exact eq_refl.
	rewrite (proj2 (leb_le _ _) (le_trans _ _ _ qlek (le_add_r _ _))); exact (f_equal _ (plus_n_Sm _ _)).
Qed.
Lemma nincrs_app : forall p u v q, nincrs p (U.BApp u v) q = U.BApp (nincrs p u q) (nincrs p v q).
Proof using.
	intros p u v q; induction p as [|p IHp]; [exact eq_refl|cbn; rewrite IHp; exact eq_refl].
Qed.
Lemma nincrs_abs : forall p u q, nincrs p (U.BAbs u) q = U.BAbs (nincrs p u (S q)).
Proof using.
	intros p u q; induction p as [|p IHp]; [exact eq_refl|cbn; rewrite IHp; exact eq_refl].
Qed.
Lemma bfb_nincrs_iff : forall p u q k, U.bfb k (nincrs p u q) <-> (k < q /\ U.bfb k u) \/ (p + q <= k /\ U.bfb (k - p) u).
Proof using.
	intros p u q k; split; generalize dependent k; generalize dependent q; generalize dependent u;
	  induction p as [|p IHp]; intros u q k; cbn.
	1,3: rewrite sub_0_r.
	1: intros H; destruct (lt_ge_cases k q) as [H1|H1]; [left|right]; split; assumption.
	1: intros [[_ H]|[_ H]]; exact H.
	1: intros H; destruct (lt_ge_cases k q) as [kltq|qlek]; [|inversion qlek; subst].
	1:  assert (tmp := U.bfb_incr_iff k (nincrs p u q) q); rewrite (proj2 (leb_gt _ _) kltq) in tmp.
	1:   apply tmp, IHp in H; clear tmp; destruct H as [[_ H]|[H _]].
	1:    left; split; assumption.
	1:    contradiction (lt_neq _ _ (le_trans _ _ _ kltq (le_trans _ _ _ (le_add_l _ _) H)) eq_refl).
	1:  contradiction (U.bfb_incr_eq _ _ H).
	1:  assert (tmp := U.bfb_incr_iff m (nincrs p u q) q); rewrite (proj2 (leb_le _ _) H0) in tmp.
	1:   apply tmp, IHp in H; clear tmp; destruct H as [[H _]|[H1 H2]].
	1:    contradiction (lt_neq _ _ (le_trans _ _ _ H H0) eq_refl).
	1:    right; split; [refine (le_n_S _ _ H1)|exact H2].
	intros [[H1 H2]|[H1 H2]].
	1: specialize (IHp _ _ _ (or_introl (conj H1 H2))).
	1:  assert (tmp := U.bfb_incr_iff k (nincrs p u q) q); rewrite (proj2 (leb_gt _ _) H1) in tmp; exact (proj2 tmp IHp).
	destruct k as [|k]; [inversion H1|].
	specialize (IHp _ _ _ (or_intror (conj (le_S_n _ _ H1) H2))).
	assert (tmp := U.bfb_incr_iff k (nincrs p u q) q);
	  rewrite (proj2 (leb_le _ _) (le_trans _ _ _ (le_add_l _ _) (le_S_n _ _ H1))) in tmp;
	  exact (proj2 tmp IHp).
Qed.
Lemma nincrs_rev : forall p u q, nincrs (S p) u q = nincrs p (U.incr_bound u q) q.
Proof using.
	intros p u q; cbn; induction p as [|p IHp]; [exact eq_refl|cbn; exact (f_equal (fun v => U.incr_bound v _) IHp)].
Qed.

Lemma of_bterm_add : forall p q l u,
	(over_tcontext sigma sigma_stack)^* (BSubst (of_bterm_aux u (q + l)) (dshift q (nshifts p)))
	   (of_bterm_aux (nincrs p u q) (p + q + l)).
Proof using.
	intros p q l u.
	generalize dependent q; induction u as [x|k|u IHu v IHv|u IH]; intros q.
	- rewrite nincrs_var.
	  unfold of_bterm_aux.
	  destruct q as [|q]; [rewrite add_0_r; cbn|].
	  1: destruct l as [|l]; destruct p as [|p]; [rewrite add_0_r| | |].
	  1,3:  exact (rt_step (tc_step (SSubstId _))).
	  1:  rewrite add_0_r; exact rt_refl.
	  1:  cbn; refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	  1:   rewrite (eq_refl : nat_to_bound_aux (_ + _) = nshifts (S _)), nshifts_eq_comp, add_comm, nshifts_comp_add, <-nshifts_eq_comp.
	  1:   assert (tmp := nshifts_comp_wd (S l) (nat_to_bound_aux p)); unfold nshifts in tmp |- *.
	  1:   match type of tmp with clos_refl_trans _ ?l ?r => remember l as u0 eqn:eq0; remember r as u1 eqn:eq1 end.
	  1:   clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	         [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  rewrite <-plus_n_Sm, !plus_Sn_m.
	  refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	  match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	    assert (tmp : (over_scontext sigma sigma_stack)^* l r); [|remember l as u0 eqn:eq0; remember r as u1 eqn:eq1] end.
	  2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	       [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  refine (rt_trans (nshifts_comp_wd (S _) _) _).
	  rewrite <-plus_Sn_m, add_comm, nshifts_comp_add.
	  rewrite (nshifts_eq_comp _ : nat_to_bound_aux _ = _), add_comm, nshifts_comp_add; refine (nshifts_comp_over_scontext_rt _).
	  refine (rt_trans (nshifts_dshift _ _) _).
	  rewrite nshifts_eq_comp, nshifts_comp_add.
	  exact (nshifts_comp_wd _ _).
	- rewrite nincrs_bound.
	  specialize (lt_ge_cases k q) as [kltq|qlek]; [rewrite (proj2 (ltb_lt _ _) kltq)|rewrite (proj2 (ltb_ge _ _) qlek)].
	  1: specialize (U.le_is_ex_add _ _ kltq) as [q' ->].
	  1:  rewrite (add_comm _ _ : (q' + S k = S (k + q'))%nat), plus_n_Sm.
	  1:  exact (nat_le_dshift _ _ _).
	  specialize (U.le_is_ex_add _ _ qlek) as [k' ->]; clear qlek.
	  cbn; rewrite add_comm; refine (rt_trans (nat_add_dshift _ _ _) _).
	  destruct q as [|q]; destruct p as [|p]; cbn.
	  1: rewrite add_0_r; destruct k' as [|k].
	  1:  exact (rt_step (tc_step (SSubstId _))).
	  1:  rewrite nshifts_comp_rev, (f_equal (BSubst BZero) (nshifts_eq_comp _) : nat_to_bound (S _) = _).
	  1:   exact (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_step (Sidr _))))).
	  1: rewrite <-plus_n_Sm, (f_equal (BSubst BZero) (nshifts_eq_comp _) : nat_to_bound (S _) = _), nshifts_comp_add, <-nshifts_eq_comp.
	  1:  exact rt_refl.
	  1: rewrite add_0_r, !(nshifts_eq_comp _ : nat_to_bound_aux _ = _), add_comm, nshifts_comp_add.
	  1:   exact (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_step (Sidl _))))).
	  rewrite !(nshifts_eq_comp _ : nat_to_bound_aux _ = nshifts_comp _ _), <-nshifts_eq_comp, (add_comm q), <-add_assoc.
	  rewrite (add_comm q), !nshifts_comp_add.
	  assert (tmp := nshifts_comp_over_scontext_rt (n:=k') (nshifts_comp_wd (S p) (nshifts_comp q Sshift))).
	  match type of tmp with clos_refl_trans _ ?l ?r =>
	        remember l as u0 eqn:eq0; remember r as u1 eqn:eq1;
	        clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	          [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)] end.
	- rewrite nincrs_app.
	  specialize (IHu q).
	  specialize (IHv q).
	  cbn.
	  refine (rt_trans (rt_step (tc_step (SApp _ _ _))) _).
	  match type of IHu with clos_refl_trans _ ?l ?r =>
	        remember l as u1 eqn:equ1; remember r as u2 eqn:equ2 end.
	  match type of IHv with clos_refl_trans _ ?l ?r =>
	        remember l as v1 eqn:eqv1; remember r as v2 eqn:eqv2 end.
	  refine (rt_trans (y:=BApp u2 v1) _ _); [rename IHu into IH|rename IHv into IH].
	  1,2: clear - IH; induction IH as [u v H|u|u v w _ IH1 _ IH2];
	         [|exact rt_refl|exact (rt_trans IH1 IH2)].
	  1: exact (rt_step (tc_app_l H)).
	  exact (rt_step (tc_app_r H)).
	- rewrite nincrs_abs.
	  specialize (IH (S q)).
	  cbn.
	  refine (rt_trans (rt_step (tc_step (SAbs _ _)) : _^* _ (BAbs (BSubst (of_bterm_aux _ (S _ + _)) (dshift (S _) _)))) _).
	  rewrite <-plus_Sn_m, plus_n_Sm.
	  match type of IH with clos_refl_trans _ ?l ?r =>
	        remember l as u1 eqn:equ1; remember r as u2 eqn:equ2 end.
	  clear - IH; induction IH as [u v H|u|u v w _ IH1 _ IH2];
	         [exact (rt_step (tc_abs H))|exact rt_refl|exact (rt_trans IH1 IH2)].
Qed.

Lemma of_bterm_subst : forall p q u v,
	(over_tcontext sigma sigma_stack)^*
		(BSubst (of_bterm_aux u (S (p + q))) (dshift p (Sdot (of_bterm_aux v q) Sid)))
		(of_bterm_aux (U.bsubstb u p (nincrs p v O)) (p + q)).
Proof using.
	intros p q u; generalize dependent p; induction u as [x|k|u1 IH1 u2 IH2|u IH]; intros p v.
	- cbn.
	  refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	  destruct p as [|p].
	  1: cbn; destruct q as [|q]; [exact (rt_trans (rt_step (tc_subst_r (sc_step (Sshapp _ _)))) (rt_step (tc_step (SSubstId _))))|].
	  1:  match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	        assert (tmp : (over_scontext sigma sigma_stack)^* l r); [|remember l as u0 eqn:eq0; remember r as u1 eqn:eq1] end.
	  2:  clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	           [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  1:  refine (rt_trans (nshifts_comp_wd (S (S _)) _) _).
	  1:  rewrite (nshifts_eq_comp _ : nat_to_bound_aux q = _), !(nshifts_comp_rev (S _)).
	  1:  refine (nshifts_comp_over_scontext_rt (rt_trans (rt_step (sc_comp_r (sc_step (Sshapp _ _)))) (rt_step (sc_step (Sidr _))))).
	  rewrite plus_Sn_m.
	  match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	    assert (tmp : (over_scontext sigma sigma_stack)^* l r); [|remember l as u0 eqn:eq0; remember r as u1 eqn:eq1] end.
	  2: clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	          [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  refine (rt_trans (nshifts_comp_wd (S (S _)) _) _).
	  rewrite <-plus_Sn_m, plus_n_Sm.
	  refine (rt_trans (nat_aux_add_dshift p _ _) _).
	  rewrite add_comm, (nshifts_eq_comp _ : nat_to_bound_aux _ = _), nshifts_comp_add, nshifts_comp_rev, <-nshifts_eq_comp.
	  refine (nshifts_comp_over_scontext_rt _).
	  refine (rt_trans (rt_step (sc_comp_r (sc_step (Sdotcomp _ _ _)))) _).
	  refine (rt_trans (rt_step (sc_step (Sshapp _ _))) _).
	  exact (rt_step (sc_step (Sidl _))).
	- simpl of_bterm_aux.
	  destruct (lt_ge_cases k p) as [kltp|plek].
	  1: rewrite (proj2 (ltb_lt _ _) kltp); cbn; apply U.le_is_ex_add in kltp; destruct kltp as [p' ->].
	  1:  rewrite add_comm, (plus_n_Sm _ _ : (S _ + _)%nat = _); exact (nat_le_dshift _ _ _).
	  rewrite (proj2 (ltb_ge _ _) plek).
	  apply U.le_is_ex_add in plek; destruct plek as [k' ->]; rename k' into k.
	  destruct k as [|k]; [cbn|].
	  1: rewrite eqb_refl.
	  1:  assert (tmp := nat_add_dshift p O); rewrite add_0_r in tmp; refine (rt_trans (tmp _) _); clear tmp; cbn.
	  1:  destruct p as [|p].
	  1:   exact (rt_step (tc_step (SEval _ _))).
	  1:   refine (rt_trans (rt_step (tc_subst_r (sc_step (Sdotcomp _ _ _)))) _).
	  1:    refine (rt_trans (rt_step (tc_step (SEval _ _))) _).
	  1:    refine (rt_trans (of_bterm_add (S _) O _ _) _).
	  1:    rewrite add_0_r; exact rt_refl.
	  rewrite eqb_sym, (plus_n_Sm _ _ : (S _ + _)%nat = _), (proj2 (eqb_neq _ _) (lt_neq _ _ (le_add_l _ _))).
	  rewrite <-(plus_n_Sm _ _ : (S _ + _)%nat = _), add_comm; refine (rt_trans (nat_add_dshift _ _ _) _).
	  rewrite <-plus_n_Sm; unfold pred, of_bterm_aux; fold of_bterm_aux.
	  rewrite nshifts_comp_rev.
	  destruct p as [|p].
	  1: refine (rt_trans (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_step (Sshapp _ _))))) _).
	  1:  destruct k as [|k]; [exact (rt_step (tc_step (SSubstId _)))|rewrite nshifts_comp_rev; unfold add, nat_to_bound].
	  1:  rewrite (nshifts_eq_comp _ : nat_to_bound_aux _ = _).
	  1:  exact (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_step (Sidr _))))).
	  refine (rt_trans (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_comp_r (sc_step (Sdotcomp _ _ _)))))) _).
	  refine (rt_trans (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_step (Sshapp _ _))))) _).
	  cbn; rewrite !(nshifts_eq_comp _ : nat_to_bound_aux _ = _), add_comm, nshifts_comp_add.
	  exact (rt_step (tc_subst_r (nshifts_comp_over_scontext (sc_step (Sidl _))))).
	- cbn; refine (rt_trans (rt_step (tc_step (SApp _ _ _))) _).
	  specialize (IH1 p v).
	  specialize (IH2 p v).
	  match type of IH1 with clos_refl_trans _ ?l ?r =>
	        remember l as u11 eqn:equ11; remember r as u12 eqn:equ12 end.
	  match type of IH2 with clos_refl_trans _ ?l ?r =>
	        remember l as u21 eqn:equ21; remember r as u22 eqn:equ22 end.
	  refine (rt_trans (y:=BApp u12 u21) _ _); [rename IH1 into IH|rename IH2 into IH].
	  1,2: clear - IH; induction IH as [u v H|u|u v w _ IH1 _ IH2];
	         [|exact rt_refl|exact (rt_trans IH1 IH2)].
	  1: exact (rt_step (tc_app_l H)).
	  exact (rt_step (tc_app_r H)).
	- cbn; refine (rt_trans (rt_step (tc_step (SAbs _ _))) _).
	  rewrite <-plus_Sn_m, (eq_refl : Sdot _ (Scomp (dshift _ _) _) = dshift (S _) _).
	  specialize (IH (S p) v); simpl nincrs in IH.
	  match type of IH with clos_refl_trans _ ?l ?r =>
	        remember l as u1 eqn:equ1; remember r as u2 eqn:equ2 end.
	  clear - IH; induction IH as [u v H|u|u v w _ IH1 _ IH2];
	    [|exact rt_refl|exact (rt_trans IH1 IH2)].
	  exact (rt_step (tc_abs H)).
Qed.

Fixpoint incr_stack_st_aux k nmk := match nmk with
	| O => ([], S k)
	| S nmk => (U.BBound k :: fst (incr_stack_st_aux (S k) nmk), snd (incr_stack_st_aux (S k) nmk))
end.
Definition incr_stack_st st n :=
	(map (fun u => U.incr_bound u n) (fst st) ++ fst (incr_stack_st_aux (snd st) (n - snd st)),
	 snd (incr_stack_st_aux (snd st) (n - snd st))).

Lemma same_st_aux_refl : forall st1 st2 n1 n2, st1 = st2 -> n1 = n2 -> same_st_aux' st1 n1 st2 n2.
Proof using.
	intros st1; induction st1 as [|hd1 st1 IHst]; intros [|hd2 st2] n n2 eq <-.
	1: exact eq_refl.
	1,2: discriminate eq.
	injection eq as <- <-; split; [exact eq_refl|exact (IHst _ _ _ eq_refl eq_refl)].
Qed.
Lemma same_st_aux_trans : forall st1 st2 st3 n1 n2 n3, same_st_aux' st1 n1 st2 n2 -> same_st_aux' st2 n2 st3 n3 -> same_st_aux' st1 n1 st3 n3.
Proof using.
	intros st1; induction st1 as [|hd1 st1 IHst]; intros st2 st3 n n2 n3 H1 H2.
	1: cbn in H1; generalize dependent st3; generalize dependent n3; generalize dependent n2; generalize dependent n;
	     induction st2 as [|hd2 st2 IHst]; intros n n2 H1 n3 st3 H2.
	1: subst n2; exact H2.
	1: destruct H1 as [<- H1]; destruct st3 as [|hd3 st3]; [destruct H2 as [[= <-] H2]|destruct H2 as [<- H2]].
	1:  exact eq_refl.
	1:  split; [exact eq_refl|exact (IHst _ _ H1 _ _ H2)].
	destruct st2 as [|hd2 st2]; cbn in H1.
	1: destruct H1 as [-> H1]; destruct st3 as [|hd3 st3].
	1:  cbn in H2; subst; split; [exact eq_refl|exact H1].
	1:  split; [exact (proj1 H2)|exact (IHst _ _ _ _ _ H1 (proj2 H2))].
	destruct H1 as [<- H1]; destruct st3 as [|hd3 st3].
	1: exact (conj (proj1 H2) (IHst _ _ _ _ _ H1 (proj2 H2))).
	exact (conj (proj1 H2) (IHst _ _ _ _ _ H1 (proj2 H2))).
Qed.
Lemma fst_incr_incr_stack_st_aux : forall k nmk,
	fst (incr_stack_st_aux (S k) nmk) = map (fun u => U.incr_bound u O) (fst (incr_stack_st_aux k nmk)).
Proof using.
	intros k nmk; generalize dependent k; induction nmk as [|nmk IH]; intros k.
	1: exact eq_refl.
	exact (f_equal (cons _) (IH _)).
Qed.
Lemma snd_incr_incr_stack_st_aux : forall k nmk,
	snd (incr_stack_st_aux (S k) nmk) = S (snd (incr_stack_st_aux k nmk)).
Proof using.
	intros k nmk; generalize dependent k; induction nmk as [|nmk IH]; intros k.
	1: exact eq_refl.
	exact (IH _).
Qed.

Lemma incr_bterm_of :
	(forall u n st, U.incr_bound (bterm_of_aux u st) n = bterm_of_aux u (incr_stack_st st n)) /\
	(forall s n st, same_st_aux (incr_stack_st (bterm_of_st_aux s st) n) (bterm_of_st_aux s (incr_stack_st st n))).
Proof using.
	refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	- intros x n st; exact eq_refl.
	- intros [|n] [[|hd st] k]; try exact eq_refl; unfold bterm_of_aux, incr_stack_st, fst, snd, map, app, U.incr_bound.
	  remember (S n - k) as nmk eqn:eqnmk; destruct nmk as [|nmk]; symmetry in eqnmk.
	  1: apply sub_0_le in eqnmk; rewrite (proj2 (leb_le _ _) eqnmk); exact eq_refl.
	  assert (tmp : S n - k <> O) by (rewrite eqnmk; discriminate).
	  rewrite sub_0_le in tmp; rewrite (proj2 (leb_nle _ _) tmp); exact eq_refl.
	- intros u IHu v IHv n st; exact (f_equal2 _ (IHu _ _) (IHv _ _)).
	- intros u IH n st; cbn; rewrite (IH _ _); cbn.
	  refine (f_equal _ (proj1 bterm_of_aux_same_st _ _ _ _)); cbn; split; [exact eq_refl|].
	  destruct st as [st k]; cbn.
	  rewrite map_app, !map_map; cbn; refine (same_st_aux_refl _ _ _ _ _ _).
	  2: exact (snd_incr_incr_stack_st_aux _ _).
	  refine (f_equal2 _ (map_ext _ _ _ _) (fst_incr_incr_stack_st_aux _ _)).
	  clear; intros u; exact (eq_sym (U.incr_bound_comm (le_0_n _))).
	- intros u IHu s IHs n st; cbn.
	  rewrite IHu; exact (proj1 bterm_of_aux_same_st _ _ _ (IHs _ _)).
	- intros n st; exact (same_st_aux_refl _ _ _ _ eq_refl eq_refl).
	- intros u IHu s IHs n st; cbn.
	  split; [exact (IHu _ _)|exact (IHs _ _)].
	- intros n [[|hd st] k]; cbn.
	  2: exact (same_st_aux_refl _ _ _ _ eq_refl eq_refl).
	  pose (m := k).
	  rewrite (eq_refl : incr_stack_st_aux k = incr_stack_st_aux m),
	          (eq_refl : incr_stack_st_aux (S k) = incr_stack_st_aux (S m)).
	  generalize dependent m; generalize dependent k; induction n as [|n IHn]; intros k m.
	  1: exact eq_refl.
	  destruct k as [|k].
	  1: simpl sub; rewrite sub_0_r; exact (same_st_aux_refl _ _ _ _ eq_refl eq_refl).
	  exact (IHn _ _).
	- intros s IHs t IHt n st; cbn.
	  refine (same_st_aux_trans _ _ _ _ _ _ (IHs _ _) _).
	  exact (proj2 bterm_of_aux_same_st _ _ _ (IHt _ _)).
Qed.

Lemma bterm_of_sigma :
	(forall u v, over_tcontext sigma sigma_stack u v -> forall st, bterm_of_aux u st = bterm_of_aux v st) /\
	(forall s t, over_scontext sigma sigma_stack s t -> forall st, same_st_aux (bterm_of_st_aux s st) (bterm_of_st_aux t st)).
Proof using.
	refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	- intros x v H; inversion H; inversion H0.
	- intros v H; inversion H; inversion H0.
	- intros u1 IH1 u2 IH2 v H st; inversion H; subst.
	  1: inversion H0.
	  1: exact (f_equal (fun u => U.BApp u _) (IH1 _ H3 _)).
	  exact (f_equal (fun u => U.BApp _ u) (IH2 _ H3 _)).
	- intros u IH v H st; inversion H; subst.
	  1: inversion H0.
	  exact (f_equal (fun u => U.BAbs u) (IH _ H1 _)).
	- intros u IHu s IHs v H st; inversion H; cbn; clear H; subst.
	  2: exact (IHu _ H3 _).
	  2: exact (proj1 bterm_of_aux_same_st _ _ _ (IHs _ H3 _)).
	  inversion H0 as [| |u' s' eq1 eq2| |]; try exact eq_refl; clear H0; subst; cbn.
	  refine (f_equal _ (proj1 bterm_of_aux_same_st _ _ _ _)); cbn.
	  split; [exact eq_refl|].
	  assert (tmp := proj2 incr_bterm_of s O st); cbn in tmp;
	    unfold incr_stack_st in tmp; cbn in tmp; rewrite !app_nil_r in tmp.
	  exact tmp.
	- intros v H; inversion H; inversion H0.
	- intros u IHu s IHs v H st; inversion H; subst.
	  2: exact (conj (IHu _ H3 _) (same_st_aux_refl _ _ _ _ eq_refl eq_refl)).
	  2: exact (conj eq_refl (IHs _ H3 _)).
	  inversion H0; clear H H0; subst; cbn.
	  1: destruct st as [[|hd st] k].
	  1:  split; exact eq_refl.
	  1:  split; [exact eq_refl|exact (same_st_aux_refl _ _ _ _ eq_refl eq_refl)].
	  destruct (bterm_of_st_aux v st) as [[|hd' st'] k']; cbn; split; try exact eq_refl.
	  exact (same_st_aux_refl _ _ _ _ eq_refl eq_refl).
	- intros v H; inversion H; inversion H0.
	- intros s IHs t IHt v H st; inversion H; clear H; subst; cbn.
	  2: exact (IHs _ H3 _).
	  2: exact (proj2 bterm_of_aux_same_st _ _ _ (IHt _ H3 _)).
	  inversion H0; clear H0; subst; cbn.
	  2: split; [exact eq_refl|].
	  1-5: exact (same_st_aux_refl _ _ _ _ eq_refl eq_refl).
Qed.

Lemma bterm_of_bterm : forall u, bterm_of (of_bterm u) = u.
Proof using.
	intros u; unfold bterm_of, of_bterm.
	remember O as n eqn:eq; rewrite (f_equal _ eq : ([], n) = ([], O)); clear eq.
	generalize dependent n; induction u as [x|k|u IHu v IHv|u IH]; intros n.
	- destruct n as [|n]; exact eq_refl.
	- unfold of_bterm_aux, nat_to_bound.
	  destruct k as [|k]; [exact eq_refl|cbn].
	  assert (tmp : forall k m, bterm_of_st_aux (nat_to_bound_aux k) ([], m)
	            = ([], (S k + m)%nat)).
	  2: rewrite tmp, add_comm; exact eq_refl.
	  clear; intros k; induction k as [|k IHk]; intros n.
	  1: exact eq_refl.
	  cbn; rewrite IHk; exact eq_refl.
	- exact (f_equal2 U.BApp (IHu _) (IHv _)).
	- exact (f_equal U.BAbs (eq_trans (proj1 bterm_of_aux_same_st _ _ _ (same_st_aux_bound_S _ _)) (IH _))).
Qed.

Fixpoint bstack_of_st_aux st n := match st with
	| [] => nshifts n
	| hd :: tl => Sdot (of_bterm_aux hd n) (bstack_of_st_aux tl n)
end.
Definition bstack_of_st st := bstack_of_st_aux (fst st) (snd st).

Lemma of_bterm_of_aux :
	(forall u st, length (fst st) <= snd st ->
		(over_tcontext sigma sigma_stack)^*
			(match bstack_of_st st with Sid => u | s => BSubst u s end)
			(of_bterm_aux (bterm_of_aux u st) (snd st))) /\
	(forall s st, length (fst st) <= snd st ->
		(over_scontext sigma sigma_stack)^* (Scomp s (bstack_of_st st)) (bstack_of_st (bterm_of_st_aux s st))).
Proof using.
	unfold bstack_of_st; refine (bval_mutind _ _ _ _ _ _ _ _ _ _ _).
	- intros x [st [|n]] Hst; [destruct st; [exact rt_refl|inversion Hst]|cbn in *].
	  destruct st as [|hd st]; [destruct n; exact rt_refl|cbn in Hst |- *; apply le_S_n in Hst].
Qed.
Lemma of_bterm_of : forall u, (over_tcontext sigma sigma_stack)^* (BSubst u Sid) (of_bterm (bterm_of u)).
Proof using.
	intros u; unfold bterm_of, of_bterm.
	pose (nshift := fun n => match n with O => Sid | S n => nat_to_bound_aux n end).
	pose (convert_pair := fun '(l, n) => (fix inner l := match l with [] => nshift n | hd :: tl => Sdot (of_bterm_aux hd n) (inner tl) end) l).
	assert (conv_eq : forall v,
	    convert_pair v = match fst v with [] => nshift (snd v)
	                       | hd :: tl => Sdot (of_bterm_aux hd (snd v)) (convert_pair (tl, snd v)) end)
	  by (intros [[|hd tl] n]; exact eq_refl).
	pose (l := @nil U.bterm); fold l.
	pose (n := O); fold n.
	rewrite (eq_refl : Sid = convert_pair (l, n)).
	generalize dependent n; generalize dependent l; generalize dependent u.
	refine (bterm_ind _ (fun s =>
		forall l n,
			length l = length (fst (bterm_of_st_aux s (l, n))) /\
			(over_scontext sigma sigma_stack)^*
				(Scomp s (convert_pair (l, n)))
				(convert_pair (bterm_of_st_aux s (l, n))))
		_ _ _ _ _ _ _ _ _).
	- intros x l [|n]; cbn; admit.
	- intros [|hd tl] n; [destruct n as [|n]; [|exact rt_refl]|].
	  1: exact (rt_step (tc_step (SSubstId _))).
	  rewrite conv_eq; lazy beta delta [fst snd bterm_of_aux] iota.
	  exact (rt_step (tc_step (SEval _ _))).
	- intros u IHu v IHv l n; refine (rt_trans (rt_step (tc_step (SApp _ _ _))) _).
	  specialize (IHu l n); specialize (IHv l n); simpl of_bterm_aux.
	  remember (BSubst u (convert_pair (l, n))) as u0 eqn:equ0.
	  remember (of_bterm_aux (bterm_of_aux u (l, n)) n) as u1 eqn:equ1.
	  remember (BSubst v (convert_pair (l, n))) as v0 eqn:eqv0.
	  remember (of_bterm_aux (bterm_of_aux v (l, n)) n) as v1 eqn:eqv1.
	  clear l n u v equ0 equ1 eqv0 eqv1 conv_eq convert_pair nshift.
	  refine (rt_trans (y:=BApp u1 v0) _ _); [induction IHu as [u v H|u|u v w _ IH1 _ IH2]|induction IHv as [u v H|u|u v w _ IH1 _ IH2]].
	  2,5: exact rt_refl.
	  2,4: exact (rt_trans IH1 IH2).
	  1: exact (rt_step (tc_app_l H)).
	  exact (rt_step (tc_app_r H)).
	- intros u IH l n; simpl of_bterm_aux.
	  refine (rt_trans (rt_step (tc_step (SAbs _ _))) _).
	  specialize (IH (U.BBound O :: map (fun v => U.incr_bound v O) l) (S n)).
	  rewrite conv_eq in IH; lazy beta delta [fst snd] iota in IH; simpl of_bterm_aux in IH.
	  refine (rt_trans (y:=BAbs (BSubst u (Sdot BZero (convert_pair (map (fun v => U.incr_bound v O) l, S n))))) _ _).
	  2: match type of IH with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IH end.
	  2: induction IH as [u v H|u|u v w _ IH1 _ IH2]; [exact (rt_step (tc_abs H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  assert (tmp : (over_scontext sigma sigma_stack)^* (Scomp (convert_pair (l, n)) Sshift) (convert_pair (map (fun v => U.incr_bound v O) l, S n))).
	  2: match type of tmp with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp end.
	  2: induction tmp as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (tc_abs (tc_subst_r (sc_dot_r H))))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  clear u IH.
	  induction l as [|hd tl IHl]; [|rewrite conv_eq, (conv_eq (map _ _, _)); lazy beta delta [fst snd] iota].
	  1: destruct n as [|n]; [exact (rt_step (sc_step (Sidl _)))|cbn].
	  1:  clear; induction n as [|n IHn]; [exact rt_refl|cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _)].
	  1:  match type of IHn with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHn end.
	  1:  induction IHn as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  simpl map; lazy iota.
	  refine (rt_trans (rt_step (sc_step (Sdotcomp _ _ _))) _).
	  match type of IHl with clos_refl_trans _ ?l ?r => remember l as v0 eqn:eqv0; remember r as v1 eqn:eqv1 end.
	  refine (rt_trans (y:=Sdot (BSubst (of_bterm_aux hd n) Sshift) v1) _ _).
	  1: clear - IHl; induction IHl as [u' v H|u'|u' v w _ IH1 _ IH2];
	       [exact (rt_step (sc_dot_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  match goal with |- clos_refl_trans _ (Sdot ?l _) (Sdot ?r _) => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1 end.
	  assert (tmp : (over_tcontext sigma sigma_stack)^* u0 u1).
	  2: clear - tmp; induction tmp as [u' v H|u'|u' v w _ IH1 _ IH2];
	       [exact (rt_step (sc_dot_l H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  subst u0 u1; clear tl v0 eqv0 v1 eqv1 IHl; rename hd into u.
	  pose (m := O); rewrite (eq_refl : n = (m + n)%nat); fold m.
	  rewrite (eq_refl : Sshift = (fix inner m := match m with O => Sshift | S m => Sdot BZero (Scomp (inner m) Sshift) end) m).
	  generalize dependent m;
	    induction u as [x|k|u IHu v IHv|u IH]; intros m.
	  + unfold U.incr_bound, of_bterm_aux; remember (add m n) as k eqn:eqk.
	  destruct k as [|k]; [destruct m; [exact rt_refl|discriminate eqk]|].
	  refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _); cbn.
	  match goal with |- clos_refl_trans _ (BSubst _ ?l) (BSubst _ ?r) =>
	      assert (tmp : (over_scontext sigma sigma_stack)^* l r);
	        [|remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	            [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)]] end.
	  match goal with |- clos_refl_trans _ (Scomp _ ?l) _ => remember l as s0 eqn:eqs0 end.
	  refine (rt_trans (y:=Scomp Sshift ((fix inner k := match k with O => s0 | S k => Scomp Sshift (inner k) end) k)) _ _).
	  1: clear; induction k as [|k IHk]; [exact rt_refl|cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _)].
	  1:  match type of IHk with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHk end.
	  1:  induction IHk as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  clear x conv_eq convert_pair nshift.
	  match goal with |- clos_refl_trans _ (Scomp _ ?l) (Scomp _ ?r) =>
	      assert (tmp : (over_scontext sigma sigma_stack)^* l r);
	        [|remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp; induction tmp as [u v H|u|u v w _ IH1 _ IH2];
	            [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)]] end.
	  destruct n as [|n].
	  1: rewrite add_0_r in eqk; subst.
	  1:  induction k as [|k IHk].
	  1:   exact (rt_step (sc_step))
	  assert (tmp : (fix inner k := match k with O => s0 | S k => Scomp Sshift (inner k) end) k =
	                (fix inner k := match k with
	                    | O => (fix inner k := match k with O => s0 | S k => Scomp Sshift (inner k) end) m
	                    | S k => Scomp Sshift (inner k) end) n).
	  1: clear eqs0; generalize dependent k; generalize dependent m; induction n as [|n IHn]; intros m k eqk.
	  1:  rewrite add_0_r in eqk; subst.
	  generalize dependent k; generalize dependent m; induction n as [|n IHn]; intros m eqs0 k eqk.
	  1: rewrite add_0_r in eqk; subst m s0.
	  1:   induction k as [|n IHn]; [exact rt_refl|cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _)].
	  1:   match type of IHn with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHn end.
	  1:   induction IHn as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  cbn in eqk; injection eqk as eqk; destruct k as [|k].
	  1: destruct m as [|m]; [|discriminate eqk].
	  1:  destruct n as [|n]; [|discriminate eqk].
	  1:  exact (rt_step (sc_step (Sshapp _ _))).
	  cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _).
	  specialize (IHm _ _ eqk).
	  
	  
	  
	  1:  induction k as [|k IHk]; [exact (rt_step (sc_step (Sshapp _ _)))|cbn].
	  1:  refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _).
	  1:
	  
	  destruct k as [|k]; [destruct m; [cbn in eqk; subst n; exact rt_refl|discriminate eqk]|].
	  refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _); cbn.
	  (* generalize dependent k; generalize dependent n; induction m as [|m IHm]; intros n k eqk. *)
	  generalize dependent n; generalize dependent m; induction k as [|k IHk]; intros m n eqk.
	  1: destruct m as [|m].
	  1:  cbn in eqk; subst; exact rt_refl.
	  1:  destruct m as [|m]; [destruct n as [|n]; [|discriminate eqk]|discriminate eqk].
	  2:  cbn in eqk; subst n; cbn.
	  2:   refine (rt_trans (rt_step (tc_subst_r (sc_step (Scompcomp _ _ _)))) _).
	  2:   assert (tmp : (over_scontext sigma sigma_stack)^* (Scomp (nat_to_bound_aux k) Sshift) (Scomp Sshift (nat_to_bound_aux k))).
	  3:   match type of tmp with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp end.
	  3:   induction tmp as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (tc_subst_r (sc_comp_r H)))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  2:   clear; induction k as [|n IHn]; [exact rt_refl|cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _)].
	  2:   match type of IHn with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHn end.
	  2:   induction IHn as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  cbn in eqk; injection eqk as eqk.
	  destruct n as [|n]; [rewrite add_comm in eqk; subst; cbn|].
	  specialize (IHm _ (add m n) (plus_n_Sm _ _)); cbn in IHm.
	  
	  
	  
	    1: exact rt_refl.
	    1: refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	    1:  assert (tmp : (over_scontext sigma sigma_stack)^* (Scomp (nat_to_bound_aux n) Sshift) (Scomp Sshift (nat_to_bound_aux n))).
	    2:  match type of tmp with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp end.
	    2:  induction tmp as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	    1:  induction n as [|n]; [exact rt_refl|cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _)].
	    1:  match type of IHn with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHn end.
	    1:  induction IHn as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	    2: remember (add m n) as k eqn:eqk; clear m n eqk; rename k into n.
	    1,2: refine (rt_trans (rt_step (tc_step (SSubst2 _ _ _))) _).
	    1,2: assert (tmp : (over_scontext sigma sigma_stack)^* (Scomp (nat_to_bound_aux n) Sshift) (Scomp Sshift (nat_to_bound_aux n))).
	    2,4: match type of tmp with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - tmp end.
	    2,3: induction tmp as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (tc_subst_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	    1,2: induction n as [|n]; [exact rt_refl|cbn; refine (rt_trans (rt_step (sc_step (Scompcomp _ _ _))) _)].
	    1,2: match type of IHn with clos_refl_trans _ ?l ?r => remember l as u0 eqn:equ0; remember r as u1 eqn:equ1; clear - IHn end.
	    1,2: induction IHn as [u' v H|u'|u' v w _ IH1 _ IH2]; [exact (rt_step (sc_comp_r H))|exact rt_refl|exact (rt_trans IH1 IH2)].
	  + lazy beta delta [U.incr_bound of_bterm_aux nat_to_bound] iota.
	  destruct k as [|k]; [destruct m as [|m]|].
	  assert (tmp1 : (over_tcontext sigma sigma_stack)^* (BSubst (of_bterm_aux hd n) Sshift) (of_bterm_aux (U.incr_bound hd O) (S n))).
	  1: clear IHl IH.
	  assert (tmp1 : (over_tcontext sigma sigma_stack)^* (BSubst (of_bterm_aux hd n) Sshift) (of_bterm_aux (U.incr_bound hd O) (S n))).
	
	pose (st0 := fun (l : list U.bterm) n => (length l + n)%nat).
	pose (prepend_list (l : list U.bterm) s := (fix inner l := match l with [] => s | hd :: tl => Streams.Cons hd (inner tl) end) l).
	pose (st1 := fun l n => Streams.map U.BBound (stream_nat_from (st0 l n))%nat).
	remember O as n eqn:eq; rewrite (eq_refl : stream_nat_from n = stream_nat_from (length l + n)); clear eq.
	rewrite (eq_refl : Streams.map _ (stream_nat_from (_ + _)) = prepend_list l (st1 l n)).
	generalize dependent n; generalize dependent l; generalize dependent u.
	refine (bterm_ind _ (fun s =>
		forall l n, exists l',
			length l = length l' /\
			Streams.EqSt (bterm_of_st_aux s (prepend_list l (st1 l n))) (prepend_list l' (st1 l' n)) /\
			(over_scontext sigma sigma_stack)^*
				(Scomp s (convert_list l n))
				(convert_list l' n))
		_ _ _ _ _ _ _ _ _).
	- intros x [|hd l] n; [|cbn].
	induction u as [x| |u IH| |u IHu v IHv| |u IHu v IHv]; intros l n.
	| UVar : V -> bunified
	| UZero : bunified
	| UAbs : bunified -> bunified
	| Uid : bunified
	| Udot : bunified -> bunified -> bunified
	| Ushift : bunified
	| Ucomp : bunified -> bunified -> bunified.
	- destruct n as [|n]; exact eq_refl.
	- unfold of_bterm_aux, nat_to_bound.
	  destruct k as [|k]; [exact eq_refl|cbn].
	  assert (tmp : forall k m, bterm_of_st_aux (nat_to_bound_aux k) (Streams.map U.BBound (stream_nat_from m))
	            = Streams.map U.BBound (stream_nat_from (S k + m))).
	  2: rewrite tmp, add_comm; exact eq_refl.
	  clear; intros k; induction k as [|k IHk]; intros n.
	  1: exact eq_refl.
	  cbn; rewrite IHk; exact eq_refl.
	- exact (f_equal2 U.BApp (IHu _) (IHv _)).
	- cbn; rewrite <-(IH (S n)) at 2; refine (f_equal U.BAbs (proj1 bterm_of_aux_ext _ _ _ (Streams.eqst _ _ _ _))).
	  1: exact eq_refl.
	  cbn; clear; pose (k := O);
	    rewrite (eq_refl : stream_nat_from O = stream_nat_from k), (eq_refl : stream_nat_from (S O) = stream_nat_from (S k)).
	  refine (Streams.ntheq_eqst _ _ _); unfold Streams.Str_nth.
	  intros n; generalize dependent k; induction n as [|n IHn]; intros k.
	  1: exact eq_refl.
	  exact (IHn (S k)).
Qed.

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

End UntypedLambdaSigma.
