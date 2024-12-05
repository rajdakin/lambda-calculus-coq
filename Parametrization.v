Require Export List. Export List.ListNotations.
Require Export PeanoNat. Export Nat.
Export Logic.

Module Type Variables.
Parameter (V : Type).

Parameter (dec_V : forall x y : V, { x = y } + { x <> y }).

Parameter (V_of_nat : nat -> V)
          (V_inj : forall m n, V_of_nat m = V_of_nat n -> m = n).
Coercion V_of_nat : nat >-> V.

Parameter (onat_of_V : V -> option nat)
          (onat_correct : forall v n, onat_of_V v = Some n -> v = V_of_nat n)
          (onat_complete : forall v, onat_of_V v = None -> forall n, v <> V_of_nat n).
End Variables.

Module Type VarPropsT.
Declare Module Export M : Variables.
Parameter onat_Some_iff : forall v n, onat_of_V v = Some n <-> v = V_of_nat n.
Parameter onat_of_nat : forall n, onat_of_V (V_of_nat n) = Some n.
Parameter V_inf : forall m n, m <> n -> V_of_nat m <> V_of_nat n.
Parameter if_dec_eq : forall {T} v w (A B : T), v = w -> (if dec_V v w then A else B) = A.
Parameter if_dec_refl : forall {T} v (A B : T), (if dec_V v v then A else B) = A.
Parameter if_dec_neq : forall {T} v w (A B : T), v <> w -> (if dec_V v w then A else B) = B.
End VarPropsT.

Module VarProps (M0 : Variables) <: VarPropsT.
Module Export M := M0.

Lemma onat_Some_iff : forall v n, onat_of_V v = Some n <-> v = V_of_nat n.
Proof using.
	intros v n; split.
	1: exact (onat_correct _ _).
	intros H; remember (onat_of_V v) as o eqn:eq; destruct o as [m|].
	- rewrite (onat_correct _ _ (eq_sym eq)) in H; apply V_inj in H; exact (f_equal _ H).
	- contradiction (onat_complete _ (eq_sym eq) _ H).
Qed.

Lemma onat_of_nat : forall n, onat_of_V (V_of_nat n) = Some n.
Proof using.
	intros n; exact (proj2 (onat_Some_iff _ _) eq_refl).
Qed.

Lemma V_inf : forall m n, m <> n -> V_of_nat m <> V_of_nat n.
Proof using.
	intros m n mnen H; exact (mnen (V_inj _ _ H)).
Qed.

Lemma if_dec_eq : forall {T} v w (A B : T), v = w -> (if dec_V v w then A else B) = A.
Proof using.
	intros T v w A B eq; destruct (dec_V v w) as [_|ne]; [exact eq_refl|contradiction (ne eq)].
Qed.
Lemma if_dec_refl : forall {T} v (A B : T), (if dec_V v v then A else B) = A.
Proof using. intros T v A B; exact (if_dec_eq _ _ _ _ eq_refl). Qed.
Lemma if_dec_neq : forall {T} v w (A B : T), v <> w -> (if dec_V v w then A else B) = B.
Proof using.
	intros T v w A B ne; destruct (dec_V v w) as [eq|_]; [contradiction (ne eq)|exact eq_refl].
Qed.
End VarProps.
