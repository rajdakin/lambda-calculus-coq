Module Type AssocReqs.
Parameter key : Type.
Parameter key_dec : forall k1 k2 : key, { k1 = k2 } + { k1 <> k2 }.
End AssocReqs.

Require Import List. Import ListNotations.

Module Type Map.
Parameter key : Type.
Parameter key_dec : forall k1 k2 : key, { k1 = k2 } + { k1 <> k2 }.
Parameter t : Type -> Type.
Parameter empty : forall {val}, t val.
Parameter add : forall {val}, t val -> key -> val -> t val.
Parameter mem : forall {val}, t val -> key -> Prop.
Parameter find_opt : forall {val}, t val -> key -> option val.
Parameter find : forall {val}, t val -> key -> val -> val.
Parameter real_find : forall {val}, forall (m : t val) (k : key), mem m k -> val.
Parameter real_find_eq : forall {val} m k d H, @find val m k d = real_find m k H.
Parameter mem_empty : forall {val} k, ~ @mem val empty k.
Parameter mem_add : forall {val} m k1 v k2, @mem val (add m k1 v) k2 <-> k1 = k2 \/ mem m k2.
Parameter find_opt_None : forall {val} (m : t val) k, find_opt m k = None <-> ~ mem m k.
Parameter find_opt_Some : forall {val} (m : t val) k v, find_opt m k = Some v <-> mem m k /\ find m k v = v.
Parameter find_empty : forall {val} k d, @find val empty k d = d.
Parameter find_add : forall {val} m k1 v k2 d, @find val (add m k1 v) k2 d = if key_dec k1 k2 then v else find m k2 d.
Parameter find_add_key : forall {val} m k v d, @find val (add m k v) k d = v.
Parameter find_add_other : forall {val} m k1 v k2 d, k1 <> k2 -> @find val (add m k1 v) k2 d = find m k2 d.
Parameter find_mem : forall {val} m k, mem m k -> forall d1 d2, @find val m k d1 = find m k d2.
Parameter find_not_mem : forall {val} m k, ~ mem m k -> forall d, @find val m k d = d.
Parameter mem_dec : forall {val} m k, { @mem val m k } + { ~ mem m k }.
Parameter update : forall {val}, t val -> t val -> t val.
Parameter mem_update : forall {val} (m1 m2 : t val) k, mem (update m1 m2) k <-> mem m1 k \/ mem m2 k.
Parameter find_update : forall {val} (m1 m2 : t val) k d, find (update m1 m2) k d = if mem_dec m1 k then find m1 k d else find m2 k d.
Parameter map : forall {v1 v2}, t v1 -> (v1 -> v2) -> t v2.
Parameter map_ext : forall {v1 v2} m (f1 f2 : v1 -> v2), (forall v, f1 v = f2 v) -> map m f1 = map m f2.
Parameter mem_map : forall {v1 v2} (m : t v1) (f : v1 -> v2) k, mem (map m f) k <-> mem m k.
Parameter find_map_mem : forall {v1 v2} (m : t v1) (f : v1 -> v2) k d H, find (map m f) k d = f (real_find m k H).
Parameter find_map_f : forall {v1 v2} (m : t v1) (f : v1 -> v2) k d, find (map m f) k (f d) = f (find m k d).
Parameter find_map_add : forall {v1 v2} (m : t v1) (f : v1 -> v2) k1 v k2 d, find (map (add m k1 v) f) k2 d = find (add (map m f) k1 (f v)) k2 d.
End Map.

Module Make (T : AssocReqs) : Map
	with Definition key := T.key
	with Definition key_dec := T.key_dec.
Definition key := T.key.
Definition key_dec := T.key_dec.

Section WithVal.
Context {val : Type}.

Definition t := list (key * val).

Implicit Types (m : t) (k : key) (d v : val).

Definition empty : t := [].

Definition add m k v := (k, v) :: m.

Fixpoint mem m k := match m with
	| [] => False
	| (hdk, hdv) :: tl => hdk = k \/ mem tl k
end.

Fixpoint find_opt m k := match m with
	| [] => None
	| (hdk, hdv) :: tl => if key_dec hdk k then Some hdv else find_opt tl k
end.

Fixpoint find m k d := match m with
	| [] => d
	| (hdk, hdv) :: tl => if key_dec hdk k then hdv else find tl k d
end.

Fixpoint real_find (m : t) (k : key) (H : mem m k) {struct m} : val.
Proof using.
	destruct m as [|[hdk hdv] m].
	1: contradiction H.
	destruct (key_dec hdk k) as [eq|ne].
	1: exact hdv.
	refine (real_find m k _).
	destruct H as [H|H]; [contradiction (ne H)|exact H].
Defined.

Lemma real_find_eq : forall m k d H, find m k d = real_find m k H.
Proof using.
	intros m k d H; induction m as [|[hdk hdv] m IH].
	1: contradiction H.
	simpl; destruct (key_dec hdk k) as [|]; [exact eq_refl|exact (IH _)].
Qed.

Lemma find_opt_None : forall m k, find_opt m k = None <-> ~ mem m k.
Proof using.
	intros m k; split; induction m as [|[hdk hdv] tl IH]; intros H.
	1: intros [].
	1: cbn in H; destruct (key_dec hdk k) as [|ne]; intros [->|H2]; [discriminate H|discriminate H|contradiction (ne eq_refl)|exact (IH H H2)].
	1: exact eq_refl.
	cbn; destruct (key_dec hdk k) as [->|ne]; [contradiction (H (or_introl eq_refl))|exact (IH (fun H2 => H (or_intror H2)))].
Qed.

Lemma find_opt_Some : forall m k v, find_opt m k = Some v <-> mem m k /\ find m k v = v.
Proof using.
	intros m k; split; induction m as [|[hdk hdv] tl IH]; intros H.
	1: discriminate H.
	1: cbn in H; cbn; destruct (key_dec hdk k) as [eq|ne]; split;
	     [left; exact eq|injection H as H; exact H|right; exact (proj1 (IH H))|exact (proj2 (IH H))].
	1: contradiction (proj1 H).
	cbn in *.
	destruct (key_dec hdk k) as [->|ne];
	  [exact (f_equal _ (proj2 H))|exact (IH (conj ltac:(destruct H as [[H|H] _]; [contradiction (ne H)|exact H]) (proj2 H)))].
Qed.

Lemma mem_empty : forall k, ~ mem empty k.
Proof using.
	intros k [].
Qed.

Lemma mem_add : forall m k1 v k2, mem (add m k1 v) k2 <-> k1 = k2 \/ mem m k2.
Proof using. intros m k1 v k2; split; exact (fun H => H). Qed.

Lemma find_empty : forall k d, find empty k d = d.
Proof using. intros k d; exact eq_refl. Qed.

Lemma find_add : forall m k1 v k2 d, find (add m k1 v) k2 d = if key_dec k1 k2 then v else find m k2 d.
Proof using. intros m k1 v k2 d; exact eq_refl. Qed.

Lemma find_add_key : forall m k v d, find (add m k v) k d = v.
Proof using. intros m k v d; simpl; destruct (key_dec k k) as [_|ne]; [exact eq_refl|contradiction (ne eq_refl)]. Qed.

Lemma find_add_other : forall m k1 v k2 d, k1 <> k2 -> find (add m k1 v) k2 d = find m k2 d.
Proof using. intros m k1 v k2 d Hne; simpl; destruct (key_dec k1 k2) as [eq|_]; [contradiction (Hne eq)|exact eq_refl]. Qed.

Lemma find_mem : forall m k, mem m k -> forall d1 d2, find m k d1 = find m k d2.
Proof using.
	intros m k; induction m as [|[hdk hdv] m IH].
	1: intros [].
	intros H d1 d2; simpl; destruct (key_dec hdk k) as [eq|ne].
	1: exact eq_refl.
	destruct H as [H|H]; [contradiction (ne H)|exact (IH H _ _)].
Qed.
Lemma find_not_mem : forall m k, ~ mem m k -> forall d, find m k d = d.
Proof using.
	intros m k; induction m as [|[hdk hdv] m IH].
	1: intros _ d; exact eq_refl.
	intros H d; simpl; destruct (key_dec hdk k) as [eq|ne].
	1: contradiction (H (or_introl eq)).
	exact (IH (fun H' => H (or_intror H')) _).
Qed.

Lemma mem_dec : forall m k, { mem m k } + { ~ mem m k }.
Proof using.
	intros m k; induction m as [|[hdk ?] m [IH|IH]].
	- right; intros [].
	- left; right; exact IH.
	- simpl; destruct (key_dec hdk k) as [eq|ne].
	  1: left; left; exact eq.
	  right; intros [f|f]; [exact (ne f)|exact (IH f)].
Qed.

Definition update : t -> t -> t := @app _.

Lemma mem_update : forall m1 m2 k, mem (update m1 m2) k <-> mem m1 k \/ mem m2 k.
Proof using.
	intros m1 m2 k; split; induction m1 as [|[hdk hdv] m1 IH]; intros H.
	- right; exact H.
	- destruct H as [H|H]; [left; left; exact H|specialize (IH H) as [IH|IH]; [left; right; exact IH|right; exact IH]].
	- destruct H as [[]|H]; exact H.
	- destruct H as [[H|H]|H]; [left; exact H|right; exact (IH (or_introl H))|right; exact (IH (or_intror H))].
Qed.

Lemma find_update : forall m1 m2 k d, find (update m1 m2) k d = if mem_dec m1 k then find m1 k d else find m2 k d.
Proof using.
	unfold update; intros m1 m2 k d; induction m1 as [|[hdk hdv] m1 IH].
	- destruct (mem_dec [] k) as [[]|_]; exact eq_refl.
	- simpl; destruct (mem_dec ((hdk, hdv) :: m1) k) as [[H|H]|H].
	  1-3: destruct (key_dec hdk k) as [eq|ne].
	  1,3: exact eq_refl.
	  1: contradiction (ne H).
	  1: rewrite IH; destruct (mem_dec m1 k) as [m|nm]; [exact eq_refl|contradiction (nm H)].
	  1: contradiction (H (or_introl eq)).
	  1: rewrite IH; destruct (mem_dec m1 k) as [m|_]; [contradiction (H (or_intror m))|exact eq_refl].
Qed.

End WithVal.
Arguments t _ : clear implicits.

Section Map.
Context {v1 v2 : Type}.

Implicit Types (m : t v1) (f : v1 -> v2) (k : key).

Fixpoint map m f := match m with
	| [] => []
	| (hdk, hdv) :: m => (hdk, f hdv) :: map m f
end.

Lemma map_ext : forall m f1 f2, (forall v, f1 v = f2 v) -> map m f1 = map m f2.
Proof using.
	intros m f1 f2 Hf; induction m as [|[hdk hdv] m IH]; [exact eq_refl|exact (f_equal2 (fun a b => (hdk, a) :: b) (Hf _) IH)].
Qed.

Lemma mem_map : forall m f k, mem (map m f) k <-> mem m k.
Proof using.
	intros m f k; split; induction m as [|[hdk hdv] m IH]; intros H.
	1,3: exact H.
	1,2: simpl in H |- *; destruct H as [H|H]; [left; exact H|right; exact (IH H)].
Qed.

Lemma find_map_mem : forall m f k d H, find (map m f) k d = f (real_find m k H).
Proof using.
	intros m f k d H; induction m as [|[hdk hdv] m IH].
	1: contradiction H.
	simpl; destruct (key_dec hdk k) as [_|ne]; [exact eq_refl|destruct H as [H|H]; [contradiction (ne H)|exact (IH _)]].
Qed.

Lemma find_map_f : forall m f k d, find (map m f) k (f d) = f (find m k d).
Proof using.
	intros m f k d; induction m as [|[hdk hdv] m IH].
	1: exact eq_refl.
	simpl; destruct (key_dec hdk k); [exact eq_refl|exact IH].
Qed.

Lemma find_map_add : forall (m : t v1) (f : v1 -> v2) k1 v k2 d, find (map (add m k1 v) f) k2 d = find (add (map m f) k1 (f v)) k2 d.
Proof using.
	intros m f k1 v k2 d; exact eq_refl.
Qed.

End Map.

End Make.
