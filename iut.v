Require Import Ltac.

Definition stroke : forall (p q : Prop), Prop.
Admitted.

Axiom ax_mp : forall (p q r : Prop) (min : p) (maj : (stroke p (stroke q r))), r.

Axiom ax_luk : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).

Theorem nicod : forall (p q r s t : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).
    intros.
    assert (L1 : forall (p0 q0 r0 s0 t0 : Prop), (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke p0 (stroke r0 q0)))).
    {
        intros.
        pose (S1 := (ax_luk p0 r0 q0 t0)).
        pose (S2 := (ax_luk t0 t0 t0 s0)).
        pose (S3 := (ax_luk (stroke t0 (stroke t0 t0)) (stroke s0 (stroke s0 s0)) (stroke (stroke s0 t0) (stroke (stroke t0 s0) (stroke t0 s0))) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))))).
        pose (S4 := (ax_mp (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke s0 (stroke s0 s0)) (stroke (stroke s0 t0) (stroke (stroke t0 s0) (stroke t0 s0))))) (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))))) (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0)))) (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0)))))) S2 S3)).
        pose (S5 := (ax_luk (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0)))) (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0)))) (stroke p0 (stroke r0 q0)))).
        pose (S6 := (ax_mp (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0)))) (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0)))))) (stroke (stroke p0 (stroke r0 q0)) (stroke (stroke p0 (stroke r0 q0)) (stroke p0 (stroke r0 q0)))) (stroke (stroke (stroke p0 (stroke r0 q0)) (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))))) (stroke (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke p0 (stroke r0 q0))) (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke p0 (stroke r0 q0))))) S4 S5)).
        exact (ax_mp (stroke (stroke p0 (stroke r0 q0)) (stroke (stroke t0 (stroke t0 t0)) (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))))) (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke p0 (stroke r0 q0))) (stroke (stroke (stroke (stroke t0 r0) (stroke (stroke p0 t0) (stroke p0 t0))) (stroke s0 (stroke s0 s0))) (stroke p0 (stroke r0 q0))) S1 S6).
    }
    assert (L2 : forall (s0 t0 : Prop), (stroke (stroke t0 s0) (stroke (stroke s0 t0) (stroke s0 t0)))).
    {
        intros.
        pose (S1 := (ax_luk r q p s0)).
        pose (S2 := (ax_luk (stroke r (stroke q p)) (stroke s0 (stroke s0 s0)) (stroke (stroke s0 q) (stroke (stroke r s0) (stroke r s0))) s0)).
        pose (S3 := (ax_mp (stroke (stroke r (stroke q p)) (stroke (stroke s0 (stroke s0 s0)) (stroke (stroke s0 q) (stroke (stroke r s0) (stroke r s0))))) (stroke s0 (stroke s0 s0)) (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) S1 S2)).
        pose (S4 := (L1 p p p s0 t0)).
        pose (S5 := (ax_luk (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0) p)).
        pose (S6 := (ax_luk (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke p (stroke p p)) (stroke (stroke p (stroke (stroke r (stroke q p)) s0)) (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) p) (stroke (stroke s0 (stroke s0 (stroke s0 s0))) p))) (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0))))).
        pose (S7 := (ax_mp (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke (stroke p (stroke p p)) (stroke (stroke p (stroke (stroke r (stroke q p)) s0)) (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) p) (stroke (stroke s0 (stroke s0 (stroke s0 s0))) p))))) (stroke (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0))))) (stroke (stroke (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0))) (stroke p (stroke p p))) (stroke (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0)))) (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0)))))) S5 S6)).
        pose (S8 := (ax_mp (stroke (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0))) (stroke p (stroke p p))) (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0)))) (stroke (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0)))) S4 S7)).
        pose (S9 := (ax_mp (stroke (stroke s0 (stroke s0 (stroke s0 s0))) (stroke (stroke (stroke r (stroke q p)) s0) (stroke (stroke r (stroke q p)) s0))) (stroke (stroke t0 p) (stroke (stroke p t0) (stroke p t0))) (stroke s0 (stroke s0 s0)) S3 S8)).
        pose (S10 := (ax_luk s0 s0 s0 t0)).
        exact (ax_mp (stroke s0 (stroke s0 s0)) (stroke t0 (stroke t0 t0)) (stroke (stroke t0 s0) (stroke (stroke s0 t0) (stroke s0 t0))) S9 S10).
    }
    pose (S1 := (L1 p r q t s)).
    pose (S2 := (L2 (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))))).
    pose (S3 := (ax_mp (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke p (stroke q r))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t)))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t)))) S1 S2)).
    pose (S4 := (L2 (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t)))).
    pose (S5 := (ax_luk (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke p (stroke q r)))).
    pose (S6 := (ax_mp (stroke (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t))))) (stroke (stroke p (stroke q r)) (stroke (stroke p (stroke q r)) (stroke p (stroke q r)))) (stroke (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t)))) (stroke (stroke (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))) (stroke (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))))) S4 S5)).
    pose (S7 := (ax_mp (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke t (stroke t t)))) (stroke (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))) (stroke (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r)))) S3 S6).
    pose (S8 := (L2 (stroke p (stroke q r)) (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))))).
    exact (ax_mp (stroke (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))) (stroke (stroke p (stroke q r)) (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))) (stroke (stroke p (stroke q r)) (stroke (stroke t (stroke t t)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))) S7 S8).
Qed.

Theorem nicod_id : forall (t : Prop), (stroke t (stroke t t)).
    intros.
    assert (A : forall (s t0 : Prop) (pi := (stroke t0 (stroke t0 t0))) (Q_1 := (stroke (stroke s t0) (stroke (stroke t0 s) (stroke t0 s)))), (stroke pi (stroke pi Q_1))).
    {
        intros.
        exact (nicod t0 t0 t0 s t0).
    }
    assert (B : forall (s t0 : Prop) (pi := (stroke t0 (stroke t0 t0))) (Q_1 := (stroke (stroke s t0) (stroke (stroke t0 s) (stroke t0 s)))), (stroke (stroke s pi) (stroke (stroke pi s) (stroke pi s)))).
    {
        intros.
        pose (S1 := (nicod pi pi Q_1 s t0)).
        exact (ax_mp (stroke pi (stroke pi Q_1)) pi (stroke (stroke s pi) (stroke (stroke pi s) (stroke pi s))) (A s t0) S1).
    }
    assert (C : forall (s t0 u : Prop) (pi := (stroke t0 (stroke t0 t0))), (stroke (stroke u (stroke pi s)) (stroke (stroke (stroke s pi) u) (stroke (stroke s pi) u)))).
    {
        intros.
        pose (S1 := (nicod (stroke s pi) (stroke pi s) (stroke pi s) u t0)).
        exact (ax_mp (stroke (stroke s pi) (stroke (stroke pi s) (stroke pi s))) pi (stroke (stroke u (stroke pi s)) (stroke (stroke (stroke s pi) u) (stroke (stroke s pi) u))) (B s t0) S1).
    }
    assert (D : forall (p q r s t0 : Prop) (P := (stroke p (stroke q r))) (pi := (stroke t0 (stroke t0 t0))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))), (stroke (stroke Q pi) P)).
    {
        intros.
        exact (ax_mp (stroke P (stroke pi Q)) (stroke (stroke Q pi) P) (stroke (stroke Q pi) P) (nicod p q r s t0) (C Q t0 P)).
    }
    assert (E : forall (p q r s t0 T : Prop) (P := (stroke p (stroke q r))) (H : (stroke T (stroke P P))), (stroke (stroke s P) (stroke (stroke T s) (stroke T s)))).
    {
        intros.
        pose (S1 := (nicod T P P s t0)).
        exact (ax_mp (stroke T (stroke P P)) (stroke t0 (stroke t0 t0)) (stroke (stroke s P) (stroke (stroke T s) (stroke T s))) H S1).
    }
    assert (F : forall (p q r s t0 T : Prop) (P := (stroke p (stroke q r))) (pi := (stroke t0 (stroke t0 t0))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (H0 : T) (H1 : (stroke T (stroke P P))), pi).
    {
        intros.
        pose (S1 := (E p q r (stroke Q pi) t0 T H1)).
        pose (S2 := (ax_mp (stroke (stroke Q pi) P) (stroke T (stroke Q pi)) (stroke T (stroke Q pi)) (D p q r s t0) S1)).
        exact (ax_mp T Q pi H0 S2).
    }
    assert (S1 : forall (s t0 : Prop) (pi := (stroke t0 (stroke t0 t0))) (Q_1 := (stroke (stroke s t0) (stroke (stroke t0 s) (stroke t0 s)))), pi).
    {
        intros.
        pose (H0 := (A s t0)).
        pose (H1 := (C Q_1 t0 pi)).
        exact (F (stroke Q_1 pi) t0 (stroke t0 t0) s t0 (stroke pi (stroke pi Q_1)) H0 H1).
    }
    exact (S1 t t).
Qed.

Theorem nicod_perm : forall (p s : Prop), (stroke (stroke s p) (stroke (stroke p s) (stroke p s))).
    intros.
    pose (S1 := (nicod p p p s s)).
    exact (ax_mp (stroke p (stroke p p)) (stroke s (stroke s s)) (stroke (stroke s p) (stroke (stroke p s) (stroke p s))) (nicod_id p) S1).
Qed.

Theorem nicod_taut : forall (p : Prop), (stroke (stroke (stroke p p) (stroke p p)) (stroke p p)).
    intros.
    pose (S1 := (nicod_perm (stroke (stroke p p) (stroke p p)) (stroke p p))).
    exact (ax_mp (stroke (stroke p p) (stroke (stroke p p) (stroke p p))) (stroke (stroke (stroke p p) (stroke p p)) (stroke p p)) (stroke (stroke (stroke p p) (stroke p p)) (stroke p p)) (nicod_id (stroke p p)) S1).
Qed.

Theorem nicod_add : forall (p s : Prop), (stroke s (stroke (stroke p (stroke s s)) (stroke p (stroke s s)))).
    intros.
    assert (A : forall (p0 s0 : Prop), (stroke (stroke (stroke p0 (stroke s0 s0)) (stroke p0 (stroke s0 s0))) (stroke (stroke s0 s0) p0))).
    {
        intros.
        pose (S1 := (nicod_perm p0 (stroke s0 s0))).
        exact (ax_mp (stroke (stroke (stroke s0 s0) p0) (stroke (stroke p0 (stroke s0 s0)) (stroke p0 (stroke s0 s0)))) (stroke (stroke (stroke p0 (stroke s0 s0)) (stroke p0 (stroke s0 s0))) (stroke (stroke s0 s0) p0)) (stroke (stroke (stroke p0 (stroke s0 s0)) (stroke p0 (stroke s0 s0))) (stroke (stroke s0 s0) p0)) S1 (nicod_perm (stroke (stroke p0 (stroke s0 s0)) (stroke p0 (stroke s0 s0))) (stroke (stroke s0 s0) p0))).
    }
    pose (S1 := (nicod (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) (stroke s s) p s s)).
    pose (S2 := (ax_mp (stroke (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) (stroke (stroke s s) p)) (stroke s (stroke s s)) (stroke (stroke s (stroke s s)) (stroke (stroke (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) s) (stroke (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) s))) (A p s) S1)).
    pose (S3 := (ax_mp (stroke s (stroke s s)) (stroke (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) s) (stroke (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) s) (nicod_id s) S2)).
    exact (ax_mp (stroke (stroke (stroke p (stroke s s)) (stroke p (stroke s s))) s) (stroke s (stroke (stroke p (stroke s s)) (stroke p (stroke s s)))) (stroke s (stroke (stroke p (stroke s s)) (stroke p (stroke s s)))) S3 (nicod_perm s (stroke (stroke p (stroke s s)) (stroke p (stroke s s))))).
Qed.

Theorem nicod_genimpl_lemma : forall (p s : Prop), (stroke (stroke p p) (stroke (stroke s p) (stroke s p))).
    intros.
    assert (A : forall (p0 s0 : Prop), (stroke (stroke (stroke s0 p0) (stroke s0 p0)) (stroke p0 s0))).
    {
        intros.
        pose (S1 := (nicod_perm s0 p0)).
        exact (ax_mp (stroke (stroke p0 s0) (stroke (stroke s0 p0) (stroke s0 p0))) (stroke (stroke (stroke s0 p0) (stroke s0 p0)) (stroke p0 s0)) (stroke (stroke (stroke s0 p0) (stroke s0 p0)) (stroke p0 s0)) S1 (nicod_perm (stroke (stroke s0 p0) (stroke s0 p0)) (stroke p0 s0))).
    }
    assert (L : forall (p0 s0 u : Prop), (stroke (stroke u p0) (stroke (stroke (stroke (stroke s0 p0) (stroke s0 p0)) u) (stroke (stroke (stroke s0 p0) (stroke s0 p0)) u)))).
    {
        intros.
        pose (S1 := (nicod (stroke (stroke s0 p0) (stroke s0 p0)) p0 s0 u u)).
        exact (ax_mp (stroke (stroke (stroke s0 p0) (stroke s0 p0)) (stroke p0 s0)) (stroke u (stroke u u)) (stroke (stroke u p0) (stroke (stroke (stroke (stroke s0 p0) (stroke s0 p0)) u) (stroke (stroke (stroke s0 p0) (stroke s0 p0)) u))) (A p0 s0) S1).
    }
    pose (S1 := (L p s (stroke p p))).
    pose (S2 := (ax_mp (stroke p (stroke p p)) (stroke (stroke p p) p) (stroke (stroke p p) p) (nicod_id p) (nicod_perm (stroke p p) p))).
    pose (S3 := (ax_mp (stroke (stroke p p) p) (stroke (stroke (stroke s p) (stroke s p)) (stroke p p)) (stroke (stroke (stroke s p) (stroke s p)) (stroke p p)) S2 S1)).
    exact (ax_mp (stroke (stroke (stroke s p) (stroke s p)) (stroke p p)) (stroke (stroke p p) (stroke (stroke s p) (stroke s p))) (stroke (stroke p p) (stroke (stroke s p) (stroke s p))) S3 (nicod_perm (stroke p p) (stroke (stroke s p) (stroke s p)))).
Qed.

Theorem nicod_genimpl : forall (p q r s : Prop) (P := (stroke p (stroke q r))) (Q := (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))), (stroke P (stroke Q Q)).
    intros.
    assert (L : forall (p0 q0 r0 s0 t : Prop) (P0 := (stroke p0 (stroke q0 r0))) (pi := (stroke t (stroke t t))) (Q0 := (stroke (stroke s0 q0) (stroke (stroke p0 s0) (stroke p0 s0)))), (stroke (stroke P0 (stroke pi Q0)) (stroke (stroke (stroke Q0 Q0) P0) (stroke (stroke Q0 Q0) P0)))).
    {
        intros.
        pose (S1 := (nicod (stroke Q0 Q0) (stroke pi Q0) (stroke pi Q0) P0 t)).
        exact (ax_mp (stroke (stroke Q0 Q0) (stroke (stroke pi Q0) (stroke pi Q0))) pi (stroke (stroke P0 (stroke pi Q0)) (stroke (stroke (stroke Q0 Q0) P0) (stroke (stroke Q0 Q0) P0))) (nicod_genimpl_lemma Q0 pi) S1).
    }
    pose (S1 := (ax_mp (stroke (stroke p (stroke q r)) (stroke (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))) (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))) (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))) (nicod p q r s s) (L p q r s s))).
    exact (ax_mp (stroke (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke p (stroke q r))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))) S1 (nicod_perm (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))))).
Qed.

Theorem nicod_syll : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))).
    intros.
    assert (A : forall (q0 s0 u : Prop), (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0)))).
    {
        intros.
        pose (S1 := (nicod_genimpl (stroke q0 s0) (stroke s0 q0) (stroke s0 q0) u)).
        pose (S2 := (ax_mp ((stroke (stroke q0 s0) (stroke (stroke s0 q0) (stroke s0 q0)))) (stroke (stroke u (stroke s0 q0)) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (stroke (stroke u (stroke s0 q0)) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (nicod_perm s0 q0) S1)).
        exact (ax_mp (stroke (stroke u (stroke s0 q0)) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0))) (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0))) S2 (nicod_perm (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0)))).
    }
    assert (B : forall (q0 s0 u : Prop), (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke (stroke s0 q0) u))).
    {
        intros.
        pose (S1 := (nicod_genimpl (stroke (stroke s0 q0) u) (stroke u (stroke s0 q0)) (stroke u (stroke s0 q0)) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)))).
        pose (S2 := (ax_mp (stroke (stroke (stroke s0 q0) u) (stroke (stroke u (stroke s0 q0)) (stroke u (stroke s0 q0)))) (stroke (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0))) (stroke (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))))) (stroke (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0))) (stroke (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))))) (nicod_perm u (stroke s0 q0)) S1)).
        pose (S3 := (ax_mp (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke u (stroke s0 q0))) (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (A q0 s0 u) S2)).
        exact (ax_mp (stroke (stroke (stroke s0 q0) u) (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u))) (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke (stroke s0 q0) u)) (stroke (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke (stroke s0 q0) u)) S3 (nicod_perm (stroke (stroke (stroke q0 s0) u) (stroke (stroke q0 s0) u)) (stroke (stroke s0 q0) u))).
    }
    pose (S1 := (nicod_genimpl (stroke p (stroke q r)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))))).
    pose (S2 := (ax_mp (stroke (stroke p (stroke q r)) (stroke (stroke (stroke s q) (stroke (stroke p s) (stroke p s))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))) (stroke (stroke (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))))) (stroke (stroke (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))))))) (nicod_genimpl p q r s) S1).
    exact (ax_mp (stroke (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s)))) (stroke (stroke s q) (stroke (stroke p s) (stroke p s)))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))) (stroke (stroke p (stroke q r)) (stroke (stroke (stroke q s) (stroke (stroke p s) (stroke p s))) (stroke (stroke q s) (stroke (stroke p s) (stroke p s))))) (B q s (stroke (stroke p s) (stroke p s))) S2).
Qed.

Theorem nicod_assoc : forall (p q r : Prop), (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))).
    intros.
    assert (L : forall (p0 q0 : Prop) (L := (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0)))), L).
    {
        intros.
        assert (A : (stroke q0 (stroke L L))).
        {
            pose (L1 := (nicod_syll p0 q0 q0 p0)).
            pose (S1 := (nicod_add p0 q0)).
            pose (S2 := (nicod_syll q0 (stroke p0 (stroke q0 q0)) (stroke p0 (stroke q0 q0)) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0)))))).
            pose (S3 := (ax_mp (stroke q0 (stroke (stroke p0 (stroke q0 q0)) (stroke p0 (stroke q0 q0)))) (stroke (stroke (stroke p0 (stroke q0 q0)) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))))) (stroke (stroke (stroke p0 (stroke q0 q0)) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))))) S1 S2)).
            pose (L2 := (ax_mp (stroke (stroke p0 (stroke q0 q0)) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) L1 S3)).
            pose (L3 := (nicod_syll (stroke q0 p0) (stroke p0 p0) (stroke p0 p0) p0)).
            pose (S4 := (nicod_id p0)).
            pose (S5 := (ax_mp (stroke p0 (stroke p0 p0)) (stroke (stroke p0 p0) p0) (stroke (stroke p0 p0) p0) S4 (nicod_perm (stroke p0 p0) p0))).
            pose (L4 := (ax_mp (stroke (stroke p0 p0) p0) (stroke q0 (stroke (stroke (stroke p0 p0) p0) (stroke (stroke p0 p0) p0))) (stroke q0 (stroke (stroke (stroke p0 p0) p0) (stroke (stroke p0 p0) p0))) S5 (nicod_add q0 (stroke (stroke p0 p0) p0)))).
            pose (S6 := (nicod_syll q0 (stroke (stroke p0 p0) p0) (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0)))).
            pose (S7 := (ax_mp (stroke q0 (stroke (stroke (stroke p0 p0) p0) (stroke (stroke p0 p0) p0))) (stroke (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) L4 S6)).
            pose (S8 := (nicod_syll (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0)))))).
            pose (S9 := (ax_mp (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))))) (stroke (stroke (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))))) L3 S8)).
            pose (S10 := (ax_mp (stroke (stroke (stroke (stroke p0 p0) p0) (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) S7 S9)).
            pose (S11 := (nicod_syll q0 (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0)))))).
            pose (S12 := (ax_mp (stroke q0 (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))))) (stroke (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke q0 (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke q0 (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))))) (stroke (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke (stroke q0 (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke q0 (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))))) L2 S11)).
            exact (ax_mp (stroke (stroke (stroke q0 p0) (stroke (stroke p0 p0) (stroke p0 p0))) (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke q0 (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) (stroke q0 (stroke (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))) (stroke q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0))))) S10 S12).
        }
        assert (B : (stroke (stroke L L) (stroke q0 q0))).
        {
            assert (L1 : forall (q1 s : Prop), (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s)))).
            {
                intros.
                pose (S1 := (nicod_genimpl_lemma q1 s)).
                pose (S2 := (nicod_syll (stroke q1 q1) (stroke s q1) (stroke s q1) (stroke (stroke q1 s) (stroke q1 s)))).
                pose (S3 := (ax_mp (stroke (stroke q1 q1) (stroke (stroke s q1) (stroke s q1))) (stroke (stroke (stroke s q1) (stroke (stroke q1 s) (stroke q1 s))) (stroke (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s))) (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s))))) (stroke (stroke (stroke s q1) (stroke (stroke q1 s) (stroke q1 s))) (stroke (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s))) (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s))))) S1 S2)).
                exact (ax_mp (stroke (stroke s q1) (stroke (stroke q1 s) (stroke q1 s))) (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s))) (stroke (stroke q1 q1) (stroke (stroke q1 s) (stroke q1 s))) (nicod_perm q1 s) S3).
            }
            pose (S1 := (L1 q0 (stroke (stroke (stroke q0 p0) p0) (stroke (stroke q0 p0) p0)))).
            exact (ax_mp (stroke (stroke q0 q0) (stroke L L)) (stroke (stroke L L) (stroke q0 q0)) (stroke (stroke L L) (stroke q0 q0)) S1 (nicod_perm (stroke L L) (stroke q0 q0))).
        }
        pose (S1 := (nicod_syll (stroke L L) q0 q0 (stroke L L))).
        pose (S2 := (ax_mp (stroke (stroke L L) (stroke q0 q0)) (stroke (stroke q0 (stroke L L)) (stroke (stroke (stroke L L) (stroke L L)) (stroke (stroke L L) (stroke L L)))) (stroke (stroke q0 (stroke L L)) (stroke (stroke (stroke L L) (stroke L L)) (stroke (stroke L L) (stroke L L)))) B S1)).
        pose (S3 := (ax_mp (stroke q0 (stroke L L)) (stroke (stroke L L) (stroke L L)) (stroke (stroke L L) (stroke L L)) A S2)).
        exact (ax_mp (stroke (stroke L L) (stroke L L)) L L S3 (nicod_taut L)).
    }
    pose (S1 := (nicod_syll p (stroke q r) (stroke q r) r)).
    pose (S2 := (L r q)).
    pose (S3 := (nicod_syll q (stroke (stroke q r) r) (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r)))).
    pose (S4 := (ax_mp (stroke q (stroke (stroke (stroke q r) r) (stroke (stroke q r) r))) (stroke (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) S2 S3)).
    pose (S5 := (nicod_syll (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r)))))).
    pose (S6 := (ax_mp (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))))) (stroke (stroke (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))))) (stroke (stroke (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))))) S1 S5)).
    exact (ax_mp (stroke (stroke (stroke (stroke q r) r) (stroke (stroke p r) (stroke p r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) (stroke (stroke p (stroke (stroke q r) (stroke q r))) (stroke (stroke q (stroke (stroke p r) (stroke p r))) (stroke q (stroke (stroke p r) (stroke p r))))) S4 S6).
Qed.

Theorem nicod_sum : forall (p q r : Prop), (stroke (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))).
    intros.
    assert (L : forall (p0 q0 r0 s : Prop), (stroke (stroke q0 s) (stroke (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke p0 s) (stroke p0 s))) (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke p0 s) (stroke p0 s)))))).
    {
        intros.
        pose (S1 := (nicod_syll p0 q0 r0 s)).
        pose (S2 := (nicod_assoc (stroke p0 (stroke q0 r0)) (stroke q0 s) (stroke (stroke p0 s) (stroke p0 s)))).
        exact (ax_mp (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke (stroke q0 s) (stroke (stroke p0 s) (stroke p0 s))) (stroke (stroke q0 s) (stroke (stroke p0 s) (stroke p0 s))))) (stroke (stroke q0 s) (stroke (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke p0 s) (stroke p0 s))) (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke p0 s) (stroke p0 s))))) (stroke (stroke q0 s) (stroke (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke p0 s) (stroke p0 s))) (stroke (stroke p0 (stroke q0 r0)) (stroke (stroke p0 s) (stroke p0 s))))) S1 S2).
    }
    exact (L (stroke p p) q q (stroke r r)).
Qed.

Definition not := fun (p : Prop) => (stroke p p).
Definition or := fun (p q : Prop) => (stroke (stroke p p) (stroke q q)).
Definition impl := fun (p q : Prop) => (or (not p) q).

Theorem mp : forall (p q : Prop) (min : p) (maj : (impl p q)), q.
    intros.
    pose (S1 := (ax_mp p (stroke (stroke p p) (stroke p p)) (stroke (stroke p p) (stroke p p)) min (nicod_add (stroke p p) p))).
    exact (ax_mp (stroke (stroke p p) (stroke p p)) q q S1 maj).
Qed.

Theorem pm_taut : forall (p : Prop), (impl (or p p) p).
    intros.
    pose (S1 := (nicod_taut p)).
    pose (S2 := (nicod_taut (or p p))).
    pose (S3 := (nicod_syll (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (or p p) (or p p) (stroke p p))).
    pose (S4 := (ax_mp (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke (or p p) (or p p))) (stroke (stroke (or p p) (stroke p p)) (stroke (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke p p)) (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke p p)))) (stroke (stroke (or p p) (stroke p p)) (stroke (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke p p)) (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke p p)))) S2 S3)).
    exact (ax_mp (stroke (or p p) (stroke p p)) (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke p p)) (stroke (stroke (stroke (or p p) (or p p)) (stroke (or p p) (or p p))) (stroke p p)) S1 S4).
Qed.

Theorem pm_add : forall (p q : Prop), (impl q (or p q)).
    intros.
    pose (S1 := (nicod_taut q)).
    pose (S2 := (nicod_add (stroke p p) q)).
    pose (S3 := (nicod_syll (stroke (stroke q q) (stroke q q)) q q (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q))))).
    pose (S4 := (ax_mp (stroke (stroke (stroke q q) (stroke q q)) (stroke q q)) (stroke (stroke q (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))))) (stroke (stroke q (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))))) S1 S3)).
    exact (ax_mp (stroke q (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke p p) (stroke q q)))) S2 S4).
Qed.

Theorem pm_perm : forall (p q : Prop), (impl (or p q) (or q p)).
    intros.
    pose (S1 := (nicod_taut (or p q))).
    pose (S2 := (nicod_perm (stroke q q) (stroke p p))).
    pose (S3 := (nicod_syll (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (or p q) (or p q) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p))))).
    pose (S4 := (ax_mp (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (or p q) (or p q))) (stroke (stroke (or p q) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))))) (stroke (stroke (or p q) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))))) S1 S3)).
    exact (ax_mp (stroke (or p q) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke q q) (stroke p p)) (stroke (stroke q q) (stroke p p)))) S2 S4).
Qed.

Theorem pm_assoc : forall (p q r : Prop), (impl (or p (or q r)) (or q (or p r))).
    intros.
    pose (S1 := (nicod_taut (or p (or q r)))).
    pose (S2 := (nicod_assoc (stroke p p) (stroke q q) (stroke r r))).
    pose (S3 := (nicod_syll (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (or p (or q r)) (or p (or q r)) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r))))))).
    pose (S4 := (ax_mp (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (or p (or q r)) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) (stroke (stroke (or p (or q r)) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) S1 S3)).
    exact (ax_mp (stroke (or p (or q r)) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (or p (or q r)) (or p (or q r))) (stroke (or p (or q r)) (or p (or q r)))) (stroke (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke q q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) S2 S4).
Qed.

Theorem pm_sum : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or p r))).
    intros.
    pose (S1 := (nicod_sum p q r)).
    pose (S2 := (nicod_add (stroke q q) q)).
    pose (S3 := (nicod_syll q (stroke (stroke q q) (stroke q q)) (stroke (stroke q q) (stroke q q)) (stroke r r))).
    pose (S4 := (ax_mp (stroke q (stroke (stroke (stroke q q) (stroke q q)) (stroke (stroke q q) (stroke q q)))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke q (stroke r r)) (stroke q (stroke r r)))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke q (stroke r r)) (stroke q (stroke r r)))) S2 S3)).
    pose (S5 := (nicod_syll (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke q (stroke r r)) (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r))))))).
    pose (S6 := (ax_mp (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke q (stroke r r)) (stroke q (stroke r r)))) (stroke (stroke (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) (stroke (stroke (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) S4 S5)).
    pose (S7 := (ax_mp (stroke (stroke q (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) S1 S6)).
    pose (S8 := (nicod_taut (or p q))).
    pose (S9 := (nicod_syll (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (or p q) (or p q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r))))).
    pose (S10 := (ax_mp (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (or p q) (or p q))) (stroke (stroke (or p q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (or p q) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) S8 S9)).
    pose (S11 := (nicod_syll (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r))))))).
    pose (S12 := (ax_mp (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) (stroke (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) S7 S11)).
    pose (S13 := (ax_mp (stroke (stroke (stroke (stroke p p) (stroke q q)) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke q q) (stroke q q)) (stroke r r)) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) S10 S12)).
    pose (S14 := (nicod_taut (impl q r))).
    pose (S15 := (nicod_syll (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (impl q r) (impl q r) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r))))))).
    pose (S16 := (ax_mp (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (impl q r) (impl q r))) (stroke (stroke (impl q r) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) (stroke (stroke (impl q r) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))))) S14 S15)).
    exact (ax_mp (stroke (impl q r) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) (stroke (stroke (stroke (impl q r) (impl q r)) (stroke (impl q r) (impl q r))) (stroke (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))) (stroke (stroke (stroke (or p q) (or p q)) (stroke (or p q) (or p q))) (stroke (stroke (stroke p p) (stroke r r)) (stroke (stroke p p) (stroke r r)))))) S13 S16).
Qed.
