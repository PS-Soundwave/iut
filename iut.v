Require Import Ltac.

(* Stroke, understood through boolean logic as computing p nand q *)
Axiom stroke : forall (p q : Prop), Prop.

(* Nicod's single rule of inference for the stroke, as well as Lukasieqicz' singular axiom, using 1 less variable than Nicod's *)
Axiom ax_mp : forall (p q r : Prop) (min : p) (maj : (stroke p (stroke q r))), r.
Axiom ax_luk : forall (p q r s : Prop), (stroke (stroke p (stroke q r)) (stroke (stroke s (stroke s s)) (stroke (stroke s q) (stroke (stroke p s) (stroke p s))))).

(* A theorem from metamath, to bridge from the single axiom of Lukasiewicz to the traditional axiom of Nicod *)
(* We would be remiss to note that there is a much easier to follow development of Nicod's conclusions from Lukasiewicz' singular axiom due to Charle *)
(* We don't use this, as instead of following the work of Bernstein to correct ommissions in Nicod's original work and arrive at PM's axioms, Charle opts to instead provide proofs of Lukasiewicz' trio of axioms *)
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

(* The theorems of Nicod, from his single axiom. Included mostly to avoid having 3 axioms of propositional logic when only 1 is necessary *)

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
    assert (E : forall (p q r s t0 T : Prop) (P := (stroke p (stroke q r))) (WimplTP : (stroke T (stroke P P))), (stroke (stroke s P) (stroke (stroke T s) (stroke T s)))).
    {
        intros.
        pose (S1 := (nicod T P P s t0)).
        exact (ax_mp (stroke T (stroke P P)) (stroke t0 (stroke t0 t0)) (stroke (stroke s P) (stroke (stroke T s) (stroke T s))) WimplTP S1).
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

(* TODO: There's a few more theorems here. They're not particularly useful, but worth including for completeness of Nicod's work *)

(* PM Section 1 *)

(* Logical negation, disjunction, and material implication, consistent with PM's definitions *)
Definition not := fun (p : Prop) => (stroke p p).
Definition or := fun (p q : Prop) => (stroke (stroke p p) (stroke q q)).
Definition impl := fun (p q : Prop) => (or (not p) q).

(* The following proofs are original work, though presumably remarkably similar to those of Bernstein. *)
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

Theorem or_comm : forall (p q : Prop), (impl (or p q) (or q p)).
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

Theorem or_subr : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or p r))).
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

(* PM Section 2 *)

Theorem pm_abs : forall (p : Prop), (impl (impl p (not p)) (not p)).
    intros.
    exact (pm_taut (not p)).
Qed.

Theorem add : forall (p q : Prop), (impl q (impl p q)).
    intros.
    exact (pm_add (not p) q).
Qed.

Theorem con1 : forall (p q : Prop), (impl (impl p (not q)) (impl q (not p))).
    intros.
    exact (or_comm (not p) (not q)).
Qed.

Theorem comm : forall (p q r : Prop), (impl (impl p (impl q r)) (impl q (impl p r))).
    intros.
    exact (pm_assoc (not p) (not q) r).
Qed.

Theorem syll2 : forall (p q r : Prop), (impl (impl q r) (impl (impl p q) (impl p r))).
    intros.
    exact (or_subr (not p) q r).
Qed.

Theorem syll : forall (p q r : Prop), (impl (impl p q) (impl (impl q r) (impl p r))).
    intros.    
    pose (S1 := (comm (impl q r) (impl p q) (impl p r))).
    pose (S2 := (syll2 p q r)).
    exact (mp (impl (impl q r) (impl (impl p q) (impl p r))) (impl (impl p q) (impl (impl q r) (impl p r))) S2 S1).
Qed.

Theorem pm_2_07 : forall (p : Prop), (impl p (or p p)).
    intros.
    exact (pm_add p p).
Qed.

Theorem id : forall (p : Prop), (impl p p).
    intros.
    pose (S1 := (syll2 p (or p p) p)).
    pose (S2 := (pm_taut p)).
    pose (S3 := (mp (impl (or p p) p) (impl (impl p (or p p)) (impl p p)) S2 S1)).
    pose (S4 := (pm_2_07 p)).
    exact (mp (impl p (or p p)) (impl p p) S4 S3).
Qed.

Theorem pm_2_1 : forall (p : Prop), (or (not p) p).
    intros.
    exact (id p).
Qed.

Theorem exmid : forall (p : Prop), (or p (not p)).
    intros.
    pose (S1 := (or_comm (not p) p)).
    exact (mp (or (not p) p) (or p (not p)) (pm_2_1 p) S1).
Qed.

Theorem intro_dneg : forall (p : Prop), (impl p (not (not p))).
    intros.
    exact (exmid (not p)).
Qed.

Theorem pm_2_13 : forall (p : Prop), (or p (not (not (not p)))).
    intros.
    pose (S1 := (or_subr p (not p) (not (not (not p))))).
    pose (S2 := (intro_dneg (not p))).
    pose (S3 := (mp (impl (not p) (not (not (not p)))) (impl (or p (not p)) (or p (not (not (not p))))) S2 S1)).
    exact (mp (or p (not p)) (or p (not (not (not p)))) (exmid p) S3).
Qed.

Theorem elim_dneg : forall (p : Prop), (impl (not (not p)) p).
    intros.
    pose (S1 := (or_comm p (not (not (not p))))).
    exact (mp (or p (not (not (not p)))) (or (not (not (not p))) p) (pm_2_13 p) S1).
Qed.

Theorem con2 : forall (p q : Prop), (impl (impl (not p) q) (impl (not q) p)).
    intros.
    pose (S1 := (syll2 (not p) q (not (not q)))).
    pose (S2 := (intro_dneg q)).
    pose (S3 := (mp (impl q (not (not q))) (impl (impl (not p) q) (impl (not p) (not (not q)))) S2 S1)).
    pose (S4 := (con1 (not p) (not q))).
    pose (S5 := (syll2 (not q) (not (not p)) p)).
    pose (S6 := (mp (impl (not (not p)) p) (impl (impl (not q) (not (not p))) (impl (not q) p)) (elim_dneg p) S5)).
    pose (S7 := (syll2 (impl (not p) q) (impl (not p) (not (not q))) (impl (not q) (not (not p))))).
    pose (S8 := (mp (impl (impl (not p) (not (not q))) (impl (not q) (not (not p)))) (impl (impl (impl (not p) q) (impl (not p) (not (not q)))) (impl (impl (not p) q) (impl (not q) (not (not p))))) S4 S7)).
    pose (S9 := (mp (impl (impl (not p) q) (impl (not p) (not (not q)))) (impl (impl (not p) q) (impl (not q) (not (not p)))) S3 S8)).
    pose (S10 := (syll2 (impl (not p) q) (impl (not q) (not (not p))) (impl (not q) p))).
    pose (S11 := (mp (impl (impl (not q) (not (not p))) (impl (not q) p)) (impl (impl (impl (not p) q) (impl (not q) (not (not p)))) (impl (impl (not p) q) (impl (not q) p))) S6 S10)).
    exact (mp (impl (impl (not p) q) (impl (not q) (not (not p)))) (impl (impl (not p) q) (impl (not q) p)) S9 S11).
Qed.

(* Not present in PM. Encodes its abbreviated syllogism notation *)
Theorem sylli : forall (p q r : Prop) (P : (impl p q)) (Q : (impl q r)), (impl p r).
    intros.
    exact (mp (impl q r) (impl p r) Q (mp (impl p q) (impl (impl q r) (impl p r)) P (syll p q r))).
Qed.

Theorem con : forall (p q : Prop), (impl (impl p q) (impl (not q) (not p))).
    intros.
    pose (S1 := (mp (impl q (not (not q))) (impl (impl p q) (impl p (not (not q)))) (intro_dneg q) (syll2 p q (not (not q))))).
    pose (S2 := (con1 p (not q))).
    exact (sylli (impl p q) (impl p (not (not q))) (impl (not q) (not p)) S1 S2).
Qed.

Theorem con3 : forall (p q : Prop), (impl (impl (not q) (not p)) (impl p q)).
    intros.
    pose (S1 := (con1 (not q) p)).
    pose (S2 := (mp (impl (not (not q)) q) (impl (impl p (not (not q))) (impl p q)) (elim_dneg q) (syll2 p (not (not q)) q))).
    exact (sylli (impl (not q) (not p)) (impl p (not (not q))) (impl p q) S1 S2).
Qed.

Theorem contra : forall (p : Prop), (impl (impl (not p) p) p).
    intros.
    pose (S1 := (mp (impl p (not (not p))) (impl (impl (not p) p) (impl (not p) (not (not p)))) (intro_dneg p) (syll2 (not p) p (not (not p))))).
    pose (S2 := (pm_abs (not p))).
    pose (S3 := (sylli (impl (not p) p) (impl (not p) (not (not p))) (not (not p)) S1 S2)).
    pose (S4 := (elim_dneg p)).
    exact (sylli (impl (not p) p) (not (not p)) p S3 S4).
Qed.

Theorem intro_orr : forall (p q : Prop), (impl p (or p q)).
    intros.
    pose (S1 := (pm_add q p)).
    pose (S2 := (or_comm q p)).
    exact (sylli p (or q p) (or p q) S1 S2).
Qed.

Theorem exfalso : forall (p q : Prop), (impl (not p) (impl p q)).
    intros.
    exact (intro_orr (not p) q).
Qed.

Theorem pm_2_24 : forall (p q : Prop), (impl p (impl (not p) q)).
    intros.
    exact (mp (impl (not p) (impl p q)) (impl p (impl (not p) q)) (exfalso p q) (comm (not p) p q)).
Qed.

Theorem pm_2_25 : forall (p q : Prop), (or p (impl (or p q) q)).
    intros.
    pose (S1 := (pm_2_1 (or p q))).
    exact (mp (or (not (or p q)) (or p q)) (or p (impl (or p q) q)) S1 (pm_assoc (not (or p q)) p q)).
Qed.

Theorem pm_2_26 : forall (p q : Prop), (or (not p) (impl (impl p q) q)).
    intros.
    exact (pm_2_25 (not p) q).
Qed.

Theorem mpd : forall (p q : Prop), (impl p (impl (impl p q) q)).
    intros.
    exact (pm_2_26 p q).
Qed.

Theorem pm_2_3 : forall (p q r : Prop), (impl (or p (or q r)) (or p (or r q))).
    intros.
    pose (S1 := (or_comm q r)).
    exact (mp (impl (or q r) (or r q)) (impl (or p (or q r)) (or p (or r q))) S1 (or_subr p (or q r) (or r q))).
Qed.

Theorem or_assocc : forall (p q r : Prop), (impl (or p (or q r)) (or (or p q) r)).
    intros.
    pose (S1 := (pm_2_3 p q r)).
    pose (S2 := (sylli (or p (or q r)) (or p (or r q)) (or r (or p q)) S1 (pm_assoc p r q))).
    exact (sylli (or p (or q r)) (or r (or p q)) (or (or p q) r) S2 (or_comm r (or p q))).
Qed.

Theorem or_assoc : forall (p q r : Prop), (impl (or (or p q) r) (or p (or q r))).
    intros.
    pose (S1 := (or_comm (or p q) r)).
    pose (S2 := (sylli (or (or p q) r) (or r (or p q)) (or p (or r q)) S1 (pm_assoc r p q))).
    exact (sylli (or (or p q) r) (or p (or r q)) (or p (or q r)) S2 (pm_2_3 p r q)).
Qed.

Definition or3 := fun (p q r : Prop) => (or (or p q) r).

Theorem pm_2_36 : forall (p q r : Prop), (impl (impl q r) (impl (or p q) (or r p))).
    intros.
    pose (S1 := (mp (impl (or p r) (or r p)) (impl (impl (or p q) (or p r)) (impl (or p q) (or r p))) (or_comm p r) (syll2 (or p q) (or p r) (or r p)))).
    pose (S2 := (or_subr p q r)).
    exact (sylli (impl q r) (impl (or p q) (or p r)) (impl (or p q) (or r p)) S2 S1).
Qed.

Theorem pm_2_37 : forall (p q r : Prop), (impl (impl q r) (impl (or q p) (or p r))).
    intros.
    pose (S1 := (mp (impl (or q p) (or p q)) (impl (impl (or p q) (or p r)) (impl (or q p) (or p r))) (or_comm q p) (syll (or q p) (or p q) (or p r)))).
    pose (S2 := (or_subr p q r)).
    exact (sylli (impl q r) (impl (or p q) (or p r)) (impl (or q p) (or p r)) S2 S1).
Qed.

Theorem or_subl : forall (p q r : Prop), (impl (impl q r) (impl (or q p) (or r p))).
    intros.
    pose (S1 := (mp (impl (or p r) (or r p)) (impl (impl (or q p) (or p r)) (impl (or q p) (or r p))) (or_comm p r) (syll2 (or q p) (or p r) (or r p)))).
    pose (S2 := (pm_2_37 p q r)).
    exact (sylli (impl q r) (impl (or q p) (or p r)) (impl (or q p) (or r p)) S2 S1).
Qed.

Theorem pm_2_4 : forall (p q : Prop), (impl (or p (or p q)) (or p q)).
    intros.
    pose (S1 := (or_assocc p p q)).
    pose (S2 := (mp (impl (or p p) p) (impl (or (or p p) q) (or p q)) (pm_taut p) (or_subl q (or p p) p))).
    exact (sylli (or p (or p q)) (or (or p p) q) (or p q) S1 S2).
Qed.

Theorem pm_2_41 : forall (p q : Prop), (impl (or q (or p q)) (or p q)).
    intros.
    pose (S1 := (pm_assoc q p q)).
    pose (S2 := (mp (impl (or q q) q) (impl (or p (or q q)) (or p q)) (pm_taut q) (or_subr p (or q q) q))).
    exact (sylli (or q (or p q)) (or p (or q q)) (or p q) S1 S2).
Qed.

Theorem pm_2_42 : forall (p q : Prop), (impl (or (not p) (impl p q)) (impl p q)).
    intros.
    exact (pm_2_4 (not p) q).
Qed.

Theorem pm_2_43 : forall (p q : Prop), (impl (impl p (impl p q)) (impl p q)).
    intros.
    exact (pm_2_42 p q).
Qed.

Theorem pm_2_45 : forall (p q : Prop), (impl (not (or p q)) (not p)).
    intros.
    exact (mp (impl p (or p q)) (impl (not (or p q)) (not p)) (intro_orr p q) (con p (or p q))).
Qed.

Theorem pm_2_46 : forall (p q : Prop), (impl (not (or p q)) (not q)).
    intros.
    exact (mp (impl q (or p q)) (impl (not (or p q)) (not q)) (pm_add p q) (con q (or p q))).
Qed.

Theorem pm_2_47 : forall (p q : Prop), (impl (not (or p q)) (or (not p) q)).
    intros.
    exact (sylli (not (or p q)) (not p) (or (not p) q) (pm_2_45 p q) (intro_orr (not p) q)).
Qed.

Theorem pm_2_48 : forall (p q : Prop), (impl (not (or p q)) (or p (not q))).
    intros.
    exact (sylli (not (or p q)) (not q) (or p (not q)) (pm_2_46 p q) (pm_add p (not q))).
Qed.

Theorem pm_2_49 : forall (p q : Prop), (impl (not (or p q)) (or (not p) (not q))).
    intros.
    exact (sylli (not (or p q)) (not p) (or (not p) (not q)) (pm_2_45 p q) (intro_orr (not p) (not q))).
Qed.

Theorem pm_2_5 : forall (p q : Prop), (impl (not (impl p q)) (impl (not p) q)).
    intros.
    exact (pm_2_47 (not p) q).
Qed.

Theorem pm_2_51 : forall (p q : Prop), (impl (not (impl p q)) (impl p (not q))).
    intros.
    exact (pm_2_48 (not p) q).
Qed.

Theorem pm_2_52 : forall (p q : Prop), (impl (not (impl p q)) (impl (not p) (not q))).
    intros.
    exact (pm_2_49 (not p) q).
Qed.

Theorem pm_2_521 : forall (p q : Prop), (impl (not (impl p q)) (impl q p)).
    intros.
    exact (sylli (not (impl p q)) (impl (not p) (not q)) (impl q p) (pm_2_52 p q) (con3 q p)).
Qed.

Theorem pm_2_53 : forall (p q : Prop), (impl (or p q) (impl (not p) q)).
    intros.
    exact (mp (impl p (not (not p))) (impl (or p q) (impl (not p) q)) (intro_dneg p) (or_subl q p (not (not p)))).
Qed.

Theorem pm_2_54 : forall (p q : Prop), (impl (impl (not p) q) (or p q)).
    intros.
    exact (mp (impl (not (not p)) p) (impl (impl (not p) q) (or p q)) (elim_dneg p) (or_subl q (not (not p)) p)).
Qed.

Theorem pm_2_55 : forall (p q : Prop), (impl (not p) (impl (or p q) q)).
    intros.
    exact (mp (impl (or p q) (impl (not p) q)) (impl (not p) (impl (or p q) q)) (pm_2_53 p q) (comm (or p q) (not p) q)).
Qed.

Theorem pm_2_56 : forall (p q : Prop), (impl (not q) (impl (or p q) p)).
    intros.
    pose (S1 := (pm_2_55 q p)).
    pose (S2 := (mp (impl (or p q) (or q p)) (impl (impl (or q p) p) (impl (or p q) p)) (or_comm p q) (syll (or p q) (or q p) p))).
    exact (sylli (not q) (impl (or q p) p) (impl (or p q) p) S1 S2).
Qed.

Theorem pm_2_6 : forall (p q : Prop), (impl (impl (not p) q) (impl (impl p q) q)).
    intros.
    pose (S1 := (or_subl q (not p) q)).
    pose (S2 := (mp (impl (or q q) q) (impl (impl (or (not p) q) (or q q)) (impl (or (not p) q) q)) (pm_taut q) (syll2 (or (not p) q) (or q q) q))).
    exact (sylli (impl (not p) q) (impl (or (not p) q) (or q q)) (impl (impl p q) q) S1 S2).
Qed.

Theorem pm_2_61 : forall (p q : Prop), (impl (impl p q) (impl (impl (not p) q) q)).
    intros.
    exact (mp (impl (impl (not p) q) (impl (impl p q) q)) (impl (impl p q) (impl (impl (not p) q) q)) (pm_2_6 p q) (comm (impl (not p) q) (impl p q) q)).
Qed.

Theorem pm_2_62 : forall (p q : Prop), (impl (or p q) (impl (impl p q) q)).
    intros.
    exact (sylli (or p q) (impl (not p) q) (impl (impl p q) q) (pm_2_53 p q) (pm_2_6 p q)).
Qed.

Theorem pm_2_621 : forall (p q : Prop), (impl (impl p q) (impl (or p q) q)).
    intros.
    exact (mp (impl (or p q) (impl (impl p q) q)) (impl (impl p q) (impl (or p q) q)) (pm_2_62 p q) (comm (or p q) (impl p q) q)).
Qed.

Theorem pm_2_63 : forall (p q : Prop), (impl (or p q) (impl (or (not p) q) q)).
    intros.
    exact (pm_2_62 p q).
Qed.

Theorem pm_2_64 : forall (p q : Prop), (impl (or p q) (impl (or p (not q)) p)).
    intros.
    pose (S1 := pm_2_63 q p).
    pose (S2 := (or_comm p (not q))).
    pose (S3 := (mp (impl (or p (not q)) (or (not q) p)) (impl (impl (or (not q) p) p) (impl (or p (not q)) p)) S2 (syll (or p (not q)) (or (not q) p) p))).
    pose (S4 := (sylli (or q p) (impl (or (not q) p) p) (impl (or p (not q)) p) S1 S3)).
    exact (sylli (or p q) (or q p) (impl (or p (not q)) p) (or_comm p q) S4).
Qed.

Theorem pm_2_65 : forall (p q : Prop), (impl (impl p q) (impl (impl p (not q)) (not p))).
    intros.
    exact (pm_2_64 (not p) q).
Qed.

Theorem pm_2_67 : forall (p q : Prop), (impl (impl (or p q) q) (impl p q)).
    intros.
    pose (S1 := (mp (impl (impl (not p) q) (or p q)) (impl (impl (or p q) q) (impl (impl (not p) q) q)) (pm_2_54 p q) (syll (impl (not p) q) (or p q) q))).
    pose (S2 := (mp (impl p (impl (not p) q)) (impl (impl (impl (not p) q) q) (impl p q)) (pm_2_24 p q) (syll p (impl (not p) q) q))).
    exact (sylli (impl (or p q) q) (impl (impl (not p) q) q) (impl p q) S1 S2).
Qed.

Theorem pm_2_68 : forall (p q : Prop), (impl (impl (impl p q) q) (or p q)).
    intros.
    pose (S1 := (pm_2_67 (not p) q)).
    exact (sylli (impl (or (not p) q) q) (impl (not p) q) (or p q) S1 (pm_2_54 p q)).
Qed.

Theorem pm_2_69 : forall (p q : Prop), (impl (impl (impl p q) q) (impl (impl q p) p)).
    intros.
    pose (S1 := (pm_2_68 p q)).
    pose (S2 := (sylli (impl (impl p q) q) (or p q) (or q p) S1 (or_comm p q))).
    exact (sylli (impl (impl p q) q) (or q p) (impl (impl q p) p) S2 (pm_2_62 q p)).
Qed.

Theorem pm_2_73 : forall (p q r : Prop), (impl (impl p q) (impl (or3 p q r) (or q r))).
    intros.
    pose (S1 := (pm_2_621 p q)).
    exact (sylli (impl p q) (impl (or p q) q) (impl (or (or p q) r) (or q r)) S1 (or_subl r (or p q) q)).
Qed.

Theorem pm_2_74 : forall (p q r : Prop), (impl (impl q p) (impl (or3 p q r) (or p r))).
    intros.
    pose (S1 := (pm_2_73 q p r)).
    pose (S2 := (or_assoc p q r)).
    pose (S3 := (sylli (or3 p q r) (or p (or q r)) (or q (or p r)) S2 (pm_assoc p q r))).
    pose (S4 := (sylli (or3 p q r) (or q (or p r)) (or3 q p r) S3 (or_assocc q p r))).
    pose (S5 := (mp (impl (or3 p q r) (or3 q p r)) (impl (impl (or3 q p r) (or p r)) (impl (or3 p q r) (or p r))) S4 (syll (or3 p q r) (or3 q p r) (or p r)))).
    exact (sylli (impl q p) (impl (or3 q p r) (or p r)) (impl (or3 p q r) (or p r)) S1 S5).
Qed.

Theorem pm_2_75 : forall (p q r : Prop), (impl (or p q) (impl (or p (impl q r)) (or p r))).
    intros.
    pose (S1 := (pm_2_74 p (not q) r)).
    pose (S2 := (sylli (or q p) (impl (not q) p) (impl (or3 p (not q) r) (or p r)) (pm_2_53 q p) S1)).
    pose (S3 := (sylli (or p q) (or q p) (impl (or3 p (not q) r) (or p r)) (or_comm p q) S2)).
    pose (S4 := (or_assocc p (not q) r)).
    pose (S5 := (mp (impl (or p (or (not q) r)) (or (or p (not q)) r)) (impl (impl (or3 p (not q) r) (or p r)) (impl (or p (impl q r)) (or p r))) S4 (syll (or p (or (not q) r)) (or (or p (not q)) r) (or p r)))).
    exact (sylli (or p q) (impl (or3 p (not q) r) (or p r)) (impl (or p (impl q r)) (or p r)) S3 S5).
Qed.

Theorem pm_2_76 : forall (p q r : Prop), (impl (or p (impl q r)) (impl (or p q) (or p r))).
    intros.
    exact (mp (impl (or p q) (impl (or p (impl q r)) (or p r))) (impl (or p (impl q r)) (impl (or p q) (or p r))) (pm_2_75 p q r) (comm (or p q) (or p (impl q r)) (or p r))).
Qed.

Theorem pm_2_77 : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (impl p q) (impl p r))).
    intros.
    exact (pm_2_76 (not p) q r).
Qed.

Theorem pm_2_8 : forall (q r s : Prop), (impl (or q r) (impl (or (not r) s) (or q s))).
    intros.
    pose (S1 := (sylli (or q r) (or r q) (impl (not r) q) (or_comm q r) (pm_2_53 r q))).
    exact (sylli (or q r) (impl (not r) q) (impl (or (not r) s) (or q s)) S1 (or_subl s (not r) q)).
Qed.

Theorem pm_2_81 : forall (p q r s : Prop), (impl (impl q (impl r s)) (impl (or p q) (impl (or p r) (or p s)))).
    intros.
    pose (S1 := (or_subr p q (impl r s))).
    pose (S2 := (mp (impl (or p (impl r s)) (impl (or p r) (or p s))) (impl (impl (or p q) (or p (impl r s))) (impl (or p q) (impl (or p r) (or p s)))) (pm_2_76 p r s) (syll2 (or p q) (or p (impl r s)) (impl (or p r) (or p s))))).
    exact (sylli (impl q (impl r s)) (impl (or p q) (or p (impl r s))) (impl (or p q) (impl (or p r) (or p s))) S1 S2).
Qed.

Theorem pm_2_82 : forall (p q r s : Prop), (impl (or3 p q r) (impl (or3 p (not r) s) (or3 p q s))).
    intros.
    pose (S1 := (mp (impl (or q r) (impl (or (not r) s) (or q s))) (impl (or p (or q r)) (impl (or p (or (not r) s)) (or p (or q s)))) (pm_2_8 q r s) (pm_2_81 p (or q r) (or (not r) s) (or q s)))).
    pose (S2 := (sylli (or3 p q r) (or p (or q r)) (impl (or p (or (not r) s)) (or p (or q s))) (or_assoc p q r) S1)).
    pose (S3 := (mp (impl (or p (or q s)) (or3 p q s)) (impl (impl (or p (or (not r) s)) (or p (or q s))) (impl (or p (or (not r) s)) (or3 p q s))) (or_assocc p q s) (syll2 (or p (or (not r) s)) (or p (or q s)) (or3 p q s)))).
    pose (S4 := (sylli (or3 p q r) (impl (or p (or (not r) s)) (or p (or q s))) (impl (or p (or (not r) s)) (or3 p q s)) S2 S3)).
    pose (S5 := (mp (impl (or3 p (not r) s) (or p (or (not r) s))) (impl (impl (or p (or (not r) s)) (or3 p q s)) (impl (or3 p (not r) s) (or3 p q s))) (or_assoc p (not r) s) (syll (or3 p (not r) s) (or p (or (not r) s)) (or3 p q s)))).
    exact (sylli (or3 p q r) (impl (or p (or (not r) s)) (or3 p q s)) (impl (or3 p (not r) s) (or3 p q s)) S4 S5).
Qed.

Theorem sylldc : forall (p q r s : Prop), (impl (impl p (impl q r)) (impl (impl p (impl r s)) (impl p (impl q s)))).
    intros.
    pose (S1 := (pm_2_82 (not p) (not q) r s)).
    pose (S2 := (sylli (or (not p) (or (not q) r)) (or3 (not p) (not q) r) (impl (or3 (not p) (not r) s)
    (or3 (not p) (not q) s)) (or_assocc (not p) (not q) r) S1)).
    pose (S3 := (mp (impl (or3 (not p) (not q) s) (or (not p) (or (not q) s))) (impl (impl (or3 (not p) (not r) s) (or3 (not p) (not q) s)) (impl (or3 (not p) (not r) s) (or (not p) (or (not q) s)))) (or_assoc (not p) (not q) s) (syll2 (or3 (not p) (not r) s) (or3 (not p) (not q) s) (or (not p) (or (not q) s))))).
    pose (S4 := (sylli (or (not p) (or (not q) r)) (impl (or3 (not p) (not r) s) (or3 (not p) (not q) s)) (impl (or3 (not p) (not r) s) (or (not p) (or (not q) s))) S2 S3)).
    pose (S5 := (mp (impl (or (not p) (or (not r) s)) (or3 (not p) (not r) s)) (impl (impl (or3 (not p) (not r) s) (or (not p) (or (not q) s))) (impl (or (not p) (or (not r) s)) (or (not p) (or (not q) s)))) (or_assocc (not p) (not r) s) (syll (or (not p) (or (not r) s)) (or3 (not p) (not r) s) (or (not p) (or (not q) s))))).
    exact (sylli (or (not p) (or (not q) r)) (impl (or3 (not p) (not r) s) (or (not p) (or (not q) s))) (impl (or (not p) (or (not r) s)) (or (not p) (or (not q) s))) S4 S5).
Qed.

Theorem pm_2_85 : forall (p q r : Prop), (impl (impl (or p q) (or p r)) (or p (impl q r))).
    intros.
    pose (S1 := (mp (impl q (or p q)) (impl (impl (or p q) r) (impl q r)) (pm_add p q) (syll q (or p q) r))).
    pose (S2 := (pm_2_55 p r)).
    pose (S3 := (sylli (not p) (impl (or p r) r) (impl (impl (or p q) (or p r)) (impl (or p q) r)) S2 (syll2 (or p q) (or p r) r))).
    pose (S4 := (sylli (not p) (impl (impl (or p q) (or p r)) (impl (or p q) r)) (impl (impl (or p q) (or p r)) (impl q r)) S3 (mp (impl (impl (or p q) r) (impl q r)) (impl (impl (impl (or p q) (or p r)) (impl (or p q) r)) (impl (impl (or p q) (or p r)) (impl q r))) S1 (syll2 (impl (or p q) (or p r)) (impl (or p q) r) (impl q r))))).
    pose (S5 := (mp (impl (not p) (impl (impl (or p q) (or p r)) (impl q r))) (impl (impl (or p q) (or p r)) (impl (not p) (impl q r))) S4 (comm (not p) (impl (or p q) (or p r)) (impl q r)))).
    exact (sylli (impl (or p q) (or p r)) (impl (not p) (impl q r)) (or p (impl q r)) S5 (pm_2_54 p (impl q r))).
Qed.

Theorem pm_2_86: forall (p q r : Prop), (impl (impl (impl p q) (impl p r)) (impl p (impl q r))).
    intros.
    exact (pm_2_85 (not p) q r).
Qed.

(* PM Section 3 *)

(* Logical conjunction and trivalent implication *)
Definition and := fun (p q : Prop) => (not (or (not p) (not q))).
Definition impl3 := fun (p q r : Prop) => (and (impl p q) (impl q r)).

Theorem andi : forall (p q : Prop) (Wp : p) (Wq : q), (and p q).
    intros.
    pose (S1 := (exmid (or (not p) (not q)))).
    pose (S2 := (mp (or (or (not p) (not q)) (not (or (not p) (not q)))) (or (not p) (or (not q) (not (or (not p) (not q))))) S1 (or_assoc (not p) (not q) (not (or (not p) (not q)))))).
    pose (S3 := (mp p (impl q (and p q)) Wp S2)).
    exact (mp q (and p q) Wq S3).
Qed.

Theorem elim_and : forall (p q : Prop), (impl (and p q) (not (or (not p) (not q)))).
    intros.
    exact (id (and p q)).
Qed.

Theorem intro_and : forall (p q : Prop), (impl (not (or (not p) (not q))) (and p q)).
    intros.
    exact (id (and p q)).
Qed.

Theorem pm_3_12 : forall (p q : Prop), (or3 (not p) (not q) (and p q)).
    intros.
    exact (exmid (or (not p) (not q))).
Qed.

Theorem demorgan_and : forall (p q : Prop), (impl (not (and p q)) (or (not p) (not q))).
    intros.
    exact (mp (impl (not (or (not p) (not q))) (and p q)) (impl (not (and p q)) (or (not p) (not q))) (intro_and p q) (con2 (or (not p) (not q)) (and p q))).
Qed.

Theorem demorgan_andc : forall (p q : Prop), (impl (or (not p) (not q)) (not (and p q))).
    intros.
    exact (mp (impl (and p q) (not (or (not p) (not q)))) (impl (or (not p) (not q)) (not (and p q))) (elim_and p q) (con1 (and p q) (or (not p) (not q)))).
Qed.

Theorem andd : forall (p q : Prop), (impl p (impl q (and p q))).
    intros.
    exact (mp (or3 (not p) (not q) (and p q)) (impl p (impl q (and p q))) (pm_3_12 p q) (or_assoc (not p) (not q) (and p q))).
Qed.

Theorem pm_3_21 : forall (p q : Prop), (impl q (impl p (and p q))).
    intros.
    exact (mp (impl p (impl q (and p q))) (impl q (impl p (and p q))) (andd p q) (comm p q (and p q))).
Qed.

Theorem and_comm : forall (p q : Prop), (impl (and p q) (and q p)).
    intros.
    pose (S1 := (demorgan_and q p)).
    pose (S2 := (sylli (not (and q p)) (or (not q) (not p)) (or (not p) (not q)) S1 (or_comm (not q) (not p)))).
    pose (S3 := (sylli (not (and q p)) (or (not p) (not q)) (not (and p q)) S2 (demorgan_andc p q))).
    exact (mp (impl (not (and q p)) (not (and p q))) (impl (and p q) (and q p)) S3 (con3 (and p q) (and q p))).
Qed.

Theorem non_contra : forall (p q : Prop), (not (and p (not p))).
    intros.
    pose (S1 := (exmid (not p))).
    exact (mp (or (not p) (not (not p))) (not (and p (not p))) S1 (demorgan_andc p (not p))).
Qed.

Theorem simpl : forall (p q : Prop), (impl (and p q) p).
    intros.
    pose (S1 := (add q p)).
    pose (S2 := (mp (impl p (impl q p)) (or (or (not p) (not q)) p) S1 (or_assocc (not p) (not q) p))).
    exact (mp (or (or (not p) (not q)) p) (impl (not (or (not p) (not q))) p) S2 (pm_2_53 (or (not p) (not q)) p)).
Qed.

Theorem simpr : forall (p q : Prop), (impl (and p q) q).
    intros.
    exact (sylli (and p q) (and q p) q (and_comm p q) (simpl q p)).
Qed.

Theorem exp : forall (p q r : Prop), (impl (impl (and p q) r) (impl p (impl q r))).
    intros.
    pose (S1 := (id (impl (and p q) r))).
    pose (S2 := (sylli (impl (and p q) r) (impl (and p q) r) (impl (not r) (or (not p) (not q))) S1 (con2 (or (not p) (not q)) r))).
    pose (S3 := (sylli (impl (and p q) r) (impl (not r) (or (not p) (not q))) (impl p (impl (not r) (not q))) S2 (comm (not r) p (not q)))).
    pose (S4 := (mp (impl (impl (not r) (not q)) (impl q r)) (impl (impl p (impl (not r) (not q))) (impl p (impl q r))) (con3 q r) (syll2 p (impl (not r) (not q)) (impl q r)))).
    exact (sylli (impl (and p q) r) (impl p (impl (not r) (not q))) (impl p (impl q r)) S3 S4).
Qed.

Theorem imp : forall (p q r : Prop), (impl (impl p (impl q r)) (impl (and p q) r)).
    intros.
    pose (S1 := (id (impl p (impl q r)))).
    pose (S2 := (sylli (impl p (impl q r)) (impl p (impl q r)) (or (or (not p) (not q)) r)) S1 (or_assocc (not p) (not q) r)).
    exact (sylli (impl p (impl q r)) (or (or (not p) (not q)) r) (impl (and p q) r) S2 (pm_2_53 (or (not p) (not q)) r)).
Qed.

Theorem andsyll : forall (p q r : Prop), (impl (and (impl p q) (impl q r)) (impl p r)).
    intros.
    exact (mp (impl (impl p q) (impl (impl q r) (impl p r))) (impl (and (impl p q) (impl q r)) (impl p r)) (syll p q r) (imp (impl p q) (impl q r) (impl p r))).
Qed.

Theorem andsyll2 : forall (p q r : Prop), (impl (and (impl q r) (impl p q)) (impl p r)).
    intros.
    exact (mp (impl (impl q r) (impl (impl p q) (impl p r))) (impl (and (impl q r) (impl p q)) (impl p r)) (syll2 p q r) (imp (impl q r) (impl p q) (impl p r))).
Qed.

Theorem andmp : forall (p q : Prop), (impl (and p (impl p q)) q).
    intros.
    exact (mp (impl p (impl (impl p q) q)) (impl (and p (impl p q)) q) (mpd p q) (imp p (impl p q) q)).
Qed.

Theorem pm_3_37 : forall (p q r : Prop), (impl (impl (and p q) r) (impl (and p (not r)) (not q))).
    intros.
    pose (S1 := (con q r)).
    pose (S2 := (mp (impl (impl q r) (impl (not r) (not q))) (impl (impl p (impl q r)) (impl p (impl (not r) (not q)))) S1 (syll2 p (impl q r) (impl (not r) (not q))))).
    pose (S3 := (exp p q r)).
    pose (S4 := (imp p (not r) (not q))).
    exact (sylli (impl (and p q) r) (impl p (impl q r)) (impl (and p (not r)) (not q)) S3 (sylli (impl p (impl q r)) (impl p (impl (not r) (not q))) (impl (and p (not r)) (not q)) S2 S4)).
Qed.

Theorem pm_3_4 : forall (p q : Prop), (impl (and p q) (impl p q)).
    intros.
    exact (mp (impl (not (impl p q)) (impl p (not q))) (impl (and p q) (impl p q)) (pm_2_51 p q) (con2 (impl p q) (or (not p) (not q)))).
Qed.

(* TODO: Complete PM section 3 from 3.41 *)

(* PM Section 4 *)

(* Bidirectional implication *)
Definition bi := fun (p q : Prop) => (and (impl p q) (impl q p)).

(* TODO: Complete PM sections 4 and 5 *)

(* The type of classes. Any predicative type such as Set would do, but it would be confusing to use Set where we really mean a potentially proper class *)
Axiom Class : Type.

(* Since Coq doesn't have implicit subtyping, we have to make the "sets are classes" subtyping explicit, either through a typeclass, or in this case, a predicate on classes with the interpretation "is a set" *)
Axiom is_set : forall (p : Class), Prop.

(* Universal quantification over sets. The restriction to sets is enforced by our choice of axioms *)
Axiom all : forall (P : forall (x : Class), Prop), Prop.
(* Existential quantification over sets *)
Definition ex := fun (P : forall (x : Class), Prop) => (not (all (fun (x : Class) => (not (P x))))).

(* Axiom of specialization. The hypothesis that the argument specialized for must be a set is what restricts the domain of discourse to sets *)
Axiom ax_spec : forall (P : forall (x : Class), Prop) (y : Class) (Vy : (is_set y)), (impl (all P) (P y)).

(* Axioms of generalization and quantified implication. Axioms of free logic, in that they apply over all domains of discourse, in the presence of a suitable axiom of specialization *)
Axiom ax_gen : forall (P : forall (x : Class), Prop) (Wp : forall (x : Class), (P x)), (all P).
Axiom ax_quant_impl : forall (p : Prop) (Q : forall (x : Class), Prop), (impl (all (fun (x : Class) => (impl p (Q x)))) (impl p (all Q))).

(* PM Section 10 *)

Theorem pm_10_14 : forall (P Q : forall (x : Class), Prop) (y : Class) (Vy : (is_set y)), (impl (and (all P) (all Q)) (and (P y) (Q y))).
    intros.
    pose (S1 := (ax_spec P y Vy)).
    pose (S2 := (ax_spec Q y Vy)).
    pose (S3 := (andi (impl (all P) (P y)) (impl (all Q) (Q y)) S1 S2)).
Admitted.

(* TODO: Complete PM section 10 *)

(* Define "element of" *)
Axiom el : forall (p q : Set), Prop.
