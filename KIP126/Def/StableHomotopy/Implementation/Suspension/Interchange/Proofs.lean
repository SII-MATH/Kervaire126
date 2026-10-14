module

public import KIP126.Def.StableHomotopy.Implementation.PointSet
public import KIP126.Def.Topology.Cube.Rotation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open Topology
open scoped unitInterval

universe u

/-- Any continuous boundary-preserving square deformation acts on the two
suspension coordinates. This constructs the quotient family explicitly. -/
theorem suspensionRotationFamily_exists (A B : BasedSpace.{u}) (f : C(A × I, B))
    (hp : ∀ t, f (A.point, t) = B.point)
    (h0 : ∀ x, f (x, 0) = B.point) (h1 : ∀ x, f (x, 1) = B.point)
    (R : C(I × (I × I), I × I))
    (hR : ∀ s p, (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) →
      (R (s, p)).1 = 0 ∨ (R (s, p)).1 = 1 ∨
        (R (s, p)).2 = 0 ∨ (R (s, p)).2 = 1) :
    ∃ H : C(I × (A.suspension × I), B.suspension),
      (∀ u x s t, H (u, (suspensionProjection A (x, s), t)) =
        suspensionProjection B (f (x, (R (u, (t, s))).1), (R (u, (t, s))).2)) ∧
      (∀ u z t, z = A.suspension.point ∨ t = 0 ∨ t = 1 →
        H (u, (z, t)) = B.suspension.point) := by
  let raw (p : A × I) (ut : I × I) : B.suspension :=
    suspensionProjection B (f (p.1, (R (ut.1, (ut.2, p.2))).1), (R (ut.1, (ut.2, p.2))).2)
  have raw_boundary (p : A × I) (ut : I × I)
      (hb : p.1 = A.point ∨ p.2 = 0 ∨ p.2 = 1 ∨ ut.2 = 0 ∨ ut.2 = 1) :
      raw p ut = B.suspension.point := by
    apply suspensionProjection_collapsed
    rcases hb with hx | hb
    · exact Or.inl (by change f (p.1, _) = _; rw [hx, hp])
    · have hb' : ut.2 = 0 ∨ ut.2 = 1 ∨ p.2 = 0 ∨ p.2 = 1 := by tauto
      rcases hR ut.1 (ut.2, p.2) hb' with h | h | h | h
      · exact Or.inl (by rw [h, h0])
      · exact Or.inl (by rw [h, h1])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have raw_respects (ut : I × I) (p q : A × I) (hpq : SuspensionRelation A p q) :
      raw p ut = raw q ut := by
    have h (p : A × I) (hh : SuspensionCollapsed A p) :
        raw p ut = B.suspension.point := by
      apply raw_boundary
      rcases hh with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
    exact (h p hpq.1).trans (h q hpq.2).symm
  let G (z : A.suspension × (I × I)) : B.suspension :=
    Quot.lift (fun p => raw p z.2) (raw_respects z.2) z.1
  have hG : Continuous G := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    have hc : Continuous (fun z : (A × I) × (I × I) => R (z.2.1, (z.2.2, z.1.2))) :=
      R.continuous.comp (continuous_snd.fst.prodMk (continuous_snd.snd.prodMk continuous_fst.snd))
    exact (suspensionProjection B).continuous.comp
      ((f.continuous.comp (continuous_fst.fst.prodMk hc.fst)).prodMk hc.snd)
  let H : C(I × (A.suspension × I), B.suspension) :=
    ⟨fun z => G (z.2.1, (z.1, z.2.2)),
      hG.comp (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))⟩
  refine ⟨H, fun _ _ _ _ => rfl, ?_⟩
  intro u z t hz
  rcases hz with hz | hz | hz
  · subst z
    exact raw_boundary (A.point, 0) (u, t) (Or.inl rfl)
  · subst t
    induction z using Quot.inductionOn with
    | h p => exact raw_boundary p (u, 0) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · subst t
    induction z using Quot.inductionOn with
    | h p => exact raw_boundary p (u, 1) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end KIP126.StableHomotopy.Implementation.BasedSpace
