module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.OnePoint.Data
public import KIP126.Def.Topology.Collapse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open Topology Set BasedSpace
open scoped unitInterval OnePoint

/-- The actual iterated reduced suspension is the one-point compactification
of real affine space, with the chosen basepoint sent to infinity. -/
theorem exists_sphereLevel_homeomorph_onePoint (n : ℕ) :
    ∃ e : sphereLevel n ≃ₜ OnePoint (Fin n → ℝ), e (sphereLevel n).point = ∞ := by
  classical
  induction n with
  | zero =>
    change ∃ e : Fin 2 ≃ₜ OnePoint (Fin 0 → ℝ), e 0 = ∞
    let e : Fin 2 ≃ OnePoint (Fin 0 → ℝ) := {
      toFun := fun x => if x = 0 then ∞ else ((0 : Fin 0 → ℝ) : OnePoint (Fin 0 → ℝ))
      invFun := fun x => x.elim 0 (fun _ => 1)
      left_inv := by intro x; fin_cases x <;> simp
      right_inv := by
        intro x
        induction x using OnePoint.rec with
        | infty => simp
        | coe v =>
          have hv : v = 0 := Subsingleton.elim _ _
          simp [hv] }
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) continuous_of_discreteTopology, rfl⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    let X := sphereLevel n
    letI : CompactSpace X := e.symm.compactSpace
    letI : T2Space X := e.symm.t2Space
    let S : Set (X × I) := {p | SuspensionCollapsed X p}
    have hS : IsClosed S :=
      (isClosed_eq continuous_fst continuous_const).union
        ((isClosed_eq continuous_snd continuous_const).union
          (isClosed_eq continuous_snd continuous_const))
    obtain ⟨c, hc, _⟩ := KIP126.Topology.exists_collapse_homeomorph_onePoint S hS
      ⟨(X.point, 0), Or.inl rfl⟩
    let p : {x : X // x ≠ X.point} ≃ₜ (Fin n → ℝ) :=
      (e.subtype (fun x => by
        change (x ≠ (sphereLevel n).point) ↔ (e x ≠ ∞)
        rw [← he]
        exact not_congr e.injective.eq_iff.symm)).trans (onePointComplementHomeomorph _)
    let q : (Sᶜ : Set (X × I)) ≃ₜ (Fin (n + 1) → ℝ) :=
      (suspensionComplementHomeomorph X).trans
        ((p.prodCongr intervalInteriorHomeomorphReal).trans
          (((Homeomorph.refl (Fin n → ℝ)).prodCongr
            (Homeomorph.funUnique (Fin 1) ℝ).symm).trans (Fin.appendHomeomorph n 1)))
    refine ⟨c.trans q.onePointCongr, ?_⟩
    change q.onePointCongr (c (Quot.mk _ (X.point, 0))) = ∞
    rw [hc]
    rfl

/-- The repository's point-set sphere levels are genuine Euclidean spheres. -/
theorem exists_sphereLevel_homeomorph_euclideanSphere (n : ℕ) :
    Nonempty (sphereLevel n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  obtain ⟨e, _⟩ := exists_sphereLevel_homeomorph_onePoint n
  exact ⟨e.trans (onePointEquivSphereOfFinrankEq (by simp))⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
