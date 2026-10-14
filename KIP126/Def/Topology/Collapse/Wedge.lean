module

public import KIP126.Def.Topology.Coproduct.Wedge.Proofs
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section

section

namespace KIP126.Topology

open scoped OnePoint

universe u v
variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)]
  [∀ j, T2Space (X j)]

/-- The actual proper summand inclusions extend over infinity and agree at
the common point of the quotient wedge. -/
def onePointWedgeToSigma :
    C(Wedge (fun j => OnePoint (X j)) (fun _ => ∞), OnePoint (Σ j, X j)) :=
  wedgeDesc _ _ ∞ (fun j => ⟨OnePoint.map (Sigma.mk j),
    OnePoint.continuous_map continuous_sigmaMk (by
      rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
      exact _root_.Topology.IsClosedEmbedding.sigmaMk.tendsto_cocompact)⟩)
    (fun _ => rfl)

end KIP126.Topology

end

section

namespace KIP126.Topology

open scoped OnePoint

universe u v
variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)]
  [∀ j, T2Space (X j)]

/-- A compact neighborhood inside one open summand remains a compact
neighborhood in the actual topological disjoint union. -/
instance sigma_weaklyLocallyCompactSpace [∀ j, WeaklyLocallyCompactSpace (X j)] :
    WeaklyLocallyCompactSpace (Σ j, X j) where
  exists_compact_mem_nhds z := by
    obtain ⟨K, hK, hzK⟩ := exists_compact_mem_nhds z.2
    exact ⟨Sigma.mk z.1 '' K, hK.image continuous_sigmaMk,
      isOpenMap_sigmaMk.image_mem_nhds hzK⟩

@[simp] theorem onePointWedgeToSigma_point :
    onePointWedgeToSigma X (wedgePoint (fun j => OnePoint (X j)) (fun _ => ∞)) = ∞ :=
  rfl

@[simp] theorem onePointWedgeToSigma_inclusion (j : J) (x : OnePoint (X j)) :
    onePointWedgeToSigma X
      (wedgeInclusion (fun j => OnePoint (X j)) (fun _ => ∞) j x) =
      OnePoint.map (Sigma.mk j) x := rfl

/-- The quotient identifies precisely the individual points at infinity;
the remaining points retain their summand and their original coordinate. -/
theorem onePointWedgeToSigma_bijective : Function.Bijective (onePointWedgeToSigma X) := by
  let g : OnePoint (Σ j, X j) → Wedge (fun j => OnePoint (X j)) (fun _ => ∞) :=
    fun y => y.elim (wedgePoint _ _) (fun z => wedgeInclusion _ _ z.1 z.2)
  have hleft : Function.LeftInverse g (onePointWedgeToSigma X) := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl z =>
        rcases z with ⟨j, x⟩
        induction x using OnePoint.rec with
        | infty => exact (wedgeInclusion_point j).symm
        | coe x => rfl
      | inr z => cases z; rfl
  have hright : Function.RightInverse g (onePointWedgeToSigma X) := by
    intro y
    induction y using OnePoint.rec with
    | infty => rfl
    | coe y => rcases y with ⟨j, x⟩; rfl
  exact ⟨hleft.injective, hright.surjective⟩

/-- For a finite family of locally compact Hausdorff spaces, the genuine
quotient wedge of their one-point compactifications is the one-point
compactification of their disjoint union, with the original inclusions. -/
theorem exists_onePointWedge_homeomorph_sigma [Finite J]
    [∀ j, LocallyCompactSpace (X j)] :
    ∃ h : Wedge (fun j => OnePoint (X j)) (fun _ => ∞) ≃ₜ OnePoint (Σ j, X j),
      h (wedgePoint _ _) = ∞ ∧
      ∀ j (x : OnePoint (X j)), h (wedgeInclusion _ _ j x) =
        OnePoint.map (Sigma.mk j) x := by
  let e := Equiv.ofBijective (onePointWedgeToSigma X) (onePointWedgeToSigma_bijective X)
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) (onePointWedgeToSigma X).continuous,
    rfl, fun _ _ => rfl⟩

end KIP126.Topology

end
