module

public import KIP126.Def.StableHomotopy.Implementation.PointSet
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Order.Interval.Set.IsoIoo

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open Topology Set
open scoped unitInterval OnePoint

noncomputable section

/-- The interior of the actual suspension interval is a real line. -/
def intervalInteriorHomeomorphReal : {t : I // t ≠ 0 ∧ t ≠ 1} ≃ₜ ℝ := by
  let e : {t : I // t ≠ 0 ∧ t ≠ 1} ≃ₜ Set.Ioo (-1 : ℝ) 1 := {
    toFun := fun t => ⟨2 * (t.val : ℝ) - 1, by
      have h0 : (0 : ℝ) < t.val := unitInterval.pos_iff_ne_zero.mpr t.property.1
      have h1 : (t.val : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr t.property.2
      constructor <;> linarith⟩
    invFun := fun t => ⟨⟨((t : ℝ) + 1) / 2, by
      constructor <;> linarith [t.property.1, t.property.2]⟩, by
      constructor
      · intro h
        have h' := congrArg (fun s : I => (s : ℝ)) h
        dsimp at h'
        linarith [t.property.1]
      · intro h
        have h' := congrArg (fun s : I => (s : ℝ)) h
        dsimp at h'
        linarith [t.property.2]⟩
    left_inv := by intro t; apply Subtype.ext; apply Subtype.ext; dsimp; ring
    right_inv := by intro t; apply Subtype.ext; dsimp; ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact e.trans (orderIsoIooNegOneOne ℝ).symm.toHomeomorph

/-- Removing infinity from a one-point compactification recovers its space. -/
def onePointComplementHomeomorph (V : Type*) [TopologicalSpace V] :
    {x : OnePoint V // x ≠ ∞} ≃ₜ V :=
  (Homeomorph.setCongr (OnePoint.compl_infty :
    ({∞}ᶜ : Set (OnePoint V)) = Set.range ((↑) : V → OnePoint V))).trans
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.symm

/-- The uncollapsed part of the suspension cylinder is the punctured space
times an open interval. -/
def suspensionComplementHomeomorph (X : BasedSpace) :
    {p : X × I // ¬ SuspensionCollapsed X p} ≃ₜ
      {x : X // x ≠ X.point} × {t : I // t ≠ 0 ∧ t ≠ 1} where
  toFun p := ⟨⟨p.val.1, fun h => p.property (Or.inl h)⟩,
    ⟨p.val.2, ⟨fun h => p.property (Or.inr (Or.inl h)),
      fun h => p.property (Or.inr (Or.inr h))⟩⟩⟩
  invFun p := ⟨(p.1.val, p.2.val), by
    rintro (h | h | h)
    · exact p.1.property h
    · exact p.2.property.1 h
    · exact p.2.property.2 h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end

end KIP126.StableHomotopy.Implementation.BasedSpace
