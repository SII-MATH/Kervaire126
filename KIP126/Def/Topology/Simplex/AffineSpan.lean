module

public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

namespace KIP126.Topology.Simplex

open Affine

variable {ι E F : Type*} [Nonempty ι]
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The specified independent vertices, regarded as a basis of their actual
affine span. -/
noncomputable def independentSpanBasis (v : ι → E) (hv : AffineIndependent ℝ v) :
    AffineBasis ι ℝ (affineSpan ℝ (Set.range v)) where
  toFun i := ⟨v i, mem_affineSpan ℝ (Set.mem_range_self i)⟩
  ind' := hv.of_comp (affineSpan ℝ (Set.range v)).subtype
  tot' := by
    convert affineSpan_coe_preimage_eq_top (k := ℝ) (Set.range v) using 2
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩

/-- The actual affine equivalence determined by matching the two given
independent vertex families in their affine spans. -/
noncomputable def independentSpanAffineEquiv
    (v : ι → E) (w : ι → F)
    (hv : AffineIndependent ℝ v) (hw : AffineIndependent ℝ w) :
    affineSpan ℝ (Set.range v) ≃ᵃ[ℝ] affineSpan ℝ (Set.range w) := by
  let i : ι := Classical.choice inferInstance
  let b := independentSpanBasis v hv
  let c := independentSpanBasis w hw
  exact (AffineEquiv.vaddConst ℝ (b i)).symm.trans
    (((b.basisOf i).equiv (c.basisOf i) (Equiv.refl _)).toAffineEquiv.trans
      (AffineEquiv.vaddConst ℝ (c i)))

end KIP126.Topology.Simplex

end

section

namespace KIP126.Topology.Simplex

open Affine

variable {ι E F : Type*} [Nonempty ι]
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

@[simp] theorem independentSpanAffineEquiv_vertex
    (v : ι → E) (w : ι → F)
    (hv : AffineIndependent ℝ v) (hw : AffineIndependent ℝ w) (j : ι) :
    independentSpanAffineEquiv v w hv hw ⟨v j, mem_affineSpan ℝ (Set.mem_range_self j)⟩ =
      ⟨w j, mem_affineSpan ℝ (Set.mem_range_self j)⟩ := by
  classical
  let i : ι := Classical.choice inferInstance
  let b := independentSpanBasis v hv
  let c := independentSpanBasis w hw
  change (b.basisOf i).equiv (c.basisOf i) (Equiv.refl _) (b j -ᵥ b i) +ᵥ c i = c j
  by_cases h : j = i
  · subst j
    simp
  · rw [← b.basisOf_apply i ⟨j, h⟩, Module.Basis.equiv_apply]
    simp

end KIP126.Topology.Simplex

end
