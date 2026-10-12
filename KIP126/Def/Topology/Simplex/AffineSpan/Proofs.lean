module

public import KIP126.Def.Topology.Simplex.AffineSpan.Data
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

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
