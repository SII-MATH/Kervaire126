import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
import KIP126.Def.ClassicalAdams.TowerFiltration.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory Pretriangulated KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Vanishing of the exact-couple connecting homomorphism is exactly
vanishing of the actual connecting map on this representative, not
vanishing of that connecting map as a morphism of spectra. -/
theorem adamsK_eq_zero_iff_comp_δ_eq_zero (s t : ℤ) (x : adamsE1 unit X s t) :
    adamsK unit X s t x = 0 ↔ x ≫ (adamsLayerTriangle unit X s).mor₃ = 0 := by
  have he := les_homotopy_exact_g
    (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
    (t - s) x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := he.mp hx
    change y ≫ (adamsLayerTriangle unit X s).mor₂ = x at hy
    exact (congrArg (fun z => z ≫ (adamsLayerTriangle unit X s).mor₃)
      hy.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun z => y ≫ z)
          (comp_distTriang_mor_zero₂₃ _ (adamsLayerTriangle_distinguished unit X s))).trans
            (Limits.comp_zero)))
  · intro hx
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _
      (adamsLayerTriangle_distinguished unit X s) x hx
    exact he.mpr ⟨y, hy.symm⟩

/-- A representative with zero connecting image is an actual r-cycle
for every finite page. This assertion alone does not imply nonzero survival. -/
theorem adamsCycles_mem_of_comp_δ_eq_zero (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (x : adamsE1 unit X s t) (hx : x ≫ (adamsLayerTriangle unit X s).mor₃ = 0) :
    x ∈ adamsCycles unit X r hr s t := by
  change adamsK unit X s t x ∈ LinearMap.range _
  refine ⟨0, ?_⟩
  rw [map_zero, (adamsK_eq_zero_iff_comp_δ_eq_zero unit X s t x).mpr hx]

/-- The same criterion reaches the actual intersection used for the internal
SSData's infinite cycle object; it says nothing about its boundary quotient. -/
theorem adamsCycleSubmodule_top_mem_of_comp_δ_eq_zero (s t : ℤ)
    (x : adamsCycleAmbient unit X s t)
    (hx : x.val ≫ (adamsLayerTriangle unit X s).mor₃ = 0) :
    x ∈ adamsCycleSubmodule unit X s t ⊤ := by
  apply (mem_adamsCycleSubmodule_top unit X s t x).mpr
  intro n
  exact adamsCycles_mem_of_comp_δ_eq_zero unit X (n + 2) (by omega) s t x.val hx

end
end KIP126.Classical.Adams
