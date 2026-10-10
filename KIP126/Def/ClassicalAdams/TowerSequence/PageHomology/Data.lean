import KIP126.Def.ClassicalAdams.TowerSequence.PagePassage.Proofs

/-!
# Homology of the actual Adams quotient pages

This isomorphism uses the same tower's specified page-passage quotient map.
Both the internal sequence and the optional Mathlib wrapper can reuse it
without importing the wrapper's spectral-sequence type.
-/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The page-passage isomorphism obtained by inverting the specified quotient map. -/
def adamsPageHomologyIso (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    (adamsPageComplex unit X r hr).homology p ≅
      adamsPageObject unit X (r + 1) (by omega) p :=
  ((adamsPageComplex unit X r hr).sc p).moduleCatHomologyIso ≪≫
    (LinearEquiv.ofBijective (adamsNextPageToHomology unit X r hr p)
      (adamsNextPageToHomology_bijective unit X r hr p)).toModuleIso.symm

end

end KIP126.Classical.Adams
