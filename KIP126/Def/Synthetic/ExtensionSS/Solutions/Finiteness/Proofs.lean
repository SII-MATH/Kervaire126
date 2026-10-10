import KIP126.Def.Synthetic.ExtensionSS.Solutions.Data
import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Finiteness.Proofs
import KIP126.Def.Algebra.ModuleCat.FreeRankOne.Proofs

namespace KIP126.Synthetic.SpectralSequence.SyntheticExtensionData

open CategoryTheory KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}

/-- A strict ESS fiber is finite when the actual source homotopy group is
finite. Boundedness of its filtration alone does not imply this hypothesis. -/
theorem finite_solutions_of_finite_source (D : SyntheticExtensionData F g)
    (degree : ℤ × ℤ) (n s : ℤ)
    (x : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ (D.complex degree).assocGraded s 1)
    (y : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ (D.complex degree).assocGraded (s + n) 0)
    [Finite (syntheticHomotopy X degree)] :
    Finite (FilteredComplex.Solutions.Fiber (D.complex degree) n s 1 x y) := by
  haveI : Finite (ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ (D.complex degree).A 1) := by
    change Finite (ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ syntheticHomotopy X degree)
    exact KIP126.Core.ModuleCat.finite_freeRankOne_hom _
  exact FilteredComplex.Solutions.finite_of_finite_source_hom

end KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
