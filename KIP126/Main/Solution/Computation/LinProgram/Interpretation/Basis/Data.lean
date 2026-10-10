import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

namespace KIP126.Classical.Adams
open KIP126.LinE2 KIP126.Core.Algebra

/-- The actual internal E₂ coordinates delivered by the same Challenge2
witness as `linE2Presentation`. No scalar-action instance is added to SSData. -/
noncomputable def sphereE2Coordinates (s t : ℕ) (ht : t ≤ 261) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ] (BasisIndex s t →₀ F2) :=
  KIP126.Main.StageInput.computation.results.sphereBasis.coordinates s t ht

/-- The delivered basis vector with the specified CSV position. -/
noncomputable def sphereE2Basis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) :=
  (sphereE2Coordinates s t ht).symm (Finsupp.single i 1)

/-- Lookup by the original additive-basis CSV index, not an algebra generator ID. -/
noncomputable def sphereE2BasisByCSV? (s t : ℕ) (ht : t ≤ 261) (index : ℕ) :
    Option (sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ))) :=
  (findBasisIndex? s t index).map (sphereE2Basis s t ht)

end KIP126.Classical.Adams
