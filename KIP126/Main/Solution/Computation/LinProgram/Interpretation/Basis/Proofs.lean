import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Basis.Data
import KIP126.Main.Solution.Computation.LinProgram.Basis.Proofs

namespace KIP126.Classical.Adams
open KIP126.LinE2

theorem sphereE2Coordinates_basis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    sphereE2Coordinates s t ht (sphereE2Basis s t ht i) = Finsupp.single i 1 :=
  (sphereE2Coordinates s t ht).apply_symm_apply _

/-- The recovered data basis and the delivered actual basis use precisely
the presentation from that same Challenge2 witness. -/
theorem linToSphereE2_dataBasis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    linToSphereE2 s t ht (dataBasis s t ht i) = sphereE2Basis s t ht i :=
  (linToSphereE2 s t ht).apply_symm_apply _

theorem sphereE2Basis_ne_zero (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    sphereE2Basis s t ht i ≠ 0 := by
  intro h
  apply dataBasis_ne_zero s t ht i
  apply (linToSphereE2 s t ht).injective
  simpa only [linToSphereE2_dataBasis, map_zero] using h

theorem sphereE2Coordinates_reconstruct (s t : ℕ) (ht : t ≤ 261)
    (x : sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ))) :
    (sphereE2Coordinates s t ht).symm (sphereE2Coordinates s t ht x) = x :=
  (sphereE2Coordinates s t ht).symm_apply_apply x

end KIP126.Classical.Adams
