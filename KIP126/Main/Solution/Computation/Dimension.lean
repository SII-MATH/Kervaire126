import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

namespace KIP126.Classical.Adams

/-- The computation interface supplies the exhaustive two-element description
on the actual internal second page, for its own fixed presentation. -/
theorem sphereAdamsData_square_eq_zero_or (x : sphereAdamsData.Page 2 (2, 128)) :
    x = 0 ∨ x = computedH6Square := by
  exact KIP126.Main.StageInput.witness.computation.results.sphereSquare.exhaustive x

/-- Every nonzero element in this bidegree is the fixed computational square. -/
theorem sphereAdamsData_eq_computedH6Square_of_ne_zero
    (x : sphereAdamsData.Page 2 (2, 128)) (hx : x ≠ 0) : x = computedH6Square :=
  (sphereAdamsData_square_eq_zero_or x).resolve_left hx

end KIP126.Classical.Adams
