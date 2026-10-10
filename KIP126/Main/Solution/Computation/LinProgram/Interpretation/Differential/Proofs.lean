import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.Predicates
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Data

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory

/-- At the square's numerical degree, the natural-index reindexing is identity. -/
theorem sphereE2SecondDifferential_h6_square :
    sphereE2SecondDifferential 2 128 = (sphereAdamsData.d 2 (2, 128)).hom := by
  with_unfolding_all
    change (sphereAdamsData.d 2 (2, 128) ≫ 𝟙 _).hom = _
    rw [Category.comp_id]

/-- The coordinate differential is zero exactly when the actual differential is. -/
theorem LinE2Presentation.secondDifferential_eq_zero_iff (P : LinE2Presentation)
    (s t : ℕ) (ht : t + 1 ≤ 261) (x : KIP126.LinE2.E2At s t) :
    P.secondDifferential s t ht x = 0 ↔
      sphereE2SecondDifferential s t (P.comparison s t (by omega) x) = 0 := by
  exact (P.comparison (s + 2) (t + 1) ht).symm.map_eq_zero_iff

/-- No properness assumption on the archived ideal is needed for 2x = 0. -/
theorem linE2_add_self_eq_zero (x : KIP126.LinE2.E2) : x + x = 0 := by
  have h : (1 + 1 : KIP126.Core.Algebra.F2) = 0 := by decide
  calc
    x + x = (1 : KIP126.Core.Algebra.F2) • x + 1 • x := by simp only [one_smul]
    _ = (1 + 1 : KIP126.Core.Algebra.F2) • x := (add_smul _ _ _).symm
    _ = 0 := by rw [h, zero_smul]

/-- In the covered range, Leibniz makes every homogeneous square a d₂-cycle.
The class itself need not be a d₂-cycle. -/
theorem LinE2Presentation.secondDifferential_square_eq_zero (P : LinE2Presentation)
    (hL : P.SecondDifferentialLeibniz) (s t : ℕ) (ht : t + t + 1 ≤ 261)
    (x : KIP126.LinE2.E2At s t) :
    P.secondDifferential (s + s) (t + t) ht (KIP126.LinE2.mulAt x x) = 0 := by
  apply Subtype.ext
  change (P.secondDifferential (s + s) (t + t) ht (KIP126.LinE2.mulAt x x)).val = 0
  rw [hL s t s t ht x x, mul_comm x.val]
  exact linE2_add_self_eq_zero _

/-- Conditional vanishing for the existing computational square, not for a
newly chosen differential. The compatibility hL is not supplied by the Lin axiom. -/
theorem computedH6Square_d_two_eq_zero_of_leibniz
    (hL : linE2Presentation.SecondDifferentialLeibniz) :
    (sphereAdamsData.d 2 (2, 128)).hom computedH6Square = 0 := by
  have h := linE2Presentation.secondDifferential_square_eq_zero hL 1 64 (by decide)
    KIP126.LinE2.dataH6
  have hs : KIP126.LinE2.mulAt KIP126.LinE2.dataH6 KIP126.LinE2.dataH6 =
      KIP126.LinE2.dataH6Sq := by
    apply Subtype.ext
    exact (pow_two _).symm
  rw [hs] at h
  have hz := (linE2Presentation.secondDifferential_eq_zero_iff 2 128 (by decide)
    KIP126.LinE2.dataH6Sq).mp h
  rw [sphereE2SecondDifferential_h6_square] at hz
  exact hz

end
end KIP126.Classical.Adams
