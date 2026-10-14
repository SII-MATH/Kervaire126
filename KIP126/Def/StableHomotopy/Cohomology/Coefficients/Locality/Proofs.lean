module

public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Basic.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H)

include R in
/-- The actual coefficient identity is killed by two, using its specified
unit and multiplication. -/
theorem mod2_id_two_nsmul_zero : 2 • 𝟙 H.HF2 = 0 := by
  simpa only [two_nsmul] using mod2_id_add_self H R

include R in
/-- Coefficient smash vanishes on every object on which two is invertible. -/
theorem mod2Free_isZero_of_two_isIso (X : C) [IsIso (2 • 𝟙 X)] :
    IsZero (H.HF2 ⊗ X) := by
  have he : (tensorLeft H.HF2).map (2 • 𝟙 X) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, two_nsmul]
    exact mod2Free_id_add_self H R X
  letI : IsIso ((tensorLeft H.HF2).map (2 • 𝟙 X)) := inferInstance
  exact IsZero.of_epi_eq_zero ((tensorLeft H.HF2).map (2 • 𝟙 X)) he

include R in
/-- If coefficient smash is conservative, a two-invertible object is zero.
No boundedness or convergence assumption is used. -/
theorem isZero_of_two_isIso_of_hf2_conservative
    [(tensorLeft H.HF2).ReflectsIsomorphisms] (X : C) [IsIso (2 • 𝟙 X)] :
    IsZero X := by
  have hz := mod2Free_isZero_of_two_isIso H R X
  letI : IsIso ((tensorLeft H.HF2).map (0 : X ⟶ X)) := by
    have h : (tensorLeft H.HF2).map (0 : X ⟶ X) = 𝟙 ((tensorLeft H.HF2).obj X) := by
      rw [Functor.map_zero]
      exact ((IsZero.iff_id_eq_zero _).mp hz).symm
    rw [h]
    infer_instance
  letI : IsIso (0 : X ⟶ X) := isIso_of_reflects_iso (0 : X ⟶ X) (tensorLeft H.HF2)
  exact IsZero.of_epi_zero X X

end KIP126.StableHomotopy.Cohomology
