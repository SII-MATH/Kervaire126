import KIP126.Def.StableHomotopy.Cohomology.Connecting.Data
import KIP126.Def.StableHomotopy.Cohomology.Suspension.Data

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory MonoidalCategory

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The connecting homomorphism is pushforward along the triangle's last
map followed by the specified homological desuspension. -/
theorem mod2HomologyConnecting_factor (T : HoCofiberSequence (C := C)) (n : ℤ)
    (x : Mod2Homology H n T.Z) :
    mod2HomologyConnecting H T n x =
      mod2HomologyDesuspend H T.X n (Mod2Homology.pushforward H T.h n x) := by
  simp only [mod2HomologyConnecting, connectingHomomorphism, HoCofiberSequence.map,
    mod2HomologyDesuspend, homotopyDesuspend, Mod2Homology.pushforward, inducedMap,
    AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Functor.id_obj, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map (x ≫ H.HF2 ◁ T.h ≫ _) ≫ _ =
      (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
        (shiftFunctor C (-1)).map ((x ≫ H.HF2 ◁ T.h) ≫ _) ≫ _
  rw [Category.assoc]
  rfl

/-- The analogous factorization after two coefficient factors. -/
theorem mod2HomologyConnecting_map_factor (T : HoCofiberSequence (C := C)) (n : ℤ)
    (x : Mod2Homology H n (H.HF2 ⊗ T.Z)) :
    mod2HomologyConnecting H (T.map (tensorLeft H.HF2)) n x =
      mod2DoubleHomologyDesuspend H T.X n
        (Mod2Homology.pushforward H (H.HF2 ◁ T.h) n x) := by
  rw [mod2HomologyConnecting_factor]
  change mod2HomologyDesuspend H (H.HF2 ⊗ T.X) n
    (x ≫ H.HF2 ◁ (H.HF2 ◁ T.h ≫ _)) =
      mod2HomologyDesuspend H (H.HF2 ⊗ T.X) n
        ((x ≫ H.HF2 ◁ (H.HF2 ◁ T.h)) ≫ H.HF2 ◁ _)
  rw [whiskerLeft_comp, Category.assoc]

end KIP126.StableHomotopy.Cohomology
