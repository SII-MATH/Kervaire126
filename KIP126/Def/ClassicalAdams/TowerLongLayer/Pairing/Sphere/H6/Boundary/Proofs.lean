import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Boundary.Predicates
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Boundary.Proofs
import KIP126.Def.ClassicalAdams.SphereInitial.FiltrationOne.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C] [MonoidalPreadditive C]
  {H : Mod2EilenbergMacLane (C := C)} (M : SphereH6LongLayerMaps H)
  (R : Mod2RingStructure H)
  [∀ Y : C, (tensorRight Y).CommShift ℤ]
  [∀ Y : C, (tensorRight Y).IsTriangulated]

/-- Both square-product boundary conditions follow from filtration-one
boundary vanishing, without assumptions on the chosen spectrum product. -/
theorem SphereH6LongLayerMaps.square_boundary : (M.squarePairing R).BoundaryCompatible :=
  (M.squarePairing R).boundaryCompatible_of_eq_bot
    (sphereAdamsBoundaries_filtration_one H 2 (by decide) 64)
    (sphereAdamsBoundaries_filtration_one H 2 (by decide) 64)

variable {M R}

theorem SphereH6LongLayerMaps.CrossBoundaryCompatible.left_boundary
    (h : M.CrossBoundaryCompatible R) : (M.leftPairing R).BoundaryCompatible := by
  refine ⟨h.left, ?_⟩
  intro a b hb
  have hz := adamsJ_eq_zero_of_boundaries_eq_bot 1 64
    (sphereAdamsBoundaries_filtration_one H 2 (by decide) 64) b hb
  rw [hz, map_zero]
  exact Submodule.zero_mem _

theorem SphereH6LongLayerMaps.CrossBoundaryCompatible.right_boundary
    (h : M.CrossBoundaryCompatible R) : (M.rightPairing R).BoundaryCompatible := by
  refine ⟨?_, h.right⟩
  intro a ha b
  have hz := adamsJ_eq_zero_of_boundaries_eq_bot 1 64
    (sphereAdamsBoundaries_filtration_one H 2 (by decide) 64) a ha
  rw [hz, map_zero, LinearMap.zero_apply]
  exact Submodule.zero_mem _

end
end KIP126.Classical.Adams
