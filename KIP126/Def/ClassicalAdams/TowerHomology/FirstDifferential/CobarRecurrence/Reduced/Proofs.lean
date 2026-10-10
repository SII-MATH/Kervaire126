import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.CobarRecurrence.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Cobar.Reduced.Map.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ]

/-- The actual first differential on a sphere-boundary source factors
through the proved double-reduced coproduct. Its ordinary representative
is retained, so this is not a replacement differential on a separate model. -/
theorem sphereAdamsHomologyD1_firstBoundary_reduced
    (hK : Mod2KunnethSuspensionCompatible H R K)
    (hD : Mod2KunnethDiagonalCompatible H R K)
    (hU : Mod2KunnethUnitCompatible H R K)
    (hM : Mod2MilnorCoproductCompatible H R K B) (n : ℤ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      reducedCooperationTensorInclusion H R
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1)) (n - 1)
        (adamsNextHomologyTensorEquiv H R K (adamsTower H.unit SphereSpectrum 1) (n - 1)
          (adamsHomologyD1 H (adamsTower H.unit SphereSpectrum 1) (n - 1)
            (adamsTensorBoundary H R K SphereSpectrum n
              ((sphereCooperationTensorEquiv H R n).symm a.val)))) =
      cooperationTensorLowerMap H R
        (cooperationTensor H R (fun i => mod2HomologyF2 H R i SphereSpectrum))
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
        (adamsTensorBoundary H R K SphereSpectrum) n
        (gradedTensorAssoc (Mod2Cooperations H) (Mod2Cooperations H)
          (fun i => mod2HomologyF2 H R i SphereSpectrum) n
          (DirectSum.lof F2 ℤ _ n
            (reducedCooperationSquareInclusion H R n
              (cooperationReducedCobarDiagonal H R B K hU hM n a) ⊗ₜ[F2]
                (sphereHomologyScalarEquiv H R (n - n) (sub_self n)).symm 1))) := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  refine (sphereAdamsHomologyD1_tensorBoundary_cobar H R K hK hD hU n
    ((sphereCooperationTensorEquiv H R n).symm a.val)).trans ?_
  rw [sphereCooperationTensorEquiv_symm_apply, cooperationTensorCobarSplit_lof_tmul,
    cooperationReducedCobarDiagonal_inclusion]

end
end KIP126.Classical.Adams
