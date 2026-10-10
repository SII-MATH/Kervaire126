import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Data
import KIP126.Def.ClassicalAdams.TowerHomology.FirstDifferential.Tensor.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Proofs

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The successor coordinate is the proved tower recurrence followed by the
monomial tensor conversion; it is not an independently chosen page basis. -/
theorem sphereTowerHomologyWordEquiv_succ (s : ℕ) (n : ℤ)
    (x : mod2HomologyF2 H R n (adamsTower H.unit SphereSpectrum (s + 1))) :
    sphereTowerHomologyWordEquiv H R K B (s + 1) n x =
      reducedTensorMilnorWordEquiv H R B
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
        s (sphereTowerHomologyWordEquiv H R K B s) n
        (adamsTowerHomologyTensorEquiv H R K SphereSpectrum s (n + 1)
          (LinearEquiv.cast (R := ZMod 2)
            (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum (s + 1)))
            (show n = (n + 1) - 1 by omega) x)) := rfl

variable [(mod2UnitNatTrans H).CommShift ℤ]

/-- In the derived word coordinates, the actual first differential is the
already constructed reduced coaction step. The further equality with the
explicit Milnor polynomial differential still needs coproduct compatibility. -/
theorem sphereTowerHomologyWordEquiv_d1 (s : ℕ) (n : ℤ)
    (x : mod2HomologyF2 H R (n + 1) (adamsTower H.unit SphereSpectrum s)) :
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum (s + 1)))
      (show n = (n + 1) - 1 by omega)
    sphereTowerHomologyWordEquiv H R K B (s + 1) n
      (e.symm (adamsHomologyD1 H (adamsTower H.unit SphereSpectrum s) (n + 1) x)) =
      reducedTensorMilnorWordEquiv H R B
        (fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum s))
        s (sphereTowerHomologyWordEquiv H R K B s) n
        (mod2CobarStep H R K (adamsTower H.unit SphereSpectrum s) (n + 1) x) := by
  dsimp only
  rw [sphereTowerHomologyWordEquiv_succ, LinearEquiv.apply_symm_apply]
  change reducedTensorMilnorWordEquiv H R B _ s _ n
    (adamsNextHomologyTensorEquiv H R K _ _ (adamsHomologyD1 H _ _ x)) = _
  rw [adamsHomologyD1_eq_cobarStep]

end

end KIP126.Classical.Adams
