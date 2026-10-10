import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Predicates
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.LongLayer.Cancellation.Proofs
import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Classes.Proofs
import KIP126.Def.ClassicalAdams.TowerLongLayer.Pairing.Sphere.H6.Leibniz.Proofs
import KIP126.Def.ClassicalAdams.TowerSSData.Differential.Second.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

local notation "C₀" => standardFoundation.Spectrum
local notation "H₀" => standardFoundation.hf2
variable [BraidedCategory C₀] [MonoidalPreadditive C₀]
  [∀ Y : C₀, (tensorRight Y).CommShift ℤ]
  [∀ Y : C₀, (tensorRight Y).IsTriangulated]

/-- The three-product Lin comparison supplies the cancellation needed by the
pure geometric square lemma, independently of the boundary identity. -/
theorem SphereH6LongLayerMaps.LinCompatible.cross_sum_zero
    {R : Mod2RingStructure H₀} {M : SphereH6LongLayerMaps H₀}
    {h : M.Compatible R} (hLin : M.LinCompatible R h)
    (x : sphereAdamsData.Page 2 (3, 65)) (y : sphereAdamsData.Page 2 (1, 64)) :
    (fun a b : sphereAdamsData.Page 2 (4, 129) => a + b)
      ((M.leftPairing R).onInternalPage h.left h.left_boundary x y)
      ((M.rightPairing R).onInternalPage h.right h.right_boundary y x) = 0 := by
  have hl := hLin.left x y
  have hr := hLin.right y x
  have hc := linE2Presentation.h6_cross_products_add_eq_zero x y
  simp only [Nat.reduceAdd, Nat.cast_ofNat] at hc
  simp only [Int.reduceAdd] at hl hr
  exact (congrArg₂ (fun a b : sphereAdamsData.Page 2 (4, 129) => a + b) hl hr).trans hc

/-- Three specified spectrum pairings, their descent conditions, their Lin
product comparisons, and the long-layer boundary identity suffice for the
actual computational square's d₂ to vanish. This does not assume a global
page Leibniz law, but does not construct the listed geometric witnesses. -/
theorem computedH6Square_d_two_eq_zero_of_longLayer
    (R : Mod2RingStructure H₀) (M : SphereH6LongLayerMaps H₀)
    (h : M.Compatible R) (hLin : M.LinCompatible R h) (hδ : M.RelativeBoundary R h) :
    (sphereAdamsData.d 2 (2, 128)).hom computedH6Square = 0 := by
  have hz := M.internalD_square_eq_zero_of_cross_sum R h hδ computedH6
    (hLin.cross_sum_zero _ computedH6)
  have hsq := (hLin.square computedH6 computedH6).trans computedH6_mul_self
  have hi := congrArg (adamsTowerInternalD (H₀).unit SphereSpectrum 0 2 128).hom hsq
  change ((adamsTowerPreSS (H₀).unit SphereSpectrum).d 2 (2, 128)).hom computedH6Square = 0
  rw [adamsTowerPreSS_d_two_h6_eq]
  exact hi.symm.trans hz

end
end KIP126.Classical.Adams
