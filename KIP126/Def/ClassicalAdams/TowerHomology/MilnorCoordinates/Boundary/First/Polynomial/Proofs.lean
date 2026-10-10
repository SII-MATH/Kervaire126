import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Boundary.First.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Realization.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- The actual sphere boundary on any reduced cooperation has exactly
its existing one-slot Milnor polynomial. This is a computed coordinate
formula, not an assumed compatibility for an Adams differential. -/
theorem sphereFirstBoundary_polynomial_reduced (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R (n + 1)),
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
      (show n = (n + 1) - 1 by omega)
    milnorWordPolynomial 1 (n + 1)
      (sphereTowerHomologyWordEquiv H R K B 1 n
        (e.symm (adamsTensorBoundary H R K SphereSpectrum (n + 1)
          ((sphereCooperationTensorEquiv H R (n + 1)).symm a.val)))) =
      cooperationMilnorPolynomial H R B (n + 1) a.val := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  refine (congrArg (milnorWordPolynomial 1 (n + 1))
    (sphereTowerHomologyWordEquiv_firstBoundary_reduced H R K B n a)).trans ?_
  let f := (milnorWordPolynomial 1 (n + 1)).comp
    ((Finsupp.domLCongr (R := ZMod 2) (singleMilnorWordEquiv (n + 1))).toLinearMap.comp
      (B.basis (n + 1)).repr.toLinearMap)
  let g := (cooperationMilnorPolynomial H R B (n + 1)).comp
    (LinearMap.ker (cooperationCounitF2 H R (n + 1))).subtype
  have hfg : f = g := by
    apply (B.basis (n + 1)).ext
    intro d
    change milnorWordPolynomial 1 (n + 1)
      (Finsupp.domLCongr (R := ZMod 2) (singleMilnorWordEquiv (n + 1))
        ((B.basis (n + 1)).repr (B.basis (n + 1) d))) =
      cooperationMilnorPolynomial H R B (n + 1) (B.basis (n + 1) d).val
    rw [Module.Basis.repr_self, Finsupp.domLCongr_single,
      milnorWordPolynomial_single, singleMilnorWord_exponents,
      cooperationMilnorPolynomial_reduced_basis]
    rfl
  exact LinearMap.congr_fun hfg a

end
end KIP126.Classical.Adams
