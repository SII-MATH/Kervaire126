import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Cochains.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Single.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.H6.Proofs

namespace KIP126.StableHomotopy.Cohomology

noncomputable section
open CategoryTheory KIP126.Steenrod.Milnor KIP126.Core.Algebra

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- The cochain equivalence retains the original cooperation polynomial. -/
theorem reducedCooperationCochainEquiv_val (n : ℕ) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R n),
      (reducedCooperationCochainEquiv H R B n a).val =
        cooperationMilnorPolynomial H R B n a.val := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  let f := (cochains 1 n).subtype.comp (reducedCooperationCochainEquiv H R B n).toLinearMap
  let g := (cooperationMilnorPolynomial H R B n).comp
    (LinearMap.ker (cooperationCounitF2 H R n)).subtype
  have h : f = g := by
    apply (B.basis n).ext
    intro d
    change ((cochainsWordEquiv 1 n).symm
      (Finsupp.domLCongr (R := F2) (singleMilnorWordEquiv n)
        ((B.basis n).repr (B.basis n d)))).val =
      cooperationMilnorPolynomial H R B n (B.basis n d).val
    rw [Module.Basis.repr_self, Finsupp.domLCongr_single,
      cochainsWordEquiv_symm_single_val, singleMilnorWord_exponents,
      cooperationMilnorPolynomial_reduced_basis]
    rfl
  exact LinearMap.congr_fun h a

/-- The cooperation-polynomial source quantifier is exactly the source
of the existing normalized cobar differential, with no missing cochains. -/
theorem reducedCooperation_polynomial_boundary_iff (n : ℕ) (y : cochains 2 n) :
    letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    (∃ a : LinearMap.ker (cooperationCounitF2 H R n),
      differentialPolynomial 1 (cooperationMilnorPolynomial H R B n a.val) = y.val) ↔
      ∃ x : cochains 1 n, differential 1 n x = y := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨reducedCooperationCochainEquiv H R B n a, Subtype.ext ?_⟩
    change differentialPolynomial 1 (reducedCooperationCochainEquiv H R B n a).val = y.val
    rw [reducedCooperationCochainEquiv_val]
    exact ha
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := (reducedCooperationCochainEquiv H R B n).surjective x
    refine ⟨a, ?_⟩
    have h := congrArg Subtype.val hx
    change differentialPolynomial 1 (reducedCooperationCochainEquiv H R B n a).val = y.val at h
    rwa [reducedCooperationCochainEquiv_val] at h

end
end KIP126.StableHomotopy.Cohomology
