module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.InvertTwo.Bond.Proofs
public import KIP126.Def.Algebra.Colimit.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Conservativity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Multiplication by two is bijective on the original stable groups of
the fixed doubled-bond sphere, in every integer degree. -/
theorem Prespectrum.sphereInvertTwo_two_nsmul_bijective (d : ℤ) :
    Function.Bijective (fun x : StableHomotopy sphereInvertTwo d => (2 : ℕ) • x) := by
  have hp : Function.Bijective (fun x : stableGroupColimit sphereInvertTwo d => x ^ 2) := by
    apply KIP126.Core.DirectLimit.pow_bijective_of_successor_eq_pow
      (stableLevelTransition sphereInvertTwo d) 2 (stableLevelBond sphere d)
    intro i x
    rw [stableLevelTransition_succ sphereInvertTwo d (Nat.le_refl i),
      stableLevelTransition_self]
    exact sphereInvertTwo_stableLevelBond d i x
  let e := stableHomotopyAddEquiv sphereInvertTwo d
  have he (x : StableHomotopy sphereInvertTwo d) : e ((2 : ℕ) • x) = (2 : ℕ) • e x := by
    simp only [two_nsmul, e.map_add]
  constructor
  · intro x y h
    apply e.injective
    apply Additive.toMul.injective
    apply hp.injective
    simpa only [he, toMul_nsmul] using
      congrArg (fun z => (e z).toMul) h
  · intro x
    obtain ⟨y,hy⟩ := hp.surjective (e x).toMul
    refine ⟨e.symm (Additive.ofMul y), ?_⟩
    apply e.injective
    rw [he, AddEquiv.apply_symm_apply]
    exact (ofMul_pow 2 y).symm.trans (congrArg Additive.ofMul hy)

/-- The scalar two is an actual isomorphism of the fixed source object
S[1/2], detected by all of its original stable homotopy groups. -/
theorem Prespectrum.sphereInvertTwo_two_id_isIso :
    IsIso ((2 : ℕ) • 𝟙 (sourceLocalization.obj sphereInvertTwo)) := by
  apply (source_isIso_iff_stableHomotopy_bijective _).mpr
  intro d
  rw [← sourceStableHomotopyAddFunctor_forget_map]
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact sphereInvertTwo_two_nsmul_bijective d

end KIP126.StableHomotopy.Implementation
