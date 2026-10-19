module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Colimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type}

theorem stablePiComparison_add (X : J → Prespectrum.{u}) (d : ℤ)
    (x y : StableHomotopy (piPrespectrum X) d) :
    stablePiComparison X d (x + y) = stablePiComparison X d x + stablePiComparison X d y :=
  funext fun j => stableHomotopyMap_add (piProjection X j) d x y

theorem stablePiComparison_zero (X : J → Prespectrum.{u}) (d : ℤ) :
    stablePiComparison X d 0 = 0 :=
  funext fun j => stableHomotopyMap_zero (piProjection X j) d

theorem stablePiColimitMap_bijective (X : J → Prespectrum.{u}) (d : ℤ) :
    Function.Bijective (stablePiColimitMap X d) :=
  KIP126.Core.DirectLimit.map_bijective _ _ _ _
    (fun k => levelPiComparison_bijective X (stableGroupStage d k) (stableGroupDimension d k))

theorem stablePiColimitCode_bijective [Finite J] (X : J → Prespectrum.{u}) (d : ℤ) :
    Function.Bijective (stablePiColimitCode X d) :=
  (KIP126.Core.DirectLimit.piComparison_bijective
    (fun j => stableLevelGroup (X j) d) (fun j => stableLevelTransition (X j) d)).comp
      ((stablePiColimitMap_bijective X d).comp (stableHomotopyGroupEquiv (piPrespectrum X) d).bijective)

theorem stablePiColimitCode_component (X : J → Prespectrum.{u}) (d : ℤ)
    (x : StableHomotopy (piPrespectrum X) d) (j : J) :
    stablePiColimitCode X d x j = stableGroupCode (X j) d (stablePiComparison X d x j) := by
  obtain ⟨k,p,q,hx,_⟩ := exists_stableLevelClass_pair (piPrespectrum X) d x x
  subst x
  change _ = stableGroupCode (X j) d
    (stableHomotopyMap (piProjection X j) d (stableLevelClass (piPrespectrum X) d k p))
  rw [stableLevelClass_natural, stableGroupCode_levelClass]
  unfold stablePiColimitCode
  rw [stableGroupCode_levelClass]
  rfl

/-- The actual stable homotopy groups commute with finite pointwise products.
The finite index hypothesis provides a common stabilization stage. -/
theorem stablePiComparison_bijective [Finite J] (X : J → Prespectrum.{u}) (d : ℤ) :
    Function.Bijective (stablePiComparison X d) := by
  constructor
  · intro x y h
    apply (stablePiColimitCode_bijective X d).injective
    funext j
    rw [stablePiColimitCode_component, stablePiColimitCode_component, h]
  · intro y
    obtain ⟨x,hx⟩ := (stablePiColimitCode_bijective X d).surjective
      (fun j => stableGroupCode (X j) d (y j))
    refine ⟨x,funext fun j => ?_⟩
    apply (stableHomotopyGroupEquiv (X j) d).injective
    exact (stablePiColimitCode_component X d x j).symm.trans (congrFun hx j)

end KIP126.StableHomotopy.Implementation.Prespectrum
