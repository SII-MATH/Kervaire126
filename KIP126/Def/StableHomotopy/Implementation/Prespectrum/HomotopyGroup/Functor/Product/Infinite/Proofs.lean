module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Infinite.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The original abelian stable homotopy functor preserves all actual small
products of source objects, using the constructed stabilized replacements. -/
instance sourceStableHomotopyAddFunctor_preservesSmallProducts (J : Type) (d : ℤ) :
    PreservesLimitsOfShape (Discrete J) (sourceStableHomotopyAddFunctor.{u} d) where
  preservesLimit {K} := by
    let L := Prespectrum.stabilizedInclusion.{u} ⋙ Prespectrum.t1Inclusion ⋙ sourceLocalization
    letI : L.EssSurj := Localization.essSurj L Prespectrum.stabilizedStableEquivalences
    let Y : J → Prespectrum.StabilizedPrespectrum.{u} := fun j => L.objPreimage (K.obj ⟨j⟩)
    let X : J → Prespectrum.{u} := fun j => (Y j).obj.obj
    letI (j : J) (n : ℕ) : T1Space ((X j).level n) := inferInstanceAs
      (T1Space ((Y j).obj.obj.level n))
    let hX : ∀ j, (X j).HasBijectiveStabilization := fun j => (Y j).property
    letI : PreservesLimit (Discrete.functor (fun j => sourceLocalization.obj (X j)))
        (sourceStableHomotopyAddFunctor d) :=
      preservesLimit_of_preserves_limit_cone
        ((Fan.isLimitMapConeEquiv sourceLocalization X (Prespectrum.piFan X))
          (Prespectrum.sourcePiFan_isLimit_of_stabilization X hX))
        (sourceStableHomotopyAddFunctor_productIsLimit_of_stabilization X hX d)
    exact preservesLimit_of_iso_diagram
      (K₁ := Discrete.functor (fun j => sourceLocalization.obj (X j)))
      (sourceStableHomotopyAddFunctor d)
      (Discrete.natIso (fun j => L.objObjPreimageIso (K.obj j)))

/-- Forgetting the abelian group structure gives the same preservation
statement for the original stable-homotopy-set functor. -/
instance sourceStableHomotopyFunctor_preservesSmallProducts (J : Type) (d : ℤ) :
    PreservesLimitsOfShape (Discrete J) (sourceStableHomotopyFunctor.{u} d) := by
  rw [← sourceStableHomotopyAddFunctor_forget]
  infer_instance

end KIP126.StableHomotopy.Implementation
