module

public import KIP126.Def.Algebra.Colimit.Coproduct.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.SourceFiniteSupport.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual integer-graded stable homotopy preserves each small coproduct
in the original stable localization. Compact representatives supply the
finite support needed beyond finite additivity. -/
instance sourceStableHomotopyAddFunctor_preservesCoproduct {J : Type u}
    (X : J → SourceCategory.{u}) (d : ℤ) :
    PreservesColimit (Discrete.functor X) (sourceStableHomotopyAddFunctor d) :=
  KIP126.Foundation.preservesCoproduct_of_finite_support _ _
    (Prespectrum.sourceStableHomotopy_coproduct_finite_support X d)

instance sourceStableHomotopyAddFunctor_preservesCoproductsOfShape (J : Type u) (d : ℤ) :
    PreservesColimitsOfShape (Discrete J) (sourceStableHomotopyAddFunctor.{u} d) where
  preservesColimit {K} := by
    letI : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
        (sourceStableHomotopyAddFunctor d) :=
      sourceStableHomotopyAddFunctor_preservesCoproduct (K.obj ∘ Discrete.mk) d
    exact preservesColimit_of_iso_diagram (sourceStableHomotopyAddFunctor d)
      Discrete.natIsoFunctor.symm

/-- This includes all ordinary small families in every spectrum universe. -/
instance sourceStableHomotopyAddFunctor_preservesSmallCoproductsOfShape (J : Type) (d : ℤ) :
    PreservesColimitsOfShape (Discrete J) (sourceStableHomotopyAddFunctor.{u} d) := by
  exact preservesColimitsOfShape_of_equiv
    (Discrete.equivalence (Equiv.ulift : ULift.{u} J ≃ J)) _

end KIP126.StableHomotopy.Implementation
