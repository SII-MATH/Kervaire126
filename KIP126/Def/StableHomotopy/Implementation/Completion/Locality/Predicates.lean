module

public import KIP126.Def.StableHomotopy.Implementation.Completion

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- HF₂ locality on objects of the original stable localization. On a
localized prespectrum this is exactly the existing locality predicate. -/
def SourceIsHF2Local (X : SourceCategory.{0}) : Prop :=
  ∀ {A B : SourceCategory.{0}} (f : A ⟶ B), HF2Equivalences f →
    Function.Bijective (fun a : B ⟶ X => f ≫ a)

end KIP126.StableHomotopy.Implementation
