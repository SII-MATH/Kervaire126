module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Prespectrum.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

theorem singularPrespectrum_level_isGood (X : Prespectrum.{u}) (n : ℕ) :
    ((singularPrespectrum X).level n).IsGood :=
  singularRealization_isGood (X.level n)

theorem singularPrespectrumMap_id (X : Prespectrum.{u}) :
    singularPrespectrumMap (𝟙 X) = 𝟙 (singularPrespectrum X) := by
  apply Prespectrum.Hom.ext
  funext n
  exact singularRealizationMap_id (X.level n)

theorem singularPrespectrumMap_comp {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularPrespectrumMap (f ≫ g) = singularPrespectrumMap f ≫ singularPrespectrumMap g := by
  apply Prespectrum.Hom.ext
  funext n
  exact singularRealizationMap_comp
    (⟨f.level n,f.point n⟩ : X.level n ⟶ Y.level n)
    (⟨g.level n,g.point n⟩ : Y.level n ⟶ Z.level n)

theorem singularPrespectrumEvaluation_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    singularPrespectrumMap f ≫ singularPrespectrumEvaluation Y =
      singularPrespectrumEvaluation X ≫ f := by
  apply Prespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact singularEvaluation_natural (⟨f.level n,f.point n⟩ : X.level n ⟶ Y.level n) x

end KIP126.StableHomotopy.Implementation
