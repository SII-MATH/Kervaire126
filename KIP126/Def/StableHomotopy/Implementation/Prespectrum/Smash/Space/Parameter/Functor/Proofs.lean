module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The original parameter maps commute strictly with every spectrum map. -/
@[reassoc] theorem spaceSmashMap_parameter_natural {A B : BasedSpace.{0}}
    (a : A ⟶ B) {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap a (𝟙 X) ≫ spaceSmashMap (𝟙 B) f =
      spaceSmashMap (𝟙 A) f ≫ spaceSmashMap a (𝟙 Y) := by
  simp only [← spaceSmashMap_comp,Category.id_comp,Category.comp_id]

end KIP126.StableHomotopy.Implementation.Prespectrum
