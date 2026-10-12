module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Colimit.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Gluing.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits

/-- Stable gluing applies to the original parameter smash pushout,
using its actual cubical cofibrations and the three input comparisons. -/
theorem spaceSmashMap_stableEquivalence_of_parameter_pushout
    {A B C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} A]
    [UCompactlyGeneratedSpace.{0} B] [UCompactlyGeneratedSpace.{0} C]
    {a : A ⟶ B} {b : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout a b i j) {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hAX : IsCubicallyCofibrant (spaceSmash A X))
    (hCX : IsCubicallyCofibrant (spaceSmash C X))
    (hAY : IsCubicallyCofibrant (spaceSmash A Y))
    (hCY : IsCubicallyCofibrant (spaceSmash C Y))
    (haX : IsCubicalCofibration (spaceSmashMap a (𝟙 X)))
    (haY : IsCubicalCofibration (spaceSmashMap a (𝟙 Y)))
    (hfA : stableEquivalences (spaceSmashMap (𝟙 A) f))
    (hfB : stableEquivalences (spaceSmashMap (𝟙 B) f))
    (hfC : stableEquivalences (spaceSmashMap (𝟙 C) f)) :
    stableEquivalences (spaceSmashMap (𝟙 D) f) :=
  isPushout_stableEquivalence_gluing_of_cubicalCofibration
    hAX hCX hAY hCY haX haY
    (spaceSmashParameter_isPushout h X) (spaceSmashParameter_isPushout h Y)
    (spaceSmashMap (𝟙 A) f) (spaceSmashMap (𝟙 B) f)
    (spaceSmashMap (𝟙 C) f) (spaceSmashMap (𝟙 D) f)
    (spaceSmashMap_parameter_natural a f) (spaceSmashMap_parameter_natural b f)
    (spaceSmashMap_parameter_natural i f) (spaceSmashMap_parameter_natural j f)
    hfA hfB hfC

end KIP126.StableHomotopy.Implementation.Prespectrum
