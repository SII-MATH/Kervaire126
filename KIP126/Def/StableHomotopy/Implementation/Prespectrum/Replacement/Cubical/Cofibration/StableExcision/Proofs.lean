module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Excision.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Actual cubical cofibrations between cofibrant inputs satisfy stable
excision. Level homotopy extension is proved from the original lifting
property through its relative-cellular retract. -/
theorem IsCubicalCofibration.stable_pushout
    {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : IsCubicalCofibration f)
    (hA : IsCubicallyCofibrant A) (hC : IsCubicallyCofibrant C)
    (h : IsPushout f g i j) (hg : stableEquivalences g) :
    stableEquivalences i :=
  isPushout_stableEquivalence_of_cubicalCofibration hA hC hf h
    (hf.level_hasHomotopyExtension hA) hg

end KIP126.StableHomotopy.Implementation.Prespectrum
