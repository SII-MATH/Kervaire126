module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- Genuine stable excision for an actual homotopy-extension pushout
whose four displayed objects have the actual cubical lifting property.
The retained cone comparison and proved cone detection supply the result. -/
theorem isPushout_stableEquivalence_of_isCubicallyCofibrant
    {A B C D : Prespectrum.{u}}
    (hA : IsCubicallyCofibrant A) (hB : IsCubicallyCofibrant B)
    (hC : IsCubicallyCofibrant C) (hD : IsCubicallyCofibrant D)
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j)
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n))) (hg : stableEquivalences g) :
    stableEquivalences i :=
  stableEquivalence_target_of_coneMap hA hB hC hD g i h.w hg
    (coneMap_stableEquivalence_of_isPushout h hf)

end KIP126.StableHomotopy.Implementation.Prespectrum
