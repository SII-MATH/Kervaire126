module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The actual fixed-space isomorphism commutes with every original
strict map of spectra. -/
@[reassoc] theorem spaceSmashIso_natural {A B : BasedSpace.{0}} (e : A ≅ B)
    {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    spaceSmashMap (𝟙 A) f ≫ (spaceSmashIso e (Iso.refl Y)).hom =
      (spaceSmashIso e (Iso.refl X)).hom ≫ spaceSmashMap (𝟙 B) f := by
  change spaceSmashMap (𝟙 A) f ≫ spaceSmashMap e.hom (𝟙 Y) =
    spaceSmashMap e.hom (𝟙 X) ≫ spaceSmashMap (𝟙 B) f
  simp only [← spaceSmashMap_comp,Category.id_comp,Category.comp_id]

/-- A genuine based-space isomorphism transports stable invariance of
the original fixed-space smash, without any condition on the levels. -/
theorem spaceSmashMap_stableEquivalence_iff_of_iso {A B : BasedSpace.{0}}
    (e : A ≅ B) {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    stableEquivalences (spaceSmashMap (𝟙 A) f) ↔
      stableEquivalences (spaceSmashMap (𝟙 B) f) := by
  simp only [stableEquivalence_iff_source_isIso]
  have h := congrArg sourceLocalization.map (spaceSmashIso_natural e f)
  simp only [Functor.map_comp] at h
  constructor
  · intro hf
    letI := hf
    exact IsIso.of_isIso_fac_left h.symm
  · intro hf
    letI := hf
    exact IsIso.of_isIso_fac_right h

end KIP126.StableHomotopy.Implementation.Prespectrum
