module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Iso.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Cofibration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary actual coproduct cocones retain cubical cofibrancy. -/
theorem isCubicallyCofibrant_of_cofan {J : Type u} {X : J → Prespectrum.{u}}
    (c : Cofan X) (hc : IsColimit c) (hX : ∀ j, IsCubicallyCofibrant (X j)) :
    IsCubicallyCofibrant c.pt := by
  intro E B p hp
  exact IsCubicallyCofibrant.of_iso (isCubicallyCofibrant_coproduct X hX)
    ((coproductIsCoproduct X).coconePointUniqueUpToIso hc) p hp

private theorem cofan_comparison_comm {J : Type u} {X Y : J → Prespectrum.{u}}
    (c : Cofan X) (d : Cofan Y) (hc : IsColimit c) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.inj j ≫ g = f j ≫ d.inj j) :
    CategoryTheory.Limits.Sigma.map f ≫
        ((coproductIsCoproduct Y).coconePointUniqueUpToIso hd).hom =
      ((coproductIsCoproduct X).coconePointUniqueUpToIso hc).hom ≫ g := by
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_map_assoc]
  change f j ≫ (Sigma.ι Y j ≫ (coproductIsCoproduct Y).desc d) =
    Sigma.ι X j ≫ (coproductIsCoproduct X).desc c ≫ g
  have hX : Sigma.ι X j ≫ (coproductIsCoproduct X).desc c = c.inj j :=
    (coproductIsCoproduct X).fac c ⟨j⟩
  have hY : Sigma.ι Y j ≫ (coproductIsCoproduct Y).desc d = d.inj j :=
    (coproductIsCoproduct Y).fac d ⟨j⟩
  rw [hY,← Category.assoc,hX,hg]

/-- Any actual coproduct of cubical cofibrations is a cubical
cofibration, independently of the chosen coproduct presentation. -/
theorem isCubicalCofibration_of_cofan_map {J : Type u} {X Y : J → Prespectrum.{u}}
    (c : Cofan X) (d : Cofan Y) (hc : IsColimit c) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.inj j ≫ g = f j ≫ d.inj j)
    (hf : ∀ j, IsCubicalCofibration (f j)) : IsCubicalCofibration g := by
  have hs : IsCubicalCofibration (CategoryTheory.Limits.Sigma.map f) := by
    intro E B p hp
    letI (j : J) := hf j p hp
    infer_instance
  intro E B p hp
  exact ((isCubicalCofibration_iff_of_iso
    ((coproductIsCoproduct X).coconePointUniqueUpToIso hc)
    ((coproductIsCoproduct Y).coconePointUniqueUpToIso hd)
    _ g (cofan_comparison_comm c d hc hd f g hg)).mp hs) p hp

/-- Actual coproduct comparisons of stable equivalences between
cofibrant spectra are stable equivalences for any coproduct cocones. -/
theorem stableEquivalence_of_cofan_map {J : Type u} {X Y : J → Prespectrum.{u}}
    (c : Cofan X) (d : Cofan Y) (hc : IsColimit c) (hd : IsColimit d)
    (hX : ∀ j, IsCubicallyCofibrant (X j)) (hY : ∀ j, IsCubicallyCofibrant (Y j))
    (f : ∀ j, X j ⟶ Y j) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.inj j ≫ g = f j ≫ d.inj j)
    (hf : ∀ j, stableEquivalences (f j)) : stableEquivalences g := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (coproductMap_stableEquivalence_of_isCubicallyCofibrant hX hY f hf)
  have h := congrArg sourceLocalization.map (cofan_comparison_comm c d hc hd f g hg)
  simp only [Functor.map_comp] at h
  exact IsIso.of_isIso_fac_left h.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
