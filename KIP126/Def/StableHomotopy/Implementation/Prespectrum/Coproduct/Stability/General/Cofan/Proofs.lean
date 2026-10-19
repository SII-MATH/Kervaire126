module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Stability.General.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary actual coproduct cocones preserve stable equivalences,
retaining the specified original injections and comparison map. -/
theorem stableEquivalence_of_cofan_map_general
    {J : Type} {X Y : J → Prespectrum.{0}}
    (c : Cofan X) (d : Cofan Y) (hc : IsColimit c) (hd : IsColimit d)
    (f : ∀ j, X j ⟶ Y j) (g : c.pt ⟶ d.pt)
    (hg : ∀ j, c.inj j ≫ g = f j ≫ d.inj j)
    (hf : ∀ j, stableEquivalences (f j)) : stableEquivalences g := by
  let eX := (coproductIsCoproduct X).coconePointUniqueUpToIso hc
  let eY := (coproductIsCoproduct Y).coconePointUniqueUpToIso hd
  have he : CategoryTheory.Limits.Sigma.map f ≫ eY.hom = eX.hom ≫ g := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_map_assoc]
    have hX : Sigma.ι X j ≫ eX.hom = c.inj j :=
      (coproductIsCoproduct X).fac c ⟨j⟩
    have hY : Sigma.ι Y j ≫ eY.hom = d.inj j :=
      (coproductIsCoproduct Y).fac d ⟨j⟩
    rw [hY, ← Category.assoc, hX, hg]
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (coproductMap_stableEquivalence_general f hf)
  have h := congrArg sourceLocalization.map he
  simp only [Functor.map_comp] at h
  exact IsIso.of_isIso_fac_left h.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
