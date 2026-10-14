module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Cofibration.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- For actual cubical cofibrations with cofibrant sources, equivalence on
the source and on the original quotient cofiber detects target equivalence.
The cone-to-quotient comparisons use the proved geometric extension property. -/
theorem stableEquivalence_target_of_cofiberMap
    {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : IsCubicalCofibration f) (hg : IsCubicalCofibration g)
    (hX : IsCubicallyCofibrant X) (hX' : IsCubicallyCofibrant X')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (ha : stableEquivalences a) (hc : stableEquivalences (cofiberMap a b h)) :
    stableEquivalences b := by
  apply stableEquivalence_target_of_coneMap hX (hX.of_cubicalCofibration hf)
    hX' (hX'.of_cubicalCofibration hg) a b h ha
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ hc
  letI := stableEquivalences.Q_inverts _ (hf.coneToCofiber_stableEquivalence hX)
  letI := stableEquivalences.Q_inverts _ (hg.coneToCofiber_stableEquivalence hX')
  have e := congrArg sourceLocalization.map (coneToCofiber_map a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
