module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Detection.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- A strict square of actual cubical cofibrations induces a stable
equivalence on the original quotient cofibers when its two original
object maps are stable equivalences. -/
theorem cofiberMap_stableEquivalence_of_cubicalCofibration
    {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : IsCubicalCofibration f) (hg : IsCubicalCofibration g)
    (hX : IsCubicallyCofibrant X) (hX' : IsCubicallyCofibrant X')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (cofiberMap a b h) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (coneMap_stableEquivalence_of_isCubicallyCofibrant
    hX (hX.of_cubicalCofibration hf) hX' (hX'.of_cubicalCofibration hg) a b h ha hb)
  letI := stableEquivalences.Q_inverts _ (hf.coneToCofiber_stableEquivalence hX)
  letI := stableEquivalences.Q_inverts _ (hg.coneToCofiber_stableEquivalence hX')
  have e := congrArg sourceLocalization.map (coneToCofiber_map a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_left e.symm

/-- Stable equivalences among actual cubical cofibrations are detected
by the original quotient cofiber, with its geometric hypotheses proved. -/
theorem IsCubicalCofibration.stableEquivalence_iff_source_cofiber_isZero
    {X Y : Prespectrum.{u}} {f : X ⟶ Y} (hf : IsCubicalCofibration f)
    (hX : IsCubicallyCofibrant X) :
    stableEquivalences f ↔ IsZero (sourceLocalization.obj (Prespectrum.pointSetCofiber f)) := by
  rw [stableEquivalence_iff_source_cone_isZero hX (hX.of_cubicalCofibration hf) f]
  letI := stableEquivalences.Q_inverts _ (hf.coneToCofiber_stableEquivalence hX)
  let e := asIso (sourceLocalization.map (coneToCofiber f))
  exact ⟨fun h => h.of_iso e.symm,fun h => h.of_iso e⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
