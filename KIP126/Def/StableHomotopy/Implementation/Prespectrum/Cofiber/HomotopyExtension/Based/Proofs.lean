module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Stability.General.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Comparison.Based.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Levelwise based homotopy extension suffices for stable invariance of the actual
quotient cofiber; the original objects need no cofibrancy premise. -/
theorem cofiberMap_stableEquivalence_of_based_homotopyExtension
    {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map f))
    (hg : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map g))
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (cofiberMap a b h) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (coneMap_stableEquivalence a b h ha hb)
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence_of_based_homotopyExtension f hf)
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence_of_based_homotopyExtension g hg)
  have e := congrArg sourceLocalization.map (coneToCofiber_map a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_left e.symm

/-- Stable equivalences on a source and its actual quotient cofiber detect
target equivalences when both original arrows have levelwise based homotopy extension. -/
theorem stableEquivalence_target_of_cofiberMap_based_homotopyExtension
    {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map f))
    (hg : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor n).map g))
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (ha : stableEquivalences a) (hc : stableEquivalences (cofiberMap a b h)) :
    stableEquivalences b := by
  apply stableEquivalence_target_of_coneMap_general a b h ha
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ hc
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence_of_based_homotopyExtension f hf)
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence_of_based_homotopyExtension g hg)
  have e := congrArg sourceLocalization.map (coneToCofiber_map a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
