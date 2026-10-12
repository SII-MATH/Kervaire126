module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Stability.General.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Pushout.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Levelwise homotopy extension suffices for stable invariance of the actual
quotient cofiber; the original objects need no cofibrancy premise. -/
theorem cofiberMap_stableEquivalence_of_level_homotopyExtension
    {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n)))
    (hg : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (g.level n)))
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (cofiberMap a b h) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ (coneMap_stableEquivalence a b h ha hb)
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence f hf)
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence g hg)
  have e := congrArg sourceLocalization.map (coneToCofiber_map a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_left e.symm

/-- Stable equivalences on a source and its actual quotient cofiber detect
target equivalences when both original arrows have levelwise homotopy extension. -/
theorem stableEquivalence_target_of_cofiberMap_level_homotopyExtension
    {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n)))
    (hg : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (g.level n)))
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (ha : stableEquivalences a) (hc : stableEquivalences (cofiberMap a b h)) :
    stableEquivalences b := by
  apply stableEquivalence_target_of_coneMap_general a b h ha
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ hc
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence f hf)
  letI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence g hg)
  have e := congrArg sourceLocalization.map (coneToCofiber_map a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
