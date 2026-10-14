module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.HomotopyExtension.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Stable excision for the actual strict pushout of a levelwise
homotopy-extension map, without cofibrancy assumptions on its objects. -/
theorem isPushout_stableEquivalence_of_level_homotopyExtension
    {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j)
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n))) (hg : stableEquivalences g) :
    stableEquivalences i :=
  stableEquivalence_target_of_coneMap_general g i h.w hg
    (coneMap_stableEquivalence_of_isPushout h hf)

/-- The two actual levelwise homotopy-extension pushouts glue stable
equivalences of their three inputs, retaining the given map on the outputs. -/
theorem isPushout_stableEquivalence_gluing_of_level_homotopyExtension
    {A B C D A' B' C' D' : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ D'} {j' : C' ⟶ D'}
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n)))
    (hf' : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f'.level n)))
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hab : f ≫ b = a ≫ f') (_hac : g ≫ c = a ≫ g')
    (hbd : i ≫ d = b ≫ i') (hcd : j ≫ d = c ≫ j')
    (ha : stableEquivalences a) (hb : stableEquivalences b) (hc : stableEquivalences c) :
    stableEquivalences d := by
  have hj (n : ℕ) : KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (j.level n)) :=
    KIP126.Topology.HomotopyExtension.hasHomotopyExtension_of_isPushout
      (isPushout_level h n) (hf n)
  have hj' (n : ℕ) : KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (j'.level n)) :=
    KIP126.Topology.HomotopyExtension.hasHomotopyExtension_of_isPushout
      (isPushout_level h' n) (hf' n)
  apply stableEquivalence_target_of_cofiberMap_level_homotopyExtension hj hj' c d hcd hc
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (cofiberMap_stableEquivalence_of_level_homotopyExtension hf hf' a b hab ha hb)
  have e := congrArg sourceLocalization.map (cofiberPushoutIso_natural h h' a b c d hab hbd hcd)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_left e

end KIP126.StableHomotopy.Implementation.Prespectrum
