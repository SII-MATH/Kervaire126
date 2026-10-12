module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Map.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Comparison.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Pushout.Proofs
public import KIP126.Def.Topology.HomotopyExtension.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual cofiber comparison of a pushout square is its quotient
pushout isomorphism. -/
theorem cofiberMap_eq_pushoutIso {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) :
    cofiberMap g i h.w = (cofiberPushoutIso h).hom := by
  apply cofiberHom_ext
  rw [cofiberProjection_map, cofiberPushoutIso_projection]

/-- Pushing out a levelwise homotopy-extension map gives a stable
equivalence between the two actual mapping cones. -/
theorem coneMap_stableEquivalence_of_isPushout {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j)
    (hf : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n))) :
    stableEquivalences (coneMap g i h.w) := by
  have hj (n : ℕ) : KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (j.level n)) :=
    KIP126.Topology.HomotopyExtension.hasHomotopyExtension_of_isPushout
      (isPushout_level h n) (hf n)
  haveI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence f hf)
  haveI := stableEquivalences.Q_inverts _ (coneToCofiber_stableEquivalence j hj)
  haveI : IsIso (cofiberMap g i h.w) := by
    rw [cofiberMap_eq_pushoutIso h]
    infer_instance
  apply (stableEquivalence_iff_source_isIso _).mpr
  have he := congrArg sourceLocalization.map (coneToCofiber_map g i h.w)
  simp only [CategoryTheory.Functor.map_comp] at he
  exact IsIso.of_isIso_fac_right he

end KIP126.StableHomotopy.Implementation.Prespectrum
