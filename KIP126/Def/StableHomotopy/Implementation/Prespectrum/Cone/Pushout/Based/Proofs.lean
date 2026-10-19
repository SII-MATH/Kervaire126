module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.HomotopyExtension.Based.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Naturality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Pushout.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The original cone comparison of a based-HEP pushout is a stable
equivalence through the actual quotient-cofiber pushout isomorphism. -/
theorem coneMap_stableEquivalence_of_based_homotopyExtension_pushout
    {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j)
    (hf : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map f)) :
    stableEquivalences (coneMap g i h.w) := by
  have hj (n : ℕ) : BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map j) :=
    BasedSpace.hasBasedHomotopyExtension_of_isPushout
      ((evaluationFunctor.{u} n).map_isPushout h) (hf n)
  letI := stableEquivalences.Q_inverts _
    (coneToCofiber_stableEquivalence_of_based_homotopyExtension f hf)
  letI := stableEquivalences.Q_inverts _
    (coneToCofiber_stableEquivalence_of_based_homotopyExtension j hj)
  haveI : IsIso (cofiberMap g i h.w) := by
    rw [cofiberMap_eq_pushoutIso h]
    infer_instance
  apply (stableEquivalence_iff_source_isIso _).mpr
  have he := congrArg sourceLocalization.map (coneToCofiber_map g i h.w)
  simp only [Functor.map_comp] at he
  exact IsIso.of_isIso_fac_right he

/-- Stable excision for the actual strict pushout of a levelwise
based-homotopy-extension map, without cofibrancy assumptions on its objects. -/
theorem isPushout_stableEquivalence_of_based_homotopyExtension
    {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j)
    (hf : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map f)) (hg : stableEquivalences g) :
    stableEquivalences i :=
  stableEquivalence_target_of_coneMap_general g i h.w hg
    (coneMap_stableEquivalence_of_based_homotopyExtension_pushout h hf)

/-- The two actual levelwise based-homotopy-extension pushouts glue stable
equivalences of their three inputs, retaining the given map on the outputs. -/
theorem isPushout_stableEquivalence_gluing_of_based_homotopyExtension
    {A B C D A' B' C' D' : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ D'} {j' : C' ⟶ D'}
    (hf : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map f))
    (hf' : ∀ n, BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map f'))
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hab : f ≫ b = a ≫ f') (_hac : g ≫ c = a ≫ g')
    (hbd : i ≫ d = b ≫ i') (hcd : j ≫ d = c ≫ j')
    (ha : stableEquivalences a) (hb : stableEquivalences b) (hc : stableEquivalences c) :
    stableEquivalences d := by
  have hj (n : ℕ) : BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map j) :=
    BasedSpace.hasBasedHomotopyExtension_of_isPushout
      ((evaluationFunctor.{u} n).map_isPushout h) (hf n)
  have hj' (n : ℕ) : BasedSpace.HasBasedHomotopyExtension ((evaluationFunctor.{u} n).map j') :=
    BasedSpace.hasBasedHomotopyExtension_of_isPushout
      ((evaluationFunctor.{u} n).map_isPushout h') (hf' n)
  apply stableEquivalence_target_of_cofiberMap_based_homotopyExtension hj hj' c d hcd hc
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (cofiberMap_stableEquivalence_of_based_homotopyExtension hf hf' a b hab ha hb)
  have e := congrArg sourceLocalization.map (cofiberPushoutIso_natural h h' a b c d hab hbd hcd)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_left e

end KIP126.StableHomotopy.Implementation.Prespectrum
