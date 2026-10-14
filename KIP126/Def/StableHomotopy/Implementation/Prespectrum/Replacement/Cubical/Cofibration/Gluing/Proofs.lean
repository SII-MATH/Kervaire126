module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Cofibration.Detection.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Naturality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- Actual strict pushouts along cubical cofibrations glue stable equivalences
of their three inputs. Cofibrancy and homotopy extension of both pushed-out
arrows follow from the actual original cofibrations. -/
theorem isPushout_stableEquivalence_gluing_of_cubicalCofibration
    {A B C D A' B' C' D' : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ D'} {j' : C' ⟶ D'}
    (hA : IsCubicallyCofibrant A) (hC : IsCubicallyCofibrant C)
    (hA' : IsCubicallyCofibrant A') (hC' : IsCubicallyCofibrant C')
    (hf : IsCubicalCofibration f) (hf' : IsCubicalCofibration f')
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hab : f ≫ b = a ≫ f') (_hac : g ≫ c = a ≫ g')
    (hbd : i ≫ d = b ≫ i') (hcd : j ≫ d = c ≫ j')
    (ha : stableEquivalences a) (hb : stableEquivalences b) (hc : stableEquivalences c) :
    stableEquivalences d := by
  apply stableEquivalence_target_of_cofiberMap (hf.pushout h) (hf'.pushout h') hC hC' c d hcd hc
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _
    (cofiberMap_stableEquivalence_of_cubicalCofibration hf hf' hA hA' a b hab ha hb)
  have e := congrArg sourceLocalization.map (cofiberPushoutIso_natural h h' a b c d hab hbd hcd)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_left e

end KIP126.StableHomotopy.Implementation.Prespectrum
