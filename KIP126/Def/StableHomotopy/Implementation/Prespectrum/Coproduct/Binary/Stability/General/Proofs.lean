module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Pushout.Based.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Proofs
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every initial spectrum map has based homotopy extension levelwise:
the prescribed homotopy on its sole point is constant. -/
theorem zeroMap_level_hasBasedHomotopyExtension (X : Prespectrum.{u}) (n : ℕ) :
    BasedSpace.HasBasedHomotopyExtension
      ((evaluationFunctor n).map (zeroMap zeroPrespectrum X)) := by
  intro Z f p hp h0
  refine ⟨f.map.comp ContinuousMap.fst,?_,fun _ => rfl,?_⟩
  · intro t
    exact f.point
  · intro a t
    have ha : a = (zeroPrespectrum.level n).point := by
      exact @Subsingleton.elim PUnit inferInstance _ _
    subst a
    exact f.point.trans (hp t).symm

/-- Actual binary coproducts preserve stable equivalences between
arbitrary original spectra, by their actual based-HEP pushout squares. -/
theorem coprodMap_stableEquivalence_general
    {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : stableEquivalences f) (hg : stableEquivalences g) :
    stableEquivalences (coprod.map f g) := by
  have h (A B : Prespectrum.{u}) :
      IsPushout (zeroMap zeroPrespectrum A) (zeroMap zeroPrespectrum B)
        (coprod.inl : A ⟶ A ⨿ B) coprod.inr := by
    have h := IsPushout.of_is_coproduct (coprodIsCoprod A B)
      zeroPrespectrum_isZero.isInitial
    have ha : zeroPrespectrum_isZero.isInitial.to A = zeroMap zeroPrespectrum A :=
      zeroPrespectrum_isZero.eq_of_src _ _
    have hb : zeroPrespectrum_isZero.isInitial.to B = zeroMap zeroPrespectrum B :=
      zeroPrespectrum_isZero.eq_of_src _ _
    change IsPushout (zeroPrespectrum_isZero.isInitial.to A)
      (zeroPrespectrum_isZero.isInitial.to B) coprod.inl coprod.inr at h
    rwa [ha,hb] at h
  exact isPushout_stableEquivalence_gluing_of_based_homotopyExtension
    (zeroMap_level_hasBasedHomotopyExtension X) (zeroMap_level_hasBasedHomotopyExtension X')
    (h X Y) (h X' Y') (𝟙 zeroPrespectrum) f g (coprod.map f g)
    (zeroPrespectrum_isZero.eq_of_src _ _) (zeroPrespectrum_isZero.eq_of_src _ _)
    (coprod.inl_map f g) (coprod.inr_map f g) (stableEquivalences.id_mem _) hf hg

end KIP126.StableHomotopy.Implementation.Prespectrum
