module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Source.Finite.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.FiniteSupport.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Finite original coproducts preserve stable equivalences, using the
proved preservation of their actual cocones by the source localization. -/
theorem coproductMap_stableEquivalence_of_finite
    {J : Type} [Finite J] {X Y : J → Prespectrum.{0}}
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, stableEquivalences (f j)) :
    stableEquivalences (CategoryTheory.Limits.Sigma.map f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI (j : J) := stableEquivalences.Q_inverts (f j) (hf j)
  have e : sigmaComparison sourceLocalization X ≫ sourceLocalization.map (CategoryTheory.Limits.Sigma.map f) =
      CategoryTheory.Limits.Sigma.map (fun j => sourceLocalization.map (f j)) ≫ sigmaComparison sourceLocalization Y := by
    apply Sigma.hom_ext
    intro j
    rw [← Category.assoc,ι_comp_sigmaComparison,← Functor.map_comp,Sigma.ι_map,
      Functor.map_comp,← Category.assoc,Sigma.ι_map,Category.assoc,ι_comp_sigmaComparison]
  exact IsIso.of_isIso_fac_left e

/-- Arbitrary original coproduct maps preserve stable equivalences when
all original summand levels are T1. Compact representatives have finite
support; actual subfamily retractions detect the finite kernel. -/
theorem coproductMap_stableEquivalence_of_level_t1Space
    {J : Type} {X Y : J → Prespectrum.{0}}
    [∀ j n, T1Space ((X j).level n)] [∀ j n, T1Space ((Y j).level n)]
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, stableEquivalences (f j)) :
    stableEquivalences (CategoryTheory.Limits.Sigma.map f) := by
  classical
  have hnat (s : Set J) : coproductSubfamilyMap X s ≫ CategoryTheory.Limits.Sigma.map f =
      CategoryTheory.Limits.Sigma.map (fun j : s => f j.val) ≫ coproductSubfamilyMap Y s := by
    apply Sigma.hom_ext
    intro j
    simp only [coproductSubfamilyMap, Sigma.ι_desc_assoc, Sigma.ι_map_assoc,
      Sigma.ι_desc, Sigma.ι_map]
  have hfinite (s : Finset J) : stableEquivalences (CategoryTheory.Limits.Sigma.map (fun j : (s : Set J) => f j.val)) :=
    coproductMap_stableEquivalence_of_finite _ (fun j => hf j.val)
  intro d
  have hcomp {A B C : Prespectrum.{0}} (a : A ⟶ B) (b : B ⟶ C)
      (z : StableHomotopy A d) : stableHomotopyMap (a ≫ b) d z =
        stableHomotopyMap b d (stableHomotopyMap a d z) := by
    induction z using Quot.inductionOn with | h z => rfl
  have hinj (Z : J → Prespectrum.{0}) (s : Set J) :
      Function.Injective (stableHomotopyMap (coproductSubfamilyMap Z s) d) := by
    apply Function.LeftInverse.injective
      (g := stableHomotopyMap (coproductSubfamilyRetraction Z s) d)
    intro z
    rw [← hcomp,coproductSubfamilyMap_retraction]
    induction z using Quot.inductionOn with | h z => rfl
  constructor
  · apply (injective_iff_map_eq_zero (stableHomotopyAddHom (CategoryTheory.Limits.Sigma.map f) d)).mpr
    intro a ha
    change stableHomotopyMap (CategoryTheory.Limits.Sigma.map f) d a = 0 at ha
    obtain ⟨s,b,hb⟩ := stableHomotopy_coproduct_finite_support X d a
    have hb' : stableHomotopyMap (CategoryTheory.Limits.Sigma.map (fun j : (s : Set J) => f j.val)) d b = 0 := by
      apply hinj Y (s : Set J)
      rw [stableHomotopyMap_zero,← hcomp,← hnat,hcomp,hb]
      exact ha
    have hb0 : b = 0 := (hfinite s d).injective
      (hb'.trans (stableHomotopyMap_zero _ d).symm)
    rw [← hb,hb0,stableHomotopyMap_zero]
  · intro a
    obtain ⟨s,b,hb⟩ := stableHomotopy_coproduct_finite_support Y d a
    obtain ⟨z,hz⟩ := (hfinite s d).surjective b
    refine ⟨stableHomotopyMap (coproductSubfamilyMap X (s : Set J)) d z,?_⟩
    rw [← hcomp,hnat,hcomp,hz,hb]

end KIP126.StableHomotopy.Implementation.Prespectrum
