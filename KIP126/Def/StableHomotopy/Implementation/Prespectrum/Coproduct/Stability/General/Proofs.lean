module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Stability.T1.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.FiniteSupport.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- Arbitrary original coproducts preserve stable equivalences. Actual
compact cubical representatives acquire finite support by a based
specialization homotopy; no separation assumption is required. -/
theorem coproductMap_stableEquivalence_general
    {J : Type} {X Y : J → Prespectrum.{0}}
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
    obtain ⟨s,b,hb⟩ := stableHomotopy_coproduct_finite_support_general X d a
    have hb' : stableHomotopyMap (CategoryTheory.Limits.Sigma.map (fun j : (s : Set J) => f j.val)) d b = 0 := by
      apply hinj Y (s : Set J)
      rw [stableHomotopyMap_zero,← hcomp,← hnat,hcomp,hb]
      exact ha
    have hb0 : b = 0 := (hfinite s d).injective
      (hb'.trans (stableHomotopyMap_zero _ d).symm)
    rw [← hb,hb0,stableHomotopyMap_zero]
  · intro a
    obtain ⟨s,b,hb⟩ := stableHomotopy_coproduct_finite_support_general Y d a
    obtain ⟨z,hz⟩ := (hfinite s d).surjective b
    refine ⟨stableHomotopyMap (coproductSubfamilyMap X (s : Set J)) d z,?_⟩
    rw [← hcomp,hnat,hcomp,hz,hb]

end KIP126.StableHomotopy.Implementation.Prespectrum
