module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct.Stability.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits

/-- The actual binary coproduct of cofibrant spectra in the fixed
universe retains its original cubical lifting property. -/
theorem isCubicallyCofibrant_binaryCoproduct {X Y : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y) :
    IsCubicallyCofibrant (X ⨿ Y) := by
  apply isCubicallyCofibrant_coproduct (pairFunction X Y)
  intro j
  cases j
  · exact hX
  · exact hY

/-- In the fixed original spectrum universe, actual binary coproducts
preserve stable equivalences between proved cofibrant spectra. -/
theorem coprodMap_stableEquivalence_of_isCubicallyCofibrant
    {X Y X' Y' : Prespectrum.{0}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (hX' : IsCubicallyCofibrant X') (hY' : IsCubicallyCofibrant Y')
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : stableEquivalences f) (hg : stableEquivalences g) :
    stableEquivalences (coprod.map f g) := by
  let a : ∀ j, pairFunction X Y j ⟶ pairFunction X' Y' j := fun j =>
    WalkingPair.casesOn j f g
  have hA : ∀ j, IsCubicallyCofibrant (pairFunction X Y j) := by
    intro j
    cases j
    · exact hX
    · exact hY
  have hB : ∀ j, IsCubicallyCofibrant (pairFunction X' Y' j) := by
    intro j
    cases j
    · exact hX'
    · exact hY'
  have ha : ∀ j, stableEquivalences (a j) := by
    intro j
    cases j
    · exact hf
    · exact hg
  have he : CategoryTheory.Limits.Sigma.map a = coprod.map f g := by
    apply coprod.hom_ext
    · change Sigma.ι (pairFunction X Y) WalkingPair.left ≫ _ = _
      exact (Sigma.ι_map a WalkingPair.left).trans (coprod.inl_map f g).symm
    · change Sigma.ι (pairFunction X Y) WalkingPair.right ≫ _ = _
      exact (Sigma.ι_map a WalkingPair.right).trans (coprod.inr_map f g).symm
  rw [← he]
  exact coproductMap_stableEquivalence_of_isCubicallyCofibrant hA hB a ha

end KIP126.StableHomotopy.Implementation.Prespectrum
