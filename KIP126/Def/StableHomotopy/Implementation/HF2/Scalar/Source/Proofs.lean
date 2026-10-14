module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Addition.Proofs
public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Preadditive
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Source.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits
open Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- The two concrete coefficient projections jointly detect arbitrary
source maps into the paired coefficient realization. -/
theorem source_pair_hom_ext {A : SourceCategory.{0}}
    {f g : A ⟶ sourceLocalization.obj pairPrespectrum}
    (hf : f ≫ sourceLocalization.map pairFst = g ≫ sourceLocalization.map pairFst)
    (hg : f ≫ sourceLocalization.map pairSnd = g ≫ sourceLocalization.map pairSnd) : f = g := by
  letI := stableEquivalences.Q_inverts pairComparison pairComparison_stableEquivalence
  apply (cancel_mono (sourceLocalization.map pairComparison)).mp
  apply sourcePi_hom_ext
  intro j
  simp only [Category.assoc,← Functor.map_comp]
  fin_cases j
  · exact hf
  · exact hg

/-- The realized simplicial diagonal equals the sum of the two actual
inclusions in the original additive stable source category. -/
theorem source_diagonal_eq_add : sourceLocalization.map diagonal =
    sourceLocalization.map inl + sourceLocalization.map inr := by
  apply source_pair_hom_ext
  · simp only [Preadditive.add_comp,← Functor.map_comp,diagonal_pairFst,inl_pairFst,
      inr_pairFst,CategoryTheory.Functor.map_id,Functor.map_zero,add_zero]
  · simp only [Preadditive.add_comp,← Functor.map_comp,diagonal_pairSnd,inl_pairSnd,
      inr_pairSnd,CategoryTheory.Functor.map_id,Functor.map_zero,zero_add]

/-- The actual Dold--Kan coefficient spectrum has characteristic two as
an object of the original stable source category. The proof uses the
literal simplicial addition and diagonal maps, not detection by its
homotopy groups. -/
theorem hf2RealizationPrespectrum_id_add_id :
    𝟙 (sourceLocalization.obj hf2RealizationPrespectrum) + 𝟙 _ = 0 := by
  have h := congrArg (fun k => k ≫ sourceLocalization.map addition) source_diagonal_eq_add
  simpa only [Preadditive.add_comp,← Functor.map_comp,diagonal_addition,
    inl_addition,inr_addition,Functor.map_zero,CategoryTheory.Functor.map_id] using h.symm

theorem hf2RealizationPrespectrum_two_id :
    (2 : ℕ) • 𝟙 (sourceLocalization.obj hf2RealizationPrespectrum) = 0 := by
  simpa only [two_nsmul] using hf2RealizationPrespectrum_id_add_id

end KIP126.StableHomotopy.Implementation.HF2Scalar
