module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Level.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open Prespectrum

/-- The realization of the paired simplicial coefficient model, with
the actual paired cone bonds. -/
noncomputable def pairPrespectrum : Prespectrum.{0} where
  level := pairLevel
  bond := pairBond
  bond_point := pairBond_point
  bond_zero := pairBond_zero
  bond_one := pairBond_one

noncomputable def pairFst : pairPrespectrum ⟶ hf2RealizationPrespectrum where
  level n := (SSet.toTop.map (fst (hf2SimplicialSet n) (hf2SimplicialSet n))).hom
  point := pairLevel_fst_point
  bond := pairBond_fst

noncomputable def pairSnd : pairPrespectrum ⟶ hf2RealizationPrespectrum where
  level n := (SSet.toTop.map (snd (hf2SimplicialSet n) (hf2SimplicialSet n))).hom
  point := pairLevel_snd_point
  bond := pairBond_snd

/-- Actual comparison with the original pointwise binary product. -/
noncomputable def pairComparison : pairPrespectrum ⟶
    piPrespectrum (fun _ : Fin 2 => hf2RealizationPrespectrum) :=
  piLift ![pairFst,pairSnd]

end KIP126.StableHomotopy.Implementation.HF2Scalar
