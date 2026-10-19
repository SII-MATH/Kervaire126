module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Level.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Opposite
open HF2Bond
set_option backward.isDefEq.respectTransparency false

/-- Addition of the actual Dold--Kan coefficient simplices. -/
noncomputable def additionSet (n : ℕ) : pairSet n ⟶ hf2SimplicialSet n where
  app a := ↾fun x => @Add.add ((hf2SimplicialModule n).obj a) inferInstance x.1 x.2
  naturality a b f := by
    ext x
    exact (((hf2SimplicialModule n).map f).hom.map_add x.1 x.2).symm

/-- The actual zero-preserving diagonal on coefficient simplices. -/
noncomputable def diagonalSet (n : ℕ) : hf2SimplicialSet n ⟶ pairSet n :=
  lift (𝟙 _) (𝟙 _)

noncomputable def inlSet (n : ℕ) : hf2SimplicialSet n ⟶ pairSet n where
  app a := ↾fun x => (x,(0 : (hf2SimplicialModule n).obj a))
  naturality a b f := by
    ext x
    exact Prod.ext rfl (((hf2SimplicialModule n).map f).hom.map_zero).symm

noncomputable def inrSet (n : ℕ) : hf2SimplicialSet n ⟶ pairSet n where
  app a := ↾fun x => ((0 : (hf2SimplicialModule n).obj a),x)
  naturality a b f := by
    ext x
    exact Prod.ext (((hf2SimplicialModule n).map f).hom.map_zero).symm rfl

/-- The zero simplicial coefficient map, retained before realization. -/
noncomputable def zeroSet (n : ℕ) : hf2SimplicialSet n ⟶ hf2SimplicialSet n :=
  Functor.whiskerRight (0 : hf2SimplicialModule n ⟶ hf2SimplicialModule n)
    (forget (ModuleCat (ZMod 2)))

end KIP126.StableHomotopy.Implementation.HF2Scalar
