module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Coproduct.Subfamily.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
universe u

/-- The actual strict inclusion of the coproduct of a subfamily. -/
noncomputable def coproductSubfamilyMap {J : Type u} (X : J → Prespectrum.{u}) (s : Set J) :
    (∐ fun j : s => X j.val) ⟶ ∐ X :=
  Sigma.desc (fun j : s => Sigma.ι X j.val)

/-- Evaluating the actual strict coproduct gives the actual based
coproduct of its original levels. -/
noncomputable def coproductLevelIso {J : Type u} (X : J → Prespectrum.{u}) (n : ℕ) :
    (∐ X : Prespectrum.{u}).level n ≅ ∐ fun j => (X j).level n :=
  PreservesCoproduct.iso (evaluationFunctor n) X

end KIP126.StableHomotopy.Implementation.Prespectrum
