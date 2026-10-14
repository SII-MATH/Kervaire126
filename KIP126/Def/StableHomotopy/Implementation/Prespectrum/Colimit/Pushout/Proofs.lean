module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Colimit.Evaluation.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Colimit.Connected.Proofs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual prespectrum pushout gives the actual topological pushout at
each level, since the span indexing category is connected. -/
theorem isPushout_level {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) (n : ℕ) :
    IsPushout (TopCat.ofHom (f.level n)) (TopCat.ofHom (g.level n))
      (TopCat.ofHom (i.level n)) (TopCat.ofHom (j.level n)) :=
  (evaluationFunctor.{u} n ⋙ BasedSpace.forgetToTop.{u}).map_isPushout h

end KIP126.StableHomotopy.Implementation.Prespectrum
