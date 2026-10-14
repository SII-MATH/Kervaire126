module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Naturality

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Loop addition is natural for every target morphism in the original
stable localization, including formal inverses of stable equivalences. -/
theorem sourceLoopAdd_postcomp {X Y : Prespectrum.{u}} {A : SourceCategory.{u}}
    (f g : A ⟶ sourceLocalization.obj (Prespectrum.loop X))
    (b : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) :
    sourceLoopAdd X f g ≫ sourceLoopFunctor.map b =
      sourceLoopAdd Y (f ≫ sourceLoopFunctor.map b) (g ≫ sourceLoopFunctor.map b) := by
  unfold sourceLoopAdd
  rw [Category.assoc, source_loopConcat_natural, ← Category.assoc,
    sourcePiLift_comp_sourcePiMap]
  congr 2
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

@[reassoc] theorem sourceLoopNeg_postcomp {X Y : Prespectrum.{u}} {A : SourceCategory.{u}}
    (f : A ⟶ sourceLocalization.obj (Prespectrum.loop X))
    (b : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) :
    sourceLoopNeg X f ≫ sourceLoopFunctor.map b =
      sourceLoopNeg Y (f ≫ sourceLoopFunctor.map b) := by
  simp only [sourceLoopNeg, Category.assoc, source_loopInverse_natural]

end KIP126.StableHomotopy.Implementation.Prespectrum
