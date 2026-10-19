module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Lift.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Kernel.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Apply the second map to the retained path in the first fiber. -/
def fiberCompositeInclusion {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber f ⟶ fiber (f ≫ g) :=
  fiberMap f (f ≫ g) (𝟙 X) g (by simp)

/-- Project the source point through f, retaining its entire composite null-path. -/
def fiberCompositeProjection {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (f ≫ g) ⟶ fiber g :=
  fiberMap (f ≫ g) g f (𝟙 Z) (by simp)

/-- Read the source coordinate of the retained fiber-valued path. -/
def fiberCompositeRetraction {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber (fiberCompositeProjection f g) ⟶ fiber f where
  level n :=
    { toFun z := ⟨(z.val.1.val.1,((fiberProjection g).level n).comp z.val.2),⟨
        congrArg (fun a : (fiber g).level n => a.val.1) z.property.1,
        congrArg (fun a : (fiber g).level n => a.val.1) z.property.2⟩⟩
      continuous_toFun := (continuous_subtype_val.fst.subtype_val.fst.prodMk
        ((ContinuousMap.continuous_postcomp ((fiberProjection g).level n)).comp
          continuous_subtype_val.snd)).subtype_mk _ }
  point _ := rfl
  bond _ _ _ := rfl

/-- Slide the original retained path to its endpoint, retaining its image tail. -/
def fiberCompositeNullLevel {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    C(I × (fiber f).level n,(fiber g).level n) := by
  let paths : C((I × (fiber f).level n) × I,Z.level n) :=
    ⟨fun z => g.level n (z.1.2.val.2 (Set.Icc.convexComb z.1.1 1 z.2)),by fun_prop⟩
  refine ⟨fun z => ⟨(z.2.val.2 z.1,paths.curry z),⟨?_,?_⟩⟩,
    ((continuous_snd.subtype_val.snd.eval continuous_fst).prodMk
      paths.curry.continuous).subtype_mk _⟩
  · exact congrArg (fun s => g.level n (z.2.val.2 s)) (Set.Icc.convexComb_zero z.1 1)
  · exact (congrArg (fun s => g.level n (z.2.val.2 s)) (Set.Icc.convexComb_one z.1 1)).trans
      ((congrArg (g.level n) z.2.property.2).trans (g.point n))

/-- The composite of the two actual fiber maps has an explicit strict nullhomotopy. -/
def fiberCompositeNullPath {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiber f ⟶ pathPrespectrum (fiber g) where
  level n := ((fiberCompositeNullLevel f g n).comp ⟨Prod.swap,continuous_swap⟩).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro v
      exact g.point n
  bond n p t := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro v
      exact g.bond n _ t

end KIP126.StableHomotopy.Implementation.Prespectrum
