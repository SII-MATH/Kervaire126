module

public import KIP126.Def.StableHomotopy.Implementation.Generators
public import Mathlib.CategoryTheory.Limits.IsLimit

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory CategoryTheory.Limits
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- The original based colimit topology detects continuity of arbitrary
functions from continuity on all stages, including for disconnected diagrams. -/
theorem continuous_of_isColimit {J : Type v} [Category.{w} J]
    (F : J ⥤ BasedSpace.{u}) (c : Cocone F) (hc : IsColimit c)
    {Y : Type u} [TopologicalSpace Y] (f : c.pt → Y)
    (hf : ∀ j, Continuous (f ∘ (c.ι.app j).map)) : Continuous f := by
  let Z : BasedSpace.{u} := ⟨TopCat.of Y,f c.pt.point⟩
  let s : Cocone F := {
    pt := Z
    ι := {
      app j := {
        map := ⟨f ∘ (c.ι.app j).map,hf j⟩
        point := congrArg f (c.ι.app j).point }
      naturality := by
        intro i j g
        apply Hom.ext
        apply ContinuousMap.ext
        intro x
        exact congrArg f (congrArg (fun q : F.obj i ⟶ c.pt => q.map x) (c.w g)) } }
  letI : TopologicalSpace (ULift.{0} Y) := ⊤
  let Z₀ : BasedSpace.{u} := ⟨TopCat.of (ULift.{0} Y),ULift.up (f c.pt.point)⟩
  let q : Z ⟶ Z₀ := {
    map := { toFun := fun x => ULift.up x, continuous_toFun := continuous_top }
    point := rfl }
  let f₀ : c.pt ⟶ Z₀ := {
    map := { toFun := fun x => ULift.up (f x), continuous_toFun := continuous_top }
    point := rfl }
  have he : hc.desc s ≫ q = f₀ := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc,hc.fac]
    rfl
  exact (hc.desc s).map.continuous.congr
    (fun x => congrArg (fun g : c.pt ⟶ Z₀ => (g.map x).down) he)

/-- Any actual based-space colimit of compactly generated spaces is
compactly generated, with its original topology and no connectedness premise. -/
theorem uCompactlyGeneratedSpace_of_isColimit {J : Type v} [Category.{w} J]
    (F : J ⥤ BasedSpace.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ j, UCompactlyGeneratedSpace.{u} (F.obj j)] :
    UCompactlyGeneratedSpace.{u} c.pt := by
  apply _root_.uCompactlyGeneratedSpace_of_continuous_maps
  intro Y tY f hf
  apply continuous_of_isColimit F c hc f
  intro j
  apply continuous_from_uCompactlyGeneratedSpace
  intro S g
  exact hf S ((c.ι.app j).map.comp g)

end KIP126.StableHomotopy.Implementation.BasedSpace
