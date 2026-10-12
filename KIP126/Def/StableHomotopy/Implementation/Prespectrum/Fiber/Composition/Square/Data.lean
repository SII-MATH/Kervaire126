module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Comparison

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Assemble a continuous deformation of the retained square into an
actual second-fiber map, keeping the original point and source path. -/
def fiberCompositeSquareLift {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (D : C(((I × (fiber (fiberCompositeProjection f g)).level n) × I) × I,Z.level n))
    (h₀ : ∀ θ z s, D (((θ,z),s),0) = g.level n (z.val.2 s).val.1)
    (h₁ : ∀ θ z s, D (((θ,z),s),1) = (Z.level n).point)
    (ht : ∀ θ z t, D (((θ,z),1),t) = (Z.level n).point) :
    C(I × (fiber (fiberCompositeProjection f g)).level n,
      (fiber (fiberCompositeProjection f g)).level n) := by
  let P := D.curry
  let H : C((I × (fiber (fiberCompositeProjection f g)).level n) × I,(fiber g).level n) :=
    ⟨fun z => ⟨((z.1.2.val.2 z.2).val.1,P z),⟨h₀ _ _ _,h₁ _ _ _⟩⟩,
      (((continuous_fst.snd.subtype_val.snd.eval continuous_snd).subtype_val.fst).prodMk
        P.continuous).subtype_mk _⟩
  let F : C(I × (fiber (fiberCompositeProjection f g)).level n,(fiber (f ≫ g)).level n) :=
    ⟨fun z => ⟨(z.2.val.1.val.1,P (z,0)),⟨(h₀ _ _ _).trans
        (congrArg (fun a : (fiber g).level n => g.level n a.val.1) z.2.property.1),h₁ _ _ _⟩⟩,
      (continuous_snd.subtype_val.fst.subtype_val.fst.prodMk
        (P.continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _⟩
  refine ⟨fun z => ⟨(F z,H.curry z),⟨?_,?_⟩⟩,
    (F.continuous.prodMk H.curry.continuous).subtype_mk _⟩
  · apply Subtype.ext
    apply Prod.ext
    · change (z.2.val.2 0).val.1 = f.level n z.2.val.1.val.1
      exact congrArg (fun a : (fiber g).level n => a.val.1) z.2.property.1
    · rfl
  · apply Subtype.ext
    apply Prod.ext
    · change (z.2.val.2 1).val.1 = (Y.level n).point
      exact congrArg (fun a : (fiber g).level n => a.val.1) z.2.property.2
    · apply ContinuousMap.ext
      intro t
      exact ht _ _ _

/-- A deformation of retained squares which fixes the zero square and
commutes with every bond gives a genuine strict prespectrum homotopy. -/
def fiberCompositeSquareHomotopy {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : ∀ n, C(((I × (fiber (fiberCompositeProjection f g)).level n) × I) × I,Z.level n))
    (h₀ : ∀ n θ z s, D n (((θ,z),s),0) = g.level n (z.val.2 s).val.1)
    (h₁ : ∀ n θ z s, D n (((θ,z),s),1) = (Z.level n).point)
    (ht : ∀ n θ z t, D n (((θ,z),1),t) = (Z.level n).point)
    (hb : ∀ n θ s t, D n (((θ,((fiber (fiberCompositeProjection f g)).level n).point),s),t) =
      (Z.level n).point)
    (hbond : ∀ n z v θ s t,
      D (n+1) (((θ,(fiber (fiberCompositeProjection f g)).bond n (z,v)),s),t) =
        Z.bond n (D n (((θ,z),s),t),v)) :
    fiber (fiberCompositeProjection f g) ⟶ pathPrespectrum (fiber (fiberCompositeProjection f g)) where
  level n := ((fiberCompositeSquareLift f g n (D n) (h₀ n) (h₁ n) (ht n)).comp
    ⟨Prod.swap,continuous_swap⟩).curry
  point n := by
    apply ContinuousMap.ext
    intro θ
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        exact hb n θ 0 t
    · apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        exact hb n θ s t
  bond n z v := by
    apply ContinuousMap.ext
    intro θ
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        exact hbond n z v θ 0 t
    · apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        exact hbond n z v θ s t

end KIP126.StableHomotopy.Implementation.Prespectrum
