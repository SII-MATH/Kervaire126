module

public import KIP126.Def.Topology.HomotopyGroup.Relative.Normalization.Data
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval Topology.Homotopy
universe u v
set_option backward.isDefEq.respectTransparency false

/-- Restricting an actual cube homotopy retains its exact boundary track. -/
theorem cubeBoundaryTransport_boundaryPath {Y : Type u} [TopologicalSpace Y]
    {n : ℕ} {p q : C(Fin n → I,Y)} (H : p.Homotopy q) :
    CubeBoundaryTransport (cubeBoundaryPath H) p q := ⟨H,fun _ _ => rfl⟩

/-- Postcomposition retains the entire prescribed boundary homotopy. -/
theorem CubeBoundaryTransport.map {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) {n : ℕ}
    {a b : C(↥(_root_.Cube.boundary (Fin n)),X)} {γ : Path a b}
    {p q : C(Fin n → I,X)} (h : CubeBoundaryTransport γ p q) :
    CubeBoundaryTransport (γ.map (cubeBoundaryPostcompose f n).continuous) (f.comp p) (f.comp q) := by
  obtain ⟨H,hH⟩ := h
  exact ⟨(ContinuousMap.Homotopy.refl f).comp H,fun t x => congrArg f (hH t x)⟩

/-- Injectivity on the actual based homotopy set implies injectivity of
homotopy classes with any prescribed disk boundary. -/
theorem homotopicRel_of_continuousHomotopyMap_injective
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (n : ℕ)
    (hf : ∀ x, Function.Injective (continuousHomotopyMap f x (f x) rfl n))
    (p q : C(Fin n → I,X))
    (hpq : ∀ x : ↥(_root_.Cube.boundary (Fin n)), p x.val = q x.val)
    (h : (f.comp p).HomotopicRel (f.comp q) (_root_.Cube.boundary (Fin n))) :
    p.HomotopicRel q (_root_.Cube.boundary (Fin n)) := by
  let e := q (fun _ => 0)
  let Q := cubeMapContraction q
  let γ := cubeBoundaryPath Q
  have hq := cubeBoundaryTransport_boundaryPath Q
  obtain ⟨p',hp'⟩ := exists_cubeBoundaryTransport γ p hpq
  let P : GenLoop (Fin n) X e := ⟨p',fun x hx => hp'.target ⟨x,hx⟩⟩
  let O : GenLoop (Fin n) X e := GenLoop.const
  have hm : (f.comp p').HomotopicRel (f.comp (ContinuousMap.const _ e))
      (_root_.Cube.boundary (Fin n)) :=
    ((hp'.map f).homotopic_iff (hq.map f)).mp h
  have heq : continuousHomotopyMap f e (f e) rfl n ⟦P⟧ =
      continuousHomotopyMap f e (f e) rfl n ⟦O⟧ := Quotient.sound hm
  have hrel : p'.HomotopicRel (ContinuousMap.const _ e) (_root_.Cube.boundary (Fin n)) :=
    Quotient.exact (hf e heq)
  exact (hp'.homotopic_iff hq).mpr hrel

/-- Surjectivity on the based homotopy set produces actual lifts up to
homotopy of disks with any already specified extendible boundary. -/
theorem exists_homotopicRel_lift_of_continuousHomotopyMap_surjective
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (n : ℕ)
    (hf : ∀ x, Function.Surjective (continuousHomotopyMap f x (f x) rfl n))
    (p : C(Fin n → I,X)) (F : C(Fin n → I,Y))
    (hF : ∀ x : ↥(_root_.Cube.boundary (Fin n)), F x.val = f (p x.val)) :
    ∃ q : C(Fin n → I,X),
      (∀ x : ↥(_root_.Cube.boundary (Fin n)), q x.val = p x.val) ∧
      (f.comp q).HomotopicRel F (_root_.Cube.boundary (Fin n)) := by
  let e := p (fun _ => 0)
  let Q := cubeMapContraction p
  let γ := cubeBoundaryPath Q
  have hp := cubeBoundaryTransport_boundaryPath Q
  let δ := γ.map (cubeBoundaryPostcompose f n).continuous
  obtain ⟨F',hF'⟩ := exists_cubeBoundaryTransport δ F hF
  let V : GenLoop (Fin n) Y (f e) := ⟨F',fun x hx => hF'.target ⟨x,hx⟩⟩
  obtain ⟨w,hw⟩ := hf e ⟦V⟧
  obtain ⟨W,rfl⟩ := Quotient.mk_surjective w
  have hW : (f.comp W.val).HomotopicRel F' (_root_.Cube.boundary (Fin n)) := Quotient.exact hw
  obtain ⟨q,hq⟩ := exists_cubeBoundaryTransport γ.symm W.val
    (fun x => W.property x.val x.property)
  refine ⟨q,hq.target,?_⟩
  have hq' : CubeBoundaryTransport γ q W.val := by
    simpa only [Path.symm_symm] using hq.symm
  exact ((hq'.map f).homotopic_iff hF').mpr hW

end KIP126.Topology
