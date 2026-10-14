module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Suspension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderHomotopy_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderHomotopy f ≫ pathEvaluation (mappingCylinder f) 0 = 𝟙 (mappingCylinder f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact mappingCylinderContraction_zero f n z

@[simp] theorem mappingCylinderHomotopy_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderHomotopy f ≫ pathEvaluation (mappingCylinder f) 1 =
      mappingCylinderProjection f ≫ mappingCylinderSection f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  exact mappingCylinderContraction_one f n z

/-- The full target image is fixed throughout the strict deformation. -/
@[simp] theorem mappingCylinderSection_homotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderSection f ≫ mappingCylinderHomotopy f =
      mappingCylinderSection f ≫ pathConstant (mappingCylinder f) := rfl

/-- The specified deformation gives a relative homotopy of every actual based loop. -/
theorem mappingCylinder_loop_deformation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((mappingCylinder f).level n) ((mappingCylinder f).level n).point) :
    GenLoop.Homotopic p
      ⟨((mappingCylinderSection f).level n).comp
        (((mappingCylinderProjection f).level n).comp p.val), by
        intro t ht
        change (mappingCylinderSection f).level n ((mappingCylinderProjection f).level n (p t)) = _
        exact (congrArg (fun z => (mappingCylinderSection f).level n
          ((mappingCylinderProjection f).level n z)) (p.property t ht)).trans
          (by rw [(mappingCylinderProjection f).point,(mappingCylinderSection f).point])⟩ := by
  refine ⟨{ toFun := fun z => mappingCylinderContraction f n (p z.2,z.1)
            continuous_toFun := (mappingCylinderContraction f n).continuous.comp
              ((p.val.continuous.comp continuous_snd).prodMk continuous_fst)
            map_zero_left := fun t => mappingCylinderContraction_zero f n (p t)
            map_one_left := fun t => mappingCylinderContraction_one f n (p t)
            prop' := ?_ }⟩
  intro s t ht
  change mappingCylinderContraction f n (p t,s) = p t
  exact (congrArg (fun z => mappingCylinderContraction f n (z,s)) (p.property t ht)).trans
    ((mappingCylinderContraction_point f n s).trans (p.property t ht).symm)

/-- The actual mapping-cylinder projection is always a stable equivalence. -/
theorem mappingCylinderProjection_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (mappingCylinderProjection f) := by
  apply stableEquivalence_of_levelwise_loops
  · intro n r p q hpq
    exact (mappingCylinder_loop_deformation f n r p).trans
      ((hpq.comp_continuousMap ((mappingCylinderSection f).level n)).trans
        (mappingCylinder_loop_deformation f n r q).symm)
  · intro n r p
    refine ⟨⟨((mappingCylinderSection f).level n).comp p.val, ?_⟩, ?_⟩
    · intro t ht
      change (mappingCylinderSection f).level n (p t) = _
      exact (congrArg ((mappingCylinderSection f).level n) (p.property t ht)).trans
        ((mappingCylinderSection f).point n)
    · exact GenLoop.Homotopic.refl p

/-- The projection is a bijection on each actual based homotopy set,
before stabilization. -/
theorem mappingCylinderProjection_levelHomotopy_bijective {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n r : ℕ) : Function.Bijective ((mappingCylinderProjection f).levelHomotopy n r) := by
  have hl (x : _root_.HomotopyGroup (Fin r) (Y.level n) (Y.level n).point) :
      (mappingCylinderProjection f).levelHomotopy n r
        ((mappingCylinderSection f).levelHomotopy n r x) = x := by
    induction x using Quotient.inductionOn with
    | h p => rfl
  have hr (x : _root_.HomotopyGroup (Fin r) ((mappingCylinder f).level n)
      ((mappingCylinder f).level n).point) :
      (mappingCylinderSection f).levelHomotopy n r
        ((mappingCylinderProjection f).levelHomotopy n r x) = x := by
    induction x using Quotient.inductionOn with
    | h p => exact Quotient.sound (mappingCylinder_loop_deformation f n r p).symm
  exact ⟨fun x y h => (hr x).symm.trans
      ((congrArg ((mappingCylinderSection f).levelHomotopy n r) h).trans (hr y)),
    fun y => ⟨(mappingCylinderSection f).levelHomotopy n r y,hl y⟩⟩

/-- Factoring an actual stable equivalence by this cylinder produces
another actual stable equivalence on the source side. -/
theorem mappingCylinderInclusion_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (mappingCylinderInclusion f) := by
  intro d
  have hc (x : StableHomotopy X d) :
      stableHomotopyMap (mappingCylinderProjection f) d
        (stableHomotopyMap (mappingCylinderInclusion f) d x) = stableHomotopyMap f d x := by
    induction x using Quot.inductionOn with
    | h p => rfl
  have hq := mappingCylinderProjection_stableEquivalence f d
  constructor
  · intro x y h
    apply (hf d).injective
    rw [← hc x,← hc y,h]
  · intro z
    obtain ⟨x,hx⟩ := (hf d).surjective (stableHomotopyMap (mappingCylinderProjection f) d z)
    exact ⟨x,hq.injective ((hc x).trans hx)⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
