module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cells.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cell.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Cofibrant.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting
set_option backward.isDefEq.respectTransparency false

private instance (n : ℕ) : T2Space (cubeBoundaryObject.{0} n) :=
  inferInstanceAs (T2Space (ULift.{0} (↥(_root_.Cube.boundary (Fin n)))))

private instance (n : ℕ) :
    UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (cubeBoundaryObject.{0} n)) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{0} ((cubeBoundaryObject.{0} n) ⊕ PUnit))

private instance (n : ℕ) :
    UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (cubeObject.{0} n)) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{0} ((cubeObject.{0} n) ⊕ PUnit))

variable {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C] {i : C ⟶ D}
  (c : AttachCells.{0} (fun n => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{0} n)) i)

include c

/-- Smashing any actual simultaneous family of whole cubical
parameter attachments gives an actual cubical cofibration. -/
theorem spaceSmashMap_cubeAttachCells_isCubicalCofibration
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X) :
    IsCubicalCofibration (spaceSmashMap i (𝟙 X)) := by
  let d := spaceSmashParameterAttachCells c X
  have hm : IsCubicalCofibration d.m :=
    isCubicalCofibration_of_cofan_map d.cofan₁ d.cofan₂ d.isColimit₁ d.isColimit₂
      (fun j => spaceSmashCubeBoundaryMap (c.π j) X) d.m d.hm
      (fun j => spaceSmashCubeBoundaryMap_isCubicalCofibration hX (c.π j))
  intro E B p hp
  exact IsCubicalCofibration.pushout hm d.isPushout.flip p hp

/-- Arbitrary simultaneous parameter-cell attachment retains the
proved cofibrancy of the original old-space smash. -/
theorem IsCubicallyCofibrant.spaceSmash_cubeAttachCells
    {X : Prespectrum.{0}} (hX : IsCubicallyCofibrant X)
    (hC : IsCubicallyCofibrant (spaceSmash C X)) :
    IsCubicallyCofibrant (spaceSmash D X) :=
  hC.of_cubicalCofibration (spaceSmashMap_cubeAttachCells_isCubicalCofibration c hX)

/-- Stable smash invariance extends across an arbitrary family of
actual cubical parameter cells, with no finiteness condition on the
family or its dimensions. -/
theorem spaceSmashMap_cubeAttachCells_stableEquivalence
    {X Y : Prespectrum.{0}} (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y)
    (f : X ⟶ Y) (hf : stableEquivalences f)
    (hCX : IsCubicallyCofibrant (spaceSmash C X))
    (hCY : IsCubicallyCofibrant (spaceSmash C Y))
    (hC : stableEquivalences (spaceSmashMap (𝟙 C) f)) :
    stableEquivalences (spaceSmashMap (𝟙 D) f) := by
  let A (j : c.ι) := BasedSpace.adjoinPoint (cubeBoundaryObject (c.π j))
  let B (j : c.ι) := BasedSpace.adjoinPoint (cubeObject (c.π j))
  letI (j : Discrete c.ι) : UCompactlyGeneratedSpace.{0}
      ((Discrete.functor A).obj j) := inferInstanceAs (UCompactlyGeneratedSpace.{0} (A j.as))
  letI (j : Discrete c.ι) : UCompactlyGeneratedSpace.{0}
      ((Discrete.functor B).obj j) := inferInstanceAs (UCompactlyGeneratedSpace.{0} (B j.as))
  letI : UCompactlyGeneratedSpace.{0} c.cofan₁.pt :=
    BasedSpace.uCompactlyGeneratedSpace_of_isColimit _ c.cofan₁ c.isColimit₁
  letI : UCompactlyGeneratedSpace.{0} c.cofan₂.pt :=
    BasedSpace.uCompactlyGeneratedSpace_of_isColimit _ c.cofan₂ c.isColimit₂
  let dx := spaceSmashParameterAttachCells c X
  let dy := spaceSmashParameterAttachCells c Y
  have hAX : IsCubicallyCofibrant dx.cofan₁.pt :=
    isCubicallyCofibrant_of_cofan dx.cofan₁ dx.isColimit₁
      (fun j => hX.spaceSmash_cubeBoundary (c.π j))
  have hAY : IsCubicallyCofibrant dy.cofan₁.pt :=
    isCubicallyCofibrant_of_cofan dy.cofan₁ dy.isColimit₁
      (fun j => hY.spaceSmash_cubeBoundary (c.π j))
  have hmX : IsCubicalCofibration dx.m :=
    isCubicalCofibration_of_cofan_map dx.cofan₁ dx.cofan₂ dx.isColimit₁ dx.isColimit₂
      (fun j => spaceSmashCubeBoundaryMap (c.π j) X) dx.m dx.hm
      (fun j => spaceSmashCubeBoundaryMap_isCubicalCofibration hX (c.π j))
  have hmY : IsCubicalCofibration dy.m :=
    isCubicalCofibration_of_cofan_map dy.cofan₁ dy.cofan₂ dy.isColimit₁ dy.isColimit₂
      (fun j => spaceSmashCubeBoundaryMap (c.π j) Y) dy.m dy.hm
      (fun j => spaceSmashCubeBoundaryMap_isCubicalCofibration hY (c.π j))
  have hA : stableEquivalences (spaceSmashMap (𝟙 c.cofan₁.pt) f) :=
    stableEquivalence_of_cofan_map dx.cofan₁ dy.cofan₁ dx.isColimit₁ dy.isColimit₁
      (fun j => hX.spaceSmash_cubeBoundary (c.π j))
      (fun j => hY.spaceSmash_cubeBoundary (c.π j))
      (fun j => spaceSmashMap (𝟙 (A j)) f) (spaceSmashMap (𝟙 c.cofan₁.pt) f)
      (fun j => spaceSmashMap_parameter_natural (c.cofan₁.inj j) f)
      (fun j => spaceSmashMap_cubeBoundary_stableEquivalence (c.π j) hX hY f hf)
  have hB : stableEquivalences (spaceSmashMap (𝟙 c.cofan₂.pt) f) :=
    stableEquivalence_of_cofan_map dx.cofan₂ dy.cofan₂ dx.isColimit₂ dy.isColimit₂
      (fun j => hX.spaceSmash_cube (c.π j)) (fun j => hY.spaceSmash_cube (c.π j))
      (fun j => spaceSmashMap (𝟙 (B j)) f) (spaceSmashMap (𝟙 c.cofan₂.pt) f)
      (fun j => spaceSmashMap_parameter_natural (c.cofan₂.inj j) f)
      (fun j => spaceSmashMap_cube_stableEquivalence (c.π j) f hf)
  exact spaceSmashMap_stableEquivalence_of_parameter_pushout c.isPushout.flip f
    hAX hCX hAY hCY hmX hmY hA hB hC

end KIP126.StableHomotopy.Implementation.Prespectrum
