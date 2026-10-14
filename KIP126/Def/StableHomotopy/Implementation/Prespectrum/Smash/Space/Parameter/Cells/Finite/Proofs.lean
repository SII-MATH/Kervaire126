module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cells.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cell.General.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Finite.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.HomotopyExtension.Based.Proofs

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

/-- A finite family of actual cubical parameter cells extends stable
smash invariance for arbitrary original input spectra. No cofibrancy,
compact generation or separation is assumed for those spectra. -/
theorem spaceSmashMap_finiteCubeAttachCells_stableEquivalence
    {C D : BasedSpace.{0}} [UCompactlyGeneratedSpace.{0} C] {i : C ⟶ D}
    (c : AttachCells.{0} (fun n => BasedSpace.adjoinPointMap (cubeBoundaryInclusion.{0} n)) i)
    [Finite c.ι] {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f)
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
  letI : Finite dx.ι := inferInstanceAs (Finite c.ι)
  have hA : stableEquivalences (spaceSmashMap (𝟙 c.cofan₁.pt) f) :=
    stableEquivalence_of_finite_cofan_map dx.cofan₁ dy.cofan₁ dx.isColimit₁ dy.isColimit₁
      (fun j => spaceSmashMap (𝟙 (A j)) f) (spaceSmashMap (𝟙 c.cofan₁.pt) f)
      (fun j => spaceSmashMap_parameter_natural (c.cofan₁.inj j) f)
      (fun j => spaceSmashMap_cubeBoundary_stableEquivalence_general (c.π j) f hf)
  have hB : stableEquivalences (spaceSmashMap (𝟙 c.cofan₂.pt) f) :=
    stableEquivalence_of_finite_cofan_map dx.cofan₂ dy.cofan₂ dx.isColimit₂ dy.isColimit₂
      (fun j => spaceSmashMap (𝟙 (B j)) f) (spaceSmashMap (𝟙 c.cofan₂.pt) f)
      (fun j => spaceSmashMap_parameter_natural (c.cofan₂.inj j) f)
      (fun j => spaceSmashMap_cube_stableEquivalence (c.π j) f hf)
  exact spaceSmashMap_stableEquivalence_of_parameter_pushout_based c.isPushout.flip f
    (level_hasBasedHomotopyExtension_of_cofan_map dx.cofan₁ dx.cofan₂
      dx.isColimit₁ dx.isColimit₂ (fun j => spaceSmashCubeBoundaryMap (c.π j) X) dx.m dx.hm
      (fun j => spaceSmashCubeBoundaryMap_level_hasBasedHomotopyExtension (c.π j) X))
    (level_hasBasedHomotopyExtension_of_cofan_map dy.cofan₁ dy.cofan₂
      dy.isColimit₁ dy.isColimit₂ (fun j => spaceSmashCubeBoundaryMap (c.π j) Y) dy.m dy.hm
      (fun j => spaceSmashCubeBoundaryMap_level_hasBasedHomotopyExtension (c.π j) Y))
    hA hB hC

end KIP126.StableHomotopy.Implementation.Prespectrum
