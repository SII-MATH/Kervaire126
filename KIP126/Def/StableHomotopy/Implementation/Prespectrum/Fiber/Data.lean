module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Data
public import KIP126.Def.Topology.HomotopyFiber.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- The actual path-to-basepoint homotopy fiber at one level. -/
abbrev fiberLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) : BasedSpace.{u} where
  space := KIP126.Topology.PathHomotopyFiber.space (f.level n) (Y.level n).point
  point := ⟨((X.level n).point,ContinuousMap.const I (Y.level n).point),⟨(f.point n).symm,rfl⟩⟩

/-- Apply the bonding map to the source and to every point of the retained path. -/
def fiberBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(fiberLevel f n × I, fiberLevel f (n+1)) := by
  let paths : C(fiberLevel f n × I, C(I,Y.level (n+1))) :=
    (⟨fun z => Y.bond n (z.1.1.val.2 z.2,z.1.2),
      (Y.bond n).continuous.comp
        ((continuous_fst.fst.subtype_val.snd.eval continuous_snd).prodMk continuous_fst.snd)⟩ :
      C((fiberLevel f n × I) × I,Y.level (n+1))).curry
  refine ⟨fun z => ⟨(X.bond n (z.1.val.1,z.2),paths z),⟨?_,?_⟩⟩,?_⟩
  · change Y.bond n (z.1.val.2 0,z.2) = f.level (n+1) (X.bond n (z.1.val.1,z.2))
    rw [z.1.property.1,f.bond]
  · change Y.bond n (z.1.val.2 1,z.2) = (Y.level (n+1)).point
    rw [z.1.property.2,Y.bond_point]
  · exact (((X.bond n).continuous.comp
      (continuous_fst.subtype_val.fst.prodMk continuous_snd)).prodMk paths.continuous).subtype_mk _

/-- The genuine pointwise homotopy-fiber prespectrum. -/
abbrev fiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.{u} where
  level := fiberLevel f
  bond := fiberBond f
  bond_point n t := by
    apply Subtype.ext
    apply Prod.ext
    · exact X.bond_point n t
    · apply ContinuousMap.ext; intro s; exact Y.bond_point n t
  bond_zero n z := by
    apply Subtype.ext
    apply Prod.ext
    · exact X.bond_zero n z.val.1
    · apply ContinuousMap.ext; intro s; exact Y.bond_zero n (z.val.2 s)
  bond_one n z := by
    apply Subtype.ext
    apply Prod.ext
    · exact X.bond_one n z.val.1
    · apply ContinuousMap.ext; intro s; exact Y.bond_one n (z.val.2 s)

/-- Forget the retained path in the actual homotopy fiber. -/
def fiberProjection {X Y : Prespectrum.{u}} (f : X ⟶ Y) : fiber f ⟶ X where
  level n := KIP126.Topology.PathHomotopyFiber.projection (f.level n) (Y.level n).point
  point _ := rfl
  bond _ _ _ := rfl

/-- A based loop lies over the source basepoint in the actual homotopy fiber. -/
def fiberConnecting {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.loop Y ⟶ fiber f where
  level n :=
    { toFun p := ⟨((X.level n).point,p.toContinuousMap),
        ⟨p.source.trans (f.point n).symm,p.target⟩⟩
      continuous_toFun := (continuous_const.prodMk continuous_induced_dom).subtype_mk _ }
  point _ := rfl
  bond n p t := by
    apply Subtype.ext
    apply Prod.ext
    · exact (X.bond_point n t).symm
    · rfl

/-- The retained path is an actual strict nullhomotopy of projection followed by f. -/
def fiberNullPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) : fiber f ⟶ pathPrespectrum Y where
  level n := KIP126.Topology.PathHomotopyFiber.path (f.level n) (Y.level n).point
  point _ := rfl
  bond _ _ _ := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
