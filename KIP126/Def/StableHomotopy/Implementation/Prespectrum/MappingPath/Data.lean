module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- Regard a strict map as a map with constant bonding comparison homotopies. -/
def strictHomotopyMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) : HomotopyMap X Y where
  level := f.level
  point := f.point
  bondHomotopy n := (f.level (n+1)).comp ((X.bond n).comp ⟨Prod.snd,continuous_snd⟩)
  bondHomotopy_zero _ _ _ := rfl
  bondHomotopy_one n x t := f.bond n x t
  bondHomotopy_collapsed n s x t h := by
    change f.level (n+1) (X.bond n (x,t)) = _
    rcases h with rfl | rfl | rfl
    · rw [X.bond_point,f.point]
    · rw [X.bond_zero,f.point]
    · rw [X.bond_one,f.point]

/-- Reuse the existing mapping-path total space for the strict map. -/
abbrev mappingPathLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) : BasedSpace.{u} :=
  (strictHomotopyMap f).pathLevel n

/-- For a strict map the bond acts directly on the retained path, so it
commutes strictly with shortening that path. -/
def mappingPathBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingPathLevel f n × I,mappingPathLevel f (n+1)) := by
  let paths : C(mappingPathLevel f n × I,C(I,Y.level (n+1))) :=
    (⟨fun z => Y.bond n (z.1.1.val.2 z.2,z.1.2),
      (Y.bond n).continuous.comp
        ((continuous_fst.fst.subtype_val.snd.eval continuous_snd).prodMk continuous_fst.snd)⟩ :
      C((mappingPathLevel f n × I) × I,Y.level (n+1))).curry
  refine ⟨fun z => ⟨(X.bond n (z.1.val.1,z.2),paths z),?_⟩,?_⟩
  · change Y.bond n (z.1.val.2 0,z.2) = f.level (n+1) (X.bond n (z.1.val.1,z.2))
    rw [z.1.property]
    exact (f.bond n z.1.val.1 z.2).symm
  · exact (((X.bond n).continuous.comp
      (continuous_fst.subtype_val.fst.prodMk continuous_snd)).prodMk paths.continuous).subtype_mk _

/-- The strict mapping-path prespectrum has the original actual total space
at every level and pointwise bonding maps. -/
abbrev mappingPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.{u} where
  level := mappingPathLevel f
  bond := mappingPathBond f
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

/-- Include a source point with the constant path at its image. -/
def mappingPathInclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) : X ⟶ mappingPath f where
  level := (strictHomotopyMap f).sourceSection
  point := (strictHomotopyMap f).sourceSection_point
  bond n x t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext; intro s; exact f.bond n x t

/-- Forget the carried path. -/
def mappingPathRetraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) : mappingPath f ⟶ X where
  level := (strictHomotopyMap f).sourceProjection.level
  point _ := rfl
  bond _ _ _ := rfl

/-- Evaluate the carried path at its free endpoint. -/
def mappingPathProjection {X Y : Prespectrum.{u}} (f : X ⟶ Y) : mappingPath f ⟶ Y where
  level := (strictHomotopyMap f).targetProjection.level
  point _ := rfl
  bond _ _ _ := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
