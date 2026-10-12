module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

/-- Shorten the retained path by multiplying its parameter by the deformation
parameter; the original source point is fixed throughout. -/
def mappingPathContraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingPathLevel f n × I,mappingPathLevel f n) := by
  let paths : C(mappingPathLevel f n × I,C(I,Y.level n)) :=
    (⟨fun z => z.1.1.val.2 (z.1.2 * z.2),
      continuous_fst.fst.subtype_val.snd.eval
        ((continuous_fst.snd.subtype_val.mul continuous_snd.subtype_val).subtype_mk _)⟩ :
      C((mappingPathLevel f n × I) × I,Y.level n)).curry
  refine ⟨fun z => ⟨(z.1.val.1,paths z),?_⟩,?_⟩
  · change z.1.val.2 (z.2 * 0) = f.level n z.1.val.1
    rw [mul_zero]
    exact z.1.property
  · exact (continuous_fst.subtype_val.fst.prodMk paths.continuous).subtype_mk _

/-- The actual path-shortening deformation commutes strictly with all bonds. -/
def mappingPathHomotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPath f ⟶ pathPrespectrum (mappingPath f) where
  level n := (mappingPathContraction f n).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl
  bond n z t := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
