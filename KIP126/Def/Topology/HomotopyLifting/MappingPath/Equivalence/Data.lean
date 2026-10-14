module

public import KIP126.Def.Topology.HomotopyLifting.MappingPath.Data
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

namespace KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The constant retained-path inclusion in the actual mapping-path space. -/
def mappingPathSourceInclusion (f : C(X,Y)) : C(X,MappingPathSpace f) :=
  ⟨fun x => ⟨(x,ContinuousMap.const _ (f x)),rfl⟩,
    (continuous_id.prodMk (ContinuousMap.continuous_const'.comp f.continuous)).subtype_mk _⟩

/-- The source projection from the actual mapping-path space. -/
def mappingPathSourceProjection (f : C(X,Y)) : C(MappingPathSpace f,X) :=
  ⟨fun z => z.val.1,continuous_subtype_val.fst⟩

/-- Multiplication of the retained path parameter is an actual deformation
from the constant-path retract to the original mapping-path point. -/
def mappingPathShortening (f : C(X,Y)) :
    ((mappingPathSourceInclusion f).comp (mappingPathSourceProjection f)).Homotopy
      (ContinuousMap.id (MappingPathSpace f)) := by
  let paths : C((I × MappingPathSpace f) × I,Y) :=
    ⟨fun z => z.1.2.val.2 (z.1.1 * z.2),
      (continuous_subtype_val.comp continuous_fst.snd).snd.eval
        ((continuous_fst.fst.subtype_val.mul continuous_snd.subtype_val).subtype_mk _)⟩
  have hp (z : I × MappingPathSpace f) : paths.curry z 0 = f z.2.val.1 := by
    change z.2.val.2 (z.1 * 0) = f z.2.val.1
    rw [mul_zero]
    exact z.2.property
  refine {
    toFun z := ⟨(z.2.val.1,paths.curry z),hp z⟩
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_snd).fst.prodMk paths.curry.continuous).subtype_mk hp
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext s
      change z.val.2 (0 * s) = f z.val.1
      rw [zero_mul]
      exact z.property
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext s
      change z.val.2 (1 * s) = z.val.2 s
      rw [one_mul]

/-- The actual mapping-path total space is homotopy equivalent to its
source, before any localization or homotopy-group computation. -/
def mappingPathSourceHomotopyEquiv (f : C(X,Y)) : ContinuousMap.HomotopyEquiv (MappingPathSpace f) X where
  toFun := mappingPathSourceProjection f
  invFun := mappingPathSourceInclusion f
  left_inv := ⟨mappingPathShortening f⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩

/-- Evaluation along the retained path compares the original source
map with endpoint projection, with its actual moving basepoint. -/
def mappingPathEndpointHomotopy (f : C(X,Y)) :
    (f.comp (mappingPathSourceProjection f)).Homotopy (mappingPathEndpoint f) where
  toFun z := z.2.val.2 z.1
  continuous_toFun := (continuous_subtype_val.comp continuous_snd).snd.eval continuous_fst
  map_zero_left z := z.property
  map_one_left _ := rfl

end KIP126.Topology.HomotopyLifting
