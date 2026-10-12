module

public import KIP126.Def.Topology.Pushout.Cells.Proofs

@[expose] public section

namespace KIP126.Topology
open CategoryTheory CategoryTheory.Limits _root_.Topology Set
universe u
set_option backward.isDefEq.respectTransparency false

/-- Choose the actual cell representative of a point outside the old space. -/
noncomputable def pushoutCellRepresentative
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (x : P) (hx : x ∉ Set.range b) : A :=
  ((Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x).resolve_right hx).choose


end KIP126.Topology
