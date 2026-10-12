module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Classical

universe u

/-- The disjoint union before imposing the reduced mapping-cylinder relations. -/
abbrev mappingCylinderRaw {X Y : Prespectrum.{u}} (_f : X ⟶ Y) (n : ℕ) :=
  (X.level n × I) ⊕ Y.level n

/-- Canonical representatives specify exactly the basepoint-cylinder collapse
and the top-end attachment. This function is not asserted to be continuous. -/
noncomputable def mappingCylinderNormalize {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    mappingCylinderRaw f n → mappingCylinderRaw f n
  | .inl (x,t) => if x = (X.level n).point then .inr (Y.level n).point
      else if t = 1 then .inr (f.level n x) else .inl (x,t)
  | .inr y => .inr y

/-- The actual reduced mapping-cylinder level, with its quotient topology. -/
noncomputable def mappingCylinderLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    BasedSpace.{u} where
  space := TopCat.of (Quotient (Setoid.ker (mappingCylinderNormalize f n)))
  point := Quotient.mk (Setoid.ker (mappingCylinderNormalize f n)) (.inr (Y.level n).point)

/-- The actual quotient map from the displayed disjoint union. -/
noncomputable def mappingCylinderMk {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingCylinderRaw f n, mappingCylinderLevel f n) :=
  ⟨Quotient.mk (Setoid.ker (mappingCylinderNormalize f n)), continuous_quot_mk⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
