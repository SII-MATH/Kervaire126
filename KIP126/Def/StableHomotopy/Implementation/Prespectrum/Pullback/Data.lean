module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

/-- The actual based pointwise pullback of two strict prespectrum maps. -/
abbrev pullbackLevel {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (n : ℕ) : BasedSpace.{u} where
  space := TopCat.of {p : X.level n × Z.level n // f.level n p.1 = g.level n p.2}
  point := ⟨((X.level n).point, (Z.level n).point), (f.point n).trans (g.point n).symm⟩

/-- Pointwise bonds preserve the pullback equation by strict naturality. -/
def pullbackBond {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (n : ℕ) :
    C(pullbackLevel f g n × I, pullbackLevel f g (n+1)) := by
  refine ⟨fun p => ⟨(X.bond n (p.1.val.1,p.2), Z.bond n (p.1.val.2,p.2)), ?_⟩, ?_⟩
  · rw [f.bond, g.bond, p.1.property]
  · exact (((X.bond n).continuous.comp
      (continuous_fst.subtype_val.fst.prodMk continuous_snd)).prodMk
      ((Z.bond n).continuous.comp
        (continuous_fst.subtype_val.snd.prodMk continuous_snd))).subtype_mk _

/-- A strict pullback prespectrum formed on the original point-set levels. -/
abbrev pullbackPrespectrum {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    Prespectrum.{u} where
  level := pullbackLevel f g
  bond := pullbackBond f g
  bond_point n t := Subtype.ext (Prod.ext (X.bond_point n t) (Z.bond_point n t))
  bond_zero n p := Subtype.ext (Prod.ext (X.bond_zero n p.val.1) (Z.bond_zero n p.val.2))
  bond_one n p := Subtype.ext (Prod.ext (X.bond_one n p.val.1) (Z.bond_one n p.val.2))

def pullbackFst {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    pullbackPrespectrum f g ⟶ X where
  level _ := ⟨fun p => p.val.1, continuous_subtype_val.fst⟩
  point _ := rfl
  bond _ _ _ := rfl

def pullbackSnd {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    pullbackPrespectrum f g ⟶ Z where
  level _ := ⟨fun p => p.val.2, continuous_subtype_val.snd⟩
  point _ := rfl
  bond _ _ _ := rfl

/-- The actual pointwise lift of a strict commutative cone. -/
def pullbackLift {A X Y Z : Prespectrum.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    (a : A ⟶ X) (b : A ⟶ Z) (h : a ≫ f = b ≫ g) :
    A ⟶ pullbackPrespectrum f g where
  level n :=
    { toFun := fun x => ⟨(a.level n x,b.level n x),
        congrArg (fun k : A ⟶ Y => k.level n x) h⟩
      continuous_toFun := ((a.level n).continuous.prodMk (b.level n).continuous).subtype_mk _ }
  point n := Subtype.ext (Prod.ext (a.point n) (b.point n))
  bond n x t := Subtype.ext (Prod.ext (a.bond n x t) (b.bond n x t))

/-- The cone with the specified actual projections. -/
def pullbackPrespectrumCone {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro p
    exact p.property)

end KIP126.StableHomotopy.Implementation.Prespectrum
