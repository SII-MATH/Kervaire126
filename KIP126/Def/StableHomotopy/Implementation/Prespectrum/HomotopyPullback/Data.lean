module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology

universe u

/-- The actual homotopy pullback, formed as a strict pullback of the
mapping-path projection. Its points retain a path from f(x) to g(z). -/
abbrev homotopyPullback {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    Prespectrum.{u} :=
  pullbackPrespectrum (mappingPathProjection f) g

def homotopyPullbackFst {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullback f g ⟶ X :=
  pullbackFst (mappingPathProjection f) g ≫ mappingPathRetraction f

def homotopyPullbackSnd {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullback f g ⟶ Z :=
  pullbackSnd (mappingPathProjection f) g

/-- The retained path gives a strict prespectrum homotopy between the
two composites of the original cospan. -/
def homotopyPullbackPath {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    homotopyPullback f g ⟶ pathPrespectrum Y where
  level _ := ⟨fun p => p.val.1.val.2, continuous_subtype_val.fst.subtype_val.snd⟩
  point _ := rfl
  bond _ _ _ := rfl

/-- A specified strict prespectrum homotopy gives an actual lift into
the path homotopy pullback, with its two maps and the entire path retained. -/
def homotopyPullbackLift {A X Y Z : Prespectrum.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    (a : A ⟶ X) (b : A ⟶ Z) (H : A ⟶ pathPrespectrum Y)
    (h₀ : H ≫ pathEvaluation Y 0 = a ≫ f)
    (h₁ : H ≫ pathEvaluation Y 1 = b ≫ g) :
    A ⟶ homotopyPullback f g where
  level n :=
    { toFun := fun x => ⟨(⟨(a.level n x, H.level n x),
        congrArg (fun k : A ⟶ Y => k.level n x) h₀⟩, b.level n x),
        congrArg (fun k : A ⟶ Y => k.level n x) h₁⟩
      continuous_toFun := ((((a.level n).continuous.prodMk
        (H.level n).continuous).subtype_mk _).prodMk (b.level n).continuous).subtype_mk _ }
  point n := Subtype.ext (Prod.ext
    (Subtype.ext (Prod.ext (a.point n) (H.point n))) (b.point n))
  bond n x t := Subtype.ext (Prod.ext
    (Subtype.ext (Prod.ext (a.bond n x t) (H.bond n x t))) (b.bond n x t))

end KIP126.StableHomotopy.Implementation.Prespectrum
