module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Operation
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Source.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Instances

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Concatenation on all morphisms into the actual localized loop object. -/
noncomputable def sourceLoopAdd (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f g : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) :
    A ⟶ sourceLocalization.obj (Prespectrum.loop X) :=
  sourcePiLift (fun _ : Fin 2 => Prespectrum.loop X)
    (Fin.cases f (fun _ : Fin 1 => g)) ≫ sourceLocalization.map (loopConcat X)

/-- Reversal on all morphisms into the actual localized loop object. -/
noncomputable def sourceLoopNeg (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) :
    A ⟶ sourceLocalization.obj (Prespectrum.loop X) :=
  f ≫ sourceLocalization.map (loopInverse X)

end KIP126.StableHomotopy.Implementation.Prespectrum
