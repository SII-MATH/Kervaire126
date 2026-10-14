module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Cofiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Pretriangulated
set_option backward.isDefEq.respectTransparency false

/-- The actual chosen fiber triangle of a map in the original stable category. -/
noncomputable def sourceChosenFiberTriangle {X Y : SourceCategory.{0}} (f : X ⟶ Y) :
    Triangle SourceCategory :=
  (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)).invRotate

/-- The actual inverse shift of the chosen cofiber, without functoriality asserted. -/
noncomputable def sourceChosenFiber {X Y : SourceCategory.{0}} (f : X ⟶ Y) : SourceCategory :=
  (sourceChosenFiberTriangle f).obj₁

/-- The signed boundary, with the fixed shift coherence, is the actual fiber inclusion. -/
noncomputable def sourceChosenFiberInclusion {X Y : SourceCategory.{0}} (f : X ⟶ Y) :
    sourceChosenFiber f ⟶ X :=
  (sourceChosenFiberTriangle f).mor₁

end KIP126.StableHomotopy.Implementation
