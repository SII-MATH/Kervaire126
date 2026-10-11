module

public import KIP126.Def.StableHomotopy.Context.Data

@[expose] public section


/-! Chosen shifted cofiber triangles and the shift identifications needed for
three-cell cofibers. Distinguishedness is proved in the companion module. -/
namespace KIP126.StableHomotopy.CofiberExtension

open CategoryTheory CategoryTheory.Pretriangulated
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Identify the iterated suspension of the bottom sphere with the six-sphere. -/
noncomputable def sphereSixIso :
    (((Sphere (C := C) 1)⟦(3 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ Sphere (C := C) 6 :=
  (shiftFunctor C (1 : ℤ)).mapIso
      ((shiftFunctor C (1 : ℤ)).mapIso
        (((shiftFunctorAdd C (1 : ℤ) (3 : ℤ)).app SphereSpectrum).symm)) ≪≫
    (shiftFunctor C (1 : ℤ)).mapIso
      (((shiftFunctorAdd C (4 : ℤ) (1 : ℤ)).app SphereSpectrum).symm) ≪≫
    ((shiftFunctorAdd C (5 : ℤ) (1 : ℤ)).app SphereSpectrum).symm

/-- The canonical identification of the two successive shifts with shift four. -/
noncomputable def shiftFourIso (X : C) :
    (X⟦(3 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X⟦(4 : ℤ)⟧ :=
  ((shiftFunctorAdd C (3 : ℤ) (1 : ℤ)).app X).symm

/-- Shift the chosen cofiber triangle, making its first two arrows positive.
The third arrow retains the actual shift-functor sign and commutation map. -/
noncomputable def shiftedCofiberTriangle [HasFunctorialCofiber (C := C)]
    {X Y : C} (f : X ⟶ Y) (n : ℤ) : Triangle C :=
  Triangle.mk (f⟦n⟧') ((HasFunctorialCofiber.cofibι f)⟦n⟧')
    (((Triangle.shiftFunctor C n).obj
      (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))).mor₃)

end KIP126.StableHomotopy.CofiberExtension
