module

public import KIP126.Def.ClassicalAdams.Suspension.Internal.Data

@[expose] public section


namespace KIP126.Classical.Adams.Suspension.Fourfold

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Core.SpectralSequence

universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- Four successive uses of the specified suspension functor. -/
abbrev quadShift (X : C) : C :=
  (((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧

/-- The comparison only reassociates the existing integer shifts. -/
def quadShiftIso (X : C) : quadShift X ≅ X⟦(4 : ℤ)⟧ :=
  (shiftFunctor C (1 : ℤ)).mapIso
      ((shiftFunctor C (1 : ℤ)).mapIso
        (((shiftFunctorAdd C (1 : ℤ) (1 : ℤ)).app X).symm)) ≪≫
    (shiftFunctor C (1 : ℤ)).mapIso
      (((shiftFunctorAdd C (2 : ℤ) (1 : ℤ)).app X).symm) ≪≫
    ((shiftFunctorAdd C (3 : ℤ) (1 : ℤ)).app X).symm

variable [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}
  (S₀ : TowerComparison H X)
  (S₁ : TowerComparison H (X⟦(1 : ℤ)⟧))
  (S₂ : TowerComparison H ((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))
  (S₃ : TowerComparison H (((X⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧))

/-- The actual fourfold quotient-page map is the composition of the two
already constructed double-desuspension maps, at every integer page. -/
def desuspendFourInternalPage (r : ℤ) (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence H.unit (quadShift X)).Page r p ⟶
      (adamsTowerInternalSpectralSequence H.unit X).Page r
        (p.1, p.2 - 1 - 1 - 1 - 1) :=
  S₂.desuspendTwiceInternalPage S₃ r p ≫
    S₀.desuspendTwiceInternalPage S₁ r (p.1, p.2 - 1 - 1)

end
end KIP126.Classical.Adams.Suspension.Fourfold
