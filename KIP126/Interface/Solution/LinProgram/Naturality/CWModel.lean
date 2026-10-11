module

public import KIP126.Interface.Solution.LinProgram.Naturality.Row245131
public import KIP126.Def.StableHomotopy.Context.CofiberExtension.Proofs

@[expose] public section


/-!
# Interface/Solution/LinProgram/Naturality/CWModel

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! A choice on the same fixed model, conditional on the explicit zero composite.
The construction does not identify this choice with an archived CW module. -/
namespace KIP126.Interface.Solution.LinProgram.NaturalityCW

open CategoryTheory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Classical.Adams
open CofiberExtension Naturality
noncomputable section
set_option backward.isDefEq.respectTransparency false

local notation "η" => standardRouteModel.auxiliary.etaMap
local notation "ν" => standardRouteModel.auxiliary.nuMap
abbrev Sp := standardFoundation.Spectrum

/-- All statements concern one extension and one octahedron. -/
def ExtensionPackage (g : Ceta⟦(3 : ℤ)⟧ ⟶ SphereSpectrum) : Prop :=
    ∃ m : ((Sphere (C := Sp) 1)⟦(3 : ℤ)⟧)⟦(1 : ℤ)⟧ ⟶
      HasFunctorialCofiber.cofib ν,
    ∃ j : HasFunctorialCofiber.cofib ν ⟶ HasFunctorialCofiber.cofib g,
      (HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧' ≫ g = ν ∧
      Triangle.mk (HasFunctorialCofiber.cofibι g)
        (HasFunctorialCofiber.cofibδ g ≫ (shiftFourIso Ceta).hom)
        ((shiftFourIso Ceta).inv ≫ (-g⟦(1 : ℤ)⟧')) ∈ distTriang Sp ∧
      Triangle.mk j
        ((HasFunctorialCofiber.cofibδ g ≫
          ((shiftedCofiberTriangle (C := Sp) η 3).mor₃)⟦(1 : ℤ)⟧') ≫
          (sphereSixIso (C := Sp)).hom)
        ((sphereSixIso (C := Sp)).inv ≫ (-m⟦(1 : ℤ)⟧')) ∈ distTriang Sp ∧
      (shiftedCofiberTriangle (C := Sp) η 3).mor₃ ≫ m =
        g ≫ HasFunctorialCofiber.cofibι ν ∧
      m ≫ HasFunctorialCofiber.cofibδ ν = -(η⟦(3 : ℤ)⟧')⟦(1 : ℤ)⟧' ∧
      HasFunctorialCofiber.cofibι ν ≫ j = HasFunctorialCofiber.cofibι g ∧
      j ≫ HasFunctorialCofiber.cofibδ g =
        HasFunctorialCofiber.cofibδ ν ≫
          ((HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧')⟦(1 : ℤ)⟧'

theorem exists_extensionPackage
    (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :
    ∃ g : Ceta⟦(3 : ℤ)⟧ ⟶ SphereSpectrum, ExtensionPackage g := by
  letI : Foundation.TensorInput standardFoundation := Def.StageInput.witness.tensorInput
  letI : IsTriangulated Sp := Foundation.TensorInput.triangulated (F := standardFoundation)
  exact exists_eta_nu_cofiber_triangles (C := Sp) η ν hzero

/-- Choose the extension once; every subsequent map and theorem uses it. -/
def extension (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :
    Ceta⟦(3 : ℤ)⟧ ⟶ SphereSpectrum :=
  Classical.choose (exists_extensionPackage hzero)

theorem extension_spec (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :
    ExtensionPackage (extension hzero) :=
  Classical.choose_spec (exists_extensionPackage hzero)

/-- The selected cofiber of that very extension, in the same foundation. -/
abbrev CW (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) : Sp :=
  HasFunctorialCofiber.cofib (extension hzero)

/-- The exact map to the fourfold shift of the existing Cη. -/
def q (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :
    CW hzero ⟶ Ceta⟦(4 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (extension hzero) ≫ (shiftFourIso Ceta).hom

/-- Both triangles and the four squares for the same selected extension.
Only the octahedron's remaining maps are existentially quantified. -/
theorem fixed_triangles (hzero : (shiftFunctor Sp (3 : ℤ)).map η ≫ ν = 0) :
    ∃ m : ((Sphere (C := Sp) 1)⟦(3 : ℤ)⟧)⟦(1 : ℤ)⟧ ⟶
      HasFunctorialCofiber.cofib ν,
    ∃ j : HasFunctorialCofiber.cofib ν ⟶ CW hzero,
      (HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧' ≫ extension hzero = ν ∧
      Triangle.mk (HasFunctorialCofiber.cofibι (extension hzero))
        (q hzero)
        ((shiftFourIso Ceta).inv ≫ (-(extension hzero)⟦(1 : ℤ)⟧')) ∈ distTriang Sp ∧
      Triangle.mk j
        ((HasFunctorialCofiber.cofibδ (extension hzero) ≫
          ((shiftedCofiberTriangle (C := Sp) η 3).mor₃)⟦(1 : ℤ)⟧') ≫
          (sphereSixIso (C := Sp)).hom)
        ((sphereSixIso (C := Sp)).inv ≫ (-m⟦(1 : ℤ)⟧')) ∈ distTriang Sp ∧
      (shiftedCofiberTriangle (C := Sp) η 3).mor₃ ≫ m =
        extension hzero ≫ HasFunctorialCofiber.cofibι ν ∧
      m ≫ HasFunctorialCofiber.cofibδ ν = -(η⟦(3 : ℤ)⟧')⟦(1 : ℤ)⟧' ∧
      HasFunctorialCofiber.cofibι ν ≫ j =
        HasFunctorialCofiber.cofibι (extension hzero) ∧
      j ≫ HasFunctorialCofiber.cofibδ (extension hzero) =
        HasFunctorialCofiber.cofibδ ν ≫
          ((HasFunctorialCofiber.cofibι η)⟦(3 : ℤ)⟧')⟦(1 : ℤ)⟧' :=
  extension_spec hzero

end
end KIP126.Interface.Solution.LinProgram.NaturalityCW
