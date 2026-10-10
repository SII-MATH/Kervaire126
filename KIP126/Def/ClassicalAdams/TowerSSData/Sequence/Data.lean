import KIP126.Def.ClassicalAdams.TowerSSData.Assembly.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.Core.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

-- Assembly uses only the public SSData interface, not its submodule implementation.
attribute [local irreducible] adamsTowerSSData

/-- The internal Adams spectral sequence constructed from the tower itself.
All pages, infinite cycles and boundaries, and differentials are specified
by the tower; the successor axioms are proved, not additional inputs. -/
def adamsTowerInternalSpectralSequence :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  toPreSS := adamsTowerPreSS unit X
  d_comp_d := adamsTowerPreSS_d_comp_d unit X
  Z_succ := adamsTowerPreSS_Z_succ unit X
  B_succ := adamsTowerPreSS_B_succ unit X

end
end KIP126.Classical.Adams
