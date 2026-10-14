module

public import KIP126.Def.Steenrod.MilnorModule.Dualization.Data
public import KIP126.Def.Algebra.GradedComodule.Structure.Basic.Data

@[expose] public section


/-! Laws of the specified degreewise transpose. The action and antipode
obligations in the imported dualization construction remain unchanged. -/
namespace KIP126.Steenrod.Milnor.Module
open CategoryTheory KIP126.Algebra

set_option backward.isDefEq.respectTransparency false

theorem dualLeftMap_comp {M N P : SourceComodule} (f : M ⟶ N) (g : N ⟶ P) :
    dualLeftMap g ≫ dualLeftMap f = dualLeftMap (f ≫ g) := by
  apply Monad.Algebra.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  rfl

theorem dualLeftMap_zero (M N : SourceComodule) :
    dualLeftMap (0 : M ⟶ N) = 0 := by
  apply Monad.Algebra.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  ext φ
  change Module.Dual KIP126.Core.Algebra.F2 (N.A n) at φ
  change (LinearMap.dualMap (0 : M.A n →ₗ[_] N.A n)) φ = 0
  apply LinearMap.ext
  intro x
  change φ 0 = 0
  exact map_zero φ

end KIP126.Steenrod.Milnor.Module
