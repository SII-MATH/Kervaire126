import KIP126.Def.Steenrod.MilnorModule.Dualization.Data
import KIP126.Def.Steenrod.MilnorExt.Data

/-! Actual evaluation and its inverse on the dual of each trivial degree
line. These maps keep the integer degree; the inverse uses scalar multiples
of the canonical coordinate functional. -/

namespace KIP126.Steenrod.Milnor.Module

open CategoryTheory KIP126.Core.Algebra KIP126.Algebra

noncomputable section

/-- Evaluate on the actual generator and return that scalar in the same line. -/
def trivialDualHom (t : ℤ) :
    (dualLeftModule (Ext.trivialAt t)).A ⟶ (trivialAt t).A := by
  classical
  intro n
  by_cases h : n = t
  · subst n
    exact ModuleCat.ofHom
      ((_root_.Module.Dual.eval F2 _ (GradedComodule.degreeLineGenerator F2 t))) ≫
        (GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)).inv
  · exact 0

/-- A scalar in the degree line gives the same scalar multiple of its
canonical coordinate functional. All off-degree components are zero. -/
def trivialDualInv (t : ℤ) :
    (trivialAt t).A ⟶ (dualLeftModule (Ext.trivialAt t)).A := by
  classical
  intro n
  by_cases h : n = t
  · subst n
    let e := GradedObject.singleObjApplyIso t (ModuleCat.of F2 F2)
    exact e.hom ≫ ModuleCat.ofHom
      (LinearMap.toSpanSingleton F2 (_root_.Module.Dual F2 (GradedComodule.degreeLine F2 t t))
        e.hom.hom)
  · exact 0

end
end KIP126.Steenrod.Milnor.Module
