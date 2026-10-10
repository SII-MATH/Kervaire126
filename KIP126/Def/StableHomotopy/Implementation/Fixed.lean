import KIP126.Def.Solution.Implementation

/-! Def selects one implementation from its own construction obligation.
No Interface or Main axiom occurs in this definition or its import closure. -/
namespace KIP126.Def

noncomputable def fixedImplementation : KIP126.Implementation :=
  Classical.choice KIP126.Def.Solution.implementation_exists

end KIP126.Def
