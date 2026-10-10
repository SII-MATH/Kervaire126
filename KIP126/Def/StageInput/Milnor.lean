import KIP126.Def.StageInput.Foundation

/-! Compatibility name for the Milnor coordinates in the same fixed Def implementation. -/
namespace KIP126.Classical.Adams

noncomputable def standardMilnorCooperations :
    MilnorCooperations standardFoundation.hf2 :=
  KIP126.Def.StageInput.witness.milnor

end KIP126.Classical.Adams
