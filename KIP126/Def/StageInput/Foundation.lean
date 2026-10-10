import KIP126.Def.StageInput

/-! Compatibility name for the foundation fixed in Def. -/
namespace KIP126.Classical.Adams

noncomputable def standardFoundation : StandardAdamsFoundation :=
  KIP126.Def.StageInput.witness.foundation

end KIP126.Classical.Adams
