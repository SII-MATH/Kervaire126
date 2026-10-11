import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section8

open KIPBase.Section7

/-- The Table 3 entries used in Fact 7.13. -/
def Table3Statement : Prop :=
  ∃ D : Near126E2.Fact7_13Classes,
    Near126E2.SurvivesToPage D.x123_9_add_h0_x123_8 12 ∧
    (∀ r source, ¬ Near126E2.Differential r source D.x123_9_add_h0_x123_8) ∧
    Near126E2.Differential 2 D.x125_8.val D.d2Target

/-- Table 3 is supplied by the Section 7 proof dependency. -/
theorem table3 : Table3Statement :=
  KIPBase.Section7.Near126E2.table3

theorem table3_fact7_13 : Table3Statement := table3

end KIPBase.Section8
