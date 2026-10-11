import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section8

open KIPBase.Section7

/-- The Table 7 entry used in Fact 7.15. -/
def Table7Statement : Prop :=
  ∃ D : Near126E2.Fact7_15Classes,
    Near126E2.SurvivesToPage D.h0SqX125_9_2 5 ∧
      ∀ r source, ¬ Near126E2.Differential r source D.h0SqX125_9_2

theorem table7 : Table7Statement :=
  KIPBase.Section7.Near126E2.table7

theorem table7_fact7_15 : Table7Statement := table7

end KIPBase.Section8
