import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section8

open KIPBase.Section7

/-- The Table 5 entries used in Fact 7.6. -/
def Table5Statement : Prop :=
  Near126E2.SurvivesToEInfinity Near126E2.h0SqX124_8 ∧
    Near126E2.IsUniqueSurvivorOnPage Near126E2.gPow4DeltaH1g 5

theorem table5 : Table5Statement :=
  KIPBase.Section7.Near126E2.table5

theorem table5_h0SqX124_8_survives :
    Near126E2.SurvivesToEInfinity Near126E2.h0SqX124_8 := table5.1

theorem table5_gPow4DeltaH1g_unique_on_E5 :
    Near126E2.IsUniqueSurvivorOnPage Near126E2.gPow4DeltaH1g 5 := table5.2

end KIPBase.Section8
