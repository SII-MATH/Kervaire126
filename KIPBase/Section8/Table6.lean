import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section8

open KIPBase.Section7

/-- The Table 6 entry used in Fact 7.6. -/
def Table6Statement : Prop :=
  Near126E2.IsPermanentCycle Near126E2.h1h4x109_12

theorem table6 : Table6Statement :=
  KIPBase.Section7.Near126E2.table6

theorem table6_h1h4x109_12_permanent :
    Near126E2.IsPermanentCycle Near126E2.h1h4x109_12 := table6

end KIPBase.Section8
