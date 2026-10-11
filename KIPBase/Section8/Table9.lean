import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section8

open KIPBase.Section7

/-- The Table 9 exclusion used in Remark 7.7. -/
def Table9Statement : Prop :=
  ¬ ∃ r, Near126E2.Differential r Near126E2.x126_6.val
    Near126E2.h1h4x109_12

theorem table9 : Table9Statement :=
  KIPBase.Section7.Near126E2.table9

theorem table9_remark7_7 : Table9Statement := table9

end KIPBase.Section8
