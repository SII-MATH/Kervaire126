import KIPBase.Section7.BjmBxCriterion

namespace KIPBase.Section8

open KIPBase.Section7

/-- The two Table 2 entries used in Section 7: the survival information for
`h₁x_{121,7}`, `h₆Md₀`, and `h₅x_{91,11}`. -/
def Table2Statement : Prop :=
  (∃ D : Near126E2.Fact7_19Classes,
    Near126E2.SurvivesToPage D.h1X121_7 6 ∧
      ∀ r source, ¬ Near126E2.Differential r source D.h1X121_7) ∧
  (∃ D : Near126E2.Fact7_21Classes,
    Near126E2.IsPermanentCycle D.h6Md0.val ∧
      Near126E2.IsPermanentCycle D.h5X91_11.val)

/-- Table 2 is supplied by the Section 7 proof dependency. -/
theorem table2 : Table2Statement :=
  KIPBase.Section7.Near126E2.table2

theorem table2_fact7_19 :
    ∃ D : Near126E2.Fact7_19Classes,
      Near126E2.SurvivesToPage D.h1X121_7 6 ∧
        ∀ r source, ¬ Near126E2.Differential r source D.h1X121_7 :=
  table2.1

theorem table2_fact7_21 :
    ∃ D : Near126E2.Fact7_21Classes,
      Near126E2.IsPermanentCycle D.h6Md0.val ∧
        Near126E2.IsPermanentCycle D.h5X91_11.val :=
  table2.2

end KIPBase.Section8
