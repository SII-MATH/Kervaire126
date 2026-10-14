import KIPBase.Section7.Table1
import KIPBase.Section8.Table2
import KIPBase.Section8.Table3
import KIPBase.Section8.Table4
import KIPBase.Section8.Table5
import KIPBase.Section8.Table6
import KIPBase.Section8.Table7
import KIPBase.Section8.Table8
import KIPBase.Section8.Table9
import KIPBase.Section8.Table10
import KIPBase.Section8.Table11
import KIPBase.Section8.Table12

namespace KIPBase.Section8

/-- The joint assertion supplied by Tables 2 through 12. -/
def LaterTables : Prop :=
  Table2Statement ∧ Table3Statement ∧ table4 ∧ Table5Statement ∧
    Table6Statement ∧ Table7Statement ∧ table8 ∧ Table9Statement ∧
    table10 ∧ table11 ∧ table12

/-- Each individual table assertion is available from the combined interface. -/
theorem table2_of_laterTables (h : LaterTables) : Table2Statement := h.1

theorem table3_of_laterTables (h : LaterTables) : Table3Statement := h.2.1

theorem table4_of_laterTables (h : LaterTables) : table4 := h.2.2.1

theorem table5_of_laterTables (h : LaterTables) : Table5Statement := h.2.2.2.1

theorem table6_of_laterTables (h : LaterTables) : Table6Statement := h.2.2.2.2.1

theorem table7_of_laterTables (h : LaterTables) : Table7Statement := h.2.2.2.2.2.1

theorem table8_of_laterTables (h : LaterTables) : table8 := h.2.2.2.2.2.2.1

theorem table9_of_laterTables (h : LaterTables) : Table9Statement := h.2.2.2.2.2.2.2.1

theorem table10_of_laterTables (h : LaterTables) : table10 := h.2.2.2.2.2.2.2.2.1

theorem table11_of_laterTables (h : LaterTables) : table11 := h.2.2.2.2.2.2.2.2.2.1

theorem table12_of_laterTables (h : LaterTables) : table12 := h.2.2.2.2.2.2.2.2.2.2

end KIPBase.Section8
