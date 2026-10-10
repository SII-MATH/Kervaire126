import KIP126.LinProgram.Interpretation.Expression.Proofs

namespace KIP126.LinE2

/-- Interpret a typed expression in the existing homogeneous quotient piece. -/
noncomputable def Expression.value {s t : ℕ} (e : Expression s t) : E2At s t :=
  ⟨e.data, e.homogeneous⟩

/-- Reuse the kernel-checked generator degree instead of unfolding the archive
while elaborating an expression. This is the same generator 69. -/
def h6Expression : Expression 1 64 :=
  cast (congrArg (fun b : ℕ × ℕ => Expression b.1 b.2) h6Generator_degree)
    (.gen h6Generator)

def h6SqExpression : Expression 2 128 := .mul h6Expression h6Expression

end KIP126.LinE2
