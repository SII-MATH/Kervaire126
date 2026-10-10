import KIP126.LinProgram.Tactic.Support.Data
import KIP126.LinProgram.Model.BasisTable.Data

/-! Degree-indexed expressions ported from KIPBase at 639057b.
Strict decoding returns errors; it makes no claim about reduction soundness.
The quotient and basis catalogue are the existing KIP126 objects. -/
set_option maxRecDepth 16384

namespace KIP126.LinE2

-- Keep symbolic degree indices opaque during dependent pattern elaboration.
attribute [local irreducible] generatorDegree

/-- 带双次数的表达式；类型保证加法同次、乘法次数相加。 -/
inductive Expression : ℕ → ℕ → Type where
  | zero (s t : ℕ) : Expression s t
  | one : Expression 0 0
  | gen (i : Generator) : Expression (generatorDegree i).1 (generatorDegree i).2
  | add {s t : ℕ} : Expression s t → Expression s t → Expression s t
  | mul {s t s' t' : ℕ} :
      Expression s t → Expression s' t' → Expression (s + s') (t + t')

def Expression.code {s t : ℕ} : Expression s t → Automation.Code
  | .zero _ _ => .scalar 0
  | .one => .scalar 1
  | .gen i => .gen i.val
  | .add a b => .add a.code b.code
  | .mul a b => .mul a.code b.code

/-- 继续使用原商环及原来的 e2_mul 表达式解释。 -/
noncomputable def Expression.data {s t : ℕ} (e : Expression s t) : E2 :=
  match e with
  | .zero _ _ => 0
  | .one => 1
  | .gen i => generator i
  | .add a b => a.data + b.data
  | .mul a b => a.data * b.data

private def wordExpression : List Generator → Σ s t, Expression s t
  | [] => ⟨0, 0, .one⟩
  | [i] => ⟨_, _, .gen i⟩
  | i :: j :: rest =>
      let ⟨s, t, e⟩ := wordExpression (j :: rest)
      ⟨(generatorDegree i).1 + s, (generatorDegree i).2 + t, .mul (.gen i) e⟩

/-- 严格解码 CSV 单项式；非法编号、语法或次数返回 error，不解释成零。 -/
def decodeExpression (s t : ℕ) (code : String) : Compute.Calc (Expression s t) := do
  let m ← Compute.parseMonomial code
  let words ← m.mapM fun (i, a) =>
    if h : i < RawData.generatorCount then
      .ok (List.replicate a (⟨i, h⟩ : Generator))
    else .error "invalid generator"
  let ⟨s', t', e⟩ := wordExpression words.flatten
  if h : s' = s ∧ t' = t then
    return h.1 ▸ h.2 ▸ e
  else throw "monomial has the wrong bidegree"

/-- Typed coordinates in the existing CSV catalogue. -/
abbrev ExpressionCoordinates (s t : ℕ) := List (BasisIndex s t)

/-- Decode a specific basis row without assuming that every row is valid. -/
def decodeBasisExpression (s t : ℕ) (i : BasisIndex s t) :
    Compute.Calc (Expression s t) :=
  decodeExpression s t (basisRowAt s t i).monomial

/-- Run the existing reducer and validate all returned local basis addresses.
Failure, degree mismatch and out-of-range input remain errors. This function
is executable; no theorem about the correctness of the reducer is assumed. -/
def Expression.coordinates {s t : ℕ} (e : Expression s t) (fuel : ℕ := 1000000) :
    Compute.Calc (ExpressionCoordinates s t) := do
  if t > 261 then throw "outside data range"
  let engine ← Compute.loadEngine
  let cs ← Automation.coordinates engine e.code fuel
  let mut result := []
  for (s', t', j) in cs do
    if s' != s || t' != t then throw "coordinate has the wrong bidegree"
    let some i := findBasisIndex? s t j | throw "unknown basis index"
    result := i :: result
  return result.reverse

end KIP126.LinE2
