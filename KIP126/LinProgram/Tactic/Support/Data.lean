import KIP126.LinProgram.Model.E2.Data
import KIP126.LinProgram.Compute.E2.Data

/-! Executable quotation and checking, ported from PR #110 at ff39e951.
No correctness theorem is assumed in this module. -/
namespace KIP126.LinE2.Automation
open Compute

inductive Code where
  | scalar : Nat → Code
  | gen : Nat → Code
  | add : Code → Code → Code
  | mul : Code → Code → Code
  | pow : Code → Nat → Code
  deriving Repr, Inhabited

noncomputable def interpret : Code → E2
  | .scalar 0 => 0
  | .scalar 1 => 1
  | .scalar (n + 2) => ((n + 2 : Nat) : E2)
  | .gen i => if h : i < RawData.generatorCount then generator ⟨i, h⟩ else 0
  | .add a b => interpret a + interpret b
  | .mul a b => interpret a * interpret b
  | .pow a n => interpret a ^ n

private def bounded (p : PolynomialF2) : Calc PolynomialF2 := do
  for m in p do
    if (degree m).2 > 261 then
      throw s!"outside data range: internal degree t = {(degree m).2} > 261"
  return p

/-- 逐节点检查范围；计算中间的幂也不会静默截断。 -/
def expand : Code → Calc PolynomialF2
  | .scalar n => .ok (if n % 2 == 0 then [] else [[]])
  | .gen i => if i < RawData.generatorCount then .ok [[(i, 1)]]
      else .error s!"unknown generator id: {i}"
  | .add a b => do bounded (Compute.add (← expand a) (← expand b))
  | .mul a b => do bounded (Compute.mul (← expand a) (← expand b))
  | .pow a n => do
      let a ← expand a
      -- 范围内的非平凡幂通常不超过 261；额外限制避免无意义的超大循环。
      if a.isEmpty then return if n == 0 then [[]] else []
      if a == [[]] then return [[]]
      if n > 261 then throw "power exceeds supported strict degree range"
      let mut r : PolynomialF2 := [[]]
      for _ in [:n] do r ← bounded (Compute.mul r a)
      return r

abbrev Coordinates := List (Nat × Nat × Nat)

/-- 全部项都必须匹配 CSV 基；非齐次结果按完整 (s,t,index) 比较。 -/
def coordinates (e : Engine) (a : Code) (fuel : Nat) : Calc Coordinates := do
  let p ← reduce e (← expand a) fuel
  let mut result := []
  for m in p do
    let some row := e.basis[m]? | throw s!"normal monomial absent from CSV basis: {repr m}"
    result := (row.s, row.t, row.index) :: result
  return result.reverse

/-- 初始化一次后比较两边。任何错误都返回 false，绝不将两个错误视为相等。 -/
def coordinateCheck (a b : Code) (fuel : Nat) : Bool :=
  match loadEngine with
  | .error _ => false
  | .ok e =>
    match coordinates e a fuel, coordinates e b fuel with
    | .ok lhs, .ok rhs => lhs == rhs
    | _, _ => false


end KIP126.LinE2.Automation
