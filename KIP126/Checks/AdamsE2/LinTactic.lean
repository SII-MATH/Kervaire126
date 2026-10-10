import KIP126.LinProgram.Tactic.LinE2
import KIP126.LinProgram.Model.Classes.Proofs
import Lean.Elab.Command

/-!
前三个具名等式直接使用 CSV 定义关系，因此不依赖计算公理或 sorry。
其余自动化证明示例仍依赖暂留 sorry 的 coordinateCheck_sound；
具体坐标检查由 e2_mul 实际执行。
失败回归确保不等坐标、错误类型、未知变量和超范围计算不会被 tactic 接受。
-/
namespace KIP126.LinE2

theorem checked_h0_mul_h1 : h0 * h1 = 0 := h0_mul_h1_eq_zero
theorem checked_h1_mul_h2 : h1 * h2 = 0 := h1_mul_h2_eq_zero
theorem checked_h1_cube : h1 ^ 3 = h0 ^ 2 * h2 := h1_cube_eq_h0_sq_mul_h2
example : (h0 + h1) * h1 = h1 ^ 2 := by e2_mul

-- 两个因子都是总 E₂ 代数中的一般元素（非齐次的和），不是单个生成元。
-- 展开后交叉项由 h₀h₁ = 0 消失，再用 h₁³ = h₀²h₂ 约化。
example : (h0 ^ 2 + h1 ^ 2) * (h0 + h1) = h0 ^ 3 + h0 ^ 2 * h2 := by
  e2_mul

-- 接受任意具体生成元编号，此处编号 4 是 c₀。
example : h0 * generator ⟨4, by decide⟩ = 0 := by e2_mul

-- 后续证明中直接使用 have；允许局部 let 和可展开的命名常量。
example : h1 ^ 3 * h0 = 0 := by
  have hc : h1 ^ 3 = h0 ^ 2 * h2 := by e2_mul
  rw [hc]
  e2_mul

example : True := by
  -- 失败必须保留目标；不同双次数的基 index=0 不能误判为相等。
  fail_if_success have : h0 = h1 := by e2_mul
  fail_if_success have : h1 ^ 2 = 0 := by e2_mul
  fail_if_success have : (1 : Nat) = 1 := by e2_mul
  fail_if_success have : h0 ^ 262 = 0 := by e2_mul
  fail_if_success have : h0 * h1 = 0 := by e2_mul 0
  trivial

example (_x : E2) : True := by
  fail_if_success have : _x * h0 = 0 := by e2_mul
  trivial

example : h0 * h1 = 0 := by
  let a := h0
  change a * h1 = 0
  e2_mul

-- 系数、单位、零次幂和非齐次加法。
example : (2 : E2) * h0 = 0 := by e2_mul
example : (1 : E2) * h0 = h0 := by e2_mul
example : h0 ^ 0 = 1 := by e2_mul
example : h0 + h1 = h1 + h0 := by e2_mul

open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``checked_h0_mul_h1, ``checked_h1_mul_h2, ``checked_h1_cube] do
    for axiomName in ← liftCoreM (collectAxioms declaration) do
      unless allowed.contains axiomName do
        throwError "unexpected axiom in a direct CSV-relation proof: {declaration} → {axiomName}"

end KIP126.LinE2
