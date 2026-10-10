import KIP126.Def.StageInput.StandardSphere.Sequence.Data
import KIP126.Def.ClassicalAdams.Tmf.Model.Predicates
import KIP126.Def.ClassicalAdams.Tmf.Model.Binding.Data

namespace KIP126.Challenge2
open Classical.Adams

/-- am14 的单位与乘法比较义务，约束已选的同一个 target/coordinates。
乘法使用实际 Adams 层配对及 target.mul；不再容许独立选择一个页面乘法。
所有张量、HF₂ ring 和相容结构来自 Def 的同一个固定实现。 -/
def StandardTmfModelMultiplicativeInterface
    (T : TmfModel standardFoundation.hf2) : Prop :=
  let c := KIP126.Def.StageInput.witness
  letI : Foundation.TensorInput c.foundationInput := c.tensorInput
  T.coordinates.RespectsUnit ∧
    Tmf.E2Presentation.RespectsMultiplication c.cooperationInput.ring T.coordinates


end KIP126.Challenge2
