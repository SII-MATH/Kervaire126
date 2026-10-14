/-
  KIPBase.Synthetic.AdamsESSShiftAxiom
  Adams ESS 权重平移相容性的外部输入与边界像数据结构。
-/
import KIPBase.Synthetic.WeightwiseShift

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

noncomputable section

variable (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- 外部输入：lambda-boundary 权重平移保持完整 ESS calculus。 -/
axiom syntheticAdamsESSShiftSystem_axiom :
    SyntheticAdamsESSShiftSystem (Syn := Syn)

/-- 将外部平移输入注册为后续构造所需的类型类实例。 -/
noncomputable instance syntheticAdamsESSShiftSystem_of_axiom :
    SyntheticAdamsESSShiftSystem (Syn := Syn) :=
  syntheticAdamsESSShiftSystem_axiom Syn

/-- 取出单个映射、次数和边界阶数的 ESS calculus 传输。 -/
noncomputable def syntheticFESS_lambdaBoundary_transport
    {X Y : Syn} (f : X ⟶ Y) (degree : ℤ × ℤ) (n : ℕ) :
    ESSCalculusTransport
      (syntheticFESS f degree)
      (syntheticFESS
        ((lambdaBoundaryShiftFunctor (Syn := Syn) n).map f)
        (degree + (1, -(n : ℤ)))) :=
  (SyntheticAdamsESSShiftSystem.lambdaBoundary (Syn := Syn) n).ess f degree

/--
δ-ESS 短页像与经典边界像的统一 ambient 数据。

这里只定义真实的子对象数据；两者相等仍是后续要证明的命题，不能以空公理
代替。统一 ambient 是后续定义比较态射和证明像相等的必要前提。
-/
structure DeltaESSBoundaryImages where
  ambient : AddCommGrpCat.{0}
  deltaImage : Subobject ambient
  classicalBoundaryImage : Subobject ambient

namespace DeltaESSBoundaryImages

/-- 两个边界像相等的正式命题。 -/
def Equal (D : DeltaESSBoundaryImages) : Prop :=
  D.deltaImage = D.classicalBoundaryImage

end DeltaESSBoundaryImages

end

end KIPBase.Synthetic
