import KIP126.Def.SpectralSequence.Computation.State.Predicates
import KIP126.Def.StageInput.StandardSphere.Sequence.Data
import KIP126.Def.StageInput.StandardSphere.Classes.Data
import KIP126.LinProgram.Model.Classes.Data
import KIP126.LinProgram.Certificates.BasisTable.Predicates
import KIP126.Def.ClassicalAdams.SphereMultiplication.Data
import KIP126.Def.ClassicalAdams.Suspension.Predicates
import KIP126.LinProgram.Generated.Differentials.Table
import KIP126.LinProgram.Generated.Staircase.Table
import KIP126.LinProgram.Interpretation.State.Data
import KIP126.LinProgram.Interpretation.Branch.Predicates
import KIP126.Interface.Challenge.Computation.Presentation
import KIP126.Def.StageInput.StandardSphere.Tmf.Predicates
import KIP126.LinProgram.Interpretation.Route.Certification
import KIP126.Interface.Challenge.Literature.Delivery

namespace KIP126

namespace Challenge2

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams LinE2
open Core.SpectralSequence

universe u v w

/-- cm1：同一实际球面 E₂ 的完整 CSV 坐标，范围为 t ≤ 261。
坐标逆像的每个单位向量，经同一 presentation 拉回后必须是指定 CSV 单项式。
等价同时保证线性无关与生成性，不将固定 CSV 认证放回基础定义，
也不为内部页面另选一个 F₂ 作用。 -/
structure SphereBasisInterface (P : LinE2Presentation) where
  coordinates : ∀ (s t : ℕ), t ≤ 261 →
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ]
      (BasisIndex s t →₀ Core.Algebra.F2)
  csv_values : ∀ (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t),
    ((P.comparison s t ht).symm
      ((coordinates s t ht).symm (Finsupp.single i 1))).val =
        basisValue (basisRowAt s t i)

/-- cm1/am4：同一 Lin presentation 的有界实际球面乘法与单位。
输出 second cycle 的底层严格等于已构造的 first-layer product；存在量词
只表达该实际乘积闭合于 cycles，不选择另一个运算。对所有输入代表元的
商类等式同时要求其值与 presentation.product 相符。范围是 t+t′≤261，
不由此宣称高页 Leibniz、全局乘法或与 cobar cup 的比较已经完成。 -/
def SphereMultiplicativeInterface (P : LinE2Presentation) : Prop :=
  let c := KIP126.Def.StageInput.witness
  letI : Foundation.TensorInput c.foundationInput := c.tensorInput
  (∃ x : LinE2.E2At 0 0, x.val = 1 ∧
    P.comparison 0 0 (by decide) x =
      Suspension.classOfSecondCycle c.foundationInput.hf2
        StableHomotopy.SphereSpectrum 0 0
        (Sphere.Multiplication.unitSecondCycle c.foundationInput.hf2)) ∧
  ∀ (s t s' t' : ℕ), t + t' ≤ 261 →
    ∀ (a : adamsCycles c.foundationInput.hf2.unit StableHomotopy.SphereSpectrum
          2 (by decide) s t)
      (b : adamsCycles c.foundationInput.hf2.unit StableHomotopy.SphereSpectrum
          2 (by decide) s' t'),
      ∃ z : adamsCycles c.foundationInput.hf2.unit StableHomotopy.SphereSpectrum
          2 (by decide) ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ),
        z.val = Sphere.Multiplication.firstProduct c.foundationInput.hf2
          c.cooperationInput.ring s t s' t' a.val b.val ∧
        P.product s t s' t'
          (Suspension.classOfSecondCycle c.foundationInput.hf2
            StableHomotopy.SphereSpectrum s t a)
          (Suspension.classOfSecondCycle c.foundationInput.hf2
            StableHomotopy.SphereSpectrum s' t' b) =
          Suspension.classOfSecondCycle c.foundationInput.hf2
            StableHomotopy.SphereSpectrum
            ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) z

/-- Literal CSV coordinates, independent of any choice of comparison map. -/
def HasCoordinates {s t : Nat} (x : E2At s t) (indices : List Nat) : Prop :=
  ∃ rows : List BasisRow,
    rows.map BasisRow.index = indices ∧
    (∀ row ∈ rows, row ∈ basisRows ∧ row.s = s ∧ row.t = t) ∧
    x.val = (rows.map basisValue).sum

/-- Mathematical meaning of one exported differential row for one fixed Lin
presentation.  The same `presentation` is used for both source and target. -/
def DifferentialStatement (presentation : Classical.Adams.LinE2Presentation)
    (row : Computation.LinProofs.DifferentialRow) : Prop :=
  ∃ (hx : row.t ≤ 261) (hy : row.t + row.r - 1 ≤ 261),
    ∃ (x : E2At row.s row.t) (y : E2At (row.s + row.r) (row.t + row.r - 1)),
      HasCoordinates x row.x ∧ HasCoordinates y row.dx ∧
      ∃ (h : ((row.s : ℤ), (row.t : ℤ)) + Classical.Adams.sphereAdamsData.diffDeg row.r =
          (((row.s + row.r : Nat) : ℤ), ((row.t + row.r - 1 : Nat) : ℤ)))
        (xr : Classical.Adams.sphereAdamsData.Page row.r ((row.s : ℤ), (row.t : ℤ)))
        (yr : Classical.Adams.sphereAdamsData.Page row.r
          (((row.s + row.r : Nat) : ℤ), ((row.t + row.r - 1 : Nat) : ℤ))),
        RepresentsOnPage Classical.Adams.sphereAdamsData row.r _
          (presentation.comparison row.s row.t hx x) xr ∧
        RepresentsOnPage Classical.Adams.sphereAdamsData row.r _
          (presentation.comparison (row.s + row.r) (row.t + row.r - 1) hy y) yr ∧
        (Classical.Adams.sphereAdamsData.d row.r _ ≫
          eqToHom (congrArg (Classical.Adams.sphereAdamsData.Page row.r) h)) xr = yr

/-- cm5：固定 staircase 解码所得结论。全部坐标经同一实际球面 E₂
比较解释；unknown incoming 仅给累计边界，unknown outgoing 仅给提升。
9000 层仅记录到 E₁₀₀₀ 的提升，不能仅凭程序阈值追加非零 E∞ 存活。 -/
def StaircaseClaimStatement (presentation : Classical.Adams.LinE2Presentation) :
    Computation.LinProofs.State.Claim → Prop
  | .equation r s t indices target =>
      ∃ (hx : t ≤ 261) (hy : t + r - 1 ≤ 261)
        (x : E2At s t) (y : E2At (s + r) (t + r - 1)),
        HasCoordinates x indices ∧ HasCoordinates y target ∧
          HasDifferential sphereAdamsData r
            ((s : ℤ), (t : ℤ)) (((s + r : ℕ) : ℤ), ((t + r - 1 : ℕ) : ℤ))
            (presentation.comparison s t hx x)
            (presentation.comparison (s + r) (t + r - 1) hy y)
  | .reaches r s t indices =>
      ∃ (ht : t ≤ 261) (x : E2At s t), HasCoordinates x indices ∧
        ReachesPage sphereAdamsData r ((s : ℤ), (t : ℤ))
          (presentation.comparison s t ht x)
  | .boundaryBy r s t indices =>
      ∃ (ht : t ≤ 261) (x : E2At s t), HasCoordinates x indices ∧
        IsBoundaryBy sphereAdamsData r ((s : ℤ), (t : ℤ))
          (presentation.comparison s t ht x)

/-- cm5 固定球面 snapshot 的逐行交付，同时要求解码成功和数学真实性。
记录缺失不会推出命题；解码失败也不能使这一义务空泛成立。
不是任意同名表，更不是从数据库哈希推出内部谱序列事实。 -/
structure SphereStaircaseInterface (presentation : Classical.Adams.LinE2Presentation) : Prop where
  rows_sound : ∀ (shard offset : Nat) (row : Computation.LinProofs.Raw.StaircaseRow),
    Computation.LinProofs.StaircaseData.lookup shard offset = some row →
      ∃ claim, Computation.LinProofs.State.decode row = some claim ∧
        StaircaseClaimStatement presentation claim

/-- The certified square facts and its standard label on the actual sphere
page, through the specified comparison. Interface proves the identification
using the fixed-data exhaustion certificate and independent cobar nonvanishing;
Main does not reconstruct this certification from its own stage assumption.
This particular equality does not assert a general cobar/product comparison. -/
structure SphereSquareInterface (presentation : Classical.Adams.LinE2Presentation) : Prop where
  nonzero : presentation.comparison 2 128 (by decide) LinE2.dataH6Sq ≠ 0
  exhaustive : ∀ x : Classical.Adams.sphereAdamsData.Page 2 (2, 128),
    x = 0 ∨ x = presentation.comparison 2 128 (by decide) LinE2.dataH6Sq
  standard_class : presentation.comparison 2 128 (by decide) LinE2.dataH6Sq =
    Classical.Adams.standardH6Square

end Challenge2
end KIP126

/-! Computation delivery on the fixed Def model and the same literature sources.
Program comparisons are explicit mathematical certificates, not metadata. -/
namespace KIP126.Challenge2
open Classical.Adams Core.SpectralSequence

/-- One interpretation of all fixed program data, including tmf coordinate
and source-class comparisons. No extra tmf object or route is chosen. -/
structure ComputationBindings (literature : LiteratureInterface) where
  presentation : LinE2Presentation
  routeRealization : Computation.Route.Realization standardRouteModel
  tmfCoordinates : Tmf.E2Presentation standardFoundation.hf2 Def.standardTmfTarget
  tmfMultiplicative : StandardTmfModelMultiplicativeInterface
    { target := Def.standardTmfTarget, coordinates := tmfCoordinates }
  tmf_v2Sixteen : tmfCoordinates.v2Sixteen =
    adamsInternalE2Induced standardFoundation.hf2.unit
      literature.bindings.route.tmfBinding.detectorIso.inv (16, 112)
      literature.bindings.br21Classes.v2Sixteen
  tmf_betaGFour : tmfCoordinates.betaGFour =
    adamsInternalE2Induced standardFoundation.hf2.unit
      literature.bindings.route.tmfBinding.detectorIso.inv (19, 114)
      literature.bindings.br21Classes.betaGFour

/-- The nonstandard x-labels are these exact program images. Their full
coordinate, product and differential correctness remains a certificate. -/
noncomputable def ComputationBindings.routeLabels {literature : LiteratureInterface}
    (bindings : ComputationBindings literature) :
    Kervaire.Route.Labels standardFoundation.hf2 where
  x_126_8_4 := bindings.routeRealization.sphere 8 134 (Computation.Near126.atom .x_126_8_4)
  x_126_8 := bindings.routeRealization.sphere 8 134 (Computation.Near126.atom .x_126_8)
  x_124_8 := bindings.routeRealization.sphere 8 132 (Computation.Near126.atom .x_124_8)
  x_109_12 := bindings.routeRealization.sphere 12 121 (Computation.Near126.atom .x_109_12)

/-- Model-bound program conclusions on the one supplied interpretation. -/
structure ComputationResults (literature : LiteratureInterface)
    (bindings : ComputationBindings literature) where
  sphereBasis : SphereBasisInterface bindings.presentation
  sphereMultiplicative : SphereMultiplicativeInterface bindings.presentation
  sphereStaircase : SphereStaircaseInterface bindings.presentation
  sphereSquare : SphereSquareInterface bindings.presentation
  sphereTable_sound : ∀ (shard offset : Nat) (row : Computation.LinProofs.DifferentialRow),
    Computation.LinProofs.RawData.lookup shard offset = some row →
      DifferentialStatement bindings.presentation row
  route : Computation.Route.CertifiedRealization bindings.routeRealization
    bindings.routeLabels literature.bindings.tmfLabels
  route_presentation : ∀ (s t : ℕ) (ht : t ≤ 261) (x : LinE2.E2At s t),
    bindings.routeRealization.sphere s t x = bindings.presentation.comparison s t ht x

/-- Computation bindings and certificates depend on the same literature delivery. -/
structure ComputationInterface (literature : LiteratureInterface) where
  bindings : ComputationBindings literature
  results : ComputationResults literature bindings

/-- The existing consumer view uses the certified interpretation without a new choice. -/
noncomputable def ComputationInterface.route {literature : LiteratureInterface}
    (computation : ComputationInterface literature) : Computation.Route.Inputs
    standardRouteModel computation.bindings.routeLabels literature.bindings.tmfLabels :=
  computation.results.route.toInputs

end KIP126.Challenge2
