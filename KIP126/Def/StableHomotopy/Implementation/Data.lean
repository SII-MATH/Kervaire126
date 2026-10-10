import KIP126.Def.Kervaire.Route.Model.Coherent.Data
import KIP126.Def.StableHomotopy.Implementation.Tensor
import KIP126.Def.StableHomotopy.Cohomology.Data
import KIP126.Def.ClassicalAdams.MilnorCooperations.Data
import KIP126.Def.ClassicalAdams.MapFiltration.Predicates
import KIP126.Def.Synthetic.Context.Data
import KIP126.Def.Synthetic.Localization.Recovery.Data
import KIP126.Def.Synthetic.QuotientTower.Predicates
import KIP126.Def.Synthetic.Completion.Predicates
import KIP126.Def.ClassicalAdams.Completion.Predicates
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Data
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Suspension.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Unit.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Coproduct.Predicates
import KIP126.Def.StableHomotopy.Context.Mapping.Data
import KIP126.Def.StableHomotopy.Context.Proofs
import KIP126.Def.StableHomotopy.Toda.Predicates
import KIP126.Def.HigherAlgebra.Operad.Moduli.Data
import KIP126.Def.HigherAlgebra.Operad.Model.Data
import KIP126.Def.HigherAlgebra.Operad.Topological.Predicates
import KIP126.Def.Topology.WeakContractibility.Predicates
import Mathlib.AlgebraicTopology.ModelCategory.Instances
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Exact.Basic

/-! Mathematical data of one fixed implementation. FoundationInput supplies
the selected stable category, HF₂ object and operations; the following
records supply Milnor coordinates, tensor compatibility and the synthetic
route language. Route witnesses are delivered later in one correlated
input package; none is chosen here. SourceComparison identifies this classical implementation with the
concrete HF₂-local source in Implementation/Completion.lean.
The Def construction chooses this package once. Interface and Main use this
same fixed background; there is no second foundation choice. -/
namespace KIP126

open StableHomotopy StableHomotopy.Cohomology Classical.Adams

namespace Foundation

open CategoryTheory MonoidalCategory

/-- 基础对象及其条件。

`stable` 使用 Def 的通用稳定范畴接口：小 Hom、加性、整数平移、幺半结构、
零对象及预三角结构；这些额外条件由同文件 `TensorInput` 明列。
`cofiber` 使用 Def 的通用 cofiber 接口，包括选定三角及交换方块的兼容提升。
HF₂ 的对象、零次同伦群与非零次数消失条件在此逐项列出。 -/
structure FoundationInput where
  Spectrum : Type 1
  stable : StableHomotopyCategory.{1, 0} Spectrum
  cofiber : @HasFunctorialCofiber Spectrum stable
  countableProducts : @CategoryTheory.Limits.HasProductsOfShape ℕ Spectrum stable.toCategory
  countableCoproducts : @CategoryTheory.Limits.HasCoproductsOfShape ℕ Spectrum stable.toCategory
  HF2 : Spectrum
  pi0Equiv : @HomotopyGroup Spectrum stable 0 HF2 ≃+ ZMod 2
  homotopy_vanishes : ∀ n : ℤ, n ≠ 0 →
    Subsingleton (@HomotopyGroup Spectrum stable n HF2)

attribute [instance] FoundationInput.stable FoundationInput.cofiber FoundationInput.countableProducts
  FoundationInput.countableCoproducts

/-- 将同一组已列出的 HF₂ 条件交给 Def 的通用构造使用。 -/
def FoundationInput.hf2 (F : FoundationInput) :
    @Mod2EilenbergMacLane F.Spectrum F.stable where
  HF2 := F.HF2
  pi0Equiv := F.pi0Equiv
  homotopy_vanishes := F.homotopy_vanishes

/-- 原基础类型名的兼容别名；唯一结构及其字段由当前边界的
`FoundationInput` 定义，不在 Def 中另设项目包装。 -/
abbrev _root_.KIP126.Classical.Adams.StandardAdamsFoundation := FoundationInput

/-- 兼容旧基础名称的恒等适配，不重新包装或选择任何数据。 -/
def FoundationInput.toStandard (F : FoundationInput) : StandardAdamsFoundation := F

/-- 兼容旧调用端的恒等适配；两个名称表示同一个边界结构。 -/
def FoundationInput.ofStandard (F : StandardAdamsFoundation) : FoundationInput := F

/-- 同一基础上的 Milnor 坐标与第一微分相容性。

坐标覆盖所有非负双次数，等价的标量环是 ℤ；第一页面及其微分来自
`F.hf2.unit` 的实际 Adams 塔构造。这里不另行假设乘法相容或永久存活。 -/
structure MilnorInput (F : FoundationInput) where
  coordinates : ∀ s t : ℕ,
    adamsPage F.hf2.unit (SphereSpectrum (C := F.Spectrum)) 1 (by decide) s t ≃ₗ[ℤ]
      Steenrod.Milnor.cochains s t
  differential_coordinates : ∀ (s t : ℕ)
      (x : adamsPage F.hf2.unit (SphereSpectrum (C := F.Spectrum)) 1 (by decide) s t),
    coordinates (s + 1) t (sphereFirstDifferential F.hf2 s t x) =
      Steenrod.Milnor.differential s t (coordinates s t x)

/-- The generic Milnor record assembled from these exact stage-zero fields. -/
def MilnorInput.toMilnor {F : FoundationInput} (M : MilnorInput F) :
    MilnorCooperations F.hf2 where
  coordinates := M.coordinates
  differential_coordinates := M.differential_coordinates

/-- Shared Section 7 objects on the SAME classical foundation and Milnor
coordinates. Only objects and structural compatibility belong here; literature
results, table certification and paper deductions are delivered separately.
Def fixes its specified source construction separately. Interface must then
establish source applicability and deliver literature and computation on that
same construction; this abstract type alone does not establish applicability. -/
structure RouteInput (F : FoundationInput) (M : MilnorInput F) where
  Syn : Type 1
  synthetic : KIP126.Synthetic.Context.SyntheticCategory.{1, 0} Syn
  cofiber : @HasFunctorialCofiber Syn synthetic.toStableHomotopyCategory
  model : @KIP126.Kervaire.Route.Model F.Spectrum F.stable F.cofiber
    F.hf2 M.toMilnor Syn synthetic cofiber

attribute [instance] RouteInput.synthetic RouteInput.cofiber

/-- a01/a03：同一基础的 tensor、悬移与三角条件。所有后续 Künneth 和
边界公式使用这里选出的 CommShift，不重新选择 suspension comparison。 -/
class TensorInput (F : FoundationInput) where
  [triangulated : IsTriangulated F.Spectrum]
  [monoidalPreadditive : MonoidalPreadditive F.Spectrum]
  [symmetric : SymmetricCategory F.Spectrum]
  [closed : MonoidalClosed F.Spectrum]
  [leftShift : ∀ X : F.Spectrum, (tensorLeft X).CommShift ℤ]
  [rightShift : ∀ X : F.Spectrum, (tensorRight X).CommShift ℤ]
  [ihomShift : ∀ X : F.Spectrum, (ihom X).CommShift ℤ]
  [leftExact : ∀ X : F.Spectrum, (tensorLeft X).IsTriangulated]
  [rightExact : ∀ X : F.Spectrum, (tensorRight X).IsTriangulated]
  [ihomExact : ∀ X : F.Spectrum, (ihom X).IsTriangulated]
  [unitShift : (mod2UnitNatTrans F.hf2).CommShift ℤ]
  leftShift_eq : ∀ X : F.Spectrum,
    leftShift X = Functor.CommShift.ofIso (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
  ihom_unit_shift : ∀ X : F.Spectrum, NatTrans.CommShift (ihom.adjunction X).unit ℤ
  ihom_counit_shift : ∀ X : F.Spectrum, NatTrans.CommShift (ihom.adjunction X).counit ℤ


attribute [reducible] TensorInput.symmetric TensorInput.closed
  TensorInput.leftShift TensorInput.rightShift TensorInput.ihomShift
attribute [instance] TensorInput.triangulated TensorInput.monoidalPreadditive
  TensorInput.symmetric TensorInput.closed
  TensorInput.leftShift TensorInput.rightShift TensorInput.leftExact TensorInput.rightExact
  TensorInput.ihomShift TensorInput.ihomExact TensorInput.unitShift

/-- a02 与 a03 的同一组页面以下输入。最后一条等式把已经公开的页面坐标
锁定为这些 cooperation 数据导出的坐标；没有额外选择第二套基。 -/
structure CooperationInput (F : FoundationInput) [TensorInput F] (M : MilnorInput F) where
  ring : Mod2RingStructure F.hf2
  kunneth : Mod2CooperationKunneth F.hf2 ring
  basis : Mod2ReducedMilnorBasis F.hf2 ring
  suspension : Mod2KunnethSuspensionCompatible F.hf2 ring kunneth
  diagonal : Mod2KunnethDiagonalCompatible F.hf2 ring kunneth
  unit : Mod2KunnethUnitCompatible F.hf2 ring kunneth
  coproduct : Mod2MilnorCoproductCompatible F.hf2 ring kunneth basis
  coordinates_eq : ∀ (s t : ℕ)
      (x : adamsPage F.hf2.unit (SphereSpectrum (C := F.Spectrum)) 1 (by decide) s t),
    M.coordinates s t x = sphereFirstPageMilnorEquiv F.hf2 ring kunneth basis s t x

/-- a04 的一般平方零义务；可从 a03 的实际 first-page complex 与坐标相容性
推出，不作为总包里另一项独立假设。 -/
def MilnorCobarSquareZero : Prop :=
  ∀ (s t : ℕ) (x : Steenrod.Milnor.cochains s t),
    Steenrod.Milnor.differential (s + 1) t
      (Steenrod.Milnor.differential s t x) = 0

/-- a06 的正向分解准则。k 必须为正；任意 filtration-zero 映射不能
被错误地认作恒等映射的空复合。 -/
def AdamsFiltrationDecomposition (F : FoundationInput) : Prop :=
  ∀ {X Y : F.Spectrum} (f : X ⟶ Y) (k : ℕ), 0 < k →
    AdamsFiltrationAtLeast F.hf2 f k → HasMod2ZeroFactorization F.hf2 f k

open CategoryTheory.Limits

universe u v

/-- a13 的通用已证切片。juggling 明确保留三角公理及悬移后的负号；
不额外选择 bracket 运算，也不提供具体 Toda 积值或 Moss 比较。 -/
structure TodaInterface (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    [IsTriangulated C] : Prop where
  composable : ∀ {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    StableHomotopy.Toda.Relation x f g h → f ≫ g = 0 ∧ g ≫ h = 0
  exists_relation : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
    f ≫ g = 0 → g ≫ h = 0 → ∃ x : X⟦(1 : ℤ)⟧ ⟶ W,
      StableHomotopy.Toda.Relation x f g h
  coset : ∀ {X Y Z W : C} {x₀ x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W},
    StableHomotopy.Toda.Relation x₀ f g h →
      (StableHomotopy.Toda.Relation x f g h ↔
        ∃ (y : Y⟦(1 : ℤ)⟧ ⟶ W) (z : X⟦(1 : ℤ)⟧ ⟶ Z),
          x - x₀ = f⟦(1 : ℤ)⟧' ≫ y + z ≫ h)
  juggling : ∀ {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V},
    StableHomotopy.Toda.Relation x f g h → h ≫ d = 0 →
      ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
        StableHomotopy.Toda.Relation y g h d ∧ x ≫ d = (-f⟦(1 : ℤ)⟧') ≫ y


/-- a13：自然性、suspension 和完整 shuffle 的陈述组。结论都是同一
cone-based Toda relation 的包含或等价；不假定不定性为零。 -/
structure TodaNaturalityInterface (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C] : Prop where
  precompose {A X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
      (hx : StableHomotopy.Toda.Relation x f g h) (a : A ⟶ X) :
      StableHomotopy.Toda.Relation (a⟦(1 : ℤ)⟧' ≫ x) (a ≫ f) g h
  postcompose {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
      (hx : StableHomotopy.Toda.Relation x f g h) (d : W ⟶ V) :
      StableHomotopy.Toda.Relation (x ≫ d) f g (h ≫ d)
  absorb_first {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ V}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
      (hx : StableHomotopy.Toda.Relation x (f ≫ g) h d) :
      StableHomotopy.Toda.Relation x f (g ≫ h) d
  absorb_last {X Y Z W V : C} {x : X⟦(1 : ℤ)⟧ ⟶ V}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} {d : W ⟶ V}
      (hx : StableHomotopy.Toda.Relation x f g (h ≫ d)) :
      StableHomotopy.Toda.Relation x f (g ≫ h) d
  shuffle_iff [IsTriangulated C] {X Y Z W V : C}
      (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (d : W ⟶ V)
      (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhd : h ≫ d = 0)
      (z : X⟦(1 : ℤ)⟧ ⟶ V) :
      (∃ x : X⟦(1 : ℤ)⟧ ⟶ W, StableHomotopy.Toda.Relation x f g h ∧ x ≫ d = z) ↔
        ∃ y : Y⟦(1 : ℤ)⟧ ⟶ V,
          StableHomotopy.Toda.Relation y g h d ∧ (-f⟦(1 : ℤ)⟧') ≫ y = z
  suspension_iff (n : ℤ) {X Y Z W : C}
      {x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W} :
      StableHomotopy.Toda.Relation
        (n.negOnePow • ((shiftFunctorComm C (1 : ℤ) n).inv.app X ≫ x⟦n⟧'))
        (f⟦n⟧') (g⟦n⟧') (h⟦n⟧') ↔ StableHomotopy.Toda.Relation x f g h

universe u' v'

/-- a13：任意指定 exact functor 的 Toda 自然性。其 CommShift 与 exactness
相对同一个 F；没有声称任意函子精确，也不将包含加强为等式。 -/
structure TodaFunctorInterface {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] : Prop where
  map
      {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
      (hx : StableHomotopy.Toda.Relation x f g h) :
      StableHomotopy.Toda.Relation ((F.commShiftIso (1 : ℤ)).inv.app X ≫ F.map x)
        (F.map f) (F.map g) (F.map h)

/-- a13：左右 tensor 的 Toda 乘积包含，使用实际 tensor 的悬移比较。
三相邻复合的 shuffle 已在 TodaNaturalityInterface 独立列出。 -/
structure TodaTensorInterface (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C] [MonoidalCategory C] : Prop where
  tensor_right (V : C) [(tensorRight V).CommShift ℤ]
      [(tensorRight V).IsTriangulated]
      {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
      (hx : StableHomotopy.Toda.Relation x f g h) :
      StableHomotopy.Toda.Relation (((tensorRight V).commShiftIso (1 : ℤ)).inv.app X ≫ (x ▷ V))
        (f ▷ V) (g ▷ V) (h ▷ V)
  tensor_left (V : C) [(tensorLeft V).CommShift ℤ]
      [(tensorLeft V).IsTriangulated]
      {X Y Z W : C} {x : X⟦(1 : ℤ)⟧ ⟶ W}
      {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
      (hx : StableHomotopy.Toda.Relation x f g h) :
      StableHomotopy.Toda.Relation (((tensorLeft V).commShiftIso (1 : ℤ)).inv.app X ≫ (V ◁ x))
        (V ◁ f) (V ◁ g) (V ◁ h)

end Foundation

/-- One candidate implementation of the entire mathematical background.
Its classical source is the explicit HF₂-local prespectrum source.
Choosing the fixed implementation and handing it to the next stage are separate. -/
structure Implementation where
  foundationInput : Foundation.FoundationInput
  milnorInput : Foundation.MilnorInput foundationInput
  tensorInput : Foundation.TensorInput foundationInput
  cooperationInput : @Foundation.CooperationInput foundationInput tensorInput milnorInput
  sourceComparison : StableHomotopy.Implementation.SourceComparison foundationInput.hf2
  sourceTensor : letI := tensorInput
    StableHomotopy.Implementation.TensorComparison sourceComparison

namespace Implementation

open Foundation

/-- 保留消费端使用的基础名称及类型，所有数据来自同一个边界见证。 -/
def foundation (c : KIP126.Implementation) : StandardAdamsFoundation :=
  c.foundationInput.toStandard

/-- 保留消费端使用的 Milnor 名称及类型，适配到同一基础上的通用记录。 -/
def milnor (c : KIP126.Implementation) :
    @MilnorCooperations c.foundation.Spectrum c.foundation.stable
      c.foundation.cofiber c.foundation.hf2 where
  coordinates := c.milnorInput.coordinates
  differential_coordinates := c.milnorInput.differential_coordinates

/-- 已有基础与 Milnor 见证连同 tensor、cooperation 逐字段组装成边界包。 -/
def ofFoundationMilnor (F : StandardAdamsFoundation)
    (M : @MilnorCooperations F.Spectrum F.stable F.cofiber F.hf2)
    (T : TensorInput (FoundationInput.ofStandard F))
    (A : @CooperationInput (FoundationInput.ofStandard F) T
      { coordinates := M.coordinates, differential_coordinates := M.differential_coordinates })
    (S : StableHomotopy.Implementation.SourceComparison F.hf2)
    (ST : letI : TensorInput F := T; StableHomotopy.Implementation.TensorComparison S) :
    KIP126.Implementation where
  foundationInput := FoundationInput.ofStandard F
  milnorInput :=
    { coordinates := M.coordinates
      differential_coordinates := M.differential_coordinates }
  tensorInput := T
  cooperationInput := A
  sourceComparison := S
  sourceTensor := ST

end Implementation

namespace Stable

open CategoryTheory MonoidalCategory
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [∀ W : C, (tensorLeft W).CommShift ℤ]
  [∀ W : C, (tensorRight W).CommShift ℤ]
  [∀ W : C, (tensorLeft W).IsTriangulated]
  [∀ W : C, (tensorRight W).IsTriangulated]

/-- Historical unsigned smash-boundary target on actual triangles.
May's TC3 source relation carries a minus sign; the route now uses the signed
`MaySourceResults` in root Challenge2. This legacy predicate is not accepted
as the source theorem, and sign removal requires an additional hypothesis. -/
def MaySmashBoundary : Prop :=
  ∀ (T U : HoCofiberSequence (C := C)) (n : ℤ)
    (a : HomotopyGroup n (T.X ⊗ U.Z))
    (b : HomotopyGroup n (T.Y ⊗ U.Y)),
    inducedMap (T.f ▷ U.Z) n a = inducedMap (T.Y ◁ U.g) n b →
    ∃ c : HomotopyGroup n (T.Z ⊗ U.X),
      inducedMap (T.g ▷ U.Y) n b = inducedMap (T.Z ◁ U.f) n c ∧
      connectingHomomorphism (U.map (tensorLeft T.X)) n a =
        connectingHomomorphism (T.map (tensorRight U.X)) n c

end Stable

namespace Synthetic

open CategoryTheory CategoryTheory.Pretriangulated MonoidalCategory
open Context

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]

/-- a09 的点集模型绑定：固定实际一阶 λ 商和同一个商映射。
此类型只记录箭头的实现；L 的局部化性质、derived tensor 及代数模型比较
仍是独立义务，不能由这一交换方块推出。项目组合集中于本文件。 -/
structure LambdaQuotientRealization {M : Type u} [Category.{v} M] [MonoidalCategory M]
    [HasFunctorialCofiber (C := Syn)] (L : M ⥤ Syn) where
  object : M
  unit : 𝟙_ M ⟶ object
  unitIso : L.obj (𝟙_ M) ≅ (S_0_0 : Syn)
  quotientIso : L.obj object ≅ XModLambdaN (S_0_0 : Syn) 1
  unit_binding : L.map unit ≫ quotientIso.hom =
    unitIso.hom ≫ XModLambdaN.incl (S_0_0 : Syn) 1

/-- a09 的相关点集输入：所有张量、operad、代数模型与商单位都来自同一组数据。
普通 Ho 局部化只固定底层同伦范畴；仍须接入该模型与 synthetic CAlg 的高阶
比较，不能把此记录的定义或字段当成该比较的证明。单位 cofibrant 显式列出，
避免把任意严格 Under(unit) 都直接当成正确的派生单位箭头模型。 -/
structure LambdaQuotientOperadicInput {M : Type (u + 1)} [Category.{u + 1} M]
    [MonoidalCategory M] [SymmetricCategory M]
    [EnrichedOrdinaryCategory TopCat.{u + 1} M]
    [HomotopicalAlgebra.ModelCategory M] [HasFunctorialCofiber (C := Syn)]
    (L : M ⥤ Syn) where
  localization : L.IsLocalization (HomotopicalAlgebra.weakEquivalences M)
  unit_cofibrant : HomotopicalAlgebra.IsCofibrant (𝟙_ M)
  tensor : HigherAlgebra.EnrichedTensor.Presentation M
  tensor_laws : HigherAlgebra.EnrichedTensor.SymmetricTensorLaws tensor
  operad : HigherAlgebra.Operad.TopologicalOperad.{u + 1}
  eInfinity : operad.IsEInfinity
  reduced : operad.IsReduced
  nullary : operad.Op HigherAlgebra.EnrichedTensor.empty
  algebraModel : HigherAlgebra.Operad.TransferredModelStructure
    tensor tensor_laws.toTensorLaws operad
  quotient : LambdaQuotientRealization L

/-- a09 的具体模空间候选：以同一模型的实际弱等价取 nerve，实现后沿保单位
忘却函子取路径纤维；基点是所选商箭头，且它由 `unit_binding` 固定到原来的
一阶 λ 商映射。不是自由指定的空间，也不是严格 action 集合的 Subsingleton。 -/
noncomputable def LambdaQuotientOperadicInput.moduli
    {M : Type (u + 1)} [Category.{u + 1} M] [MonoidalCategory M] [SymmetricCategory M]
    [EnrichedOrdinaryCategory TopCat.{u + 1} M]
    [HomotopicalAlgebra.ModelCategory M] [HasFunctorialCofiber (C := Syn)]
    {L : M ⥤ Syn} (I : LambdaQuotientOperadicInput L) : TopCat.{u + 1} :=
  HigherAlgebra.Operad.EnrichedAlgebra.unitModuli I.tensor I.tensor_laws.toTensorLaws
    I.operad I.nullary (HomotopicalAlgebra.weakEquivalences M) I.quotient.unit

/-- a09 的模型内唯一性目标，含非空性。来源目标为 Pstrągowski
`cor:ctau_is_an_algebra`；把本文献结果传到这里仍需上述高阶模型比较。
仅定义准确目标，不为任意上述输入无条件断言它成立。 -/
def LambdaQuotientOperadicInput.uniqueness
    {M : Type (u + 1)} [Category.{u + 1} M] [MonoidalCategory M] [SymmetricCategory M]
    [EnrichedOrdinaryCategory TopCat.{u + 1} M]
    [HomotopicalAlgebra.ModelCategory M] [HasFunctorialCofiber (C := Syn)]
    {L : M ⥤ Syn} (I : LambdaQuotientOperadicInput L) : Prop :=
  KIP126.Topology.WeaklyContractibleSpace I.moduli

/-! ## a09：同一 λ 与 ν 上的反演接口

以下字段只交付指定抽象背景中的范畴数据，不为任意 synthetic 背景构造它们。
局部对象由既有 `lam.app` 为同构定义；满子范畴及其包含函子不是新的选择。
来源：Pstrągowski 的 `prop:tau_inversion_functor_exists`、
`thm:tau_invertible_synthetic_spectra_are_just_spectra`，以及
`prop:spectral_yoneda_embedding_the_tau_inversion_of_the_synthetic_analogue`。
-/

/-- a09 的 λ 反演交付：所有字段绑定同一 reflector、实际局部对象及 ν。
单位与其唯一分解性质从此伴随导出，不再作为独立假设。 -/
structure LambdaInversionInterface (N : NuFunctorData C Syn) where
  reflector : Syn ⥤ LambdaInvertibleObjects Syn
  adjunction : reflector ⊣ lambdaInclusion Syn
  equivalence : LambdaInvertibleObjects Syn ≌ C
  nuLocalization : N.functor ⋙ reflector ≅ equivalence.inverse

/-- 将已展示的反射数据组装成通用记录，不作额外选择。 -/
def LambdaInversionInterface.localization {N : NuFunctorData C Syn}
    (I : LambdaInversionInterface N) : LambdaLocalization Syn where
  reflector := I.reflector
  adjunction := I.adjunction

/-- 将同一局部化、等价和 ν 比较组装成恢复数据。 -/
def LambdaInversionInterface.recovery {N : NuFunctorData C Syn}
    (I : LambdaInversionInterface N) : LambdaRecovery N where
  localization := I.localization
  equivalence := I.equivalence
  nuLocalization := I.nuLocalization

/-- a09 的独立对称幺半条件，直接约束实际 realization。
来源：Pstrągowski
`prop:tau_inversion_cocontinuous_symmetric_monoidal_left_inverse_to_synthetic_analogue`。
局部单位不必是 ambient unit，因此不要求包含函子为 strong monoidal。 -/
structure LambdaInversionInterface.SymmetricMonoidal {N : NuFunctorData C Syn}
    (I : LambdaInversionInterface N) [SymmetricCategory C] [SymmetricCategory Syn] where
  realization : (I.reflector ⋙ I.equivalence.functor).Braided

/-- 此适配保留子组中指定的同一个 realization 幺半结构。 -/
def LambdaInversionInterface.symmetricMonoidal {N : NuFunctorData C Syn}
    (I : LambdaInversionInterface N) [SymmetricCategory C] [SymmetricCategory Syn]
    (M : I.SymmetricMonoidal) : I.recovery.SymmetricMonoidal where
  realization := M.realization

/-! ## a10/a11：已可精确陈述的 synthetic 文献接口

以下类型使用当前 Def 的对象，既不 import KIPBase，也不依赖 synthetic
谱序列的迁移。参数 H 与 N 必须来自同一选定背景；本文件不为任意抽象 N
无条件断言文献结论。固定模型上的来源证明由
Challenge2 的 synthetic 来源交付及模型比较接收。

历史 `KIPBase/Synthetic/Nu.lean`、`Lift.lean` 已搭建对应接口形状，但前者的
短正合前提仅写了中间正合，后者部分三角未绑定 ν 的实际映射；下面按主论文
及 Blueprint 补足这些条件。类型可表达与固定模型／证明已交付是独立检查项。
-/

/-- 每个整数次数上的完整短正合条件；仅有中间 `Exact` 不够。 -/
def HomologyShortExact (H : Mod2EilenbergMacLane (C := C)) (T : Triangle C) : Prop :=
  ∀ n : ℤ,
    Function.Injective (Mod2Homology.pushforward H T.mor₁ n) ∧
    Function.Exact (Mod2Homology.pushforward H T.mor₁ n)
      (Mod2Homology.pushforward H T.mor₂ n) ∧
    Function.Surjective (Mod2Homology.pushforward H T.mor₂ n)

/-- 同一个 classical 三角的 ν 前两条箭头能否组成 synthetic distinguished triangle。
第三箭头落在 ΣνX；它与 ν(ΣX) 的关系由 a11 单独控制。 -/
def NuImageIsCofiber (N : NuFunctorData C Syn) (T : Triangle C) : Prop :=
  ∃ δ : N.functor.obj T.obj₃ ⟶ (N.functor.obj T.obj₁)⟦(1 : ℤ)⟧,
    Triangle.mk (N.functor.map T.mor₁) (N.functor.map T.mor₂) δ ∈ distTriang Syn

/-- a10：Pstrągowski Lemma 4.23 的完整双向判据。
来源：MainPaper `prop:1f7950df`；Pst 原文
`lemma:fibre_sequences_that_are_short_exaft_sequences_on_homology_preserved_by_synthetic_analogue_construction`。
不额外限制有限谱、连通性或完备性。 -/
def NuCofiberCriterion (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    (NuImageIsCofiber N T ↔ HomologyShortExact H T)

/-- a11 的 full lift：使用 BHS 图中的负移靶写法 νX → Σ^(0,-k)νY。
所选映射与 νf 的 λᵏ 分解等式是同一个见证的两个字段。 -/
structure SyntheticFullLift (N : NuFunctorData C Syn) {X Y : C}
    (f : X ⟶ Y) (k : ℕ) where
  map : N.functor.obj X ⟶
    (SyntheticCategory.biShift (0, -(k : ℤ))).obj (N.functor.obj Y)
  factorization : map ≫ lambdaPow k (N.functor.obj Y) = N.functor.map f

/-- a11：BHS Lemma 9.15；filtration 下界由实际 Adams 塔因子分解定义。
来源：BHS `SynRevBigraded.tex`, `lemm:adams-fil1`；MainPaper `prop:ef21f9bc`。
该类型不假设任意 full lift 都是提升三角的分量。 -/
def SyntheticLiftComparison (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (k : ℕ),
    AdamsFiltrationAtLeast H f k → Nonempty (SyntheticFullLift N f k)

/-- a11 的三角提升：前两条箭头固定为 νf、νg，第三箭头同时满足
λ 下的分解等式和 distinguished 条件，不能用无关三角填入。 -/
structure SyntheticTriangleLift (N : NuFunctorData C Syn) (T : Triangle C) where
  connecting : N.functor.obj T.obj₃ ⟶
    (SyntheticCategory.biShift (0, -1)).obj (N.functor.obj (T.obj₁⟦(1 : ℤ)⟧))
  factorization :
    connecting ≫ SyntheticCategory.lam.app (N.functor.obj (T.obj₁⟦(1 : ℤ)⟧)) =
      N.functor.map T.mor₃
  distinguished :
    Triangle.mk (N.functor.map T.mor₁) (N.functor.map T.mor₂)
      (connecting ≫ (N.boundaryLandingIso T.obj₁).hom) ∈ distTriang Syn

/-- 实际 Hom 群中的 λ-torsion：某个源上的 λ 幂消去该映射。 -/
def LambdaTorsion {A B : Syn} (f : A ⟶ B) : Prop :=
  ∃ n : ℕ, lambdaPow n A ≫ f = 0

/-- 将 full lift 的靶乘 λ^(k-1)，仅形成一次 λ 除法的候选映射。
此构造本身不声称它就是某个 distinguished triangle 的 connecting map。 -/
noncomputable def SyntheticFullLift.normalizedMap (N : NuFunctorData C Syn)
    {X Y : C} {f : X ⟶ Y} {k : ℕ} (L : SyntheticFullLift N f k) (hk : 1 ≤ k) :
    N.functor.obj X ⟶ (SyntheticCategory.biShift (0, -1)).obj (N.functor.obj Y) :=
  L.map ≫ lowerFullLiftTarget (N.functor.obj Y) k hk

/-- MainPaper `prop:41561db2` 后的 remark：任意 full lift 与选定三角分量
仅模 λ-torsion 比较，不能将这项要求加强为两个映射严格相等。 -/
def SyntheticTriangleLift.FullLiftComparison (N : NuFunctorData C Syn)
    {T : Triangle C} (D : SyntheticTriangleLift N T) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (L : SyntheticFullLift N T.mor₃ k),
    LambdaTorsion (D.connecting - SyntheticFullLift.normalizedMap N L hk)

/-- a11：BHS Lemma 9.15 的证明及 MainPaper `prop:41561db2` 给出的三角接口。
将正 filtration、完整短正合、三条映射及 λ-torsion 比较同时列出；正 filtration
蕴含同调短正合的派生证明独立处理，不从最小抽象背景中擅自省去条件。 -/
def SyntheticTriangleLiftComparison (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    AdamsFiltrationAtLeast H T.mor₃ 1 → HomologyShortExact H T →
      ∃ D : SyntheticTriangleLift N T, D.FullLiftComparison N

/-- a10/a11 的可检查交付组。三个字段都使用同一个 H 与 ν。
固定 synthetic 背景的选择仍需接入；文献证明通过显式输入提供，不将此组
安装成项目输入的无条件附加事实。 -/
structure SyntheticInterface (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) : Prop where
  nu_cofiber : NuCofiberCriterion H N
  lift : SyntheticLiftComparison H N
  triangle_lift : SyntheticTriangleLiftComparison H N

/-- a12 的有限塔前置交付，所有对象都是同一 νX 的既有 λ 幂商，
所有映射分量都是同一 cofiber construction 给出的实际商映射。
此组既不提供 homotopy limit，也不无条件断言 λ-adic 完备性。 -/
structure FiniteQuotientTowerInterface [HasFunctorialCofiber (C := Syn)]
    (N : NuFunctorData C Syn) where
  tower : ∀ X : C, FiniteLambdaQuotientTower (N.functor.obj X)
  naturality : ∀ {X Y : C} (f : X ⟶ Y),
    FiniteLambdaQuotientTower.Hom (tower X) (tower Y) (N.functor.map f)

/-- a12：BHS Proposition A.13 (`lemm:easy-e-compton`) 的完备性交付。
选定的同一 λ–ρ–δ 塔既满足映射自然性，也满足实际 cofiber boundary 方块。
`completion` 的各投影固定为商映射，Milnor 三角保留 derived-limit 信息；
没有把同伦极限改成 Ho 范畴的普通极限，也不对任意 X 无条件断言完备。
这里只陈述所需交付，所有模型构造及性质证明均是待完成义务。 -/
structure LambdaAdicCompletenessInterface [HasFunctorialCofiber (C := Syn)]
    [CategoryTheory.Limits.HasProductsOfShape ℕ C]
    [CategoryTheory.Limits.HasProductsOfShape ℕ Syn]
    (H : Mod2EilenbergMacLane (C := C)) (N : NuFunctorData C Syn)
    extends FiniteQuotientTowerInterface N where
  residual_compatible : ∀ X : C, (tower X).ResidualCompatible
  complete_iff : ∀ X : C,
    Classical.Adams.IsENilpotentComplete H.unit X ↔ IsLambdaComplete (N.functor.obj X)
  completion : ∀ X : C,
    Classical.Adams.IsENilpotentComplete H.unit X → LambdaAdicCompletion (tower X)

end Synthetic

end KIP126
