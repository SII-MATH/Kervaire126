/-
  KIPBase.Synthetic.ErPageExtension
  有限 Adams 页扩张所需的代表元与权重搬运基础设施。
-/
import KIPBase.SpectralSequence.Elementwise
import KIPBase.Synthetic.FESS
import KIPBase.Synthetic.Lift
import KIPBase.Synthetic.ShiftCofiber

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  KIPBase.SpectralSequence
  KIPBase.StableHomotopy

universe u v w

noncomputable section

/-! ### 循环代表元与页类 -/

namespace ErPageExtension

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- 谱序列环境对象中位于指定 `Z` 层的代表元。

这里把循环层作为显式参数保存，避免把显示页码和内部 `Z/B` 层编号
混为一谈。 -/
structure CycleRepresentative (E : SpectralSequence C ι)
    (level : WithTop ℕ) (k : ι) where
  T : C
  [projective : Projective T]
  value : T ⟶ (E.ssData k).V
  isCycle : Subobject.Factors ((E.ssData k).Z level) value

namespace CycleRepresentative

variable {E : SpectralSequence C ι} {level : WithTop ℕ} {k : ι}

/-- 循环代表元到循环子对象的规范分解。 -/
noncomputable def cycleLift (x : CycleRepresentative E level k) :
    x.T ⟶ Subobject.underlying.obj ((E.ssData k).Z level) :=
  ((E.ssData k).Z level).factorThru x.value x.isCycle

@[reassoc (attr := simp)] theorem cycleLift_arrow
    (x : CycleRepresentative E level k) :
    x.cycleLift ≫ ((E.ssData k).Z level).arrow = x.value :=
  Subobject.factorThru_arrow _ _ _

/-- 代表元确定的 `Z_level/B_level` 页类。 -/
noncomputable def pageClass (x : CycleRepresentative E level k) :
    x.T ⟶ (E.ssData k).page level :=
  x.cycleLift ≫ (E.ssData k).pageπ level

/-- 两个使用同一测试对象的代表元表示同一个页类。 -/
def SameClass (x y : CycleRepresentative E level k)
    (hT : x.T = y.T := by rfl) : Prop :=
  x.pageClass = eqToHom (congrArg (fun T : C => T) hT) ≫ y.pageClass

theorem sameClass_refl (x : CycleRepresentative E level k) :
    x.SameClass x := by
  simp [SameClass]

/-- 零循环代表元。 -/
noncomputable def zero (E : SpectralSequence C ι) (level : WithTop ℕ)
    (k : ι) (T : C) [Projective T] : CycleRepresentative E level k where
  T := T
  value := 0
  isCycle := Subobject.factors_zero

/-- 同一测试对象上的循环代表元可以逐项相加。 -/
noncomputable def add (x y : CycleRepresentative E level k)
    (hT : x.T = y.T := by rfl) : CycleRepresentative E level k := by
  letI : Projective x.T := x.projective
  exact
    { T := x.T
      value := x.value + eqToHom hT ≫ y.value
      isCycle := Subobject.factors_add _ _ x.isCycle
        (Subobject.factors_of_factors_right (eqToHom hT) y.isCycle) }

@[simp] theorem zero_value (E : SpectralSequence C ι) (level : WithTop ℕ)
    (k : ι) (T : C) [Projective T] :
    (zero E level k T).value = 0 := rfl

@[simp] theorem add_value (x y : CycleRepresentative E level k)
    (hT : x.T = y.T := by rfl) :
    (x.add y hT).value = x.value + eqToHom hT ≫ y.value := by
  rfl

/-- 较深循环层的代表元也给出任意较浅循环层的代表元。
这只是代表元层面的遗忘，不错误地声称存在全局页态射
`E_later → E_earlier`。 -/
noncomputable def weaken {earlier later : WithTop ℕ}
    (x : CycleRepresentative E later k) (h : earlier ≤ later) :
    CycleRepresentative E earlier k := by
  letI : Projective x.T := x.projective
  exact
    { T := x.T
      value := x.value
      isCycle := Subobject.factors_of_le x.value
        ((E.ssData k).Z_anti h) x.isCycle }

@[simp] theorem weaken_value {earlier later : WithTop ℕ}
    (x : CycleRepresentative E later k) (h : earlier ≤ later) :
    (x.weaken h).value = x.value := rfl

/-- 谱序列态射逐层搬运循环代表元。 -/
noncomputable def map {E' : SpectralSequence C ι}
    (F : SpectralSequenceMorphism E E')
    (x : CycleRepresentative E level k) :
    CycleRepresentative E' level k := by
  letI : Projective x.T := x.projective
  refine
    { T := x.T
      value := x.value ≫ F.φ k
      isCycle := ?_ }
  have hvalue : x.value ≫ F.φ k =
      (x.cycleLift ≫ (F.preserves_Z k level).choose) ≫
        ((E'.ssData k).Z level).arrow := by
    rw [Category.assoc, (F.preserves_Z k level).choose_spec,
      ← Category.assoc, x.cycleLift_arrow]
  rw [hvalue]
  exact Subobject.factors_comp_arrow _

@[simp] theorem map_value {E' : SpectralSequence C ι}
    (F : SpectralSequenceMorphism E E')
    (x : CycleRepresentative E level k) :
    (x.map F).value = x.value ≫ F.φ k := rfl

/-- 一个循环中的态射经页投影为零，当且仅当其环境态射落在同层边界中。 -/
theorem comp_pageπ_eq_zero_iff_boundary_factors
    {T : C} (z : T ⟶ Subobject.underlying.obj ((E.ssData k).Z level)) :
    z ≫ (E.ssData k).pageπ level = 0 ↔
      Subobject.Factors ((E.ssData k).B level)
        (z ≫ ((E.ssData k).Z level).arrow) := by
  let B := (E.ssData k).B level
  let Z := (E.ssData k).Z level
  let i := Subobject.ofLE B Z ((E.ssData k).B_le_Z level)
  constructor
  · intro hz
    let lift := Abelian.monoLift i z hz
    have hlift : lift ≫ i = z := Abelian.monoLift_comp i z hz
    have hfactor : lift ≫ B.arrow = z ≫ Z.arrow := by
      calc
        lift ≫ B.arrow = lift ≫ (i ≫ Z.arrow) := by
          rw [Subobject.ofLE_arrow]
        _ = (lift ≫ i) ≫ Z.arrow := (Category.assoc _ _ _).symm
        _ = z ≫ Z.arrow := by rw [hlift]
    rw [← hfactor]
    exact Subobject.factors_comp_arrow lift
  · intro hz
    let b := B.factorThru (z ≫ Z.arrow) hz
    have hb : b ≫ i = z := by
      apply (cancel_mono Z.arrow).mp
      rw [Category.assoc, Subobject.ofLE_arrow,
        Subobject.factorThru_arrow]
    change z ≫ cokernel.π i = 0
    rw [← hb, Category.assoc, cokernel.condition, comp_zero]

/-- 固定同一测试对象时，两个循环代表元给出同一页类，当且仅当
它们在环境对象中的差属于同层边界。 -/
theorem pageClass_eq_iff
    (x : CycleRepresentative E level k)
    (y : x.T ⟶ (E.ssData k).V)
    (hy : Subobject.Factors ((E.ssData k).Z level) y) :
    x.pageClass =
        ((E.ssData k).Z level).factorThru y hy ≫
          (E.ssData k).pageπ level ↔
      Subobject.Factors ((E.ssData k).B level) (x.value - y) := by
  let yLift := ((E.ssData k).Z level).factorThru y hy
  let z := x.cycleLift - yLift
  have hzvalue : z ≫ ((E.ssData k).Z level).arrow = x.value - y := by
    simp only [z, yLift, Preadditive.sub_comp,
      cycleLift_arrow, Subobject.factorThru_arrow]
  rw [← hzvalue]
  rw [← comp_pageπ_eq_zero_iff_boundary_factors z]
  change x.cycleLift ≫ (E.ssData k).pageπ level =
      yLift ≫ (E.ssData k).pageπ level ↔
    (x.cycleLift - yLift) ≫ (E.ssData k).pageπ level = 0
  simp only [Preadditive.sub_comp, sub_eq_zero]

/-- 以一个循环代表元为基点的完整页目标陪集。 -/
def targetCoset (x : CycleRepresentative E level k) :
    Set (x.T ⟶ (E.ssData k).V) :=
  { y | Subobject.Factors ((E.ssData k).B level) (x.value - y) }

@[simp] theorem value_mem_targetCoset
    (x : CycleRepresentative E level k) : x.value ∈ x.targetCoset := by
  simp only [targetCoset, Set.mem_setOf_eq, sub_self]
  exact Subobject.factors_zero

/-- 页类的 essential 性：其边界陪集不含零。 -/
def Essential (x : CycleRepresentative E level k) : Prop :=
  (0 : x.T ⟶ (E.ssData k).V) ∉ x.targetCoset

theorem essential_iff_not_boundary
    (x : CycleRepresentative E level k) :
    x.Essential ↔
      ¬ Subobject.Factors ((E.ssData k).B level) x.value := by
  simp only [Essential, targetCoset, Set.mem_setOf_eq, sub_zero]

end CycleRepresentative

/-- 显示页 `E_r` 上的代表元；内部循环层统一使用
`(r - r₀).toNat`，与 `SpectralSequence.Page` 的定义完全一致。 -/
abbrev PageRepresentative (E : SpectralSequence C ι) (r : ℤ) (k : ι) :=
  CycleRepresentative E (↑(r - E.r₀).toNat : WithTop ℕ) k

/-- 显示页代表元给出的真正 `E_r` 页类。 -/
noncomputable def PageRepresentative.class
    {E : SpectralSequence C ι} {r : ℤ} {k : ι}
    (x : PageRepresentative E r k) : x.T ⟶ E.Page r k :=
  x.pageClass

/-! ### 页微分的代表元级关系 -/

/-- 一个真正的显示页微分关系。源和目标使用同一个投射测试对象，
等式发生在商页上，而不是环境对象中。 -/
structure PageDifferentialRelation
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) where
  T : C
  [projective : Projective T]
  source : PageRepresentative E r k
  source_T : source.T = T
  target : PageRepresentative E r (k + E.diffDeg r)
  target_T : target.T = T
  relation :
    eqToHom source_T.symm ≫ source.class ≫ E.d r k =
      eqToHom target_T.symm ≫ target.class

namespace PageDifferentialRelation

variable {E : SpectralSequence C ι} {r : ℤ} {k : ι}

/-- 页微分的目标非零，即该页微分是 essential 的。 -/
def Essential (P : PageDifferentialRelation E r k) : Prop :=
  eqToHom P.target_T.symm ≫ P.target.class ≠ 0

/-- essential 性等价于目标页类不为零。 -/
theorem essential_iff (P : PageDifferentialRelation E r k) :
    P.Essential ↔ eqToHom P.target_T.symm ≫ P.target.class ≠ 0 :=
  Iff.rfl

end PageDifferentialRelation

/-! ### Extension spectral sequence 中的关系与不定性 -/

/-- 不预先伪造 λ 自同态的 ESS 关系。`target` 就是微分中实际出现的
目标；未缩放目标及其 weight-shift λ 映射应在上层比较定理中构造。 -/
structure ExtensionRelation
    (E : SpectralSequence C ι) (n : ℤ) (k : ι) where
  T : C
  [projective : Projective T]
  source : T ⟶ (E.ssData k).V
  target : T ⟶ (E.ssData (k + E.diffDeg n)).V
  relation : DifferentialRelation E n k source target

namespace ExtensionRelation

variable {E : SpectralSequence C ι} {n : ℤ} {k : ι}

/-- 长度 `n` 的 ESS 关系所使用的边界层。 -/
def boundaryLevel : WithTop ℕ :=
  ↑(n - E.r₀).toNat

/-- 固定源的所有可能目标组成目标代表元的边界陪集。 -/
def targetCoset (P : ExtensionRelation E n k) :
    Set (P.T ⟶ (E.ssData (k + E.diffDeg n)).V) :=
  { z | Subobject.Factors
      ((E.ssData (k + E.diffDeg n)).B
        (boundaryLevel (E := E) (n := n)))
      (P.target - z) }

@[simp] theorem target_mem_targetCoset (P : ExtensionRelation E n k) :
    P.target ∈ P.targetCoset := by
  simp only [targetCoset, Set.mem_setOf_eq, sub_self]
  exact Subobject.factors_zero

/-- 同一源的任何另一个关系目标都属于规范目标陪集。 -/
theorem related_target_mem_targetCoset
    (P : ExtensionRelation E n k)
    {z : P.T ⟶ (E.ssData (k + E.diffDeg n)).V}
    (hz : DifferentialRelation E n k P.source z) :
    z ∈ P.targetCoset := by
  exact DifferentialRelation.targets_sub_factors_boundary
    E n k P.relation hz

/-- ESS 关系的 essential 性。 -/
def Essential (P : ExtensionRelation E n k) : Prop :=
  EssentialDifferentialRelation E n k P.source P.target

/-- essential 当且仅当完整目标陪集不含零。 -/
theorem essential_iff_zero_not_mem_targetCoset
    (P : ExtensionRelation E n k) :
    P.Essential ↔
      (0 : P.T ⟶ (E.ssData (k + E.diffDeg n)).V) ∉ P.targetCoset := by
  constructor
  · intro h
    simpa only [targetCoset, boundaryLevel, Set.mem_setOf_eq, sub_zero] using h.2
  · intro h
    refine ⟨P.relation, ?_⟩
    simpa only [targetCoset, boundaryLevel, Set.mem_setOf_eq, sub_zero] using h

/-- 代表元级 ESS 关系给出真正商页上的微分等式。 -/
noncomputable def toPageDifferentialRelation
    (P : ExtensionRelation E n k) : PageDifferentialRelation E n k := by
  letI : Projective P.T := P.projective
  let xZ := P.relation.choose
  have hxZ := P.relation.choose_spec.1
  let yZ := P.relation.choose_spec.2.choose
  have hyZ := P.relation.choose_spec.2.choose_spec.1
  have hrelation := P.relation.choose_spec.2.choose_spec.2
  let sourceRep : PageRepresentative E n k :=
    { T := P.T
      value := P.source
      isCycle := by
        rw [← hxZ]
        exact Subobject.factors_comp_arrow xZ }
  let targetRep : PageRepresentative E n (k + E.diffDeg n) :=
    { T := P.T
      value := P.target
      isCycle := by
        rw [← hyZ]
        exact Subobject.factors_comp_arrow yZ }
  have hxLift : sourceRep.cycleLift = xZ := by
    apply (cancel_mono
      ((E.ssData k).Z (↑(n - E.r₀).toNat : WithTop ℕ)).arrow).mp
    rw [sourceRep.cycleLift_arrow, hxZ]
  have hyLift : targetRep.cycleLift = yZ := by
    apply (cancel_mono
      ((E.ssData (k + E.diffDeg n)).Z
        (↑(n - E.r₀).toNat : WithTop ℕ)).arrow).mp
    rw [targetRep.cycleLift_arrow, hyZ]
  exact
    { T := P.T
      source := sourceRep
      source_T := rfl
      target := targetRep
      target_T := rfl
      relation := by
        dsimp only [PageRepresentative.class]
        simp only [eqToHom_refl, Category.id_comp,
          CycleRepresentative.pageClass, hxLift, hyLift]
        simpa only [xZ, yZ, Category.assoc] using hrelation }

end ExtensionRelation

namespace PageDifferentialRelation

variable {E : SpectralSequence C ι} {r : ℤ} {k : ι}

/-- 商页上的微分等式可提升成代表元级 `DifferentialRelation`。 -/
noncomputable def toExtensionRelation
    (P : PageDifferentialRelation E r k) : ExtensionRelation E r k := by
  letI : Projective P.T := P.projective
  let sourceValue := eqToHom P.source_T.symm ≫ P.source.value
  let targetValue := eqToHom P.target_T.symm ≫ P.target.value
  refine
    { T := P.T
      source := sourceValue
      target := targetValue
      relation := ?_ }
  let xZ := eqToHom P.source_T.symm ≫ P.source.cycleLift
  let yZ := eqToHom P.target_T.symm ≫ P.target.cycleLift
  refine ⟨xZ, ?_, yZ, ?_, ?_⟩
  · simp only [xZ, sourceValue, Category.assoc,
      CycleRepresentative.cycleLift_arrow]
  · simp only [yZ, targetValue, Category.assoc,
      CycleRepresentative.cycleLift_arrow]
  · simpa only [PageRepresentative.class,
      CycleRepresentative.pageClass, xZ, yZ, Category.assoc] using P.relation

end PageDifferentialRelation

/-! ### 真正改变权重的 λ 作用 -/

/-- 权重分次对象上的 `λ` 幂作用。

`pow w n` 的源是权重 `w`，目标是权重 `w-n`；因此它不是固定分量
上的自同态。组合律中的 `eqToHom` 只负责整数恒等式产生的类型搬运。 -/
structure LambdaWeightShiftAction (A : ℤ → AddCommGrpCat.{0}) where
  pow : (w : ℤ) → (n : ℕ) → A w ⟶ A (w - n)
  pow_zero : ∀ w, pow w 0 = eqToHom (congrArg A (by omega))
  pow_add : ∀ w i j,
    pow w (i + j) =
      pow w i ≫ pow (w - i) j ≫ eqToHom (congrArg A (by omega))

namespace LambdaWeightShiftAction

/-- 一次 λ 乘法。 -/
def one {A : ℤ → AddCommGrpCat.{0}} (L : LambdaWeightShiftAction A)
    (w : ℤ) : A w ⟶ A (w - 1) :=
  L.pow w 1

end LambdaWeightShiftAction

/-! ### 谱序列同构在极限页上的作用 -/

/-- `E∞` 映射保持谱序列态射的恒等。该事实直接来自余核映射的
唯一性；放在本文件中避免为了有限页扩张而改动谱序列基础文件。 -/
theorem eInftyMap_id (E : SpectralSequence C ι) (k : ι) :
    (𝟙 E : SpectralSequenceMorphism E E).eInftyMap k = 𝟙 _ := by
  change
    (𝟙 E : SpectralSequenceMorphism E E).toSSDataMorphism.pageMap k ⊤ = 𝟙 _
  exact SSDataMorphism.pageMap_eq_id _ k ⊤ rfl

/-- `E∞` 映射保持谱序列态射的复合。证明只比较循环子对象上的提升，
因此不依赖 `preserves_Z` 中见证的具体选择。 -/
theorem eInftyMap_comp {E₁ E₂ E₃ : SpectralSequence C ι}
    (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (k : ι) :
    (f ≫ g).eInftyMap k = f.eInftyMap k ≫ g.eInftyMap k := by
  change
    (f ≫ g).toSSDataMorphism.pageMap k ⊤ =
      f.toSSDataMorphism.pageMap k ⊤ ≫ g.toSSDataMorphism.pageMap k ⊤
  exact SSDataMorphism.pageMap_eq_comp f.toSSDataMorphism
    g.toSSDataMorphism (f ≫ g).toSSDataMorphism k ⊤ rfl

/-! ### 经典页与 synthetic 自由 λ 区间的规范比较 -/

variable (𝒮 : Type u) [StableHomotopyCategory.{u, 0} 𝒮]
variable (Syn : Type v) [Category.{0} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The underlying additive group of a classical Adams page. -/
noncomputable abbrev classicalAdamsPage (X : 𝒮) (r s t : ℤ) :
    AddCommGrpCat.{0} :=
  (forget₂ (ModuleCat.{0, 0} IntModuleRing.{0}) AddCommGrpCat.{0}).obj
    ((AdamsSS 𝒮 X).Page r (s, t))

/-- 恒等对象映射在 synthetic Adams 的任意显示页上诱导恒等。 -/
theorem synAdamsPageMap_id_local (X : Syn) (r : ℤ)
    (k : ℤ × ℤ × ℤ) :
    synAdamsPageMap (Syn := Syn) (𝟙 X) r k = 𝟙 _ := by
  unfold synAdamsPageMap
  dsimp only
  rw [SSDataMorphism.pageMapOfEq_rfl]
  apply SSDataMorphism.pageMap_eq_id
  exact congrArg (fun F => F.φ k) (synAdamsSS_functorial_id (Syn := Syn) X)

/-- synthetic 对象同构通过 Adams 谱序列的函子性诱导任意显示页上的
同构。这里两端保持同一三重分次；shift 后的重指标另由 shift 比较处理。 -/
noncomputable def synAdamsPageIsoOfIso {X Y : Syn} (e : X ≅ Y)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page r k ≅ (SynAdamsSS Syn Y).Page r k where
  hom := synAdamsPageMap (Syn := Syn) e.hom r k
  inv := synAdamsPageMap (Syn := Syn) e.inv r k
  hom_inv_id := by
    rw [← synAdamsPageMap_comp]
    rw [e.hom_inv_id]
    exact synAdamsPageMap_id_local Syn X r k
  inv_hom_id := by
    rw [← synAdamsPageMap_comp]
    rw [e.inv_hom_id]
    exact synAdamsPageMap_id_local Syn Y r k

/-- synthetic 对象同构通过 Adams 谱序列的函子性诱导逐分次的
`E∞` 同构。逆映射由原对象同构的逆给出，两个三角恒等式由
`synAdamsSS_functorial_comp` 与上面的 `E∞` 函子律推出。 -/
noncomputable def synAdamsEInftyIsoOfIso {X Y : Syn} (e : X ≅ Y)
    (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn X).ssData k).eInfty ≅
      ((SynAdamsSS Syn Y).ssData k).eInfty where
  hom := (synAdamsSS_functorial (Syn := Syn) e.hom).eInftyMap k
  inv := (synAdamsSS_functorial (Syn := Syn) e.inv).eInftyMap k
  hom_inv_id := by
    rw [← eInftyMap_comp]
    change SpectralSequenceMorphism.eInftyMap
      (SpectralSequenceMorphism.comp
        (synAdamsSS_functorial (Syn := Syn) e.hom)
        (synAdamsSS_functorial (Syn := Syn) e.inv)) k = 𝟙 _
    rw [← synAdamsSS_functorial_comp]
    rw [e.hom_inv_id, synAdamsSS_functorial_id]
    exact eInftyMap_id _ k
  inv_hom_id := by
    rw [← eInftyMap_comp]
    change SpectralSequenceMorphism.eInftyMap
      (SpectralSequenceMorphism.comp
        (synAdamsSS_functorial (Syn := Syn) e.inv)
        (synAdamsSS_functorial (Syn := Syn) e.hom)) k = 𝟙 _
    rw [← synAdamsSS_functorial_comp]
    rw [e.inv_hom_id, synAdamsSS_functorial_id]
    exact eInftyMap_id _ k

/-- rigidity 定理在自由 λ 区间给出的范畴同构，而不只是底层群等价。 -/
noncomputable def syntheticClassicalPageIso (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t weight : ℤ)
    (hfree : r - 2 ≤ t - weight) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page r (s, t, weight) ≅
      classicalAdamsPage 𝒮 X r s t :=
  ((rigidity_free_lambda_pages 𝒮 Syn X).componentClassicalEquiv
    𝒮 Syn X r hr s t weight hfree).toAddCommGrpIso

/-- synthetic Adams 页上真实的 `λ^power` 映射；它把 weight 从
`weight` 降到 `weight-power`。 -/
noncomputable def syntheticPageLambdaPow (Y : Syn) (power : ℕ)
    (r s t weight : ℤ) :
    (SynAdamsSS Syn Y).Page r (s, t, weight) ⟶
      (SynAdamsSS Syn Y).Page r (s, t, weight - power) :=
  synAdamsLambdaPowNormalized Syn Y power r s t weight

/-- 真实 λ 幂与自由区间的经典页比较相容：乘 λ 只改变 weight，
对应的经典 Adams 页元素保持不变。 -/
theorem syntheticClassicalPageIso_lambdaPow (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t weight : ℤ)
    (hfree : r - 2 ≤ t - weight) (power : ℕ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
      r (s, t, weight)) :
    (syntheticClassicalPageIso 𝒮 Syn X r hr s t
      (weight - power) (by omega)).hom
        ((syntheticPageLambdaPow Syn ((nu 𝒮 Syn).obj X)
          power r s t weight).hom x) =
      (syntheticClassicalPageIso 𝒮 Syn X r hr s t
        weight hfree).hom x := by
  exact (rigidity_free_lambda_pages 𝒮 Syn X).componentClassicalEquiv_lambdaPow
    𝒮 Syn X r hr s t weight hfree power x

/-- 上述比较把 synthetic 页微分送到经典 Adams 页微分。 -/
theorem syntheticClassicalPageIso_differential (X : 𝒮)
    (r : ℤ) (hr : 2 ≤ r) (s t weight : ℤ)
    (hfree : r - 2 ≤ t - weight)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
      r (s, t, weight)) :
    (syntheticClassicalPageIso 𝒮 Syn X r hr
      (s + r) (t + r - 1) weight (by omega)).hom
        ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
          r s t weight).hom x) =
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom
        ((syntheticClassicalPageIso 𝒮 Syn X r hr
          s t weight hfree).hom x) := by
  exact (rigidity_free_lambda_pages 𝒮 Syn X).componentClassicalEquiv_differential
    𝒮 Syn X r hr s t weight hfree x

/-- 把 generator weight 上的 synthetic 页类先乘以 `λ^(r-2)` 降到
自由区，再用 rigidity 读成经典 Adams 页类。这里得到的是规范态射，
而不是错误地宣称 generator weight 与经典页直接同构。 -/
noncomputable def diagonalToClassicalPage (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t) ⟶
      classicalAdamsPage 𝒮 X (r : ℤ) s t :=
  syntheticPageLambdaPow Syn ((nu 𝒮 Syn).obj X) (r - 2)
      (r : ℤ) s t t ≫
    (syntheticClassicalPageIso 𝒮 Syn X (r : ℤ) (by omega)
      s t (t - (r - 2 : ℕ)) (by omega)).hom

/-- 上述 generator-to-classical 态射确实逐项执行“先乘 λ，再作
rigidity 比较”，把所有整数搬运固定在唯一的规范表达式中。 -/
theorem diagonalToClassicalPage_apply (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
      (r : ℤ) (s, t, t)) :
    (diagonalToClassicalPage 𝒮 Syn X r hr s t).hom x =
      (syntheticClassicalPageIso 𝒮 Syn X (r : ℤ) (by omega)
        s t (t - (r - 2 : ℕ)) (by omega)).hom
        ((syntheticPageLambdaPow Syn ((nu 𝒮 Syn).obj X) (r - 2)
          (r : ℤ) s t t).hom x) := by
  rfl

@[simp] theorem diagonalToClassicalPage_zero (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    (diagonalToClassicalPage 𝒮 Syn X r hr s t).hom 0 = 0 := by
  exact map_zero _

/-- 与 `diagonalToClassicalPage` 配套的微分目标比较。目标先施加
`lambdaPowTarget`，保证使用的正是 λ 与微分自然性中的目标搬运，随后
才把标准化后的自由 weight 分量读成经典 Adams 目标页。 -/
noncomputable def diagonalDifferentialTargetToClassical (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ)
        ((s, t, t) +
          (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).diffDeg (r : ℤ)) ⟶
      classicalAdamsPage 𝒮 X (r : ℤ)
        (s + (r : ℤ)) (t + (r : ℤ) - 1) := by
  let E := SynAdamsSS Syn ((nu 𝒮 Syn).obj X)
  let L := synAdamsSS_zlambda_module Syn ((nu 𝒮 Syn).obj X)
  let m := r - 2
  let hindex : SynAdamsLambdaModule.lambdaIndex m (s, t, t) +
      E.diffDeg (r : ℤ) =
      (s + (r : ℤ), t + (r : ℤ) - 1, t - (m : ℕ)) := by
    dsimp only [E, m]
    rw [SynAdamsLambdaModule.lambdaIndex_eq, synAdamsSS_diffDeg]
    ext <;> dsimp <;> omega
  exact L.lambdaPowTarget m (r : ℤ) (s, t, t) ≫
    eqToHom (congrArg (fun k => E.Page (r : ℤ) k) hindex) ≫
    (syntheticClassicalPageIso 𝒮 Syn X (r : ℤ) (by omega)
      (s + (r : ℤ)) (t + (r : ℤ) - 1) (t - (m : ℕ)) (by omega)).hom

/-- generator weight 的规范经典化与 Adams 微分交换。这里把源先降到
标准自由 weight；目标也使用同一个标准化 differential，因此没有任何
隐藏的指标传输。 -/
theorem diagonalToClassicalPage_comm_d (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
      (r : ℤ) (s, t, t)) :
    (syntheticClassicalPageIso 𝒮 Syn X (r : ℤ) (by omega)
      (s + (r : ℤ)) (t + (r : ℤ) - 1) (t - (r - 2 : ℕ)) (by omega)).hom
        ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
          (r : ℤ) s t (t - (r - 2 : ℕ))).hom
            ((syntheticPageLambdaPow Syn ((nu 𝒮 Syn).obj X) (r - 2)
              (r : ℤ) s t t).hom x)) =
      (classicalAdamsDifferentialNormalized 𝒮 X (r : ℤ) s t).hom
        ((diagonalToClassicalPage 𝒮 Syn X r hr s t).hom x) := by
  exact syntheticClassicalPageIso_differential 𝒮 Syn X
    (r : ℤ) (by omega) s t (t - (r - 2 : ℕ)) (by omega)
      ((syntheticPageLambdaPow Syn ((nu 𝒮 Syn).obj X) (r - 2)
        (r : ℤ) s t t).hom x)

/-! ### 有限 λ 商极限项到经典页 -/

/-- λ 幂与 weight `biShift` 的统一中心性数据。

一般的余纤维 shift 相容性只比较 `F(cofib g)` 与 `cofib(Fg)`；要把
后者识别为 `XModLambdaN (F X) n`，还必须统一比较 `F(λ_X^n)` 与
`λ_{F X}^n`。这里按所有对象和所有幂一次性记录该结构，而不是给每条
扩张关系任意指定 source/target comparison。 -/
class LambdaBiShiftCompatibility where
  domainIso (p : ℤ × ℤ) (n : ℕ) (X : Syn) :
    (SyntheticCategory.biShift p).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X) ≅
      (SyntheticCategory.biShift (0, -(n : ℤ))).obj
        ((SyntheticCategory.biShift p).obj X)
  lambdaPow_comm (p : ℤ × ℤ) (n : ℕ) (X : Syn) :
    (domainIso p n X).hom ≫
        lambdaPow n ((SyntheticCategory.biShift p).obj X) =
      (SyntheticCategory.biShift p).map (lambdaPow n X)

section LambdaBiShift

variable [SyntheticShiftCofiberCompatibility (Syn := Syn)]
variable [LambdaBiShiftCompatibility (Syn := Syn)]

/-- Weight shift 与有限 λ 商的规范对象同构。证明先用已存在的
`biShiftCofibIso` 移动所选余纤维，再用 λ–weight 中心性给出的箭头
同构识别两个余纤维。 -/
noncomputable def biShiftXModLambdaNIso (p : ℤ × ℤ) (X : Syn) (n : ℕ) :
    (SyntheticCategory.biShift p).obj (XModLambdaN X n) ≅
      XModLambdaN ((SyntheticCategory.biShift p).obj X) n := by
  let f := (SyntheticCategory.biShift p).map (lambdaPow n X)
  let g := lambdaPow n ((SyntheticCategory.biShift p).obj X)
  let T := chosenCofiberTriangle f
  let U := chosenCofiberTriangle g
  have hT : T ∈ distTriang Syn :=
    syn_functorial_cofiber.cofib_distinguished f
  have hU : U ∈ distTriang Syn :=
    syn_functorial_cofiber.cofib_distinguished g
  let e : T ≅ U := isoTriangleOfIso₁₂ T U hT hU
    (LambdaBiShiftCompatibility.domainIso p n X) (Iso.refl _)
    (by
      change f ≫ 𝟙 _ =
        (LambdaBiShiftCompatibility.domainIso p n X).hom ≫ g
      rw [Category.comp_id]
      exact (LambdaBiShiftCompatibility.lambdaPow_comm p n X).symm)
  exact SyntheticShiftCofiberCompatibility.biShiftCofibIso
      p (lambdaPow n X) ≪≫ Triangle.π₃.mapIso e

/-- Weight shift 与有限 λ 商的对象同构在 synthetic Adams 的每个
`E∞` 分次上诱导同构。这里尚不改变三重分次；真正的 weight 重指标
由后续的 Adams shift 比较负责。 -/
noncomputable def biShiftXModLambdaNEInftyIso
    (p : ℤ × ℤ) (X : Syn) (n : ℕ) (k : ℤ × ℤ × ℤ) :
    ((SynAdamsSS Syn
      ((SyntheticCategory.biShift p).obj (XModLambdaN X n))).ssData k).eInfty ≅
      ((SynAdamsSS Syn
        (XModLambdaN ((SyntheticCategory.biShift p).obj X) n)).ssData k).eInfty :=
  synAdamsEInftyIsoOfIso Syn (biShiftXModLambdaNIso Syn p X n) k

/-- 同一个有限 λ 商 shift 同构在任意 synthetic Adams 显示页上的版本。 -/
noncomputable def biShiftXModLambdaNPageIso
    (p : ℤ × ℤ) (X : Syn) (n : ℕ) (r : ℤ) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn
      ((SyntheticCategory.biShift p).obj (XModLambdaN X n))).Page r k ≅
      (SynAdamsSS Syn
        (XModLambdaN ((SyntheticCategory.biShift p).obj X) n)).Page r k :=
  synAdamsPageIsoOfIso Syn (biShiftXModLambdaNIso Syn p X n) r k

end LambdaBiShift

/-- `νX/λ^(r-1)` 的 generator 极限项先由有限商稳定性回到 `νX` 的
synthetic `E_r` 页，再沿 generator-to-classical 态射读成经典 Adams
`E_r` 页。这个复合完全由已有规范比较组成。 -/
noncomputable def finiteQuotientEInftyToClassicalPage (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).ssData
        (s, t, t)).eInfty ⟶
      classicalAdamsPage 𝒮 X (r : ℤ) s t :=
  (nuModLambdaPredGeneratorEInftyIsoPage 𝒮 Syn X r hr s t).hom ≫
    diagonalToClassicalPage 𝒮 Syn X r hr s t

/-- 有限商极限项比较的逐元素公式。 -/
theorem finiteQuotientEInftyToClassicalPage_apply (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ)
    (x : ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).ssData
        (s, t, t)).eInfty) :
    (finiteQuotientEInftyToClassicalPage 𝒮 Syn X r hr s t).hom x =
      (diagonalToClassicalPage 𝒮 Syn X r hr s t).hom
        ((nuModLambdaPredGeneratorEInftyIsoPage
          𝒮 Syn X r hr s t).hom.hom x) := by
  rfl

@[simp] theorem finiteQuotientEInftyToClassicalPage_zero (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    (finiteQuotientEInftyToClassicalPage 𝒮 Syn X r hr s t).hom 0 = 0 := by
  exact map_zero _

/-! ### 有限页扩张的规范经典输入 -/

/-- 有限页 `r` 使用的规范化映射
`f̂_(r-1) : Σ^(0,e(f))νX/λ^(r-1) → νY/λ^(r-1)`。 -/
noncomputable def finiteNormalizedMap {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (_hr : 2 ≤ r) :
    XModLambdaN
        ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
          ((nu 𝒮 Syn).obj X)) (r - 1) ⟶
      XModLambdaN ((nu 𝒮 Syn).obj Y) (r - 1) :=
  XModLambdaN.map (fHat 𝒮 Syn f) (r - 1)

/-- 由有限规范化映射直接构造的规范 extension spectral sequence。 -/
noncomputable def finiteExtensionSS {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) (degree : ℤ × ℤ) :
    SpectralSequence AddCommGrpCat.{0} (ℤ × ℤ) :=
  syntheticFESS (finiteNormalizedMap 𝒮 Syn f r hr) degree

@[simp] theorem finiteExtensionSS_r₀ {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) (degree : ℤ × ℤ) :
    (finiteExtensionSS 𝒮 Syn f r hr degree).r₀ = 0 := rfl

@[simp] theorem finiteExtensionSS_diffDeg {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) (degree : ℤ × ℤ) (m : ℤ) :
    (finiteExtensionSS 𝒮 Syn f r hr degree).diffDeg m = (m, -1) := rfl

/-! ### 有限规范化映射与两个 λ-Bockstein 边界的规范方块 -/

/-- 有限页扩张实际使用的四个 synthetic 谱。

这里必须保留三个不同的谱序列来源：上边产生 `f̂` 的 extension ESS，
左右两边分别产生源、目标的 `λ`-Bockstein ESS；下边则是移位后的
`f̂`。不能把这三个 ESS 的环境对象或代表元作定义等同。 -/
structure FiniteLambdaBoundarySquare {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) where
  top : XModLambdaN
      ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
        ((nu 𝒮 Syn).obj X)) (r - 1) ⟶
      XModLambdaN ((nu 𝒮 Syn).obj Y) (r - 1)
  left : XModLambdaN
      ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
        ((nu 𝒮 Syn).obj X)) (r - 1) ⟶
    (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (Syn := Syn) (0, -((r - 1 : ℕ) : ℤ))).obj
        ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
          ((nu 𝒮 Syn).obj X)))
  right : XModLambdaN ((nu 𝒮 Syn).obj Y) (r - 1) ⟶
    (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (Syn := Syn) (0, -((r - 1 : ℕ) : ℤ))).obj
        ((nu 𝒮 Syn).obj Y))
  bottom : (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (Syn := Syn) (0, -((r - 1 : ℕ) : ℤ))).obj
        ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
          ((nu 𝒮 Syn).obj X))) ⟶
    (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (Syn := Syn) (0, -((r - 1 : ℕ) : ℤ))).obj
        ((nu 𝒮 Syn).obj Y))
  comm : top ≫ right = left ≫ bottom

/-- `f̂_(r-1)` 与两端 `λ^(r-1)` 边界组成的规范方块。
交换性直接来自 `λ` 余纤维三角对 `f̂` 的函子性，而不是新增公理。 -/
noncomputable def finiteLambdaBoundarySquare {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) :
    FiniteLambdaBoundarySquare 𝒮 Syn f r hr where
  top := finiteNormalizedMap 𝒮 Syn f r hr
  left := syn_functorial_cofiber.cofibδ
    (lambdaPow (r - 1)
      ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
        ((nu 𝒮 Syn).obj X)))
  right := syn_functorial_cofiber.cofibδ
    (lambdaPow (r - 1) ((nu 𝒮 Syn).obj Y))
  bottom := (shiftFunctor Syn (1 : ℤ)).map
    ((SyntheticCategory.biShift (Syn := Syn)
      (0, -((r - 1 : ℕ) : ℤ))).map (fHat 𝒮 Syn f))
  comm := XModLambdaN.proj_naturality (fHat 𝒮 Syn f) (r - 1)

@[simp] theorem finiteLambdaBoundarySquare_top {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) :
    (finiteLambdaBoundarySquare 𝒮 Syn f r hr).top =
      finiteNormalizedMap 𝒮 Syn f r hr := rfl

/-- 规范方块的交换等式。这个等式把上边的有限 `f̂`-ESS 与两条
已有的 Adams--`λ`-Bockstein 比较放进同一个自然性图中。 -/
theorem finiteLambdaBoundarySquare_naturality {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) :
    (finiteLambdaBoundarySquare 𝒮 Syn f r hr).top ≫
        (finiteLambdaBoundarySquare 𝒮 Syn f r hr).right =
      (finiteLambdaBoundarySquare 𝒮 Syn f r hr).left ≫
        (finiteLambdaBoundarySquare 𝒮 Syn f r hr).bottom :=
  (finiteLambdaBoundarySquare 𝒮 Syn f r hr).comm

/-- 对规范有限边界方块应用带收敛数据的 synthetic Adams 函子。 -/
private theorem convergenceMorphism_ext_of_aMap
    {A B : ConvergingSS AddCommGrpCat (ℤ × ℤ × ℤ) (ℤ × ℤ)}
    (u v : A ⟶ B) (h : u.aMap = v.aMap) : u = v := by
  apply ConvergenceMorphism.ext _ h
  funext k
  have hp : u.reindex_eq = v.reindex_eq := Subsingleton.elim _ _
  have hu := u.iso_compat k
  have hv := v.iso_compat k
  rw [hp] at hu
  let tr := B.F.transportGraded ((congrFun v.reindex_eq k).symm)
  letI : IsIso tr := by
    dsimp only [tr, Filtration.transportGraded]
    infer_instance
  let e := (B.conv.iso k).hom ≫ tr
  letI : IsIso e := by
    dsimp only [e]
    infer_instance
  apply (cancel_mono e).1
  change u.eMap k ≫ (B.conv.iso k).hom ≫ tr =
    v.eMap k ≫ (B.conv.iso k).hom ≫ tr
  rw [show tr = B.F.transportGraded
    ((congrFun v.reindex_eq k).symm) from rfl, hu, hv]
  have hi : Filtration.inducedAssocGradedMap u.aMap u.filtration_compat
      (A.conv.reindex k).1 (A.conv.reindex k).2 =
    Filtration.inducedAssocGradedMap v.aMap v.filtration_compat
      (A.conv.reindex k).1 (A.conv.reindex k).2 := by
    rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap,
      Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap]
    apply Filtration.inducedGradedMapOfMap_congr
    funext s degree
    apply (cancel_mono ((B.F.F s degree).arrow)).1
    rw [(u.filtration_compat s degree).choose_spec,
      (v.filtration_compat s degree).choose_spec, congrFun h degree]
  rw [hi]

private theorem synAdamsConvergingMap_comp_local
    {A B D : Syn} (u : A ⟶ B) (v : B ⟶ D) :
    synAdamsConvergingMap (u ≫ v) =
      synAdamsConvergingMap u ≫ synAdamsConvergingMap v := by
  let F := synAdamsFunctoriality Syn
  apply convergenceMorphism_ext_of_aMap
  funext degree
  change (F.convergenceMap (u ≫ v)).aMap degree =
    (F.convergenceMap u).aMap degree ≫ (F.convergenceMap v).aMap degree
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ((synAdamsConvergence Syn D).abutmentEquiv degree).injective
  rw [F.abutment_naturality]
  change _ = ((synAdamsConvergence Syn D).abutmentEquiv degree)
    (((F.convergenceMap v).aMap degree).hom
      (((F.convergenceMap u).aMap degree).hom a))
  rw [F.abutment_naturality, F.abutment_naturality]
  simp only [Category.assoc]

noncomputable def finiteLambdaBoundaryConvergingSquare
    {X Y : 𝒮} (f : X ⟶ Y) (r : ℕ) (hr : 2 ≤ r) :
    ConvergingSSSquare
      (C := AddCommGrpCat.{0}) (ω := ℤ × ℤ × ℤ) (ω' := ℤ × ℤ) :=
  let S := finiteLambdaBoundarySquare 𝒮 Syn f r hr
  { V₁ := synAdamsConvergingSS
      (XModLambdaN
        ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
          ((nu 𝒮 Syn).obj X)) (r - 1))
    V₂ := synAdamsConvergingSS
      (XModLambdaN ((nu 𝒮 Syn).obj Y) (r - 1))
    V₃ := synAdamsConvergingSS
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (Syn := Syn)
          (0, -((r - 1 : ℕ) : ℤ))).obj
            ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj
              ((nu 𝒮 Syn).obj X))))
    V₄ := synAdamsConvergingSS
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (Syn := Syn)
          (0, -((r - 1 : ℕ) : ℤ))).obj ((nu 𝒮 Syn).obj Y)))
    f := synAdamsConvergingMap S.top
    p := synAdamsConvergingMap S.left
    q := synAdamsConvergingMap S.right
    g := synAdamsConvergingMap S.bottom
    comm := by
      rw [← synAdamsConvergingMap_comp_local,
        ← synAdamsConvergingMap_comp_local, S.comm] }

/-- 收敛方块的上边就是有限规范化映射诱导的收敛谱序列态射。 -/
theorem finiteLambdaBoundaryConvergingSquare_top
    {X Y : 𝒮} (f : X ⟶ Y) (r : ℕ) (hr : 2 ≤ r) :
    (finiteLambdaBoundaryConvergingSquare (Syn := Syn) 𝒮 f r hr).f =
      synAdamsConvergingMap
        (finiteNormalizedMap 𝒮 Syn f r hr) := rfl

/-- 因而收敛方块上边的 extension spectral sequence 与前面定义的
`finiteExtensionSS` 是同一个规范构造，而不是另选的一份 ESS。 -/
theorem finiteExtensionSS_eq_squareTop
    {X Y : 𝒮} (f : X ⟶ Y) (r : ℕ) (hr : 2 ≤ r)
    (degree : ℤ × ℤ) :
    finiteExtensionSS 𝒮 Syn f r hr degree =
      ExtensionSpectralSequence.{1, 0, 0, 0}
        (finiteLambdaBoundaryConvergingSquare (Syn := Syn) 𝒮 f r hr).f degree := rfl

/-- 有限规范化映射的 ESS 中长度 `n`、源位置 `(s,1)` 的关系。
它只记录实际 λ 缩放后的目标，因此不会把 λ 错写成固定 weight 自同态。 -/
abbrev FiniteSyntheticExtensionRelation {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (hr : 2 ≤ r) (n s t : ℤ) :=
  ExtensionRelation
    (finiteExtensionSS 𝒮 Syn f r hr (t - s, t + eHat 𝒮 f))
    n (s, 1)

namespace FiniteSyntheticExtensionRelation

variable {𝒮 Syn} {X Y : 𝒮} {f : X ⟶ Y}
variable {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}

/-- 有限扩张关系在规范收敛方块的上边仍是同一条关系；这里没有
重新选择代表元，也没有把左右两个 Bockstein ESS 与上边 ESS 混同。 -/
theorem relation_on_squareTop
    (P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (finiteLambdaBoundaryConvergingSquare (Syn := Syn) 𝒮 f r hr).f
        (t - s, t + eHat 𝒮 f))
      n (s, 1) P.source P.target := by
  exact P.relation

/-- 上边识别保持 essential 性；这是同一规范 ESS 的定义等同，因而
不会把“环境代表元非零”误当成“商页类非零”。 -/
theorem essential_on_squareTop_iff
    (P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) :
    P.Essential ↔
      EssentialDifferentialRelation
        (ExtensionSpectralSequence.{1, 0, 0, 0}
          (finiteLambdaBoundaryConvergingSquare (Syn := Syn) 𝒮 f r hr).f
          (t - s, t + eHat 𝒮 f))
        n (s, 1) P.source P.target := by
  rfl

/-- 上边识别也逐字保持完整目标陪集，其中已经包含该页以前累积的
全部边界，而不只是当前页的普通边界。 -/
theorem targetCoset_on_squareTop
    (P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) :
    P.targetCoset =
      { z | Subobject.Factors
          (((ExtensionSpectralSequence.{1, 0, 0, 0}
            (finiteLambdaBoundaryConvergingSquare (Syn := Syn) 𝒮 f r hr).f
            (t - s, t + eHat 𝒮 f)).ssData
              ((s, 1) + (n, -1))).B (↑(n - 0).toNat : WithTop ℕ))
          (P.target - z) } := by
  rfl


end FiniteSyntheticExtensionRelation

/-- 有限页 crossing：它本身是更早页 `E_(r-a)` 上的一条实际
essential 规范 ESS 关系，而不是一组互不相容的候选元素。 -/
structure FiniteSyntheticCrossing {X Y : 𝒮} {f : X ⟶ Y}
    {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}
    (_P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) where
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  a_le : a ≤ r - 2
  b_le : (b : ℤ) ≤ n - a - eHat 𝒮 f
  crossing : FiniteSyntheticExtensionRelation 𝒮 Syn f (r - a)
    (by omega) (n - a - b) (s + a) (t + a)
  essential : crossing.Essential

namespace FiniteSyntheticCrossing

variable {𝒮 Syn} {X Y : 𝒮} {f : X ⟶ Y}
variable {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}
variable {P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t}

/-- crossing 的目标经典双次数化简为 Blueprint 中的
`(s+n-b,t+n-b)`。 -/
theorem targetBidegree_eq (C : FiniteSyntheticCrossing 𝒮 Syn P) :
    ((s + C.a) + (n - C.a - C.b),
      (t + C.a) + (n - C.a - C.b)) =
      (s + n - C.b, t + n - C.b) := by
  ext <;> simp <;> ring

/-- essential crossing 的规范 ESS 目标陪集不含零。 -/
theorem zero_not_mem_targetCoset (C : FiniteSyntheticCrossing 𝒮 Syn P) :
    (0 : C.crossing.T ⟶ _) ∉ C.crossing.targetCoset :=
  (ExtensionRelation.essential_iff_zero_not_mem_targetCoset
    C.crossing).mp C.essential

end FiniteSyntheticCrossing

/-- 存在有限页 crossing。 -/
def FiniteSyntheticExtensionRelation.HasCrossing
    {X Y : 𝒮} {f : X ⟶ Y}
    {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}
    (P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) : Prop :=
  Nonempty (FiniteSyntheticCrossing 𝒮 Syn P)

/-- 当前具体 ESS 关系本身的 no-crossing 条件。 -/
def FiniteSyntheticExtensionRelation.RelationNoCrossing
    {X Y : 𝒮} {f : X ⟶ Y}
    {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}
    (P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) : Prop :=
  letI : Projective P.T := P.projective
  ESSRelationNoCrossing n (s, 1) P.relation

/-- 有限页 no-crossing 同时排除结构性 crossing，并保留方块传播所需的
具体关系级 no-crossing 证书。 -/
def FiniteSyntheticExtensionRelation.NoCrossing
    {X Y : 𝒮} {f : X ⟶ Y}
    {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}
    (P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t) : Prop :=
  ¬ P.HasCrossing ∧ P.RelationNoCrossing

namespace FiniteSyntheticExtensionRelation.NoCrossing

variable {𝒮 Syn} {X Y : 𝒮} {f : X ⟶ Y}
variable {r : ℕ} {hr : 2 ≤ r} {n s t : ℤ}
variable {P : FiniteSyntheticExtensionRelation 𝒮 Syn f r hr n s t}

/-- no-crossing 条件排除所有结构性有限页 crossing。 -/
theorem noPageCrossing (hP : P.NoCrossing) : ¬ P.HasCrossing :=
  hP.1

/-- no-crossing 条件提供 ESS 方块传播直接使用的关系级证书。 -/
theorem essRelation (hP : P.NoCrossing) : P.RelationNoCrossing :=
  hP.2

end FiniteSyntheticExtensionRelation.NoCrossing

/-- 有限 `(f,E_r)` 扩张的源在项目内部 `SSData.Z` 中的层号。
显示页为 `r`，所以内部层号是 `r-r₀`；对 Adams 谱序列即 `r-2`。 -/
def finiteSourceCycleLevel {X : 𝒮} (r : ℕ) : ℕ :=
  ((r : ℤ) - (AdamsSS 𝒮 X).r₀).toNat

/-- Blueprint 的目标记号是 `Z_(r-1-n+e(f))`。项目内部 `Z 0`
对应 Blueprint 的 `Z₁`，因此实际内部层号还要减去一次起始页偏移，
即 `r-n+e(f)-r₀ = r-2-n+e(f)`。 -/
def finiteTargetCycleLevel {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (n : ℤ) : ℕ :=
  ((r : ℤ) - n + eHat 𝒮 f - (AdamsSS 𝒮 Y).r₀).toNat

/-- 有限扩张目标代表元所在的显示 Adams 页。 -/
def finiteTargetPage {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (n : ℤ) : ℤ :=
  (r : ℤ) - n + eHat 𝒮 f

/-- 有限 `(f,E_r)` 扩张在进入 synthetic ESS 以前的经典代表元数据。

源和目标都是真正的循环代表元，而不是裸环境对象中的元素；范围条件
保证目标循环层的整数表达式非负。 -/
structure FiniteClassicalInput {X Y : 𝒮} (f : X ⟶ Y)
    (r : ℕ) (n s t : ℤ) where
  page_ge_two : 2 ≤ r
  exponent_le_length : eHat 𝒮 f ≤ n
  length_le_page : n ≤ (r : ℤ) - 2 + eHat 𝒮 f
  T : ModuleCat.{0, 0} IntModuleRing.{0}
  [projective : Projective T]
  sourceValue : T ⟶ ((AdamsSS 𝒮 X).ssData (s, t)).V
  sourceCycle : Subobject.Factors
    (((AdamsSS 𝒮 X).ssData (s, t)).Z
      (finiteSourceCycleLevel 𝒮 (X := X) r)) sourceValue
  targetValue : T ⟶ ((AdamsSS 𝒮 Y).ssData (s + n, t + n)).V
  targetCycle : Subobject.Factors
    (((AdamsSS 𝒮 Y).ssData (s + n, t + n)).Z
      (finiteTargetCycleLevel 𝒮 f r n)) targetValue

namespace FiniteClassicalInput

variable {𝒮 Syn} {X Y : 𝒮} {f : X ⟶ Y} {r : ℕ} {n s t : ℤ}

/-- 源经典循环代表元。 -/
noncomputable def source
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    CycleRepresentative (AdamsSS 𝒮 X)
      (finiteSourceCycleLevel 𝒮 (X := X) r) (s, t) := by
  letI : Projective I.T := I.projective
  exact
    { T := I.T
      value := I.sourceValue
      isCycle := I.sourceCycle }

/-- 目标经典循环代表元。 -/
noncomputable def target
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    CycleRepresentative (AdamsSS 𝒮 Y)
      (finiteTargetCycleLevel 𝒮 f r n) (s + n, t + n) := by
  letI : Projective I.T := I.projective
  exact
    { T := I.T
      value := I.targetValue
      isCycle := I.targetCycle }

/-- 源循环代表元按定义就是显示页 `E_r` 的代表元。 -/
noncomputable def sourcePageRepresentative
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    PageRepresentative (AdamsSS 𝒮 X) r (s, t) :=
  I.source

/-- 目标循环代表元按定义是显示页
`E_(r-n+e(f))` 的代表元。 -/
noncomputable def targetPageRepresentative
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    PageRepresentative (AdamsSS 𝒮 Y)
      (finiteTargetPage 𝒮 f r n) (s + n, t + n) :=
  I.target

/-- 有限扩张的经典源页类。 -/
noncomputable def sourceClass
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    I.T ⟶ (AdamsSS 𝒮 X).Page r (s, t) :=
  I.sourcePageRepresentative.class

/-- 有限扩张的经典目标页类。 -/
noncomputable def targetClass
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    I.T ⟶ (AdamsSS 𝒮 Y).Page
      (finiteTargetPage 𝒮 f r n) (s + n, t + n) :=
  I.targetPageRepresentative.class

/-- 范围条件确实保证 Blueprint 的目标循环层非负。 -/
theorem targetCycleLevel_nonneg
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    0 ≤ (r : ℤ) - 2 - n + eHat 𝒮 f := by
  have hn := I.length_le_page
  omega

/-- 范围条件保证目标显示页仍不早于 Adams 的 `E₂` 页。 -/
theorem targetPage_ge_two
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    2 ≤ finiteTargetPage 𝒮 f r n := by
  unfold finiteTargetPage
  have hn := I.length_le_page
  omega

/-- Adams 起始页为 2，因此源内部循环层正是 `(r-2).toNat`。 -/
theorem sourceCycleLevel_eq
    (_I : FiniteClassicalInput 𝒮 f r n s t) :
    finiteSourceCycleLevel 𝒮 (X := X) r = r - 2 := by
  simp only [finiteSourceCycleLevel, adamsSS_r₀]
  omega

/-- 在扩张的范围条件下，目标内部循环层就是
`r-2-n+e(f)`，没有隐藏的截断。 -/
theorem targetCycleLevel_eq
    (I : FiniteClassicalInput 𝒮 f r n s t) :
    (finiteTargetCycleLevel 𝒮 f r n : ℤ) =
      (r : ℤ) - 2 - n + eHat 𝒮 f := by
  unfold finiteTargetCycleLevel
  rw [adamsSS_r₀]
  have hnonneg : 0 ≤ (r : ℤ) - n + eHat 𝒮 f - 2 := by
    have h := I.targetCycleLevel_nonneg
    omega
  rw [Int.toNat_of_nonneg hnonneg]
  ring

end FiniteClassicalInput

end ErPageExtension

end

end KIPBase.Synthetic
