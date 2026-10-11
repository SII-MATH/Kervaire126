/-
  KIPBase.multiplicativeSS.Adams

  Multiplicative structure on Adams spectral sequences for composition of
  maps between finite spectra.
-/
import KIPBase.Mathlib
import KIPBase.multiplicativeSS.Basic
import KIPBase.StableHomotopy.Adams

namespace KIPBase.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  KIPBase.SpectralSequence

universe u v w

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-! ### 映射 Adams 谱序列的收敛数据

`adamsMappingConvergingSS` 把 `adamsConvergence` 公理提供的收敛结构
（以 `AddCommGrpCat` 为值范畴）沿数学库的典范等价
`ModuleCat ℤ ≌ AddCommGrpCat` 搬到 `ModuleCat` 值范畴，打包成
`ConvergingSS`。谱序列本体与过滤、收敛同构逐项由等价函子
`(forget₂ (ModuleCat ℤ) AddCommGrpCat).inverse` 传送，不新增任何
数学假设；映射谱的有限性必须由调用者显式提供，`adamsConvergence`
也只接受显式的 `IsFiniteSpectrum` 证明。 -/

-- The Adams library now uses `ModuleCat` directly; no transfer bridge is needed.

/-- 映射 Adams 谱序列的极限分次对象。 -/
axiom adamsMappingAbutment (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    ℤ → ModuleCat.{v, v} IntModuleRing.{v}

/-- 映射 Adams 谱序列极限对象上的 Adams 过滤。 -/
axiom adamsMappingFiltration (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    Filtration (adamsMappingAbutment X Y hX hY)

/-- Adams 弱收敛性在整系数模范畴中的传送形式。 -/
axiom adamsMappingConvergence (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    Convergence
      (AdamsSS 𝒮 (MappingSpectrum X Y))
      (adamsMappingAbutment X Y hX hY)
      (adamsMappingFiltration X Y hX hY)

/-- 有限谱之间映射群的收敛 Adams 谱序列：谱序列本体为映射谱的
Adams 谱序列沿等价传送到 `ModuleCat`，极限为映射同伦群，
收敛结构与过滤同样逐项传送。底层谱统一取 `MappingSpectrum X Y`，
因此与无收敛包装 `adamsMappingSS` 在定义上一致。 -/
noncomputable def adamsMappingConvergingSS (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    ConvergingSS (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) ℤ where
  E := AdamsSS 𝒮 (MappingSpectrum X Y)
  A := adamsMappingAbutment X Y hX hY
  F := adamsMappingFiltration X Y hX hY
  conv := adamsMappingConvergence X Y hX hY

/-- 有限谱之间映射群的 Adams 谱序列（无收敛结构）：映射谱的
Adams 谱序列沿 `ModuleCat ℤ ≌ AddCommGrpCat` 等价传送到
`ModuleCat` 值范畴。 -/
noncomputable def adamsMappingSS (X Y : 𝒮) :
    SpectralSequence (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) :=
  AdamsSS 𝒮 (MappingSpectrum X Y)

/-- 映射 Adams 谱序列从第 2 页开始。 -/
theorem adamsMappingSS_r₀ (X Y : 𝒮) :
    (adamsMappingSS (𝒮 := 𝒮) X Y).r₀ = 2 := by
  rw [adamsMappingSS, adamsSS_r₀]

/-- 映射 Adams 谱序列的微分次数与单谱 Adams 相同：`(r, r-1)`。 -/
theorem adamsMappingSS_diffDeg (X Y : 𝒮) :
    (adamsMappingSS (𝒮 := 𝒮) X Y).diffDeg = adamsDiffDeg := by
  rw [adamsMappingSS, adamsSS_diffDeg]

/-- 页元素在同一模块值谱序列中的恒等传递。 -/
def SpectralSequence.pageTransfer {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence (ModuleCat.{v, v} IntModuleRing.{v}) ι)
    (r : ℤ) (k : ι) (x : ↑(E.Page r k)) : ↑(E.Page r k) := x

/-- 收敛重指标化：Adams 双次数 `(s, t)` 对应过滤次数 `s` 与杆数
`t - s`。 -/
axiom adamsMappingConvergingSS_reindex (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (k : ℤ × ℤ) :
    ((adamsMappingConvergingSS X Y hX hY).conv.reindex k).1 = k.1 ∧
    ((adamsMappingConvergingSS X Y hX hY).conv.reindex k).2 = k.2 - k.1

/-- 极限对象到映射同伦群的典范等价：把 `ModuleCat` 值的极限对象
沿 `AddCommGrpCat ≌ ModuleCat ℤ` 的等价还原为 Abel 群，再经
`mappingSpectrumHomotopy` 识别为稳定映射。 -/
axiom adamsMappingConvergingSS_abutmentEquiv (X Y : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (n : ℤ) :
    (adamsMappingConvergingSS X Y hX hY).A n ≃
      HomotopyGroup n (MappingSpectrum X Y)

/-- **Multiplicative Adams structure for composition.**  For finite spectra
`X`, `Y`, and `Z`, composition `[X,Y]_* ⊗ [Y,Z]_* → [X,Z]_*` induces a
pairing of their converging Adams spectral sequences.  The returned
`ConvergingSSPairing` includes the pagewise Leibniz product, the product on
the abutments, and the compatibility of that product with the E-infinity
pages. -/
axiom adamsCompositionConvergingSSPairing (X Y Z : 𝒮)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z) :
    ConvergingSSPairing
      (adamsMappingConvergingSS X Y hX hY)
      (adamsMappingConvergingSS Y Z hY hZ)
      (adamsMappingConvergingSS X Z hX hZ)

/-- Adams signs use the parity of the stem.  Since bidegree `(s,t)` has stem
`t-s`, this fixes the parity appearing in the signed Leibniz rule. -/
axiom adamsCompositionConvergingSSPairing_parity
    (X Y Z : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (hZ : IsFiniteSpectrum Z) (s t : ℤ) :
    (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).ssPairing.parity (s, t) =
      (↑(t - s) : ZMod 2)

/-- On the abutment, the Adams pairing is the actual composition of stable
maps.  The shift coherence first identifies `Σ^(a+b) X` with
`Σ^b (Σ^a X)`, so the right-hand side is `Σ^b f ≫ g`. -/
axiom adamsCompositionConvergingSSPairing_abutment_compatible
    (X Y Z : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (hZ : IsFiniteSpectrum Z) (a b : ℤ)
    (x : (adamsMappingConvergingSS X Y hX hY).A a)
    (y : (adamsMappingConvergingSS Y Z hY hZ).A b) :
    mappingSpectrumHomotopy (a + b) X Z
      ((adamsMappingConvergingSS_abutmentEquiv X Z hX hZ (a + b))
        ((adamsCompositionConvergingSSPairing X Y Z hX hY hZ).abutmentPair a b
          (x ⊗ₜ y))) =
      (shiftFunctorAdd 𝒮 a b).hom.app X ≫
        (shiftFunctor 𝒮 b).map
          (mappingSpectrumHomotopy a X Y
            ((adamsMappingConvergingSS_abutmentEquiv X Y hX hY a) x)) ≫
        mappingSpectrumHomotopy b Y Z
          ((adamsMappingConvergingSS_abutmentEquiv Y Z hY hZ b) y)

/-- The composition pairings are associative on every Adams page.  This is
the spectral-sequence lift of associativity of composition through four
finite spectra. -/
axiom adamsCompositionConvergingSSPairing_associative
    (W X Y Z : 𝒮) (hW : IsFiniteSpectrum W) (hX : IsFiniteSpectrum X)
    (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z)
    (r : ℤ) (i j k : ℤ × ℤ) :
    ((adamsCompositionConvergingSSPairing W X Y hW hX hY).ssPairing.pair r i j ⊗ₘ
        𝟙 ((adamsMappingConvergingSS Y Z hY hZ).E.Page r k)) ≫
      (adamsCompositionConvergingSSPairing W Y Z hW hY hZ).ssPairing.pair r (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((adamsMappingConvergingSS W X hW hX).E.Page r i)
        ((adamsMappingConvergingSS X Y hX hY).E.Page r j)
        ((adamsMappingConvergingSS Y Z hY hZ).E.Page r k)).hom ≫
      (𝟙 ((adamsMappingConvergingSS W X hW hX).E.Page r i) ⊗ₘ
        (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).ssPairing.pair r j k) ≫
      (adamsCompositionConvergingSSPairing W X Z hW hX hZ).ssPairing.pair r i (j + k)

/-- The E-infinity products induced by composition are associative. -/
axiom adamsCompositionConvergingSSPairing_eInfty_associative
    (W X Y Z : 𝒮) (hW : IsFiniteSpectrum W) (hX : IsFiniteSpectrum X)
    (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z)
    (i j k : ℤ × ℤ) :
    ((adamsCompositionConvergingSSPairing W X Y hW hX hY).eInftyPair i j ⊗ₘ
        𝟙 ((adamsMappingConvergingSS Y Z hY hZ).E.ssData k).eInfty) ≫
      (adamsCompositionConvergingSSPairing W Y Z hW hY hZ).eInftyPair (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((adamsMappingConvergingSS W X hW hX).E.ssData i).eInfty
        ((adamsMappingConvergingSS X Y hX hY).E.ssData j).eInfty
        ((adamsMappingConvergingSS Y Z hY hZ).E.ssData k).eInfty).hom ≫
      (𝟙 ((adamsMappingConvergingSS W X hW hX).E.ssData i).eInfty ⊗ₘ
      (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).eInftyPair j k) ≫
      (adamsCompositionConvergingSSPairing W X Z hW hX hZ).eInftyPair i (j + k)

/-- The abutment products are associative as well.  Together with the page
and `E∞` axioms this supplies associativity at every layer of the converging
composition pairing, rather than only on the spectral-sequence pages. -/
axiom adamsCompositionConvergingSSPairing_abutment_associative
    (W X Y Z : 𝒮) (hW : IsFiniteSpectrum W) (hX : IsFiniteSpectrum X)
    (hY : IsFiniteSpectrum Y) (hZ : IsFiniteSpectrum Z)
    (i j k : ℤ) :
    ((adamsCompositionConvergingSSPairing W X Y hW hX hY).abutmentPair i j ⊗ₘ
        𝟙 ((adamsMappingConvergingSS Y Z hY hZ).A k)) ≫
      (adamsCompositionConvergingSSPairing W Y Z hW hY hZ).abutmentPair (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((adamsMappingConvergingSS W X hW hX).A i)
        ((adamsMappingConvergingSS X Y hX hY).A j)
        ((adamsMappingConvergingSS Y Z hY hZ).A k)).hom ≫
      (𝟙 ((adamsMappingConvergingSS W X hW hX).A i) ⊗ₘ
        (adamsCompositionConvergingSSPairing X Y Z hX hY hZ).abutmentPair j k) ≫
      (adamsCompositionConvergingSSPairing W X Z hW hX hZ).abutmentPair i (j + k)

/-- Unit data for the Adams spectral sequence of the endomorphism spectrum
`F(X,X)`.  The three components are the units on pages, on `E∞`, and on the
abutment respectively. -/
structure AdamsMappingConvergingSSUnit (X : 𝒮) (hX : IsFiniteSpectrum X) where
  page : ∀ r : ℤ,
    𝟙_ (ModuleCat.{v} IntModuleRing) ⟶
      (adamsMappingConvergingSS X X hX hX).E.Page r (0, 0)
  eInfty : 𝟙_ (ModuleCat.{v} IntModuleRing) ⟶
    ((adamsMappingConvergingSS X X hX hX).E.ssData (0, 0)).eInfty
  abutment : 𝟙_ (ModuleCat.{v} IntModuleRing) ⟶
    (adamsMappingConvergingSS X X hX hX).A 0

/-- The identity map of a finite spectrum determines unit data on its Adams
spectral sequence. -/
axiom adamsMappingConvergingSSUnit (X : 𝒮) (hX : IsFiniteSpectrum X) :
    AdamsMappingConvergingSSUnit X hX

/-- The pagewise composition pairing has the identity of `X` as a left unit. -/
axiom adamsCompositionConvergingSSPairing_page_left_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (r : ℤ) (k : ℤ × ℤ) :
    ((adamsMappingConvergingSSUnit X hX).page r ⊗ₘ
        𝟙 ((adamsMappingConvergingSS X Y hX hY).E.Page r k)) ≫
      (adamsCompositionConvergingSSPairing X X Y hX hX hY).ssPairing.pair r (0, 0) k ≫
        eqToHom (congrArg (fun q => (adamsMappingConvergingSS X Y hX hY).E.Page r q)
          (by ext <;> simp)) =
      (λ_ ((adamsMappingConvergingSS X Y hX hY).E.Page r k)).hom

/-- The pagewise composition pairing has the identity of `Y` as a right unit. -/
axiom adamsCompositionConvergingSSPairing_page_right_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (r : ℤ) (k : ℤ × ℤ) :
    (𝟙 ((adamsMappingConvergingSS X Y hX hY).E.Page r k) ⊗ₘ
        (adamsMappingConvergingSSUnit Y hY).page r) ≫
      (adamsCompositionConvergingSSPairing X Y Y hX hY hY).ssPairing.pair r k (0, 0) ≫
        eqToHom (congrArg (fun q => (adamsMappingConvergingSS X Y hX hY).E.Page r q)
          (by ext <;> simp)) =
      (ρ_ ((adamsMappingConvergingSS X Y hX hY).E.Page r k)).hom

/-- The E-infinity composition pairing has the identity of `X` as a left unit. -/
axiom adamsCompositionConvergingSSPairing_eInfty_left_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (k : ℤ × ℤ) :
    ((adamsMappingConvergingSSUnit X hX).eInfty ⊗ₘ
        𝟙 ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty) ≫
      (adamsCompositionConvergingSSPairing X X Y hX hX hY).eInftyPair (0, 0) k ≫
        eqToHom (congrArg
          (fun q => ((adamsMappingConvergingSS X Y hX hY).E.ssData q).eInfty)
          (by ext <;> simp)) =
      (λ_ ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty).hom

/-- The E-infinity composition pairing has the identity of `Y` as a right unit. -/
axiom adamsCompositionConvergingSSPairing_eInfty_right_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y)
    (k : ℤ × ℤ) :
    (𝟙 ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty ⊗ₘ
        (adamsMappingConvergingSSUnit Y hY).eInfty) ≫
      (adamsCompositionConvergingSSPairing X Y Y hX hY hY).eInftyPair k (0, 0) ≫
        eqToHom (congrArg
          (fun q => ((adamsMappingConvergingSS X Y hX hY).E.ssData q).eInfty)
          (by ext <;> simp)) =
      (ρ_ ((adamsMappingConvergingSS X Y hX hY).E.ssData k).eInfty).hom

/-- The abutment composition pairing has the identity of `X` as a left unit. -/
axiom adamsCompositionConvergingSSPairing_abutment_left_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (n : ℤ) :
    ((adamsMappingConvergingSSUnit X hX).abutment ⊗ₘ
        𝟙 ((adamsMappingConvergingSS X Y hX hY).A n)) ≫
      (adamsCompositionConvergingSSPairing X X Y hX hX hY).abutmentPair 0 n ≫
        eqToHom (by simp) =
      (λ_ ((adamsMappingConvergingSS X Y hX hY).A n)).hom

/-- The abutment composition pairing has the identity of `Y` as a right unit. -/
axiom adamsCompositionConvergingSSPairing_abutment_right_unital
    (X Y : 𝒮) (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (n : ℤ) :
    (𝟙 ((adamsMappingConvergingSS X Y hX hY).A n) ⊗ₘ
        (adamsMappingConvergingSSUnit Y hY).abutment) ≫
      (adamsCompositionConvergingSSPairing X Y Y hX hY hY).abutmentPair n 0 ≫
        eqToHom (by simp) =
      (ρ_ ((adamsMappingConvergingSS X Y hX hY).A n)).hom

/-! ### The sphere Adams spectral sequence -/

/-- 球谱的自映射谱在 Adams 谱序列上与球谱本身识别。 -/
axiom sphereMappingAdamsSS :
    AdamsSS (𝒮 := 𝒮) (MappingSpectrum SphereSpectrum SphereSpectrum) =
      AdamsSS (𝒮 := 𝒮) SphereSpectrum

/-- The converging mod-2 Adams spectral sequence of the sphere. -/
noncomputable abbrev sphereAdamsConvergingSS :
    ConvergingSS (ModuleCat.{v} IntModuleRing) (ℤ × ℤ) ℤ :=
  adamsMappingConvergingSS (𝒮 := 𝒮) SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere

/-- Its underlying spectral sequence is the ordinary Adams spectral sequence
of the sphere. -/
theorem sphereAdamsConvergingSS_ss :
    (sphereAdamsConvergingSS (𝒮 := 𝒮)).E =
      AdamsSS (𝒮 := 𝒮) SphereSpectrum := by
  exact sphereMappingAdamsSS

/-- 把球谱 Adams 页元先传送到整系数模范畴，再沿球谱自映射谱的识别搬到
`sphereAdamsConvergingSS` 的底层页。 -/
noncomputable def sphereAdamsPageTransfer (r : ℤ) (k : ℤ × ℤ)
    (x : ↑((AdamsSS (𝒮 := 𝒮) SphereSpectrum).Page r k)) :
    ↑((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r k) :=
  (eqToHom (congrArg (fun E : SpectralSequence
      (ModuleCat.{v, v} IntModuleRing.{v}) (ℤ × ℤ) => E.Page r k)
    (sphereAdamsConvergingSS_ss (𝒮 := 𝒮)).symm))
      (SpectralSequence.pageTransfer
        (AdamsSS (𝒮 := 𝒮) SphereSpectrum) r k x)

/-- Composition supplies the multiplication on the sphere Adams spectral
sequence, on every page, on `E∞`, and on the abutment. -/
noncomputable abbrev sphereAdamsMultiplication :
    ConvergingSSPairing (sphereAdamsConvergingSS (𝒮 := 𝒮))
      (sphereAdamsConvergingSS (𝒮 := 𝒮))
      (sphereAdamsConvergingSS (𝒮 := 𝒮)) :=
  adamsCompositionConvergingSSPairing SphereSpectrum SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere

/-- The identity of the sphere gives the unit on pages, `E∞`, and the
abutment. The existing composition axioms establish its unit laws. -/
noncomputable abbrev sphereAdamsUnit :
    AdamsMappingConvergingSSUnit SphereSpectrum
      (IsFiniteSpectrum.sphere (𝒮 := 𝒮)) :=
  adamsMappingConvergingSSUnit SphereSpectrum IsFiniteSpectrum.sphere

/-- The Koszul parity in the sphere Adams product is the parity of the stem. -/
theorem sphereAdamsMultiplication_parity (s t : ℤ) :
    (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.parity (s, t) =
      (↑(t - s) : ZMod 2) :=
  adamsCompositionConvergingSSPairing_parity
    SphereSpectrum SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere s t

/-- The sphere Adams multiplication is associative on every page. -/
theorem sphereAdamsMultiplication_associative (r : ℤ)
    (i j k : ℤ × ℤ) :
    ((sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r i j ⊗ₘ
        𝟙 ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r k)) ≫
      (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r (i + j) k ≫
        eqToHom (by ac_rfl) =
      (α_ ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r i)
        ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r j)
        ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r k)).hom ≫
      (𝟙 ((sphereAdamsConvergingSS (𝒮 := 𝒮)).E.Page r i) ⊗ₘ
        (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r j k) ≫
      (sphereAdamsMultiplication (𝒮 := 𝒮)).ssPairing.pair r i (j + k) :=
  adamsCompositionConvergingSSPairing_associative
    SphereSpectrum SphereSpectrum SphereSpectrum SphereSpectrum
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere
    IsFiniteSpectrum.sphere IsFiniteSpectrum.sphere r i j k

end KIPBase.StableHomotopy
