/-
  KIPBase.Synthetic.QuotientTower
  Finite λ-quotient restrictions and the λ-ρ-δ triangles of Blueprint §4.
-/
import KIPBase.Synthetic.Basic

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- A finite `λ-ρ-δ` quotient triangle for `0 < i < j`.

The final object is written as the triangulated shift of
`Σ^{0,-i}(X/λ^{j-i})`; this is the formal version of the Blueprint notation
`Σ^{1,-i}(X/λ^{j-i})`. -/
structure LambdaRhoDeltaTriangle (X : Syn) (i j : ℕ) where
  i_pos : 0 < i
  i_lt_j : i < j
  lambdaMap :
    (SyntheticCategory.biShift (0, -(i : ℤ))).obj (XModLambdaN X (j - i)) ⟶
      XModLambdaN X j
  rho : XModLambdaN X j ⟶ XModLambdaN X i
  delta : XModLambdaN X i ⟶
    ((SyntheticCategory.biShift (0, -(i : ℤ))).obj
      (XModLambdaN X (j - i)))⟦(1 : ℤ)⟧
  distinguished : Triangle.mk lambdaMap rho delta ∈ distTriang Syn

namespace LambdaRhoDeltaTriangle

variable {X : Syn} {i j : ℕ}

/-- 把有限 `λ-ρ-δ` 数据视为三角形。 -/
noncomputable def toTriangle (T : LambdaRhoDeltaTriangle X i j) : Triangle Syn :=
  Triangle.mk T.lambdaMap T.rho T.delta

/-- `toTriangle` 保留结构中给出的 distinguished 性。 -/
theorem toTriangle_distinguished (T : LambdaRhoDeltaTriangle X i j) :
    T.toTriangle ∈ distTriang Syn :=
  T.distinguished

/-- The composite `λ^i` followed by quotient restriction is zero. -/
theorem lambda_comp_rho (T : LambdaRhoDeltaTriangle X i j) :
    T.lambdaMap ≫ T.rho = 0 :=
  comp_distTriang_mor_zero₁₂ _ T.distinguished

/-- The composite of quotient restriction and the connecting map is zero. -/
theorem rho_comp_delta (T : LambdaRhoDeltaTriangle X i j) :
    T.rho ≫ T.delta = 0 :=
  comp_distTriang_mor_zero₂₃ _ T.distinguished

end LambdaRhoDeltaTriangle

/-- A coherent finite tower of `λ`-quotients.

This is the explicit finite-tower witness required by Blueprint §4.
`HasFunctorialCofiber` supplies identity and composition laws for maps of
cofibers, used by `XModLambdaN.functor` at each fixed exponent. The restriction
maps between different exponents and their distinguished triangles are the
additional data recorded here. -/
structure FiniteLambdaQuotientTower (X : Syn) where
  rho : ∀ (i j : ℕ), i ≤ j → (XModLambdaN X j ⟶ XModLambdaN X i)
  rho_id : ∀ i, rho i i le_rfl = 𝟙 (XModLambdaN X i)
  rho_comp : ∀ {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j),
    rho i j hij ≫ rho k i hki = rho k j (hki.trans hij)
  incl_rho : ∀ {i j : ℕ} (hij : i ≤ j),
    syn_functorial_cofiber.cofibι (lambdaPow j X) ≫ rho i j hij =
      syn_functorial_cofiber.cofibι (lambdaPow i X)
  triangle : ∀ {i j : ℕ}, 0 < i → i < j → LambdaRhoDeltaTriangle X i j
  triangle_rho : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (triangle hi hij).rho = rho i j hij.le

namespace FiniteLambdaQuotientTower

variable {X Y : Syn}

@[simp] theorem rho_self (T : FiniteLambdaQuotientTower X) (i : ℕ) :
    T.rho i i le_rfl = 𝟙 (XModLambdaN X i) :=
  T.rho_id i

theorem rho_trans (T : FiniteLambdaQuotientTower X)
    {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j) :
    T.rho i j hij ≫ T.rho k i hki = T.rho k j (hki.trans hij) :=
  T.rho_comp hki hij

/-- Exactness of the adjacent finite-quotient triangle: a class in
`X/λ^(i+1)` whose restriction to `X/λ` vanishes comes from the first
edge of the distinguished `λ-ρ-δ` triangle. -/
theorem exists_adjacent_lambda_preimage (Q : FiniteLambdaQuotientTower X)
    (S : Syn) (i : ℕ) (hi : 0 < i)
    (a : S ⟶ XModLambdaN X (i + 1))
    (ha : a ≫ Q.rho 1 (i + 1) (by omega) = 0) :
    ∃ z : S ⟶ (SyntheticCategory.biShift (0, -1)).obj (XModLambdaN X i),
      z ≫ (Q.triangle (by omega : 0 < 1) (by omega : 1 < i + 1)).lambdaMap = a := by
  let hlt : 1 < i + 1 := by omega
  let D := Q.triangle (by omega : 0 < 1) hlt
  have hz : a ≫ D.rho = 0 := by
    rw [Q.triangle_rho (by omega : 0 < 1) hlt]
    exact ha
  obtain ⟨z, hz'⟩ := Triangle.coyoneda_exact₂ _ D.distinguished a hz
  exact ⟨z, hz'.symm⟩

/-- The exactness step in independence of a finite-quotient lift. Once the
boundary of the first triangle edge belongs to a specified boundary group,
any two lifts of the same class have equal boundaries modulo that group. -/
theorem adjacent_lift_boundary_difference
    (Q : FiniteLambdaQuotientTower X) (S : Syn) (i : ℕ) (hi : 0 < i)
    {A : Type*} [AddCommGroup A] (d : (S ⟶ XModLambdaN X (i + 1)) →+ A)
    (B : AddSubgroup A)
    (hfirst : ∀ z : S ⟶ (SyntheticCategory.biShift (0, -1)).obj
        (XModLambdaN X i),
      d (z ≫ (Q.triangle (by omega : 0 < 1)
        (by omega : 1 < i + 1)).lambdaMap) ∈ B)
    (a b : S ⟶ XModLambdaN X (i + 1))
    (hab : a ≫ Q.rho 1 (i + 1) (by omega) =
      b ≫ Q.rho 1 (i + 1) (by omega)) :
    d a - d b ∈ B := by
  have hzero : (a - b) ≫ Q.rho 1 (i + 1) (by omega) = 0 := by
    rw [Preadditive.sub_comp, hab, sub_self]
  obtain ⟨z, hz⟩ := Q.exists_adjacent_lambda_preimage S i hi (a - b) hzero
  rw [← map_sub, ← hz]
  exact hfirst z

/-- The same statement at the quotient level: a boundary class modulo `B`
depends only on the restriction of its chosen finite-quotient lift. -/
theorem adjacent_lift_boundary_eq_mod
    (Q : FiniteLambdaQuotientTower X) (S : Syn) (i : ℕ) (hi : 0 < i)
    {A : Type*} [AddCommGroup A] (d : (S ⟶ XModLambdaN X (i + 1)) →+ A)
    (B : AddSubgroup A)
    (hfirst : ∀ z : S ⟶ (SyntheticCategory.biShift (0, -1)).obj
        (XModLambdaN X i),
      d (z ≫ (Q.triangle (by omega : 0 < 1)
        (by omega : 1 < i + 1)).lambdaMap) ∈ B)
    (a b : S ⟶ XModLambdaN X (i + 1))
    (hab : a ≫ Q.rho 1 (i + 1) (by omega) =
      b ≫ Q.rho 1 (i + 1) (by omega)) :
    (QuotientAddGroup.mk (d a : A) : A ⧸ B) =
      (QuotientAddGroup.mk (d b : A) : A ⧸ B) := by
  apply QuotientAddGroup.eq.mpr
  have h := Q.adjacent_lift_boundary_difference S i hi d B hfirst a b hab
  convert B.neg_mem h using 1 <;> abel

/-- canonical 商映射与有限塔的限制映射相容。 -/
theorem incl_comp_rho (T : FiniteLambdaQuotientTower X)
    {i j : ℕ} (hij : i ≤ j) :
    syn_functorial_cofiber.cofibι (lambdaPow j X) ≫ T.rho i j hij =
      syn_functorial_cofiber.cofibι (lambdaPow i X) :=
  T.incl_rho hij

/-- Naturality and triangle compatibility of finite quotient restrictions for
a map `f : X ⟶ Y`.  The middle components are the canonical maps on cofibers
constructed by `XModLambdaN.map`. -/
structure Hom (TX : FiniteLambdaQuotientTower X)
    (TY : FiniteLambdaQuotientTower Y) (f : X ⟶ Y) : Prop where
  rho_naturality : ∀ {i j : ℕ} (hij : i ≤ j),
    TX.rho i j hij ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ TY.rho i j hij
  lambda_naturality : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (SyntheticCategory.biShift (0, -(i : ℤ))).map
          (XModLambdaN.map f (j - i)) ≫
        (TY.triangle hi hij).lambdaMap =
      (TX.triangle hi hij).lambdaMap ≫ XModLambdaN.map f j
  delta_naturality : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    XModLambdaN.map f i ≫ (TY.triangle hi hij).delta =
      (TX.triangle hi hij).delta ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(i : ℤ))).map
            (XModLambdaN.map f (j - i)))

theorem Hom.rho_comm {TX : FiniteLambdaQuotientTower X}
    {TY : FiniteLambdaQuotientTower Y} {f : X ⟶ Y}
    (F : Hom TX TY f) {i j : ℕ} (hij : i ≤ j) :
    TX.rho i j hij ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ TY.rho i j hij :=
  F.rho_naturality hij

/-- 塔态射在每一对指数上给出真正的 `λ-ρ-δ` 三角形态射。

三个交换方块分别来自 `lambda_naturality`、`rho_naturality` 与
`delta_naturality`；这里不再把“三角形相容”仅仅保留为若干独立等式。 -/
noncomputable def Hom.triangleMorphism
    {TX : FiniteLambdaQuotientTower X}
    {TY : FiniteLambdaQuotientTower Y} {f : X ⟶ Y}
    (F : Hom TX TY f) {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    (TX.triangle hi hij).toTriangle ⟶
      (TY.triangle hi hij).toTriangle where
  hom₁ := (SyntheticCategory.biShift (0, -(i : ℤ))).map
    (XModLambdaN.map f (j - i))
  hom₂ := XModLambdaN.map f j
  hom₃ := XModLambdaN.map f i
  comm₁ := (F.lambda_naturality hi hij).symm
  comm₂ := by
    change (TX.triangle hi hij).rho ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ (TY.triangle hi hij).rho
    rw [TX.triangle_rho hi hij, TY.triangle_rho hi hij]
    exact F.rho_naturality hij.le
  comm₃ := (F.delta_naturality hi hij).symm

/-- 恒等映射保持有限 λ-商塔的全部结构。 -/
theorem Hom.id (T : FiniteLambdaQuotientTower X) :
    Hom T T (𝟙 X) := by
  constructor
  · intro i j hij
    simp
  · intro i j hi hij
    simp
  · intro i j hi hij
    simp

/-- 有限 λ-商塔态射关于底层映射的复合封闭。 -/
theorem Hom.comp
    {TX : FiniteLambdaQuotientTower X}
    {TY : FiniteLambdaQuotientTower Y}
    {Z : Syn} {TZ : FiniteLambdaQuotientTower Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (F : Hom TX TY f) (G : Hom TY TZ g) :
    Hom TX TZ (f ≫ g) := by
  constructor
  · intro i j hij
    rw [XModLambdaN.map_comp, XModLambdaN.map_comp]
    calc
      TX.rho i j hij ≫ (XModLambdaN.map f i ≫ XModLambdaN.map g i) =
          (TX.rho i j hij ≫ XModLambdaN.map f i) ≫
            XModLambdaN.map g i := by rw [Category.assoc]
      _ = (XModLambdaN.map f j ≫ TY.rho i j hij) ≫
            XModLambdaN.map g i := by rw [F.rho_naturality hij]
      _ = XModLambdaN.map f j ≫
            (TY.rho i j hij ≫ XModLambdaN.map g i) := by rw [Category.assoc]
      _ = XModLambdaN.map f j ≫
            (XModLambdaN.map g j ≫ TZ.rho i j hij) := by
              rw [G.rho_naturality hij]
      _ = (XModLambdaN.map f j ≫ XModLambdaN.map g j) ≫
            TZ.rho i j hij := by rw [Category.assoc]
  · intro i j hi hij
    rw [XModLambdaN.map_comp, XModLambdaN.map_comp, Functor.map_comp,
      Category.assoc, G.lambda_naturality hi hij, ← Category.assoc,
      F.lambda_naturality hi hij, Category.assoc]
  · intro i j hi hij
    rw [XModLambdaN.map_comp, XModLambdaN.map_comp, Category.assoc,
      G.delta_naturality hi hij, ← Category.assoc,
      F.delta_naturality hi hij, Functor.map_comp, Functor.map_comp,
      Category.assoc]

/-- 恒等塔态射诱导恒等三角形态射。 -/
@[simp] theorem Hom.triangleMorphism_id
    (T : FiniteLambdaQuotientTower X) {i j : ℕ}
    (hi : 0 < i) (hij : i < j) :
    (Hom.id T).triangleMorphism hi hij =
      𝟙 (T.triangle hi hij).toTriangle := by
  ext <;> simp [Hom.triangleMorphism, LambdaRhoDeltaTriangle.toTriangle,
    Triangle.mk]

/-- 组装三角形态射与塔态射复合相容。 -/
theorem Hom.triangleMorphism_comp
    {TX : FiniteLambdaQuotientTower X}
    {TY : FiniteLambdaQuotientTower Y}
    {Z : Syn} {TZ : FiniteLambdaQuotientTower Z}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (F : Hom TX TY f) (G : Hom TY TZ g)
    {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    (F.comp G).triangleMorphism hi hij =
      F.triangleMorphism hi hij ≫ G.triangleMorphism hi hij := by
  ext <;> simp [Hom.triangleMorphism, LambdaRhoDeltaTriangle.toTriangle,
    XModLambdaN.map_comp, Triangle.mk]

/-! ### 有限 λ-商塔组成的范畴 -/

/-- 把一个 synthetic 对象与其选定的 coherent 有限 λ-商塔打包。 -/
structure Bundled where
  /-- 塔的底层 synthetic 对象。 -/
  obj : Syn
  /-- 底层对象上的 coherent 有限 λ-商塔。 -/
  tower : FiniteLambdaQuotientTower obj

namespace Bundled

/-- 打包塔之间的态射由底层态射及其全部塔相容性组成。 -/
structure Hom (A B : Bundled (Syn := Syn)) where
  /-- 底层 synthetic 态射。 -/
  map : A.obj ⟶ B.obj
  /-- 底层态射保持限制映射及所有有限 λ-ρ-δ 三角。 -/
  compatible : FiniteLambdaQuotientTower.Hom A.tower B.tower map

@[ext]
theorem Hom.ext {A B : Bundled (Syn := Syn)} {f g : Hom A B}
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- coherent 有限 λ-商塔及其兼容态射组成一个范畴。 -/
instance : Category (Bundled (Syn := Syn)) where
  Hom := Hom
  id A := ⟨𝟙 A.obj, FiniteLambdaQuotientTower.Hom.id A.tower⟩
  comp f g := ⟨f.map ≫ g.map, f.compatible.comp g.compatible⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
theorem id_map (A : Bundled (Syn := Syn)) :
    (𝟙 A : Hom A A).map = 𝟙 A.obj :=
  rfl

@[simp]
theorem comp_map {A B C : Bundled (Syn := Syn)}
    (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).map = f.map ≫ g.map :=
  rfl

/-- 忘掉 λ-商塔结构，得到其底层 synthetic 对象。 -/
noncomputable def forget : Bundled (Syn := Syn) ⥤ Syn where
  obj A := A.obj
  map f := f.map
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 在指数 `n` 处取有限 λ-商，得到从塔范畴到 synthetic 范畴的函子。 -/
noncomputable def level (n : ℕ) : Bundled (Syn := Syn) ⥤ Syn :=
  forget ⋙ XModLambdaN.functor n

@[simp]
theorem level_obj (A : Bundled (Syn := Syn)) (n : ℕ) :
    (level n).obj A = XModLambdaN A.obj n :=
  rfl

@[simp]
theorem level_map {A B : Bundled (Syn := Syn)} (f : A ⟶ B) (n : ℕ) :
    (level n).map f = XModLambdaN.map f.map n :=
  rfl

/-- 对 `i ≤ j`，塔的限制映射组装成从第 `j` 层到第 `i` 层的自然变换。 -/
noncomputable def rhoNatTrans (i j : ℕ) (hij : i ≤ j) :
    level (Syn := Syn) j ⟶ level i where
  app A := A.tower.rho i j hij
  naturality := by
    intro A B f
    exact (f.compatible.rho_naturality hij).symm

/-- 同一层上的限制自然变换是恒等自然变换。 -/
@[simp]
theorem rhoNatTrans_self (i : ℕ) :
    rhoNatTrans (Syn := Syn) i i le_rfl = 𝟙 (level i) := by
  ext A
  exact A.tower.rho_id i

/-- 限制自然变换满足逆系统所需的复合律。 -/
theorem rhoNatTrans_comp {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j) :
    rhoNatTrans (Syn := Syn) i j hij ≫ rhoNatTrans k i hki =
      rhoNatTrans k j (hki.trans hij) := by
  ext A
  exact A.tower.rho_comp hki hij

/-- 先取第 `n` 层 λ-商，再施加权重平移 `Σ^{0,-i}`。 -/
noncomputable def shiftedLevel (i n : ℕ) : Bundled (Syn := Syn) ⥤ Syn :=
  level n ⋙ SyntheticCategory.biShift (0, -(i : ℤ))

@[simp]
theorem shiftedLevel_obj (A : Bundled (Syn := Syn)) (i n : ℕ) :
    (shiftedLevel i n).obj A =
      (SyntheticCategory.biShift (0, -(i : ℤ))).obj (XModLambdaN A.obj n) :=
  rfl

@[simp]
theorem shiftedLevel_map {A B : Bundled (Syn := Syn)}
    (f : A ⟶ B) (i n : ℕ) :
    (shiftedLevel i n).map f =
      (SyntheticCategory.biShift (0, -(i : ℤ))).map
        (XModLambdaN.map f.map n) :=
  rfl

/-- 有限 λ-ρ-δ 三角的第一条边逐塔自然地组成自然变换。 -/
noncomputable def lambdaNatTrans {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    shiftedLevel (Syn := Syn) i (j - i) ⟶ level j where
  app A := (A.tower.triangle hi hij).lambdaMap
  naturality := by
    intro A B f
    exact f.compatible.lambda_naturality hi hij

/-- 有限 λ-ρ-δ 三角的连接映射逐塔自然地组成自然变换。 -/
noncomputable def deltaNatTrans {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    level (Syn := Syn) i ⟶ shiftedLevel i (j - i) ⋙ shiftFunctor Syn (1 : ℤ) where
  app A := (A.tower.triangle hi hij).delta
  naturality := by
    intro A B f
    exact f.compatible.delta_naturality hi hij

/-- 在自然变换层，有限三角的第一条边与限制映射的复合为零。 -/
theorem lambdaNatTrans_comp_rhoNatTrans {i j : ℕ}
    (hi : 0 < i) (hij : i < j) :
    lambdaNatTrans (Syn := Syn) hi hij ≫ rhoNatTrans i j hij.le = 0 := by
  ext A
  change (A.tower.triangle hi hij).lambdaMap ≫
      A.tower.rho i j hij.le = 0
  rw [← A.tower.triangle_rho hi hij]
  exact (A.tower.triangle hi hij).lambda_comp_rho

/-- 在自然变换层，限制映射与有限三角连接映射的复合为零。 -/
theorem rhoNatTrans_comp_deltaNatTrans {i j : ℕ}
    (hi : 0 < i) (hij : i < j) :
    rhoNatTrans (Syn := Syn) i j hij.le ≫ deltaNatTrans hi hij = 0 := by
  ext A
  change A.tower.rho i j hij.le ≫
      (A.tower.triangle hi hij).delta = 0
  rw [← A.tower.triangle_rho hi hij]
  exact (A.tower.triangle hi hij).rho_comp_delta

/-- 固定 `0 < i < j` 后，每个 coherent 塔的有限 λ-ρ-δ 三角及其
兼容态射组成一个到三角形范畴的函子。 -/
noncomputable def triangleFunctor {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    Bundled (Syn := Syn) ⥤ Triangle Syn where
  obj A := (A.tower.triangle hi hij).toTriangle
  map f := f.compatible.triangleMorphism hi hij
  map_id A := FiniteLambdaQuotientTower.Hom.triangleMorphism_id A.tower hi hij
  map_comp f g :=
    FiniteLambdaQuotientTower.Hom.triangleMorphism_comp
      f.compatible g.compatible hi hij

/-- 一个 coherent 有限 λ-商塔给出由所有正指数有限商组成的 `ℕᵒᵖ`
逆系统；索引 `n` 对应 `X/λ^(n+1)`，因此不会把形式上的零次商混入
λ-adic 完备化。 -/
noncomputable def diagram (A : Bundled (Syn := Syn)) : ℕᵒᵖ ⥤ Syn where
  obj n := XModLambdaN A.obj (n.unop + 1)
  map {m n} f := A.tower.rho (n.unop + 1) (m.unop + 1)
    (Nat.add_le_add_right (leOfHom f.unop) 1)
  map_id n := by
    exact A.tower.rho_id (n.unop + 1)
  map_comp {l m n} f g := by
    exact (A.tower.rho_comp
      (Nat.add_le_add_right (leOfHom g.unop) 1)
      (Nat.add_le_add_right (leOfHom f.unop) 1)).symm

@[simp]
theorem diagram_obj (A : Bundled (Syn := Syn)) (n : ℕᵒᵖ) :
    A.diagram.obj n = XModLambdaN A.obj (n.unop + 1) :=
  rfl

/-- 底层对象通过 canonical 商映射成为其有限 λ-商逆系统上的锥。 -/
noncomputable def quotientCone (A : Bundled (Syn := Syn)) : Cone A.diagram where
  pt := A.obj
  π :=
    { app := fun n => syn_functorial_cofiber.cofibι
        (lambdaPow (n.unop + 1) A.obj)
      naturality := by
        intro m n f
        change (𝟙 A.obj) ≫ syn_functorial_cofiber.cofibι
            (lambdaPow (n.unop + 1) A.obj) =
          syn_functorial_cofiber.cofibι (lambdaPow (m.unop + 1) A.obj) ≫
            A.tower.rho (n.unop + 1) (m.unop + 1)
              (Nat.add_le_add_right (leOfHom f.unop) 1)
        rw [Category.id_comp]
        exact (A.tower.incl_rho
          (Nat.add_le_add_right (leOfHom f.unop) 1)).symm }

@[simp]
theorem quotientCone_π_app (A : Bundled (Syn := Syn)) (n : ℕᵒᵖ) :
    A.quotientCone.π.app n =
      syn_functorial_cofiber.cofibι (lambdaPow (n.unop + 1) A.obj) :=
  rfl

/-- 一个 coherent λ-商塔是 λ-adic 完备的，若底层对象及其 canonical
商映射给出的锥正是全部有限商的极限锥。用 `Nonempty` 忘掉极限见证的
非本质选择，使完备性保持为命题。 -/
def IsLambdaAdicComplete (A : Bundled (Syn := Syn)) : Prop :=
  Nonempty (IsLimit A.quotientCone)

/-- 在所需逆极限存在时，λ-adic 完备性给出底层对象与有限商极限的
canonical 同构。 -/
noncomputable def IsLambdaAdicComplete.comparisonIso
    (A : Bundled (Syn := Syn)) (hA : IsLambdaAdicComplete A)
    [HasLimit A.diagram] :
    A.obj ≅ limit A.diagram :=
  hA.some.conePointUniqueUpToIso (limit.isLimit A.diagram)

/-- 一个兼容塔态射逐层给出有限 λ-商逆系统之间的自然变换。 -/
noncomputable def Hom.diagramNatTrans {A B : Bundled (Syn := Syn)}
    (f : A ⟶ B) : A.diagram ⟶ B.diagram where
  app n := XModLambdaN.map f.map (n.unop + 1)
  naturality := by
    intro m n α
    exact f.compatible.rho_naturality
      (Nat.add_le_add_right (leOfHom α.unop) 1)

@[simp]
theorem Hom.diagramNatTrans_app {A B : Bundled (Syn := Syn)}
    (f : A ⟶ B) (n : ℕᵒᵖ) :
    f.diagramNatTrans.app n = XModLambdaN.map f.map (n.unop + 1) :=
  rfl

/-- 塔态射把源的 canonical 商锥沿逐层自然变换送到目标的 canonical
商锥；其锥点态射正是原来的底层 synthetic 态射。 -/
noncomputable def Hom.quotientConeMorphism
    {A B : Bundled (Syn := Syn)} (f : A ⟶ B) :
    (Cone.postcompose f.diagramNatTrans).obj A.quotientCone ⟶
      B.quotientCone where
  hom := f.map
  w n := XModLambdaN.incl_naturality f.map (n.unop + 1)

@[simp]
theorem Hom.quotientConeMorphism_hom
    {A B : Bundled (Syn := Syn)} (f : A ⟶ B) :
    f.quotientConeMorphism.hom = f.map :=
  rfl

/-- 取有限 λ-商逆系统的操作关于 coherent 塔函子化。 -/
noncomputable def diagramFunctor :
    Bundled (Syn := Syn) ⥤ (ℕᵒᵖ ⥤ Syn) where
  obj A := A.diagram
  map f := f.diagramNatTrans
  map_id A := by
    ext n
    exact XModLambdaN.map_id A.obj (n.unop + 1)
  map_comp f g := by
    ext n
    exact XModLambdaN.map_comp f.map g.map (n.unop + 1)

end Bundled

end FiniteLambdaQuotientTower

/-! ### The complete endpoint -/

/-- The `m = ∞` endpoint of the `λ-ρ-δ` triangle in Blueprint §4.

For finite `n > 0` its first two terms are `Σ^{0,-n} X` and `X`, and its
third term is the chosen cofiber `X/λ^n`. -/
noncomputable def infiniteLambdaRhoDeltaTriangle (X : Syn) (n : ℕ)
    (_hn : 0 < n) : Triangle Syn :=
  Triangle.mk (lambdaPow n X)
    (syn_functorial_cofiber.cofibι (lambdaPow n X))
    (syn_functorial_cofiber.cofibδ (lambdaPow n X))

/-- The complete-endpoint `λ-ρ-δ` triangle is distinguished. -/
theorem infiniteLambdaRhoDeltaTriangle_distinguished (X : Syn) (n : ℕ)
    (hn : 0 < n) :
    infiniteLambdaRhoDeltaTriangle X n hn ∈ distTriang Syn :=
  XModLambdaN.triangle_distinguished X n

/-- At the complete endpoint, multiplication by `λ^n` followed by the
quotient map is zero. -/
theorem infinite_lambda_comp_rho (X : Syn) (n : ℕ) (hn : 0 < n) :
    (infiniteLambdaRhoDeltaTriangle X n hn).mor₁ ≫
      (infiniteLambdaRhoDeltaTriangle X n hn).mor₂ = 0 :=
  comp_distTriang_mor_zero₁₂ _
    (infiniteLambdaRhoDeltaTriangle_distinguished X n hn)

/-- synthetic 态射诱导完整端 λ-ρ-δ 三角形之间的态射。 -/
noncomputable def infiniteLambdaRhoDeltaTriangleMorphism
    {X Y : Syn} (f : X ⟶ Y) (n : ℕ) (hn : 0 < n) :
    infiniteLambdaRhoDeltaTriangle X n hn ⟶
      infiniteLambdaRhoDeltaTriangle Y n hn where
  hom₁ := (SyntheticCategory.biShift (0, -(n : ℤ))).map f
  hom₂ := f
  hom₃ := XModLambdaN.map f n
  comm₁ := (lambdaPow_naturality n f).symm
  comm₂ := (XModLambdaN.incl_naturality f n).symm
  comm₃ := (XModLambdaN.proj_naturality f n).symm

/-- 完整端三角形态射把恒等态射送到恒等态射。 -/
@[simp]
theorem infiniteLambdaRhoDeltaTriangleMorphism_id
    (X : Syn) (n : ℕ) (hn : 0 < n) :
    infiniteLambdaRhoDeltaTriangleMorphism (𝟙 X) n hn =
      𝟙 (infiniteLambdaRhoDeltaTriangle X n hn) := by
  ext <;> simp [infiniteLambdaRhoDeltaTriangleMorphism,
    infiniteLambdaRhoDeltaTriangle, XModLambdaN, Triangle.mk]

/-- 完整端三角形态射保持底层态射的复合。 -/
theorem infiniteLambdaRhoDeltaTriangleMorphism_comp
    {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (hn : 0 < n) :
    infiniteLambdaRhoDeltaTriangleMorphism (f ≫ g) n hn =
      infiniteLambdaRhoDeltaTriangleMorphism f n hn ≫
        infiniteLambdaRhoDeltaTriangleMorphism g n hn := by
  ext <;> simp [infiniteLambdaRhoDeltaTriangleMorphism,
    infiniteLambdaRhoDeltaTriangle, XModLambdaN.map_comp, Triangle.mk] <;> rfl

/-- 固定正指数后，完整端 λ-ρ-δ 三角形关于 synthetic 对象函子化。 -/
noncomputable def infiniteLambdaRhoDeltaTriangleFunctor
    (n : ℕ) (hn : 0 < n) : Syn ⥤ Triangle Syn where
  obj X := infiniteLambdaRhoDeltaTriangle X n hn
  map f := infiniteLambdaRhoDeltaTriangleMorphism f n hn
  map_id X := infiniteLambdaRhoDeltaTriangleMorphism_id X n hn
  map_comp f g := infiniteLambdaRhoDeltaTriangleMorphism_comp f g n hn

/-- 在自然变换层，完整端的 λ 幂后接商映射为零。 -/
theorem lambdaPowNatTrans_comp_inclNatTrans (n : ℕ) :
    lambdaPowNatTrans (Syn := Syn) n ≫ XModLambdaN.inclNatTrans n = 0 := by
  ext X
  exact comp_distTriang_mor_zero₁₂ _
    (XModLambdaN.triangle_distinguished X n)

/-- 在自然变换层，完整端的商映射后接连接映射为零。 -/
theorem inclNatTrans_comp_projNatTrans (n : ℕ) :
    XModLambdaN.inclNatTrans (Syn := Syn) n ≫
      XModLambdaN.projNatTrans n = 0 := by
  ext X
  exact comp_distTriang_mor_zero₂₃ _
    (XModLambdaN.triangle_distinguished X n)

end KIPBase.Synthetic
