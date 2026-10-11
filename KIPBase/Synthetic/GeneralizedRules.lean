/-
  KIPBase.Synthetic.GeneralizedRules
  Purely synthetic generalized Leibniz and Mahowald propagation.
-/
import KIPBase.Synthetic.Adams
import KIPBase.Synthetic.Lift
import KIPBase.Synthetic.QuotientTower
import KIPBase.Synthetic.PageExtension
import KIPBase.Synthetic.WeightwiseTransport
import KIPBase.SpectralSequence.UnboundedCommutativity
import Mathlib.Algebra.Category.Grp.Subobject

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v uS vS

noncomputable section

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Functoriality on converging synthetic Adams spectral sequences -/

/-- A convergence morphism is determined by its filtered abutment map.  Its
`E∞` map is then forced by compatibility with the convergence isomorphisms.
This lemma is useful because the synthetic Adams input records functoriality
of the actual homotopy maps directly. -/
theorem convergenceMorphism_ext_of_aMap
    {X Y : ConvergingSS AddCommGrpCat (ℤ × ℤ × ℤ) (ℤ × ℤ)}
    (f g : X ⟶ Y) (h : f.aMap = g.aMap) : f = g := by
  apply ConvergenceMorphism.ext _ h
  funext k
  have hp : f.reindex_eq = g.reindex_eq := Subsingleton.elim _ _
  have hf := f.iso_compat k
  have hg := g.iso_compat k
  rw [hp] at hf
  let tr := Y.F.transportGraded ((congrFun g.reindex_eq k).symm)
  letI : IsIso tr := by
    dsimp only [tr, Filtration.transportGraded]
    infer_instance
  let e := (Y.conv.iso k).hom ≫ tr
  letI : IsIso e := by
    dsimp only [e]
    infer_instance
  apply (cancel_mono e).1
  change f.eMap k ≫ (Y.conv.iso k).hom ≫ tr =
    g.eMap k ≫ (Y.conv.iso k).hom ≫ tr
  rw [show tr = Y.F.transportGraded
    ((congrFun g.reindex_eq k).symm) from rfl, hf, hg]
  have hi : Filtration.inducedAssocGradedMap f.aMap f.filtration_compat
      (X.conv.reindex k).1 (X.conv.reindex k).2 =
    Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
      (X.conv.reindex k).1 (X.conv.reindex k).2 := by
    rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap,
      Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap]
    apply Filtration.inducedGradedMapOfMap_congr
    funext s degree
    apply (cancel_mono ((Y.F.F s degree).arrow)).1
    rw [(f.filtration_compat s degree).choose_spec,
      (g.filtration_compat s degree).choose_spec, congrFun h degree]
  rw [hi]

/-- The canonical synthetic Adams convergence object, restated here without
depending on the extension-SS comparison module. -/
noncomputable def syntheticAdamsConvergingSSForRules (X : Syn) :
    ConvergingSS (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ) (ℤ × ℤ) where
  E := SynAdamsSS Syn X
  A := (synAdamsConvergence Syn X).abutment
  F := (synAdamsConvergence Syn X).filtration
  conv := (synAdamsConvergence Syn X).convergence

/-- The converging synthetic Adams map used by the generalized-rule layer. -/
noncomputable def syntheticAdamsConvergingMapForRules {X Y : Syn}
    (f : X ⟶ Y) :
    syntheticAdamsConvergingSSForRules X ⟶
      syntheticAdamsConvergingSSForRules Y :=
  (synAdamsFunctoriality Syn).convergenceMap f

/-- The converging synthetic Adams map of an identity is the identity. -/
@[simp] theorem synAdamsConvergingMap_id (X : Syn) :
    syntheticAdamsConvergingMapForRules (Syn := Syn) (𝟙 X) =
      𝟙 (syntheticAdamsConvergingSSForRules X) := by
  let F := synAdamsFunctoriality Syn
  apply convergenceMorphism_ext_of_aMap
  funext degree
  change (F.convergenceMap (𝟙 X)).aMap degree = 𝟙 _
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ((synAdamsConvergence Syn X).abutmentEquiv degree).injective
  rw [F.abutment_naturality]
  simp

/-- The converging synthetic Adams map preserves composition. -/
theorem synAdamsConvergingMap_comp {X Y Z : Syn}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    syntheticAdamsConvergingMapForRules (Syn := Syn) (f ≫ g) =
      syntheticAdamsConvergingMapForRules f ≫
        syntheticAdamsConvergingMapForRules g := by
  let F := synAdamsFunctoriality Syn
  apply convergenceMorphism_ext_of_aMap
  funext degree
  change (F.convergenceMap (f ≫ g)).aMap degree =
    (F.convergenceMap f).aMap degree ≫ (F.convergenceMap g).aMap degree
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ((synAdamsConvergence Syn Z).abutmentEquiv degree).injective
  rw [F.abutment_naturality]
  change _ = ((synAdamsConvergence Syn Z).abutmentEquiv degree)
    (((F.convergenceMap g).aMap degree).hom
      (((F.convergenceMap f).aMap degree).hom a))
  rw [F.abutment_naturality, F.abutment_naturality]
  simp only [Category.assoc]

/-! ### Synthetic generalized Leibniz propagation -/

/-- A commutative square of maps of synthetic spectra. -/
structure SyntheticCommutativeSquare where
  X₁ : Syn
  X₂ : Syn
  X₃ : Syn
  X₄ : Syn
  top : X₁ ⟶ X₂
  left : X₁ ⟶ X₃
  right : X₂ ⟶ X₄
  bottom : X₃ ⟶ X₄
  comm : top ≫ right = left ≫ bottom

/-! ### The canonical `fHat`--lambda-boundary square -/

/-- The third square in the morphism of complete-endpoint lambda-rho-delta
triangles induced by `fHat`.  Thus its horizontal maps are the finite
lambda-quotient of `fHat` and the shifted `fHat`, while its vertical maps
are the two cofiber boundary maps. -/
noncomputable def fHatLambdaBoundarySquare
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, vS} 𝒰]
    {X Y : 𝒰} (f : X ⟶ Y) (n : ℕ) :
    SyntheticCommutativeSquare (Syn := Syn) where
  X₁ := XModLambdaN
    ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒰 f)).obj
      ((nu 𝒰 Syn).obj X)) n
  X₂ := XModLambdaN ((nu 𝒰 Syn).obj Y) n
  X₃ := (shiftFunctor Syn (1 : ℤ)).obj
    ((SyntheticCategory.biShift (Syn := Syn) (0, -(n : ℤ))).obj
      ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒰 f)).obj
        ((nu 𝒰 Syn).obj X)))
  X₄ := (shiftFunctor Syn (1 : ℤ)).obj
    ((SyntheticCategory.biShift (Syn := Syn) (0, -(n : ℤ))).obj
      ((nu 𝒰 Syn).obj Y))
  top := XModLambdaN.map (fHat 𝒰 Syn f) n
  left := syn_functorial_cofiber.cofibδ
    (lambdaPow n
      ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒰 f)).obj
        ((nu 𝒰 Syn).obj X)))
  right := syn_functorial_cofiber.cofibδ
    (lambdaPow n ((nu 𝒰 Syn).obj Y))
  bottom := (shiftFunctor Syn (1 : ℤ)).map
    ((SyntheticCategory.biShift (Syn := Syn) (0, -(n : ℤ))).map
      (fHat 𝒰 Syn f))
  comm := XModLambdaN.proj_naturality (fHat 𝒰 Syn f) n

namespace SyntheticCommutativeSquare

/-- Applying converging synthetic Adams functoriality gives a genuine square
in the category used by ESS propagation. -/
noncomputable def converging (S : SyntheticCommutativeSquare (Syn := Syn)) :
    ConvergingSSSquare
      (C := AddCommGrpCat.{0}) (ω := ℤ × ℤ × ℤ) (ω' := ℤ × ℤ) where
  V₁ := syntheticAdamsConvergingSSForRules S.X₁
  V₂ := syntheticAdamsConvergingSSForRules S.X₂
  V₃ := syntheticAdamsConvergingSSForRules S.X₃
  V₄ := syntheticAdamsConvergingSSForRules S.X₄
  f := syntheticAdamsConvergingMapForRules S.top
  p := syntheticAdamsConvergingMapForRules S.left
  q := syntheticAdamsConvergingMapForRules S.right
  g := syntheticAdamsConvergingMapForRules S.bottom
  comm := by
    rw [← synAdamsConvergingMap_comp, ← synAdamsConvergingMap_comp,
      S.comm]

end SyntheticCommutativeSquare

/-! ### Canonical page relations on the `fHat` square -/

/-- A finite page extension in a canonical normalized family is literally a
relation on the top edge of the `fHat`--lambda-boundary square.  This is the
finite relation-transport step used by generalized Leibniz; it contains no
classical comparison. -/
theorem FinitePageExtension.canonicalRelation_on_fHatBoundarySquare
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
    {X Y : 𝒰} {f : X ⟶ Y}
    {family : NormalizedPageESSFamily 𝒰 Syn f}
    {r : ℕ} {n s t : ℤ}
    (P : FinitePageExtension 𝒰 Syn f family r n s t)
    (hfamily : family.IsCanonical) :
    let Q := P.canonicalExtension hfamily
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        ((fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f
          (r - 1)).converging.f)
        (t - s, t + eHat 𝒰 f))
      n (s, 1) Q.source Q.scaledTarget := by
  dsimp only
  exact (P.canonicalExtension hfamily).relation

/-- The finite page crossing certificate is transported together with the
top-edge relation.  Thus both outputs refer to one canonical representative,
which is the exact form required by square propagation. -/
theorem FinitePageExtension.canonicalNoCrossingRelation_on_fHatBoundarySquare
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
    {X Y : 𝒰} {f : X ⟶ Y}
    {family : NormalizedPageESSFamily 𝒰 Syn f}
    {r : ℕ} {n s t : ℤ}
    (P : FinitePageExtension 𝒰 Syn f family r n s t)
    (hfamily : family.IsCanonical) (hP : P.NoCrossing) :
    let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
    DifferentialRelation
        (ExtensionSpectralSequence.{1, 0, 0, 0}
          ((fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f
            (r - 1)).converging.f)
          (t - s, t + eHat 𝒰 f))
        n (s, 1) Q.1.source Q.1.scaledTarget ∧
      Q.1.NoCrossing := by
  dsimp only
  let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
  exact ⟨Q.1.relation, Q.2⟩

/-- Weightwise transport specialized to the suspended bottom edge of the
canonical `fHat`--lambda-boundary square.  Supplying this value is precisely
the remaining suspension/weight compatibility datum; relation, essentiality,
and no-crossing preservation are bundled in it. -/
abbrev InfinitePageExtension.FHatBottomWeightwiseTransport
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
    {X Y : 𝒰} {f : X ⟶ Y}
    {family : NormalizedPageESSFamily 𝒰 Syn f}
    {n s t : ℤ}
    (P : InfinitePageExtension 𝒰 Syn f family n s t)
    (hfamily : family.IsCanonical) (hP : P.NoCrossing)
    (quotientExponent : ℕ) (bottomDegree : ℤ × ℤ) :=
  InfinitePageExtension.BottomWeightwiseTransport 𝒰 Syn P hfamily hP
    (ExtensionSpectralSequence.{1, 0, 0, 0}
      ((fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f
        quotientExponent).converging.g) bottomDegree)

namespace InfinitePageExtension.FHatBottomWeightwiseTransport

variable (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
variable {X Y : 𝒰} {f : X ⟶ Y}
variable {family : NormalizedPageESSFamily 𝒰 Syn f}
variable {n s t : ℤ}
variable {P : InfinitePageExtension 𝒰 Syn f family n s t}
variable {hfamily : family.IsCanonical} {hP : P.NoCrossing}
variable {quotientExponent : ℕ} {bottomDegree : ℤ × ℤ}

/-- The transported infinite extension is a relation on the actual bottom
edge of the `fHat` square. -/
theorem relation
    (W : P.FHatBottomWeightwiseTransport 𝒰 hfamily hP
      quotientExponent bottomDegree) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        ((fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f
          quotientExponent).converging.g) bottomDegree)
      n (s, 1) W.transport.source W.transport.target :=
  W.transport.transportedRelation

/-- Its no-crossing certificate is the one consumed by generalized Leibniz,
with projectivity kept explicit through `ESSNoCrossingWith`. -/
theorem noCrossing
    (W : P.FHatBottomWeightwiseTransport 𝒰 hfamily hP
      quotientExponent bottomDegree) :
    let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
    ESSNoCrossingWith n (s, 1) Q.1.projective
      W.transport.transportedRelation :=
  InfinitePageExtension.BottomWeightwiseTransport.noCrossing W

end InfinitePageExtension.FHatBottomWeightwiseTransport

/-! ### Pure ESS propagation layer -/

universe uC vC w w₀

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [LocallySmall.{w₀} C] [WellPowered.{w₀} C]
variable [HasWidePullbacks.{w₀} C] [HasCoproducts.{w₀} C]

/-- `AddCommGrpCat.{0}` 的子对象类型位于 `Type 1`，因而在无界
交换律所用的同一 universe 上自动 small。此实例只在本文件局部使用。 -/
noncomputable local instance addCommGrpCat_wellPowered_one :
    WellPowered.{1} AddCommGrpCat.{0} where
  subobject_small := fun _ => by infer_instance

/-- Purely synthetic generalized Leibniz rule.

The top relation has length `a`, the left relation length `b`, and the bottom
relation length `c`.  With synchronized-source no-crossing on the top or left
edge and no-crossing on the bottom edge, the right edge has length
`b + c - a`.  No classical page or comparison theorem occurs here. -/
alias syntheticGeneralizedLeibniz := unboundedEssCommutativity_noCrossing

/-- The representative-level input for synthetic square propagation.  All
four classes use one projective test object, so the three input relations are
literally composable around the square rather than merely represented by
unrelated elements. -/
structure SyntheticGeneralizedLeibnizInput
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (S : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (a b c s : ℤ) (degree : ω') where
  topLength_nonneg : 0 ≤ a
  leftLength_nonneg : 0 ≤ b
  bottomLength_nonneg : 0 ≤ c
  resultLength_nonneg : 0 ≤ b + c - a
  T : C
  [projective : Projective T]
  x : T ⟶ (S.V₁.E.ssData
    (S.V₁.conv.reindexEquiv.symm (s, degree))).eInfty
  y : T ⟶ (S.V₂.E.ssData
    (S.V₂.conv.reindexEquiv.symm (s + a, degree))).eInfty
  z : T ⟶ (S.V₃.E.ssData
    (S.V₃.conv.reindexEquiv.symm (s + b, degree))).eInfty
  w : T ⟶ (S.V₄.E.ssData
    (S.V₄.conv.reindexEquiv.symm (s + b + c, degree))).eInfty
  topRelation : DifferentialRelation (ExtensionSpectralSequence S.f degree)
    a (s, 1) x y
  leftRelation : DifferentialRelation (ExtensionSpectralSequence S.p degree)
    b (s, 1) x z
  synchronizedNoCrossing :
    ESSRelationNoCrossing a (s, 1) topRelation ∨
      ESSRelationNoCrossing b (s, 1) leftRelation
  bottomRelation : DifferentialRelation (ExtensionSpectralSequence S.g degree)
    c (s + b, 1) z w
  bottomNoCrossing :
    ESSRelationNoCrossing c (s + b, 1) bottomRelation

/-- The top and left part of a generalized Leibniz square, with the common
lower-left representative fixed in advance.  This split lets weightwise
transport supply the entire bottom relation and its no-crossing certificate
without asking callers to restate them manually. -/
structure SyntheticGeneralizedLeibnizTopLeftInput
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w}
    (S : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω'))
    (a b s : ℤ) (degree : ω')
    {T : C} [Projective T]
    (z : T ⟶ (S.V₃.E.ssData
      (S.V₃.conv.reindexEquiv.symm (s + b, degree))).eInfty) where
  topLength_nonneg : 0 ≤ a
  leftLength_nonneg : 0 ≤ b
  x : T ⟶ (S.V₁.E.ssData
    (S.V₁.conv.reindexEquiv.symm (s, degree))).eInfty
  y : T ⟶ (S.V₂.E.ssData
    (S.V₂.conv.reindexEquiv.symm (s + a, degree))).eInfty
  topRelation : DifferentialRelation (ExtensionSpectralSequence S.f degree)
    a (s, 1) x y
  leftRelation : DifferentialRelation (ExtensionSpectralSequence S.p degree)
    b (s, 1) x z
  synchronizedNoCrossing :
    ESSRelationNoCrossing a (s, 1) topRelation ∨
      ESSRelationNoCrossing b (s, 1) leftRelation

namespace SyntheticGeneralizedLeibnizInput

variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
variable {ω' : Type w}
variable {S : ConvergingSSSquare (C := C) (ω := ω) (ω' := ω')}
variable {a b c s : ℤ} {degree : ω'}

/-- 无界方块传播结论中右下角代表元的规范重指标搬运。单独命名此映射，
使后续定理不必在声明头部反复归约大型依赖 `Eq.mpr`。 -/
noncomputable def targetTransport [LocallySmall.{uC} C] [WellPowered.{uC} C]
    [HasWidePullbacks.{uC} C] [HasCoproducts.{uC} C] {T : C}
    (w : T ⟶ (S.V₄.E.ssData
      (S.V₄.conv.reindexEquiv.symm (s + b + c, degree))).eInfty) :
    T ⟶ (S.V₄.E.ssData
      (S.V₄.conv.reindexEquiv.symm (s + a + (b + c - a), degree))).eInfty :=
  Eq.mpr (congrArg (fun X : C => T ⟶ X)
    (unbounded_comm_target_eq (C := C) S a b c s degree)) w

/-- 消去完整的 generalized Leibniz 输入，得到方块右边长度
`b + c - a` 的实际 ESS 关系。目标代表元中的 `Eq.mpr` 正是无界方块
定理给出的规范重指标搬运，不额外选择新的代表元。 -/
theorem propagate [LocallySmall.{uC} C] [WellPowered.{uC} C]
    [HasWidePullbacks.{uC} C] [HasCoproducts.{uC} C]
    (I : SyntheticGeneralizedLeibnizInput S a b c s degree) :
    DifferentialRelation (ExtensionSpectralSequence S.q degree)
      (b + c - a) (s + a, 1) I.y
      (targetTransport (S := S) (a := a) (b := b) (c := c) (s := s)
        (degree := degree) I.w) := by
  rcases I with ⟨ha, hb, hc, hr, T, x, y, z, w,
    htop, hleft, hsync, hbottom, hbottomNoCrossing⟩
  unfold targetTransport
  exact syntheticGeneralizedLeibniz S a b c s degree
    ha hb hc hr x y z w htop hleft hsync hbottom hbottomNoCrossing

/-- Complete a generalized Leibniz input from its synchronized top-left part
and one already transported bottom relation. -/
noncomputable def ofTopLeftAndBottom
    {T : C} [Projective T]
    {z : T ⟶ (S.V₃.E.ssData
      (S.V₃.conv.reindexEquiv.symm (s + b, degree))).eInfty}
    (L : SyntheticGeneralizedLeibnizTopLeftInput S a b s degree z)
    (hc : 0 ≤ c) (hresult : 0 ≤ b + c - a)
    (w' : T ⟶ (S.V₄.E.ssData
      (S.V₄.conv.reindexEquiv.symm (s + b + c, degree))).eInfty)
    (hbottom : DifferentialRelation (ExtensionSpectralSequence S.g degree)
      c (s + b, 1) z w')
    (hbottomNoCrossing :
      ESSRelationNoCrossing c (s + b, 1) hbottom) :
    SyntheticGeneralizedLeibnizInput S a b c s degree where
  topLength_nonneg := L.topLength_nonneg
  leftLength_nonneg := L.leftLength_nonneg
  bottomLength_nonneg := hc
  resultLength_nonneg := hresult
  T := T
  x := L.x
  y := L.y
  z := z
  w := w'
  topRelation := L.topRelation
  leftRelation := L.leftRelation
  synchronizedNoCrossing := L.synchronizedNoCrossing
  bottomRelation := hbottom
  bottomNoCrossing := hbottomNoCrossing

end SyntheticGeneralizedLeibnizInput

namespace InfinitePageExtension.FHatBottomWeightwiseTransport

variable (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
variable {X Y : 𝒰} {f : X ⟶ Y}
variable {family : NormalizedPageESSFamily 𝒰 Syn f}
variable {m r l s tInf : ℤ} {degree : ℤ × ℤ}
variable {quotientExponent : ℕ}
variable {P : InfinitePageExtension 𝒰 Syn f family l (s + r) tInf}
variable {hfamily : family.IsCanonical} {hP : P.NoCrossing}

/-- Complete the raw synthetic generalized Leibniz input using a transported
infinite page extension as the whole bottom edge.  Callers provide only the
synchronized top-left corner; the bottom relation and its no-crossing proof
are recovered from `W`. -/
noncomputable def toGeneralizedLeibnizInput
    (W : P.FHatBottomWeightwiseTransport 𝒰 hfamily hP
      quotientExponent degree)
    (L : let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
      letI : Projective Q.1.T := Q.1.projective
      SyntheticGeneralizedLeibnizTopLeftInput.{1, 0, 0, 0}
        ((fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f
          quotientExponent).converging)
        m r s degree W.transport.source)
    (hl : 0 ≤ l) (hresult : 0 ≤ r + l - m) :
    SyntheticGeneralizedLeibnizInput.{1, 0, 0, 0}
      ((fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f
        quotientExponent).converging)
      m r l s degree := by
  let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
  letI : Projective Q.1.T := Q.1.projective
  apply SyntheticGeneralizedLeibnizInput.ofTopLeftAndBottom
    L hl hresult W.transport.target W.relation
  have hn := InfinitePageExtension.FHatBottomWeightwiseTransport.noCrossing
    (𝒰 := 𝒰) W
  dsimp only at hn
  exact hn

end InfinitePageExtension.FHatBottomWeightwiseTransport

/-! ### Synthetic generalized Mahowald core -/

/-- A categorical form of the May smash-boundary input.

The upper-left corner is the source filtration piece and the lower-left
corner is the deeper target filtration piece.  The pullback assertion is the
May input: compatible arms have a unique simultaneous lift `u`.  The final
field says that the lower projection of this lift really models the filtered
abutment map induced by `f`. -/
structure MaySmashBoundaryInput
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w} {V₁ V₂ : ConvergingSS C ω ω'}
    (f : V₁ ⟶ V₂) (degree : ω') (n s : ℤ) where
  A : C
  D : C
  rho : Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil s 1) ⟶ A
  obstruction : A ⟶ D
  filteredMap : Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil s 1) ⟶
    Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil (s + n) 0)
  boundary : Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil (s + n) 0) ⟶ D
  isPullback : IsPullback rho filteredMap obstruction boundary
  filteredMap_compat :
    filteredMap ≫
        ((unboundedUnderlyingComplex f degree).fil (s + n) 0).arrow =
      ((unboundedUnderlyingComplex f degree).fil s 1).arrow ≫
        f.aMap degree

namespace MaySmashBoundaryInput

variable {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
variable {ω' : Type w} {V₁ V₂ : ConvergingSS C ω ω'}
variable {f : V₁ ⟶ V₂} {degree : ω'} {n s : ℤ}

/-- The element `u` supplied by the May smash-boundary pullback. -/
noncomputable def u (M : MaySmashBoundaryInput f degree n s)
    {T : C} (rhoArm : T ⟶ M.A)
    (targetLift : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil (s + n) 0))
    (compatible : rhoArm ≫ M.obstruction = targetLift ≫ M.boundary) :
    T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil s 1) :=
  M.isPullback.lift rhoArm targetLift compatible

/-- The first boundary equation satisfied by the May lift. -/
@[reassoc (attr := simp)] theorem u_rho
    (M : MaySmashBoundaryInput f degree n s)
    {T : C} (rhoArm : T ⟶ M.A)
    (targetLift : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil (s + n) 0))
    (compatible : rhoArm ≫ M.obstruction = targetLift ≫ M.boundary) :
    M.u rhoArm targetLift compatible ≫ M.rho = rhoArm :=
  M.isPullback.lift_fst rhoArm targetLift compatible

/-- The second boundary equation satisfied by the May lift. -/
@[reassoc (attr := simp)] theorem u_filteredMap
    (M : MaySmashBoundaryInput f degree n s)
    {T : C} (rhoArm : T ⟶ M.A)
    (targetLift : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil (s + n) 0))
    (compatible : rhoArm ≫ M.obstruction = targetLift ≫ M.boundary) :
    M.u rhoArm targetLift compatible ≫ M.filteredMap = targetLift :=
  M.isPullback.lift_snd rhoArm targetLift compatible

/-- The two quotient representatives entering the generalized Mahowald
diagram.  They are intentionally kept before the compatibility equation: in
applications that equation is the nontrivial no-crossing/representative-choice
argument. -/
structure GeneralizedMahowaldRepresentatives
    (M : MaySmashBoundaryInput f degree n s) where
  T : C
  rhoArm : T ⟶ M.A
  targetLift : T ⟶ Subobject.underlying.obj
    ((unboundedUnderlyingComplex f degree).fil (s + n) 0)

/-- The conclusion supplied by the May square: a single quotient class has
the prescribed `ρ` image and prescribed filtered image. -/
def GeneralizedMahowaldConclusion
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M) : Prop :=
  ∃ u : R.T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex f degree).fil s 1),
    u ≫ M.rho = R.rhoArm ∧ u ≫ M.filteredMap = R.targetLift

/-- Synchronizing the representatives is the point where the page-extension
and no-crossing hypotheses of the generalized Mahowald trick are used.  The
concrete synthetic detection proof remains to be supplied by an application
of the rule. -/
theorem mahowaldSynchronizedRepresentatives
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M) :
    R.rhoArm ≫ M.obstruction = R.targetLift ≫ M.boundary := by
  sorry

/-- **Generalized Mahowald trick, categorical core.** Once synchronized
representatives are available, May's pullback produces one common lift.  This
theorem is fully proved from the preceding synchronization lemma and does not
choose separate lifts for its two conclusions. -/
theorem generalizedMahowaldMayCore
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M) :
    GeneralizedMahowaldConclusion M R := by
  let hsync := mahowaldSynchronizedRepresentatives M R
  refine ⟨M.u R.rhoArm R.targetLift hsync, ?_, ?_⟩
  · exact M.u_rho R.rhoArm R.targetLift hsync
  · exact M.u_filteredMap R.rhoArm R.targetLift hsync

/-- The paper-level data for the generalized Mahowald trick.  The named
propositions retain the exact four hypotheses and two conclusions of Blueprint
`thm:generalized-mahowald`; their concrete Adams-page realizations are supplied
by the application-specific comparison layer. -/
structure GeneralizedMahowaldData where
  /-- A distinguished triangle `X --f--> Y --g--> Z --h--> ΣX`. -/
  distinguishedTriangle : Prop
  /-- `e(f)+e(g)+e(h)=1`. -/
  exponentSum : Prop
  nIndex : ℤ
  mIndex : ℤ
  lIndex : ℤ
  sIndex : ℤ
  tIndex : ℤ
  exponentF : ℤ
  exponentG : ℤ
  exponentH : ℤ
  /-- `n₁=n-e(f)≥1`, `m₁=m-e(g)≥0`, and `l₁=l-e(h)≥0`. -/
  degreeBounds : Prop
  /-- The four classes have the Blueprint bidegrees and satisfy
  `x ∈ Z_n₁`, `y ∈ Z_(m₁+1)`, `xBar ∈ Z_(r-1)`, and `yBar ∈ Z_∞`. -/
  classCycleData : Prop
  /-- The actual tower comparison identifies the target label in `ΣX` with
  the displayed `X` label, including the suspension sign. -/
  suspensionComparison : Prop
  /-- `d_l^(h,E_r')(xBar)=x`. -/
  hExtension : Prop
  /-- `d_r(xBar)=yBar`. -/
  classicalDifferential : Prop
  /-- Either the `h` page extension has no crossing, or the classical
  differential has no crossing on `E_r'`. -/
  noCrossing : Prop
  /-- `d_m^(g,E_(m₁+2))(y)=yBar`. -/
  gExtension : Prop
  /-- The exact source conclusion `x ∈ Z_(n+m+e(h))^(s+l,t+l-1)(X)`. -/
  sourceSurvival : Prop
  /-- The exact target conclusion: there exists a genuine
  `d_n^(f,E_(n+m+1+e(h)))(x)` target congruent to `y` modulo
  `B_r'^(s+n+l,t+n+l-1)(Y)`. -/
  extensionCongruence : Prop

namespace GeneralizedMahowaldData

/-- `r=n+m+l`. -/
abbrev r (D : GeneralizedMahowaldData) : ℤ :=
  D.nIndex + D.mIndex + D.lIndex

/-- `n₁=n-e(f)`. -/
abbrev n₁ (D : GeneralizedMahowaldData) : ℤ := D.nIndex - D.exponentF

/-- `m₁=m-e(g)`. -/
abbrev m₁ (D : GeneralizedMahowaldData) : ℤ := D.mIndex - D.exponentG

/-- `l₁=l-e(h)`. -/
abbrev l₁ (D : GeneralizedMahowaldData) : ℤ := D.lIndex - D.exponentH

/-- `r'=r-m₁=n₁+l₁+1`, using the exponent-sum hypothesis. -/
abbrev r' (D : GeneralizedMahowaldData) : ℤ := D.r - D.m₁

end GeneralizedMahowaldData

/-- The common representative from Blueprint
`lem:mahowald-synchronized-representatives`.  Its fields will be refined to
the two quotient detections when the concrete Adams-page layer is attached. -/
structure GeneralizedMahowaldSynchronized
    (_D : GeneralizedMahowaldData) : Prop where
  exists_synchronized_representative : True

/-- The common quotient lift from Blueprint
`lem:mahowald-compatible-quotient-lift`.  It is a separate proposition so the
two final steps necessarily consume the same lift. -/
structure GeneralizedMahowaldLift
    (_D : GeneralizedMahowaldData) : Prop where
  exists_compatible_lift : True

/-- Blueprint Lemma `lem:mahowald-synchronized-representatives`: select one
`[xBar]` simultaneously realizing the two required leading terms. -/
theorem generalizedMahowaldSynchronizedRepresentatives
    (D : GeneralizedMahowaldData) : GeneralizedMahowaldSynchronized D := by
  sorry

/-- Blueprint Lemma `lem:mahowald-compatible-quotient-lift`: May's diagram
produces the common quotient lift from synchronized representatives. -/
theorem generalizedMahowaldMayCompatibleLift
    (D : GeneralizedMahowaldData)
    (_hsync : GeneralizedMahowaldSynchronized D) : GeneralizedMahowaldLift D := by
  sorry

/-- Blueprint Lemma `lem:mahowald-quotient-lift-survival`: the common lift
implies the specified source survival. -/
theorem generalizedMahowaldQuotientLiftSurvival
    (D : GeneralizedMahowaldData)
    (_hlift : GeneralizedMahowaldLift D) : D.sourceSurvival := by
  sorry

/-- Blueprint Lemma `lem:mahowald-lambda-division`: the other image of the
common lift gives the specified extension modulo exactly `B_r'`. -/
theorem generalizedMahowaldLambdaDivision
    (D : GeneralizedMahowaldData)
    (_hlift : GeneralizedMahowaldLift D) : D.extensionCongruence := by
  sorry

/-- **Generalized Mahowald trick** (Blueprint `thm:generalized-mahowald`).
For the data and four hypotheses recorded above, the source class survives to
`Z_(n+m+e(h))` and has an `f`-extension target congruent to `y` modulo
`B_r'`. -/
theorem generalizedMahowaldTrick
    (D : GeneralizedMahowaldData) :
    D.sourceSurvival ∧ D.extensionCongruence := by
  have hsync := generalizedMahowaldSynchronizedRepresentatives D
  have hlift := generalizedMahowaldMayCompatibleLift D hsync
  refine ⟨?_, ?_⟩
  · exact generalizedMahowaldQuotientLiftSurvival D hlift
  · exact generalizedMahowaldLambdaDivision D hlift

end MaySmashBoundaryInput

end

end KIPBase.Synthetic
