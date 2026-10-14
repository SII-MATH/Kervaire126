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

/-- The normalized-map and boundary ESS use the same actual source
E-infinity object. Reduce only the source column, keeping the converging
synthetic Adams data intact. -/
theorem SyntheticCommutativeSquare.top_left_source_eq (S : SyntheticCommutativeSquare (Syn := Syn))
    (degree : ℤ × ℤ) (s : ℤ) :
    (((syntheticExtensionCoreDataOfMap S.top).ess degree).ssData (s,1)).V =
      (unboundedExtensionSSData.{1,0,0,0} S.converging.p degree (s,1)).V := by
  change unboundedExtensionV
      (synAdamsConvergence Syn S.X₁).convergence
      (synAdamsConvergence Syn S.X₂).convergence degree (s,1) =
    unboundedExtensionV
      (synAdamsConvergence Syn S.X₁).convergence
      (synAdamsConvergence Syn S.X₃).convergence degree (s,1)
  simp only [unboundedExtensionV, ↓reduceIte]

/-- The same source representative, typed in the left ESS. Only the
source column is reduced to identify the two endpoint objects. -/
noncomputable def PageExtensionRelation.sourceOnLeft
    (S : SyntheticCommutativeSquare (Syn := Syn)) (degree : ℤ × ℤ)
    {k : ℕ} {n s : ℤ}
    (Q : PageExtensionRelation (syntheticExtensionCoreDataOfMap S.top)
      degree k n s) :
    Q.T ⟶ (unboundedExtensionSSData.{1,0,0,0} S.converging.p degree (s,1)).V := by
  have x := Q.source
  change Q.T ⟶ unboundedExtensionV
    (synAdamsConvergence Syn S.X₁).convergence
    (synAdamsConvergence Syn S.X₂).convergence degree (s,1) at x
  change Q.T ⟶ unboundedExtensionV
    (synAdamsConvergence Syn S.X₁).convergence
    (synAdamsConvergence Syn S.X₃).convergence degree (s,1)
  dsimp only [unboundedExtensionV] at x ⊢
  exact x

section commonLiftBoundary

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
/-- Synchronize the actual finite normalized-map relation with the lambda
boundary relation on the actual `fHat` boundary square. A finite page
extension supplies `Q` through its canonical extension. No crossing on
either the map relation or the boundary relation suffices. Both target
images and lower-right compatibility use one common source lift. -/
theorem PageExtensionRelation.common_lift_on_fHatBoundarySquare
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
    {X Y : 𝒰} {f : X ⟶ Y}
    {r : ℕ} {n s t : ℤ} {k : ℕ}
    : let S := fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f (r-1)
      let degree := (t-s, t + eHat 𝒰 f)
      ∀ (Q : PageExtensionRelation
          (syntheticExtensionCoreDataOfMap S.top) degree k n s),
        letI : Projective Q.T := Q.projective
        ∀ (m : ℤ), 0 ≤ n → 0 ≤ m →
    ∀ (z : Q.T ⟶ (unboundedExtensionSSData.{1,0,0,0}
        S.converging.p degree (s+m,0)).V),
      ∀ (hz : DifferentialRelation
        (ExtensionSpectralSequence.{1,0,0,0} S.converging.p degree)
        m (s,1) (Q.sourceOnLeft S degree) z),
      Q.NoCrossing ∨ ESSRelationNoCrossing m (s,1) hz →
      ∃ (xl : Q.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.f degree).fil s 1))
        (yl : Q.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0))
        (zl : Q.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0)),
        UnboundedExtensionIsLift S.converging.f degree s 1 xl Q.source ∧
        UnboundedExtensionIsLift S.converging.f degree (s+n) 0 yl Q.scaledTarget ∧
        UnboundedExtensionIsLift S.converging.p degree (s+m) 0 zl z ∧
        xl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil s 1).arrow ≫
          S.converging.f.aMap degree =
          yl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0).arrow ∧
        xl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil s 1).arrow ≫
          S.converging.p.aMap degree =
          zl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0).arrow ∧
        yl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0).arrow ≫
          S.converging.q.aMap degree =
          zl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0).arrow ≫
            S.converging.g.aMap degree := by
  intro S degree Q m hn hm z hz hnc
  letI : Projective Q.T := Q.projective
  have hf : DifferentialRelation
      (ExtensionSpectralSequence.{1,0,0,0} S.converging.f degree)
      n (s,1) Q.source Q.scaledTarget := Q.relation
  have hp : DifferentialRelation
      (ExtensionSpectralSequence.{1,0,0,0} S.converging.p degree)
      m (s,1) Q.source z := by
    simpa only [PageExtensionRelation.sourceOnLeft, id_eq] using hz
  have hnc' : ESSRelationNoCrossing n (s,1) hf ∨
      ESSRelationNoCrossing m (s,1) hp := by
    rcases hnc with htop | hleft
    · exact Or.inl htop
    · right
      dsimp only [ESSRelationNoCrossing,
        ExtensionDifferentialRelation.NoCrossing,
        ExtensionDifferentialRelation.NoCrossingRange] at hleft ⊢
      exact hleft
  obtain ⟨xl, yl, zl, hx, hy, hz', htop, hleft⟩ :=
    unbounded_comm_common_source_lift.{1,0,0,0} S.converging n m s degree hn hm
      Q.source Q.scaledTarget z hf hp hnc'
  exact ⟨xl, yl, zl, hx, hy, hz',
    unbounded_lift_ambient_map.{1,0,0,0} S.converging.f degree s (s+n) (by omega) xl yl htop,
    unbounded_lift_ambient_map.{1,0,0,0} S.converging.p degree s (s+m) (by omega) xl zl hleft,
    unbounded_comm_lift_square_ambient.{1,0,0,0} S.converging n m s degree hn hm xl yl zl htop hleft⟩

/-- Instantiate the actual normalized-map--boundary square with the
finite page extension's canonical relation and its transported no-crossing
certificate. No compatibility of arbitrary arms is assumed. -/
theorem FinitePageExtension.common_lift_on_fHatBoundarySquare
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
    {X Y : 𝒰} {f : X ⟶ Y}
    {family : NormalizedPageESSFamily 𝒰 Syn f}
    {r : ℕ} {n s t : ℤ}
    (P : FinitePageExtension 𝒰 Syn f family r n s t)
    (hfamily : family.IsCanonical) (hP : P.NoCrossing)
    (m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    let S := fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f (r-1)
    let degree := (t-s, t + eHat 𝒰 f)
    let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
    ∀ (z : Q.1.T ⟶ (unboundedExtensionSSData.{1,0,0,0}
        S.converging.p degree (s+m,0)).V),
      DifferentialRelation (ExtensionSpectralSequence.{1,0,0,0} S.converging.p degree)
        m (s,1) (Q.1.sourceOnLeft S degree) z →
      ∃ (xl : Q.1.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.f degree).fil s 1))
        (yl : Q.1.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0))
        (zl : Q.1.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0)),
        UnboundedExtensionIsLift S.converging.f degree s 1 xl Q.1.source ∧
        UnboundedExtensionIsLift S.converging.f degree (s+n) 0 yl Q.1.scaledTarget ∧
        UnboundedExtensionIsLift S.converging.p degree (s+m) 0 zl z ∧
        xl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil s 1).arrow ≫
          S.converging.f.aMap degree =
          yl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0).arrow ∧
        xl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil s 1).arrow ≫
          S.converging.p.aMap degree =
          zl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0).arrow ∧
        yl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0).arrow ≫
          S.converging.q.aMap degree =
          zl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0).arrow ≫
            S.converging.g.aMap degree := by
  intro S degree Q z hz
  exact PageExtensionRelation.common_lift_on_fHatBoundarySquare
    𝒰 (f := f) (r := r) (n := n) (s := s) (t := t) Q.1 m hn hm z hz
      (Or.inl Q.2)

/-- The second Mahowald no-crossing alternative: the boundary relation
has no crossing, without imposing no crossing on the finite map extension. -/
theorem FinitePageExtension.common_lift_on_fHatBoundarySquare_of_boundary_noCrossing
    (𝒰 : Type uS)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{uS, 0} 𝒰]
    {X Y : 𝒰} {f : X ⟶ Y}
    {family : NormalizedPageESSFamily 𝒰 Syn f}
    {r : ℕ} {n s t : ℤ}
    (P : FinitePageExtension 𝒰 Syn f family r n s t)
    (hfamily : family.IsCanonical)
    (m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    let S := fHatLambdaBoundarySquare (Syn := Syn) 𝒰 f (r-1)
    let degree := (t-s, t + eHat 𝒰 f)
    let Q := P.canonicalExtension hfamily
    letI : Projective Q.T := Q.projective
    ∀ (z : Q.T ⟶ (unboundedExtensionSSData.{1,0,0,0}
        S.converging.p degree (s+m,0)).V),
      ∀ (hz : DifferentialRelation
        (ExtensionSpectralSequence.{1,0,0,0} S.converging.p degree)
        m (s,1) (Q.sourceOnLeft S degree) z),
      ESSRelationNoCrossing m (s,1) hz →
      ∃ (xl : Q.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.f degree).fil s 1))
        (yl : Q.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0))
        (zl : Q.T ⟶ Subobject.underlying.obj
          ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0)),
        UnboundedExtensionIsLift S.converging.f degree s 1 xl Q.source ∧
        UnboundedExtensionIsLift S.converging.f degree (s+n) 0 yl Q.scaledTarget ∧
        UnboundedExtensionIsLift S.converging.p degree (s+m) 0 zl z ∧
        xl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil s 1).arrow ≫
          S.converging.f.aMap degree =
          yl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0).arrow ∧
        xl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil s 1).arrow ≫
          S.converging.p.aMap degree =
          zl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0).arrow ∧
        yl ≫ ((unboundedUnderlyingComplex S.converging.f degree).fil (s+n) 0).arrow ≫
          S.converging.q.aMap degree =
          zl ≫ ((unboundedUnderlyingComplex S.converging.p degree).fil (s+m) 0).arrow ≫
            S.converging.g.aMap degree := by
  intro S degree Q z hz hnc
  exact PageExtensionRelation.common_lift_on_fHatBoundarySquare
    𝒰 (f := f) (r := r) (n := n) (s := s) (t := t) Q m hn hm z hz
      (Or.inr hnc)

end commonLiftBoundary


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

/-- A synchronized pair of actual representatives. This is an output
witness of the synchronization stage, not a substitute for proving that
stage from the Mahowald page hypotheses. -/
structure GeneralizedMahowaldSynchronized
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M) : Prop where
  compatible : R.rhoArm ≫ M.obstruction = R.targetLift ≫ M.boundary

/-- One actual common lift, with both image equations referring to the
same representative. No unrelated survival or extension proposition is
stored in this witness. -/
structure GeneralizedMahowaldLift
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M) where
  representative : R.T ⟶ Subobject.underlying.obj
    ((unboundedUnderlyingComplex f degree).fil s 1)
  rho_eq : representative ≫ M.rho = R.rhoArm
  filteredMap_eq : representative ≫ M.filteredMap = R.targetLift

/-- Any common lift necessarily gives compatible arms. Previously this
was incorrectly asserted for arbitrary arms without a lift or the page
hypotheses that would produce one. -/
theorem mahowaldSynchronizedRepresentatives
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M)
    (L : GeneralizedMahowaldLift M R) :
    GeneralizedMahowaldSynchronized M R := by
  constructor
  rw [← L.rho_eq, ← L.filteredMap_eq]
  simp only [Category.assoc]
  rw [M.isPullback.w]

/-- May's pullback constructs the actual common lift from synchronized
arms. Synchronization must be supplied by its real preceding proof. -/
noncomputable def generalizedMahowaldMayCompatibleLift
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M)
    (H : GeneralizedMahowaldSynchronized M R) :
    GeneralizedMahowaldLift M R where
  representative := M.u R.rhoArm R.targetLift H.compatible
  rho_eq := M.u_rho R.rhoArm R.targetLift H.compatible
  filteredMap_eq := M.u_filteredMap R.rhoArm R.targetLift H.compatible

/-- Compatibility is exactly the existence condition for one common lift
in this pullback. This is a criterion, not an unconditional assertion of
synchronization for arbitrary input representatives. -/
theorem generalizedMahowaldSynchronizedRepresentatives
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M) :
    GeneralizedMahowaldSynchronized M R ↔ Nonempty (GeneralizedMahowaldLift M R) := by
  constructor
  · intro H
    exact ⟨generalizedMahowaldMayCompatibleLift M R H⟩
  · rintro ⟨L⟩
    exact mahowaldSynchronizedRepresentatives M R L

/-- The categorical May core, with its necessary synchronization input
explicit. This proves the two image equations for one common lift; it does
not claim the classical generalized Mahowald survival/division theorem. -/
theorem generalizedMahowaldMayCore
    (M : MaySmashBoundaryInput f degree n s)
    (R : GeneralizedMahowaldRepresentatives M)
    (H : GeneralizedMahowaldSynchronized M R) :
    GeneralizedMahowaldConclusion M R := by
  let L := generalizedMahowaldMayCompatibleLift M R H
  exact ⟨L.representative,L.rho_eq,L.filteredMap_eq⟩

/-- The filtered image of the common lift is the actual abutment map.
This supplies the map equation required by the ESS representative bridge. -/
@[reassoc] theorem GeneralizedMahowaldLift.ambient_map
    {M : MaySmashBoundaryInput f degree n s}
    {R : GeneralizedMahowaldRepresentatives M}
    (L : GeneralizedMahowaldLift M R) :
    L.representative ≫ ((unboundedUnderlyingComplex f degree).fil s 1).arrow ≫
      f.aMap degree =
      R.targetLift ≫ ((unboundedUnderlyingComplex f degree).fil (s+n) 0).arrow := by
  have h := congrArg
    (fun q => q ≫ ((unboundedUnderlyingComplex f degree).fil (s+n) 0).arrow)
    L.filteredMap_eq
  have hc := (Category.assoc L.representative M.filteredMap
    ((unboundedUnderlyingComplex f degree).fil (s+n) 0).arrow).symm.trans h
  exact (congrArg (fun q => L.representative ≫ q)
    M.filteredMap_compat.symm).trans hc

/-- The common lift yields the actual map ESS relation on its detected
endpoints. The representative is shared with both May image equations. -/
theorem GeneralizedMahowaldLift.ess_relation
    {M : MaySmashBoundaryInput f degree n s}
    {R : GeneralizedMahowaldRepresentatives M}
    (L : GeneralizedMahowaldLift M R) (hn : 0 ≤ n)
    (x : R.T ⟶ (unboundedExtensionSSData f degree (s,1)).V)
    (y : R.T ⟶ (unboundedExtensionSSData f degree (s+n,0)).V)
    (hx : UnboundedExtensionIsLift f degree s 1 L.representative x)
    (hy : UnboundedExtensionIsLift f degree (s+n) 0 R.targetLift y) :
    DifferentialRelation (ExtensionSpectralSequence f degree) n (s,1) x y := by
  exact unboundedDifferentialRelation_of_ambient_map f degree n hn s (s+n) rfl
    L.representative R.targetLift hx hy L.ambient_map

end MaySmashBoundaryInput

end

end KIPBase.Synthetic
