/-
  KIPBase.Synthetic.ExtensionSS
  §4 Synthetic extension spectral sequences.

  A synthetic f-ESS is the extension spectral sequence of the filtered
  two-term complex

      π_{*,*} X →[f] π_{*,*} Y,

  where both terms carry their synthetic Adams filtrations.  The actual
  spectral sequence is supplied by `ExtensionSpectralSequence`; the bounded
  API is retained separately. This file packages the synthetic Adams
  convergence data needed to apply these constructions.
-/
import KIPBase.Synthetic.Adams
import KIPBase.Synthetic.LambdaBoundary
import KIPBase.Synthetic.Rigidity
import KIPBase.SpectralSequence.BoundedExtension
import KIPBase.SpectralSequence.ExtensionAbutment
import KIPBase.SpectralSequence.Exactness
import Mathlib.Algebra.Category.Grp.Subobject

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  KIPBase.SpectralSequence

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/- 无界塔在小宇宙阿贝尔群上会把宽极限指标提升到 `Type 1`。
Mathlib 只直接注册同层宇宙的良幂实例；这里由 `Small` 的宇宙提升
补出证明，不改变对象、态射或谱序列数据。 -/
noncomputable local instance addCommGrpWellPoweredOne :
    WellPowered.{1} AddCommGrpCat.{0} where
  subobject_small := fun _ => by infer_instance

/-- The standard reindexing for the synthetic Adams spectral sequence:
`(s,t,w)` detects Adams filtration `s` in `π_{t-s,w}`. -/
def syntheticAdamsReindex : ℤ × ℤ × ℤ → ℤ × (ℤ × ℤ)
  | (s, t, w) => (s, (t - s, w))

/-- The synthetic Adams tridegree corresponding to filtration `s` and a
fixed abutment bidegree `(stem, weight)`. -/
def syntheticAdamsIndex (s : ℤ) (degree : ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (s, degree.1 + s, degree.2)

/-- Tridegree of a length-`r` synthetic extension differential. -/
def syntheticESSDiffDegree (r : ℤ) : ℤ × ℤ × ℤ :=
  (r, r, 0)

@[simp] theorem syntheticAdamsReindex_index (s : ℤ) (degree : ℤ × ℤ) :
    syntheticAdamsReindex (syntheticAdamsIndex s degree) = (s, degree) := by
  rcases degree with ⟨stem, weight⟩
  simp [syntheticAdamsReindex, syntheticAdamsIndex]

/-- Raising the ESS filtration by `r` at fixed stem and weight raises both
synthetic Adams coordinates `s` and `t` by `r` and preserves `w`. -/
theorem syntheticAdamsIndex_add (s r : ℤ) (degree : ℤ × ℤ) :
    syntheticAdamsIndex (s + r) degree =
      syntheticAdamsIndex s degree + syntheticESSDiffDegree r := by
  rcases degree with ⟨stem, weight⟩
  simp [syntheticAdamsIndex, syntheticESSDiffDegree, add_assoc, add_left_comm]

/-- Data required to form the synthetic extension spectral sequence of a
weight-preserving map `f : X ⟶ Y`, before imposing boundedness.

The two convergence structures identify the synthetic Adams `E∞`-pages
with the associated gradeds of the Adams filtrations.  The convergence
morphism says that the map on bigraded homotopy groups preserves those
filtrations and agrees on associated gradeds with the map induced by `f` on
synthetic Adams spectral sequences.

A morphism in `Syn` has bidegree `(0,0)`, so its induced map is
weight-preserving.  The `source_reindex` and `target_reindex` fields record
that neither convergence witness changes the weight coordinate. -/
structure SyntheticExtensionCoreData {X Y : Syn} (f : X ⟶ Y) where
  sourceAbutment : ℤ × ℤ → AddCommGrpCat.{0}
  targetAbutment : ℤ × ℤ → AddCommGrpCat.{0}
  sourceFiltration : Filtration sourceAbutment
  targetFiltration : Filtration targetAbutment
  sourceConvergence :
    Convergence (SynAdamsSS Syn X) sourceAbutment sourceFiltration
  targetConvergence :
    Convergence (SynAdamsSS Syn Y) targetAbutment targetFiltration
  source_reindex : sourceConvergence.reindex = syntheticAdamsReindex
  target_reindex : targetConvergence.reindex = syntheticAdamsReindex
  convergenceMap : ConvergenceMorphism sourceConvergence targetConvergence
  eMap_eq : convergenceMap.eMap =
    (synAdamsSS_functorial (Syn := Syn) f).eInftyMap

/-- Data for the older bounded construction.  These two bounds are not used
by the unbounded extension spectral sequence. -/
structure SyntheticExtensionData {X Y : Syn} (f : X ⟶ Y)
    extends SyntheticExtensionCoreData f where
  source_bounded : sourceFiltration.IsBounded
  target_bounded : targetFiltration.IsBounded

namespace SyntheticExtensionCoreData

variable {X Y : Syn} {f : X ⟶ Y}

/-- The unbounded synthetic extension spectral sequence. -/
noncomputable def ess (data : SyntheticExtensionCoreData f)
    (degree : ℤ × ℤ) : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  ExtensionSpectralSequence.{1, 0, 0, 0} data.convergenceMap degree

@[simp]
theorem ess_r₀ (data : SyntheticExtensionCoreData f) (degree : ℤ × ℤ) :
    (data.ess degree).r₀ = 0 :=
  rfl

@[simp]
theorem ess_diffDeg (data : SyntheticExtensionCoreData f)
    (degree : ℤ × ℤ) (r : ℤ) :
    (data.ess degree).diffDeg r = (r, -1) :=
  rfl

/-- The actual zeroth page in the source column of the unbounded ESS is
the source associated graded. No bounded extension data is used. -/
noncomputable def e0SourceIsoAssociatedGraded (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    (data.ess degree).Page 0 (s, 1) ≅
      data.sourceFiltration.associatedGraded s degree := by
  have hV : (unboundedUnderlyingComplex data.convergenceMap degree).assocGraded s 1 =
      data.sourceFiltration.associatedGraded s degree := by
    simp only [unboundedUnderlyingComplex, underlyingComplex,
      FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
    congr 1
  exact extensionE0IsoAssociatedGraded.{1, 0, 0, 0}
    data.convergenceMap degree s 1 ≪≫ eqToIso hV

/-- The actual zeroth page in the target column of the unbounded ESS is
the target associated graded. -/
noncomputable def e0TargetIsoAssociatedGraded (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    (data.ess degree).Page 0 (s, 0) ≅
      data.targetFiltration.associatedGraded s degree := by
  have hV : (unboundedUnderlyingComplex data.convergenceMap degree).assocGraded s 0 =
      data.targetFiltration.associatedGraded s degree := by
    simp only [unboundedUnderlyingComplex, underlyingComplex,
      FilteredComplex.assocGraded, Filtration.associatedGraded, twoTermFil]
    congr 1
  exact extensionE0IsoAssociatedGraded.{1, 0, 0, 0}
    data.convergenceMap degree s 0 ≪≫ eqToIso hV

/-- The source column of the unbounded ESS starts with the source Adams
limiting page, at the standard Adams tridegree. -/
noncomputable def e0SourceIso (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    (data.ess degree).Page 0 (s, 1) ≅
      ((SynAdamsSS Syn X).ssData (syntheticAdamsIndex s degree)).eInfty := by
  have hindex : data.sourceConvergence.reindex (syntheticAdamsIndex s degree) =
      (s, degree) := by
    rw [data.source_reindex, syntheticAdamsReindex_index]
  let e := data.sourceConvergence.iso (syntheticAdamsIndex s degree)
  rw [hindex] at e
  exact data.e0SourceIsoAssociatedGraded s degree ≪≫ e.symm

/-- The target column of the unbounded ESS starts with the target Adams
limiting page, at the standard Adams tridegree. -/
noncomputable def e0TargetIso (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    (data.ess degree).Page 0 (s, 0) ≅
      ((SynAdamsSS Syn Y).ssData (syntheticAdamsIndex s degree)).eInfty := by
  have hindex : data.targetConvergence.reindex (syntheticAdamsIndex s degree) =
      (s, degree) := by
    rw [data.target_reindex, syntheticAdamsReindex_index]
  let e := data.targetConvergence.iso (syntheticAdamsIndex s degree)
  rw [hindex] at e
  exact data.e0TargetIsoAssociatedGraded s degree ≪≫ e.symm

/-- The two columns of the actual zeroth page of the unbounded synthetic
`f`-ESS. -/
noncomputable def e0Page (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  (data.ess degree).Page 0 (s, 1) ⊞ (data.ess degree).Page 0 (s, 0)

/-- The corresponding direct sum of source and target Adams `E∞` terms. -/
noncomputable def eInftySum (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  ((SynAdamsSS Syn X).ssData (syntheticAdamsIndex s degree)).eInfty ⊞
    ((SynAdamsSS Syn Y).ssData (syntheticAdamsIndex s degree)).eInfty

/-- The complete zeroth-page comparison for the unbounded synthetic
extension spectral sequence. -/
noncomputable def e0PageIso (data : SyntheticExtensionCoreData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Page s degree ≅ data.eInftySum s degree :=
  biprod.mapIso (data.e0SourceIso s degree) (data.e0TargetIso s degree)

end SyntheticExtensionCoreData

/-- The canonical unbounded extension data attached to an actual map of
synthetic spectra.  Its filtered abutment map is the map supplied by coherent
synthetic Adams convergence, hence is postcomposition by `f` on represented
homotopy groups. -/
noncomputable def syntheticExtensionCoreDataOfMap {X Y : Syn} (f : X ⟶ Y) :
    SyntheticExtensionCoreData f where
  sourceAbutment := (synAdamsConvergence Syn X).abutment
  targetAbutment := (synAdamsConvergence Syn Y).abutment
  sourceFiltration := (synAdamsConvergence Syn X).filtration
  targetFiltration := (synAdamsConvergence Syn Y).filtration
  sourceConvergence := (synAdamsConvergence Syn X).convergence
  targetConvergence := (synAdamsConvergence Syn Y).convergence
  source_reindex := (synAdamsConvergence Syn X).reindex_eq
  target_reindex := (synAdamsConvergence Syn Y).reindex_eq
  convergenceMap := (synAdamsFunctoriality Syn).convergenceMap f
  eMap_eq := (synAdamsFunctoriality Syn).eMap_eq f

/-- On actual represented homotopy classes, the abutment map in the
canonical extension data is postcomposition by the original map. -/
theorem syntheticExtensionCoreDataOfMap_abutment_naturality
    {X Y : Syn} (f : X ⟶ Y) (degree : ℤ × ℤ)
    (a : (syntheticExtensionCoreDataOfMap f).sourceAbutment degree) :
    (synAdamsConvergence Syn Y).abutmentEquiv degree
        ((((syntheticExtensionCoreDataOfMap f).convergenceMap.aMap degree).hom a)) =
      (synAdamsConvergence Syn X).abutmentEquiv degree a ≫ f :=
  (synAdamsFunctoriality Syn).abutment_naturality f degree a

/-- The synthetic Adams spectral sequence together with its canonical
homotopy abutment and Adams filtration. -/
noncomputable def synAdamsConvergingSS (X : Syn) :
    ConvergingSS (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ) (ℤ × ℤ) where
  E := SynAdamsSS Syn X
  A := (synAdamsConvergence Syn X).abutment
  F := (synAdamsConvergence Syn X).filtration
  conv := (synAdamsConvergence Syn X).convergence

/-- The morphism of canonically converging synthetic Adams spectral
sequences induced by an actual map of synthetic spectra. -/
noncomputable def synAdamsConvergingMap {X Y : Syn} (f : X ⟶ Y) :
    synAdamsConvergingSS X ⟶ synAdamsConvergingSS Y :=
  (synAdamsFunctoriality Syn).convergenceMap f

namespace SyntheticExtensionData

variable {X Y : Syn} {f : X ⟶ Y}

/-- At a fixed abutment bidegree, the source convergence reindexing sends the
corresponding synthetic Adams tridegree back to that filtration and bidegree. -/
theorem source_reindex_index (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.sourceConvergence.reindex (syntheticAdamsIndex s degree) = (s, degree) := by
  rw [data.source_reindex]
  exact syntheticAdamsReindex_index s degree

/-- Target analogue of `source_reindex_index`. -/
theorem target_reindex_index (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.targetConvergence.reindex (syntheticAdamsIndex s degree) = (s, degree) := by
  rw [data.target_reindex]
  exact syntheticAdamsReindex_index s degree

/-- The chosen convergence morphism uses exactly the `E∞` map induced by the
original synthetic map `f`. -/
theorem eMap_eq_at (data : SyntheticExtensionData f)
    (index : ℤ × ℤ × ℤ) :
    data.convergenceMap.eMap index =
      (synAdamsSS_functorial (Syn := Syn) f).eInftyMap index :=
  congrFun data.eMap_eq index

/-- The bounded extension data underlying the synthetic `f`-ESS. -/
noncomputable def extension (data : SyntheticExtensionData f) :
    BoundedExtensionSS data.sourceConvergence data.targetConvergence
      data.convergenceMap data.source_bounded data.target_bounded :=
  BoundedExtensionSS.mk' _ _ _ _ _

/-- The synthetic `f`-extension spectral sequence in a fixed homotopy
bidegree `(stem, weight)`.  Its internal bidegree is `(s,k)`, where `s` is
Adams filtration and `k = 1,0` denotes respectively the source and target of
the two-term complex. -/
noncomputable def ess (data : SyntheticExtensionData f) (degree : ℤ × ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  data.extension.ess degree

/-- The synthetic `f`-ESS in a fixed weight. -/
noncomputable def essAtWeight (data : SyntheticExtensionData f)
    (weight stem : ℤ) : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  data.ess (stem, weight)

/-- A page differential in the fixed-weight synthetic ESS. -/
noncomputable def essDiffAtWeight (data : SyntheticExtensionData f)
    (weight stem r : ℤ) (k : ℤ × ℤ) :
    (data.essAtWeight weight stem).Page r k ⟶
      (data.essAtWeight weight stem).Page r
        (k + (data.essAtWeight weight stem).diffDeg r) :=
  data.extension.essDiff (stem, weight) r k

/-- The image object of a fixed-weight synthetic ESS differential. -/
noncomputable def essBoundaryAtWeight (data : SyntheticExtensionData f)
    (weight stem r : ℤ) (k : ℤ × ℤ) : AddCommGrpCat.{0} :=
  data.extension.essBoundary (stem, weight) r k

/-- Essentiality of a fixed-weight synthetic extension. -/
abbrev HasExtensionAtWeight (data : SyntheticExtensionData f)
    (weight stem r : ℤ) (k : ℤ × ℤ) : Prop :=
  HasFExtension data.extension (stem, weight) r k

/-- The underlying filtered two-term complex
`π_{*,*}X →[f] π_{*,*}Y` in a fixed homotopy bidegree. -/
noncomputable def complex (data : SyntheticExtensionData f) (degree : ℤ × ℤ) :
    FilteredComplex (AddCommGrpCat.{0}) :=
  data.extension.complex degree

/-- The `E₀` source term of the synthetic `f`-ESS. -/
noncomputable def e0Source (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  data.extension.e0PageAtOne degree s

/-- The `E₀` target term of the synthetic `f`-ESS. -/
noncomputable def e0Target (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  data.extension.e0PageAtZero degree s

/-- The source synthetic Adams `E∞`-term corresponding to filtration `s` and
the fixed homotopy bidegree `degree = (stem, weight)`. -/
noncomputable def sourceEInfty (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  ((SynAdamsSS Syn X).ssData (syntheticAdamsIndex s degree)).eInfty

/-- The target synthetic Adams `E∞`-term corresponding to filtration `s` and
the fixed homotopy bidegree `degree = (stem, weight)`. -/
noncomputable def targetEInfty (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  ((SynAdamsSS Syn Y).ssData (syntheticAdamsIndex s degree)).eInfty

/-- The source summand of the synthetic `f`-ESS `E₀`-page is the source
synthetic Adams `E∞`-term. -/
noncomputable def e0SourceIso (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Source s degree ≅ data.sourceEInfty s degree := by
  let index := syntheticAdamsIndex s degree
  have hpage : data.e0Source s degree =
      data.sourceFiltration.associatedGraded s degree :=
    data.extension.e0PageAtOne_eq degree s
  have hgraded : data.sourceFiltration.associatedGraded s degree =
      data.sourceFiltration.associatedGraded
        (data.sourceConvergence.reindex index).1
        (data.sourceConvergence.reindex index).2 := by
    rw [data.source_reindex]
    simp [index]
  exact eqToIso hpage ≪≫ eqToIso hgraded ≪≫
    (data.sourceConvergence.iso index).symm

/-- The target summand of the synthetic `f`-ESS `E₀`-page is the target
synthetic Adams `E∞`-term. -/
noncomputable def e0TargetIso (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Target s degree ≅ data.targetEInfty s degree := by
  let index := syntheticAdamsIndex s degree
  have hpage : data.e0Target s degree =
      data.targetFiltration.associatedGraded s degree :=
    data.extension.e0PageAtZero_eq degree s
  have hgraded : data.targetFiltration.associatedGraded s degree =
      data.targetFiltration.associatedGraded
        (data.targetConvergence.reindex index).1
        (data.targetConvergence.reindex index).2 := by
    rw [data.target_reindex]
    simp [index]
  exact eqToIso hpage ≪≫ eqToIso hgraded ≪≫
    (data.targetConvergence.iso index).symm

/-- The total `E₀` object of the synthetic `f`-ESS, obtained by combining the
source complex degree `1` and target complex degree `0`. -/
noncomputable def e0Page (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  data.e0Source s degree ⊞ data.e0Target s degree

/-- The direct sum of the source and target synthetic Adams `E∞`-terms. -/
noncomputable def eInftySum (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) : AddCommGrpCat.{0} :=
  data.sourceEInfty s degree ⊞ data.targetEInfty s degree

/-- Blueprint §4, `def:synthetic-extension-ss`:

`{}^f E₀^{s,t,w} ≅ E∞^{s,t,w}(X) ⊕ E∞^{s,t,w}(Y)`.

Here `degree = (t-s,w)`, so `syntheticAdamsIndex s degree = (s,t,w)`. -/
noncomputable def e0PageIso (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Page s degree ≅ data.eInftySum s degree :=
  biprod.mapIso (data.e0SourceIso s degree) (data.e0TargetIso s degree)

/-- The `d₀` component is the associated-graded map induced by `f`. -/
noncomputable def d0 (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Source s degree ⟶ data.e0Target s degree :=
  data.extension.d0 degree s

/-- The synthetic ESS `d₀` is the associated-graded map of the filtered
homotopy map induced by `f`. -/
theorem d0_eq_inducedAssocGradedMap (data : SyntheticExtensionData f)
    (s : ℤ) (degree : ℤ × ℤ) :
    data.d0 s degree =
      eqToHom (data.extension.e0PageAtOne_eq degree s) ≫
        Filtration.inducedAssocGradedMap
          data.convergenceMap.aMap data.convergenceMap.filtration_compat s degree ≫
        eqToHom (data.extension.e0PageAtZero_eq degree s).symm :=
  data.extension.d0_eq_inducedAssocGradedMap degree s

/-- The filtered-complex construction gives ESS differentials of bidegree
`(r,-1)`: filtration rises by `r` and the two-term complex degree drops from
the source side to the target side.  After restoring the fixed stem and
weight, this is the blueprint tridegree `(s,t,w) ↦ (s+r,t+r,w)`. -/
theorem ess_diffDeg (data : SyntheticExtensionData f)
    (degree : ℤ × ℤ) (r : ℤ) :
    (data.ess degree).diffDeg r = (r, -1) :=
  rfl

/-- Fixing a weight does not alter the ESS differential degree. -/
theorem essAtWeight_diffDeg (data : SyntheticExtensionData f)
    (weight stem r : ℤ) :
    (data.essAtWeight weight stem).diffDeg r = (r, -1) :=
  rfl

/-- Trigraded form of `ess_diffDeg`: a length-`r` extension differential has
degree `(r,r,0)`, hence preserves synthetic weight. -/
theorem ess_tridegree (data : SyntheticExtensionData f)
    (s r : ℤ) (degree : ℤ × ℤ) :
    syntheticAdamsIndex (s + r) degree =
      syntheticAdamsIndex s degree + syntheticESSDiffDegree r :=
  syntheticAdamsIndex_add s r degree

end SyntheticExtensionData

/-! ### Multiplication by λ -/

/-- Convergence-and-detection data for the extension spectral sequence of
multiplication by `λ^n : Σ^{0,-n}X ⟶ X`. -/
abbrev LambdaExtensionData (X : Syn) (n : ℕ) :=
  SyntheticExtensionData (lambdaPow n X)

/-- The synthetic `λ^n`-extension spectral sequence in bidegree
`(stem, weight)`.  This is the first specialization of the general synthetic
`f`-ESS requested in Blueprint §4. -/
noncomputable def lambdaESS (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (degree : ℤ × ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  data.ess degree

/-- The `d₀` component of the `λ^n`-ESS.  By construction it is the map
on associated graded Adams filtrations induced by multiplication by `λ^n`;
the later comparison theorem may identify it explicitly with `λ^n`. -/
noncomputable def lambdaESSd0 (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s : ℤ) (degree : ℤ × ℤ) :
    data.e0Source s degree ⟶ data.e0Target s degree :=
  data.d0 s degree

/-- In the `λ^n`-ESS, `d₀` is the associated-graded map induced by
multiplication by `λ^n`. -/
theorem lambdaESSd0_eq_inducedAssocGradedMap (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s : ℤ) (degree : ℤ × ℤ) :
    lambdaESSd0 X n data s degree =
      eqToHom (data.extension.e0PageAtOne_eq degree s) ≫
        Filtration.inducedAssocGradedMap
          data.convergenceMap.aMap data.convergenceMap.filtration_compat s degree ≫
        eqToHom (data.extension.e0PageAtZero_eq degree s).symm :=
  data.d0_eq_inducedAssocGradedMap s degree

/-- Concrete `E∞` formula underlying the zeroth differential of the
`λ^n`-ESS.  Conjugating the actual `E∞` map induced by
`λ^n : Σ^{0,-n}X ⟶ X` by the two convergence isomorphisms gives exactly the
map on associated gradeds.  Together with
`lambdaESSd0_eq_inducedAssocGradedMap`, this identifies the ESS `d₀`
without leaving its grading transports implicit. -/
theorem lambdaESS_lambdaPow_eInftyMap_formula (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s : ℤ) (degree : ℤ × ℤ) :
    let k := syntheticAdamsIndex s degree
    (data.sourceConvergence.iso k).inv ≫
        (synAdamsSS_functorial (Syn := Syn) (lambdaPow n X)).eInftyMap k ≫
        (data.targetConvergence.iso k).hom ≫
        data.targetFiltration.transportGraded
          (congrFun data.convergenceMap.reindex_eq k).symm =
      Filtration.inducedAssocGradedMap
        data.convergenceMap.aMap data.convergenceMap.filtration_compat
        (data.sourceConvergence.reindex k).1
        (data.sourceConvergence.reindex k).2 := by
  dsimp only
  let k := syntheticAdamsIndex s degree
  have hcompat := data.convergenceMap.iso_compat k
  rw [data.eMap_eq_at k] at hcompat
  have h := congrArg
    (fun f => (data.sourceConvergence.iso k).inv ≫ f) hcompat
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The total `E₀` object of the synthetic `λ^n`-ESS. -/
noncomputable def lambdaESSE0 (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s : ℤ) (degree : ℤ × ℤ) :
    AddCommGrpCat.{0} :=
  data.e0Page s degree

/-- The Blueprint `E₀` identification specialized to multiplication by
`λ^n : Σ^{0,-n}X ⟶ X`. -/
noncomputable def lambdaESSE0Iso (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s : ℤ) (degree : ℤ × ℤ) :
    lambdaESSE0 X n data s degree ≅ data.eInftySum s degree :=
  data.e0PageIso s degree

/-- Fully expanded zeroth-page formula for multiplication by `λ^n`:
the source summand is the synthetic Adams `E∞`-term of `Σ^{0,-n}X`, and
the target summand is the `E∞`-term of `X`, both in the tridegree selected
by the fixed homotopy bidegree and Adams filtration. -/
noncomputable def lambdaESSE0ConcreteIso (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s : ℤ) (degree : ℤ × ℤ) :
    lambdaESSE0 X n data s degree ≅
      ((SynAdamsSS Syn
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)).ssData
          (syntheticAdamsIndex s degree)).eInfty ⊞
      ((SynAdamsSS Syn X).ssData
        (syntheticAdamsIndex s degree)).eInfty :=
  data.e0PageIso s degree

/-- Trigraded form of the concrete zeroth-page formula:
`{}^{λ^n}E₀^{s,t,w} ≅ E∞^{s,t,w}(Σ^{0,-n}X) ⊕ E∞^{s,t,w}(X)`. -/
noncomputable def lambdaESSE0TrigradedIso (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (s t w : ℤ) :
    lambdaESSE0 X n data s (t - s, w) ≅
      ((SynAdamsSS Syn
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)).ssData
          (s, t, w)).eInfty ⊞
      ((SynAdamsSS Syn X).ssData (s, t, w)).eInfty := by
  have hindex : syntheticAdamsIndex s (t - s, w) = (s, t, w) := by
    ext <;> simp [syntheticAdamsIndex]
  exact lambdaESSE0ConcreteIso X n data s (t - s, w) ≪≫
    biprod.mapIso
      (eqToIso (congrArg
        (fun k => ((SynAdamsSS Syn
          ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)).ssData k).eInfty)
        hindex))
      (eqToIso (congrArg
        (fun k => ((SynAdamsSS Syn X).ssData k).eInfty) hindex))

theorem lambdaESS_diffDeg (X : Syn) (n : ℕ)
    (data : LambdaExtensionData X n) (degree : ℤ × ℤ) (r : ℤ) :
    (lambdaESS X n data degree).diffDeg r = (r, -1) :=
  rfl

/-! ### Boundary ESSs for finite λ powers -/

/-- Convergence data for the boundary of the cofiber of `λ^n`. -/
abbrev LambdaPowerBocksteinData (X : Syn) (n : ℕ) :=
  SyntheticExtensionCoreData
    (syn_functorial_cofiber.cofibδ (lambdaPow n X))

/-- The canonical extension data for the boundary
`X/λ^n ⟶ Σ(Σ^{0,-n}X)`. -/
noncomputable def canonicalLambdaPowerBocksteinData (X : Syn) (n : ℕ) :
    LambdaPowerBocksteinData X n :=
  syntheticExtensionCoreDataOfMap
    (syn_functorial_cofiber.cofibδ (lambdaPow n X))

/-- The boundary ESS attached to the cofiber of `λ^n`.  It is the filtered
two-term ESS of the actual cofiber boundary, with its raw page numbering. -/
noncomputable def canonicalLambdaPowerBocksteinESS (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  (canonicalLambdaPowerBocksteinData X n).ess degree

/-- The three canonically converging Adams spectral sequences in the exact
cofiber segment for `λ^n`. -/
noncomputable abbrev lambdaPowerBocksteinSourceCSS (X : Syn) (n : ℕ) :=
  synAdamsConvergingSS (XModLambdaN X n)

noncomputable abbrev lambdaPowerBocksteinTargetCSS (X : Syn) (n : ℕ) :=
  synAdamsConvergingSS
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X))

noncomputable abbrev lambdaPowerBocksteinAfterCSS (X : Syn) :=
  synAdamsConvergingSS
    ((shiftFunctor Syn (1 : ℤ)).obj ((𝟭 Syn).obj X))

noncomputable abbrev lambdaPowerBocksteinCSSMap (X : Syn) (n : ℕ) :
    lambdaPowerBocksteinSourceCSS X n ⟶
      lambdaPowerBocksteinTargetCSS X n :=
  synAdamsConvergingMap
    (syn_functorial_cofiber.cofibδ (lambdaPow n X))

noncomputable abbrev lambdaPowerBocksteinShiftLambdaCSSMap
    (X : Syn) (n : ℕ) :
    lambdaPowerBocksteinTargetCSS X n ⟶
      lambdaPowerBocksteinAfterCSS X :=
  synAdamsConvergingMap
    ((shiftFunctor Syn (1 : ℤ)).map (lambdaPow n X))

/-- The finite-quotient restriction square on every actual Adams page.
All four maps are induced by maps of synthetic spectra, so the square
inherits the common cycle and boundary data of Adams functoriality. -/
theorem lambdaPowerBockstein_toOne_page_square (X : Syn) (n : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    synAdamsPageMap (XModLambdaN.toOne X n) r k ≫
        synAdamsPageMap (syn_functorial_cofiber.cofibδ (lambdaPow 1 X)) r k =
      synAdamsPageMap (syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) X)) r k ≫
        synAdamsPageMap
          ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n)) r k := by
  exact (synAdamsPageMap_comp (XModLambdaN.toOne X n)
    (syn_functorial_cofiber.cofibδ (lambdaPow 1 X)) r k).symm.trans
      ((congrArg (fun f => synAdamsPageMap f r k)
        (XModLambdaN.toOne_boundary X n)).trans
          (synAdamsPageMap_comp
            (syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) X))
            ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n)) r k))

/-- The canonical quotient maps and the constructed restriction also
commute on every Adams page. -/
theorem lambdaPowerBockstein_toOne_incl_page (X : Syn) (n : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    synAdamsPageMap (syn_functorial_cofiber.cofibι (lambdaPow (n + 1) X)) r k ≫
        synAdamsPageMap (XModLambdaN.toOne X n) r k =
      synAdamsPageMap (syn_functorial_cofiber.cofibι (lambdaPow 1 X)) r k := by
  exact (synAdamsPageMap_comp
    (syn_functorial_cofiber.cofibι (lambdaPow (n + 1) X))
    (XModLambdaN.toOne X n) r k).symm.trans
      (congrArg (fun f => synAdamsPageMap f r k) (XModLambdaN.incl_toOne X n))

/-- The same square holds for the actual filtered abutment maps that
define the boundary ESSs, not merely for associated graded groups. -/
theorem lambdaPowerBockstein_toOne_abutment_square (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    (synAdamsConvergingMap (XModLambdaN.toOne X n)).aMap degree ≫
        (lambdaPowerBocksteinCSSMap X 1).aMap degree =
      (lambdaPowerBocksteinCSSMap X (n + 1)).aMap degree ≫
        (synAdamsConvergingMap
          ((shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n))).aMap degree := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ((synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -1)).obj X))).abutmentEquiv degree).injective
  let F := synAdamsFunctoriality Syn
  let ρ := XModLambdaN.toOne X n
  let δ₁ := syn_functorial_cofiber.cofibδ (lambdaPow 1 X)
  let δn := syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) X)
  let l := (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n)
  have hρ := F.abutment_naturality ρ degree a
  have hδ₁ := F.abutment_naturality δ₁ degree
    (((F.convergenceMap ρ).aMap degree).hom a)
  have hδn := F.abutment_naturality δn degree a
  have hl := F.abutment_naturality l degree
    (((F.convergenceMap δn).aMap degree).hom a)
  have hboundary := LambdaPowerBoundary.boundaryHom_toOne
    (Smn degree.1 degree.2) X n
    ((synAdamsConvergence Syn (XModLambdaN X (n + 1))).abutmentEquiv degree a)
  exact (hδ₁.trans (congrArg (fun b => b ≫ δ₁) hρ)).trans
    (hboundary.trans (hl.trans (congrArg (fun b => b ≫ l) hδn)).symm)

/-- Reducing a finite-quotient representative preserves its Adams
filtration, as required when placing it in the source of the λ-boundary
ESS. -/
theorem lambdaPowerBockstein_toOne_preserves_filtration (X : Syn) (n : ℕ)
    (m w s : ℤ) (a : Smn (Syn := Syn) m w ⟶ XModLambdaN X (n + 1))
    (ha : a ∈ synAdamsFiltration Syn (XModLambdaN X (n + 1)) m w s) :
    a ≫ XModLambdaN.toOne X n ∈
      synAdamsFiltration Syn (XModLambdaN X 1) m w s :=
  synAdamsFiltration_postcomp (XModLambdaN.toOne X n) m w s a ha

/-- The canonical Adams abutment maps induced by the cofiber boundary of
`λ^n` and suspended multiplication by `λ^n` are exact. -/
theorem lambdaPowerBockstein_abutment_exact (X : Syn) (n : ℕ)
    (degree : ℤ × ℤ) :
    AbutmentExactAt
      (lambdaPowerBocksteinSourceCSS X n)
      (lambdaPowerBocksteinTargetCSS X n)
      (lambdaPowerBocksteinAfterCSS X)
      (lambdaPowerBocksteinCSSMap X n)
      (lambdaPowerBocksteinShiftLambdaCSSMap X n)
      degree := by
  let source := synAdamsConvergence Syn (XModLambdaN X n)
  let middle := synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X))
  let target := synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj ((𝟭 Syn).obj X))
  let boundary : XModLambdaN X n ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X) :=
    syn_functorial_cofiber.cofibδ (lambdaPow n X)
  let shiftedLambda :
      (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X) ⟶
        (shiftFunctor Syn (1 : ℤ)).obj ((𝟭 Syn).obj X) :=
    (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n X)
  let f := (synAdamsFunctoriality Syn).convergenceMap boundary
  let g := (synAdamsFunctoriality Syn).convergenceMap shiftedLambda
  have htriangle : Triangle.mk (lambdaPow n X)
      (syn_functorial_cofiber.cofibι (lambdaPow n X)) boundary ∈
        distTriang Syn :=
    XModLambdaN.triangle_distinguished X n
  have hboundary : boundary ≫ shiftedLambda = 0 := by
    exact comp_distTriang_mor_zero₃₁ _ htriangle
  have hfg : f.aMap degree ≫ g.aMap degree = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply (target.abutmentEquiv degree).injective
    let aActual := (synAdamsConvergence Syn
      (XModLambdaN X n)).abutmentEquiv degree a
    have hf := (synAdamsFunctoriality Syn).abutment_naturality
      boundary degree a
    change middle.abutmentEquiv degree ((f.aMap degree).hom a) =
      aActual ≫ boundary at hf
    have hg := (synAdamsFunctoriality Syn).abutment_naturality
      shiftedLambda degree ((f.aMap degree).hom a)
    change target.abutmentEquiv degree
        ((g.aMap degree).hom ((f.aMap degree).hom a)) =
      middle.abutmentEquiv degree ((f.aMap degree).hom a) ≫
        shiftedLambda at hg
    calc
      target.abutmentEquiv degree
          ((g.aMap degree).hom ((f.aMap degree).hom a)) =
          middle.abutmentEquiv degree ((f.aMap degree).hom a) ≫
            shiftedLambda := hg
      _ = (aActual ≫ boundary) ≫
          shiftedLambda := by rw [hf]
      _ = 0 := by rw [Category.assoc, hboundary, comp_zero]
      _ = target.abutmentEquiv degree 0 :=
        (target.abutmentEquiv degree).map_zero.symm
  refine ⟨hfg, ?_⟩
  change (ShortComplex.mk (f.aMap degree) (g.aMap degree) hfg).Exact
  apply (ShortComplex.ab_exact_iff_range_eq_ker).2
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change (g.aMap degree).hom ((f.aMap degree).hom a) = 0
    have h := congrArg (fun q => q.hom a) hfg
    simpa only [AddCommGrpCat.coe_comp, Function.comp_apply,
      AddCommGrpCat.zero_apply] using h
  · intro hb
    rw [AddMonoidHom.mem_ker] at hb
    have hactual : middle.abutmentEquiv degree b ≫ shiftedLambda = 0 := by
      have hnat := (synAdamsFunctoriality Syn).abutment_naturality
        shiftedLambda degree b
      change target.abutmentEquiv degree ((g.aMap degree).hom b) =
        middle.abutmentEquiv degree b ≫ shiftedLambda at hnat
      calc
        middle.abutmentEquiv degree b ≫ shiftedLambda =
            target.abutmentEquiv degree ((g.aMap degree).hom b) := hnat.symm
        _ = target.abutmentEquiv degree 0 :=
          congrArg (target.abutmentEquiv degree) hb
        _ = 0 := (target.abutmentEquiv degree).map_zero
    obtain ⟨aActual, haActual⟩ :=
      Triangle.coyoneda_exact₁ _ htriangle
        (middle.abutmentEquiv degree b) hactual
    let a : source.abutment degree :=
      (source.abutmentEquiv degree).symm aActual
    refine ⟨a, ?_⟩
    apply (middle.abutmentEquiv degree).injective
    have hnat := (synAdamsFunctoriality Syn).abutment_naturality
      boundary degree a
    change middle.abutmentEquiv degree ((f.aMap degree).hom a) =
      source.abutmentEquiv degree a ≫ boundary at hnat
    calc
      middle.abutmentEquiv degree ((f.aMap degree).hom a) =
          source.abutmentEquiv degree a ≫ boundary := hnat
      _ = aActual ≫ boundary := by
        exact congrArg (fun q => q ≫ boundary)
          ((source.abutmentEquiv degree).apply_symm_apply aActual)
      _ = middle.abutmentEquiv degree b := haActual.symm

/-- A target limiting class together with a representative annihilated by
suspended multiplication by `λ^n`.  This is the precise representative
hypothesis used by the exact-sequence theorem for the boundary ESS. -/
abbrev LambdaPowerBocksteinPermanentRepresentative
    (X : Syn) (n : ℕ) (degree : ℤ × ℤ) (s : ℤ)
    {T : AddCommGrpCat.{0}}
    (y : T ⟶ ((lambdaPowerBocksteinTargetCSS X n).E.ssData
      ((lambdaPowerBocksteinTargetCSS X n).conv.reindexEquiv.symm
        (s, degree))).eInfty) : Prop :=
  ∃ yl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinTargetCSS X n).F.F s degree),
    (unboundedUnderlyingComplex
        (lambdaPowerBocksteinShiftLambdaCSSMap X n) degree).IsLift s 1 yl
      (y ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinShiftLambdaCSSMap X n) degree s 1).hom) ∧
    (yl ≫ ((lambdaPowerBocksteinTargetCSS X n).F.F s degree).arrow) ≫
        (lambdaPowerBocksteinShiftLambdaCSSMap X n).aMap degree = 0

/-- The zeroth source column of the `λ^(r-1)` boundary ESS is the `r`-page
of synthetic Adams on `νX`, at the diagonal generator.  The comparison is
the composite of convergence, finite-quotient stabilization, and the
inverse of the actual quotient page map. -/
noncomputable def canonicalLambdaPowerBocksteinE0SourceIsoSynAdamsPage
    (𝒮 : Type*) [StableHomotopy.StableHomotopyCategory 𝒮] (X : 𝒮)
    (r : ℕ) (hr : 2 ≤ r) (s t : ℤ) :
    (canonicalLambdaPowerBocksteinESS ((nu 𝒮 Syn).obj X) (r - 1)
      (t - s, t)).Page 0 (s, 1) ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s, t, t) := by
  let e := (canonicalLambdaPowerBocksteinData
    ((nu 𝒮 Syn).obj X) (r - 1)).e0SourceIso s (t - s, t)
  have hindex : syntheticAdamsIndex s (t - s, t) = (s, t, t) := by
    ext <;> simp [syntheticAdamsIndex]
  exact e ≪≫ eqToIso (congrArg
    (fun k => ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (r - 1))).ssData k).eInfty) hindex) ≪≫
    nuModLambdaPredGeneratorEInftyIsoPage 𝒮 Syn X r hr s t

/-- Successor-indexed form of the finite-quotient source comparison.  It
avoids transports through `(n+2)-1 = n+1` in later naturality statements. -/
noncomputable def canonicalLambdaPowerSuccBocksteinE0SourceIsoSynAdamsPage
    (𝒮 : Type*) [StableHomotopy.StableHomotopyCategory 𝒮] (X : 𝒮)
    (n : ℕ) (s t : ℤ) :
    (canonicalLambdaPowerBocksteinESS ((nu 𝒮 Syn).obj X) (n + 1)
      (t - s, t)).Page 0 (s, 1) ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page ((n + 2 : ℕ) : ℤ)
        (s, t, t) := by
  let e := (canonicalLambdaPowerBocksteinData
    ((nu 𝒮 Syn).obj X) (n + 1)).e0SourceIso s (t - s, t)
  have hindex : syntheticAdamsIndex s (t - s, t) = (s, t, t) := by
    ext <;> simp [syntheticAdamsIndex]
  exact e ≪≫ eqToIso (congrArg
    (fun k => ((SynAdamsSS Syn
      (XModLambdaN ((nu 𝒮 Syn).obj X) (n + 1))).ssData k).eInfty) hindex) ≪≫
    nuModLambdaSuccGeneratorEInftyIsoPage 𝒮 Syn X n s t

/-! ### The λ-Bockstein spectral sequence -/

/-- Convergence data for the extension spectral sequence induced by the
λ-boundary map.  No boundedness field occurs in this structure. -/
abbrev LambdaBocksteinData (X : Syn) :=
  SyntheticExtensionCoreData (lambdaBocksteinConnecting X)

/-- The canonical λ-Bockstein extension data.  Its abutment map is the
actual boundary in the λ cofiber triangle. -/
noncomputable def canonicalLambdaBocksteinData (X : Syn) :
    LambdaBocksteinData X :=
  syntheticExtensionCoreDataOfMap (lambdaBocksteinConnecting X)

/-- The finite-power construction at exponent one is the canonical
λ-Bockstein data. -/
@[simp] theorem canonicalLambdaPowerBocksteinData_one (X : Syn) :
    canonicalLambdaPowerBocksteinData X 1 =
      canonicalLambdaBocksteinData X :=
  rfl

/-- The filtered map underlying the canonical λ-Bockstein ESS is the actual
λ-boundary on represented homotopy groups. -/
theorem canonicalLambdaBocksteinData_abutment_naturality
    (X : Syn) (degree : ℤ × ℤ)
    (a : (canonicalLambdaBocksteinData X).sourceAbutment degree) :
    (synAdamsConvergence Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X))).abutmentEquiv degree
      ((((canonicalLambdaBocksteinData X).convergenceMap.aMap degree).hom a)) =
    (synAdamsConvergence Syn (XModLambdaN X 1)).abutmentEquiv degree a ≫
      lambdaBocksteinConnecting X :=
  syntheticExtensionCoreDataOfMap_abutment_naturality
    (lambdaBocksteinConnecting X) degree a

/-- The three canonically converging Adams spectral sequences in the exact
λ-Bockstein segment. -/
noncomputable abbrev lambdaBocksteinSourceCSS (X : Syn) :=
  synAdamsConvergingSS (XModLambdaN X 1)

noncomputable abbrev lambdaBocksteinTargetCSS (X : Syn) :=
  synAdamsConvergingSS
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X))

noncomputable abbrev lambdaBocksteinAfterCSS (X : Syn) :=
  synAdamsConvergingSS
    ((shiftFunctor Syn (1 : ℤ)).obj ((𝟭 Syn).obj X))

/-- The λ-boundary and the following suspended λ map as morphisms of
canonically converging Adams spectral sequences. -/
noncomputable abbrev lambdaBocksteinCSSMap (X : Syn) :
    lambdaBocksteinSourceCSS X ⟶ lambdaBocksteinTargetCSS X :=
  synAdamsConvergingMap (lambdaBocksteinConnecting X)

noncomputable abbrev lambdaBocksteinShiftLambdaCSSMap (X : Syn) :
    lambdaBocksteinTargetCSS X ⟶ lambdaBocksteinAfterCSS X :=
  synAdamsConvergingMap
    ((shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X))

/-- On canonical Adams abutments, the λ-boundary followed by suspended λ is
an exact pair.  This is the represented-Hom long exact sequence of the
λ-cofiber triangle, transported through the canonical convergence
equivalences. -/
theorem lambdaBockstein_abutment_exact (X : Syn) (degree : ℤ × ℤ) :
    AbutmentExactAt
      (synAdamsConvergingSS (XModLambdaN X 1))
      (synAdamsConvergingSS
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X)))
      (synAdamsConvergingSS
        ((shiftFunctor Syn (1 : ℤ)).obj ((𝟭 Syn).obj X)))
      (synAdamsConvergingMap (lambdaBocksteinConnecting X))
      (synAdamsConvergingMap
        ((shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X)))
      degree := by
  let source := synAdamsConvergence Syn (XModLambdaN X 1)
  let middle := synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, (-1 : ℤ))).obj X))
  let target := synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj ((𝟭 Syn).obj X))
  let f := (synAdamsFunctoriality Syn).convergenceMap
    (lambdaBocksteinConnecting X)
  let g := (synAdamsFunctoriality Syn).convergenceMap
    ((shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X))
  have hfg : f.aMap degree ≫ g.aMap degree = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    apply (target.abutmentEquiv degree).injective
    have hf := (synAdamsFunctoriality Syn).abutment_naturality
      (lambdaBocksteinConnecting X) degree a
    have hg := (synAdamsFunctoriality Syn).abutment_naturality
      ((shiftFunctor Syn (1 : ℤ)).map (SyntheticCategory.lam.app X))
      degree ((f.aMap degree).hom a)
    calc
      target.abutmentEquiv degree
          ((g.aMap degree).hom ((f.aMap degree).hom a)) =
          middle.abutmentEquiv degree ((f.aMap degree).hom a) ≫
            (shiftFunctor Syn (1 : ℤ)).map
              (SyntheticCategory.lam.app X) := hg
      _ = (source.abutmentEquiv degree a ≫
            lambdaBocksteinConnecting X) ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (SyntheticCategory.lam.app X) := by rw [hf]
      _ = 0 := by
        rw [Category.assoc,
          lambdaBockstein_connecting_comp_shift_lambda, comp_zero]
      _ = target.abutmentEquiv degree 0 :=
        (target.abutmentEquiv degree).map_zero.symm
  refine ⟨hfg, ?_⟩
  change (ShortComplex.mk (f.aMap degree) (g.aMap degree) hfg).Exact
  apply (ShortComplex.ab_exact_iff_range_eq_ker).2
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change (g.aMap degree).hom ((f.aMap degree).hom a) = 0
    have h := congrArg (fun q => q.hom a) hfg
    simpa only [AddCommGrpCat.coe_comp, Function.comp_apply,
      AddCommGrpCat.zero_apply] using h
  · intro hb
    rw [AddMonoidHom.mem_ker] at hb
    have hactual :
        middle.abutmentEquiv degree b ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (SyntheticCategory.lam.app X) = 0 := by
      have hnat := (synAdamsFunctoriality Syn).abutment_naturality
        ((shiftFunctor Syn (1 : ℤ)).map
          (SyntheticCategory.lam.app X)) degree b
      calc
        middle.abutmentEquiv degree b ≫
            (shiftFunctor Syn (1 : ℤ)).map
              (SyntheticCategory.lam.app X) =
            target.abutmentEquiv degree ((g.aMap degree).hom b) := hnat.symm
        _ = target.abutmentEquiv degree 0 := by rw [hb]
        _ = 0 := (target.abutmentEquiv degree).map_zero
    obtain ⟨aActual, haActual⟩ :=
      (lambdaBocksteinHomMap_range_iff
        (Smn (Syn := Syn) degree.1 degree.2) X
        (middle.abutmentEquiv degree b)).2 hactual
    let a : source.abutment degree :=
      (source.abutmentEquiv degree).symm aActual
    refine ⟨a, ?_⟩
    apply (middle.abutmentEquiv degree).injective
    have hnat := (synAdamsFunctoriality Syn).abutment_naturality
      (lambdaBocksteinConnecting X) degree a
    calc
      middle.abutmentEquiv degree ((f.aMap degree).hom a) =
          source.abutmentEquiv degree a ≫ lambdaBocksteinConnecting X := hnat
      _ = aActual ≫ lambdaBocksteinConnecting X := by
        exact congrArg (fun q => q ≫ lambdaBocksteinConnecting X)
          ((source.abutmentEquiv degree).apply_symm_apply aActual)
      _ = middle.abutmentEquiv degree b := haActual

/-- The raw extension spectral sequence of the λ-boundary
`X/λ ⟶ Σ^{1,-1}X`, with the ESS's original numbering starting at zero.
Identifying its pages with synthetic Adams pages requires a comparison of
the initial terms and the induced differentials; no renumbering is applied
by this definition. -/
noncomputable def lambdaBocksteinESS (X : Syn)
    (data : LambdaBocksteinData X) (degree : ℤ × ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  data.ess degree

/-- The canonical λ-Bockstein ESS, with no independently chosen convergence
or filtered abutment map. -/
noncomputable def canonicalLambdaBocksteinESS (X : Syn)
    (degree : ℤ × ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  lambdaBocksteinESS X (canonicalLambdaBocksteinData X) degree

/-- The exponent-one finite-power boundary ESS is definitionally the
canonical λ-Bockstein ESS. -/
@[simp] theorem canonicalLambdaPowerBocksteinESS_one (X : Syn)
    (degree : ℤ × ℤ) :
    canonicalLambdaPowerBocksteinESS X 1 degree =
      canonicalLambdaBocksteinESS X degree :=
  rfl

/-- A representative of a class in the middle term of the λ-cofiber exact
sequence, expressed in the small universe in which synthetic homotopy groups
live.  The first condition says that `yl` detects `y`; the second says that
its image under suspended λ is zero. -/
def LambdaBocksteinPermanentRepresentative
    (X : Syn) (degree : ℤ × ℤ) (s : ℤ)
    {T : AddCommGrpCat.{0}}
    (y : T ⟶ ((lambdaBocksteinTargetCSS X).E.ssData
      ((lambdaBocksteinTargetCSS X).conv.reindexEquiv.symm
        (s, degree))).eInfty) : Prop :=
  ∃ yl : T ⟶ Subobject.underlying.obj
      ((lambdaBocksteinTargetCSS X).F.F s degree),
    (unboundedUnderlyingComplex
        (lambdaBocksteinShiftLambdaCSSMap X) degree).IsLift s 1 yl
      (y ≫ (unboundedExtensionVComplexIso
        (lambdaBocksteinShiftLambdaCSSMap X) degree s 1).hom) ∧
    (yl ≫ ((lambdaBocksteinTargetCSS X).F.F s degree).arrow) ≫
        (lambdaBocksteinShiftLambdaCSSMap X).aMap degree = 0

/-- Small-universe specialization of the representative-to-differential
step in the ESS exact-sequence theorem.  It is stated here because the
general theorem currently ties the indexing universe for wide limits to the
object universe of the category, whereas synthetic homotopy groups use
`AddCommGrpCat.{0}`. -/
private theorem lambdaPowerBocksteinDifferentialRelation_of_lift
    (X : Syn) (q : ℕ) (degree : ℤ × ℤ)
    (r : ℤ) (hr : 0 ≤ r) (u k : ℤ) {T : AddCommGrpCat.{0}}
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree (u, k)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree (u + r, k - 1)).V}
    {xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).fil u k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).fil (u + r) (k - 1))}
    (hx : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).IsLift u k xl
      (x ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X q) degree u k).hom))
    (hy : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).IsLift (u + r) (k - 1) yl
      (y ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X q) degree (u + r) (k - 1)).hom))
    (hd : xl ≫ (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).filDiff u k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil (u + r) (k - 1))
        ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil u (k - 1))
        ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil_anti_of_le (k - 1) (by omega))) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (lambdaPowerBocksteinCSSMap X q) degree)
      r (u, k) x y := by
  classical
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  let f := lambdaPowerBocksteinCSSMap X q
  let FC := unboundedUnderlyingComplex f degree
  let xC : T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily.{1, 0, 0, 0}
        f degree (u, k)).Z
        (n : WithTop ℕ)) :=
    unboundedComplexSourceCycleLift.{1, 0, 0, 0} f degree u k n hd
  let yC : T ⟶ Subobject.underlying.obj
      ((unboundedComplexSSDataFamily.{1, 0, 0, 0} f degree
        (u + (n : ℤ), k - 1)).Z (n : WithTop ℕ)) :=
    unboundedComplexTargetCycleLift.{1, 0, 0, 0} f degree u k n hd
  let xZ := xC ≫
    (unboundedExtensionZIso.{1, 0, 0, 0}
      f degree (u, k) (n : WithTop ℕ)).inv
  let yZ := yC ≫
    (unboundedExtensionZIso.{1, 0, 0, 0} f degree
      (u + (n : ℤ), k - 1) (n : WithTop ℕ)).inv
  unfold DifferentialRelation
  dsimp only [ExtensionSpectralSequence_r₀, sub_zero,
    Int.toNat_natCast, ExtensionSpectralSequence_diffDeg]
  refine ⟨xZ, ?_, yZ, ?_, ?_⟩
  · change xZ ≫ ((unboundedExtensionSSData.{1, 0, 0, 0}
        f degree (u, k)).Z
        (n : WithTop ℕ)).arrow = x
    have hxC : xC ≫ ((unboundedComplexSSDataFamily.{1, 0, 0, 0} f degree
        (u, k)).Z (n : WithTop ℕ)).arrow =
        x ≫ (unboundedSSDataForward.{1, 0, 0, 0} f degree).φ
          (u, k) := by
      dsimp only [xC]
      rw [unboundedComplexSourceCycleLift_arrow.{1, 0, 0, 0}]
      change xl ≫ FC.filToAssocGraded u k =
        x ≫ (unboundedSSDataForward.{1, 0, 0, 0} f degree).φ
          (u, k) at hx
      exact hx
    have hback := (unboundedSSDataBackward.{1, 0, 0, 0}
      f degree).preserves_Z
      (u, k) (n : WithTop ℕ) |>.choose_spec
    have hcancel : (unboundedSSDataForward.{1, 0, 0, 0}
          f degree).φ (u, k) ≫
        (unboundedSSDataBackward.{1, 0, 0, 0}
          f degree).φ (u, k) =
        𝟙 ((unboundedExtensionSSData.{1, 0, 0, 0}
          f degree (u, k)).V) := by
      change (unboundedExtensionVComplexIso.{1, 0, 0}
          f degree u k).hom ≫
        (unboundedExtensionVComplexIso.{1, 0, 0}
          f degree u k).inv = 𝟙 _
      exact (unboundedExtensionVComplexIso.{1, 0, 0}
        f degree u k).hom_inv_id
    dsimp only [xZ, unboundedExtensionZIso]
    rw [Category.assoc, hback, ← Category.assoc, hxC,
      Category.assoc, hcancel, Category.comp_id]
  · change yZ ≫ ((unboundedExtensionSSData.{1, 0, 0, 0} f degree
        (u + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow = y
    have hyC : yC ≫ ((unboundedComplexSSDataFamily.{1, 0, 0, 0} f degree
        (u + (n : ℤ), k - 1)).Z (n : WithTop ℕ)).arrow =
        y ≫ (unboundedSSDataForward.{1, 0, 0, 0} f degree).φ
          (u + (n : ℤ), k - 1) := by
      dsimp only [yC]
      rw [unboundedComplexTargetCycleLift_arrow.{1, 0, 0, 0}]
      change yl ≫ FC.filToAssocGraded (u + (n : ℤ)) (k - 1) =
        y ≫ (unboundedSSDataForward.{1, 0, 0, 0} f degree).φ
          (u + (n : ℤ), k - 1) at hy
      exact hy
    have hback := (unboundedSSDataBackward.{1, 0, 0, 0}
      f degree).preserves_Z
      (u + (n : ℤ), k - 1) (n : WithTop ℕ) |>.choose_spec
    have hcancel : (unboundedSSDataForward.{1, 0, 0, 0} f degree).φ
          (u + (n : ℤ), k - 1) ≫
        (unboundedSSDataBackward.{1, 0, 0, 0} f degree).φ
          (u + (n : ℤ), k - 1) =
        𝟙 ((unboundedExtensionSSData.{1, 0, 0, 0} f degree
          (u + (n : ℤ), k - 1)).V) := by
      change (unboundedExtensionVComplexIso.{1, 0, 0} f degree
          (u + (n : ℤ)) (k - 1)).hom ≫
        (unboundedExtensionVComplexIso.{1, 0, 0} f degree
          (u + (n : ℤ)) (k - 1)).inv = 𝟙 _
      exact (unboundedExtensionVComplexIso.{1, 0, 0} f degree
        (u + (n : ℤ)) (k - 1)).hom_inv_id
    dsimp only [yZ, unboundedExtensionZIso]
    rw [Category.assoc, hback, ← Category.assoc, hyC,
      Category.assoc, hcancel, Category.comp_id]
  · rw [ExtensionSpectralSequence_d_nat]
    change xZ ≫ (unboundedExtensionSSData.{1, 0, 0, 0} f degree
        (u, k)).pageπ (n : WithTop ℕ) ≫
        unboundedExtensionDifferential.{1, 0, 0, 0} f degree u k n =
      yZ ≫ (unboundedExtensionSSData.{1, 0, 0, 0} f degree
        (u + (n : ℤ), k - 1)).pageπ (n : WithTop ℕ)
    dsimp only [xZ, yZ]
    simp only [Category.assoc]
    rw [← Category.assoc
        (unboundedExtensionZIso.{1, 0, 0, 0}
          f degree (u, k) (n : WithTop ℕ)).inv,
      unboundedExtensionZIso_inv_pageπ_nat,
      unboundedExtensionDifferential]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [unboundedExtensionZIso_inv_pageπ_nat]
    apply (cancel_mono (unboundedExtensionPageIso.{1, 0, 0, 0} f degree
      (u + (n : ℤ), k - 1) n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change xC ≫ FC.finitePageπ u k n ≫
        FC.finitePageDifferential u k n =
      yC ≫ FC.finitePageπ (u + (n : ℤ)) (k - 1) n
    dsimp only [xC, yC]
    exact FC.finitePageDifferential_of_lift u k n hd

/-- The preceding representative calculation with the target filtration
index written independently. -/
private theorem lambdaPowerBocksteinDifferentialRelation_of_lift_at_target
    (X : Syn) (q : ℕ) (degree : ℤ × ℤ)
    (r : ℤ) (hr : 0 ≤ r) (u s k : ℤ)
    (hus : u + r = s)
    {T : AddCommGrpCat.{0}}
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree (u, k)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree (s, k - 1)).V}
    {xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).fil u k)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).fil s (k - 1))}
    (hx : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).IsLift u k xl
      (x ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X q) degree u k).hom))
    (hy : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).IsLift s (k - 1) yl
      (y ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X q) degree s (k - 1)).hom))
    (hd : xl ≫ (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).filDiff u k =
      yl ≫ Subobject.ofLE
        ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil s (k - 1))
        ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil u (k - 1))
        (by rw [← hus]
            exact (unboundedUnderlyingComplex
              (lambdaPowerBocksteinCSSMap X q) degree).fil_anti_of_le
                (k - 1) (by omega))) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (lambdaPowerBocksteinCSSMap X q) degree)
      r (u, k) x
      (Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
        (show
          ((ExtensionSpectralSequence.{1, 0, 0, 0}
              (lambdaPowerBocksteinCSSMap X q) degree).ssData
            ((u, k) +
              (ExtensionSpectralSequence.{1, 0, 0, 0}
                (lambdaPowerBocksteinCSSMap X q) degree).diffDeg r)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              (lambdaPowerBocksteinCSSMap X q) degree (s, k - 1)).V by
            rw [ExtensionSpectralSequence_diffDeg, ← hus]
            rfl)) y) := by
  subst s
  exact lambdaPowerBocksteinDifferentialRelation_of_lift
    X q degree r hr u k hx hy hd

/- 正合列形式的代表元引理。目标复形次数固定为 `0`，这正是两项复形
中次数 `1` 的微分所到达的次数。 -/
private theorem lambdaPowerBocksteinDifferentialRelation_of_ambient_map_at_target
    (X : Syn) (q : ℕ) (degree : ℤ × ℤ)
    (r : ℤ) (hr : 0 ≤ r) (u s : ℤ)
    (hus : u + r = s)
    {T : AddCommGrpCat.{0}}
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree (u, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree (s, 0)).V}
    {xl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).fil u 1)}
    {yl : T ⟶ Subobject.underlying.obj
      ((unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).fil s 0)}
    (hx : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).IsLift u 1 xl
      (x ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X q) degree u 1).hom))
    (hy : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X q) degree).IsLift s 0 yl
      (y ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X q) degree s 0).hom))
    (ha : xl ≫ ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil u 1).arrow ≫
        (unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).d 1 =
      yl ≫ ((unboundedUnderlyingComplex
          (lambdaPowerBocksteinCSSMap X q) degree).fil s 0).arrow) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (lambdaPowerBocksteinCSSMap X q) degree)
      r (u, 1) x
      (Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
        (show
          ((ExtensionSpectralSequence.{1, 0, 0, 0}
              (lambdaPowerBocksteinCSSMap X q) degree).ssData
            ((u, 1) +
              (ExtensionSpectralSequence.{1, 0, 0, 0}
                (lambdaPowerBocksteinCSSMap X q) degree).diffDeg r)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              (lambdaPowerBocksteinCSSMap X q) degree (s, 0)).V by
            rw [ExtensionSpectralSequence_diffDeg, ← hus]
            norm_num)) y) := by
  subst s
  let f := lambdaPowerBocksteinCSSMap X q
  let FC := unboundedUnderlyingComplex f degree
  let yFC : T ⟶ unboundedExtensionV
      (lambdaPowerBocksteinSourceCSS X q).conv
      (lambdaPowerBocksteinTargetCSS X q).conv degree (u + r, 1 - 1) := y
  let ylFC : T ⟶ Subobject.underlying.obj (FC.fil (u + r) (1 - 1)) := yl
  have hyFC : FC.IsLift (u + r) (1 - 1) ylFC
      (yFC ≫ (unboundedExtensionVComplexIso f degree
        (u + r) (1 - 1)).hom) := by
    exact hy
  have haFC : xl ≫ (FC.fil u 1).arrow ≫ FC.d 1 =
      ylFC ≫ (FC.fil (u + r) (1 - 1)).arrow := by
    exact ha
  have hdiff := FC.filDiff_comp_arrow u 1
  have hd : xl ≫ FC.filDiff u 1 =
      ylFC ≫ Subobject.ofLE
        (FC.fil (u + r) (1 - 1)) (FC.fil u (1 - 1))
        (FC.fil_anti_of_le (1 - 1) (by omega)) := by
    apply (cancel_mono (FC.fil u (1 - 1)).arrow).mp
    simpa only [Category.assoc, hdiff, Subobject.ofLE_arrow] using haFC
  change DifferentialRelation
    (ExtensionSpectralSequence.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X q) degree) r (u, 1) x y
  simpa only [yFC] using
    (lambdaPowerBocksteinDifferentialRelation_of_lift
      X q degree r hr u 1 hx hyFC hd)

/-- A fixed-source, fixed-page boundary ESS relation, computed using the
actual cofiber boundary on homotopy representatives. The source and target
classes and their filtration degrees are given, rather than chosen by an
existence argument. No exhaustiveness or boundedness is needed.

This is a representative formula for the boundary ESS. To compare it with
an Adams differential one still has to produce these representatives from
that Adams differential and prove survival on the specified page. -/
theorem lambdaPowerBockstein_relation_of_homotopy_boundary
    (X : Syn) (n : ℕ) (degree : ℤ × ℤ)
    (r : ℤ) (hr : 0 ≤ r) (u s : ℤ) (hus : u + r = s)
    {T : AddCommGrpCat.{0}}
    {x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (u, 1)).V}
    {y : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      (lambdaPowerBocksteinCSSMap X n) degree (s, 0)).V}
    {xl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinSourceCSS X n).F.F u degree)}
    {yl : T ⟶ Subobject.underlying.obj
      ((lambdaPowerBocksteinTargetCSS X n).F.F s degree)}
    (hx : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X n) degree).IsLift u 1 xl
      (x ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X n) degree u 1).hom))
    (hy : (unboundedUnderlyingComplex
        (lambdaPowerBocksteinCSSMap X n) degree).IsLift s 0 yl
      (y ≫ (unboundedExtensionVComplexIso
        (lambdaPowerBocksteinCSSMap X n) degree s 0).hom))
    (hboundary : ∀ a : T,
      LambdaPowerBoundary.boundaryHom (Smn degree.1 degree.2) X n
        ((synAdamsConvergence Syn (XModLambdaN X n)).abutmentEquiv degree
          (((lambdaPowerBocksteinSourceCSS X n).F.F u degree).arrow.hom
            (xl.hom a))) =
      (synAdamsConvergence Syn
        ((shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X))).abutmentEquiv
        degree (((lambdaPowerBocksteinTargetCSS X n).F.F s degree).arrow.hom
          (yl.hom a))) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1, 0, 0, 0}
        (lambdaPowerBocksteinCSSMap X n) degree) r (u, 1) x
      (Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
        (show
          ((ExtensionSpectralSequence.{1, 0, 0, 0}
              (lambdaPowerBocksteinCSSMap X n) degree).ssData
            ((u, 1) +
              (ExtensionSpectralSequence.{1, 0, 0, 0}
                (lambdaPowerBocksteinCSSMap X n) degree).diffDeg r)).V =
            (unboundedExtensionSSData.{1, 0, 0, 0}
              (lambdaPowerBocksteinCSSMap X n) degree (s, 0)).V by
            rw [ExtensionSpectralSequence_diffDeg, ← hus]
            norm_num)) y) := by
  apply lambdaPowerBocksteinDifferentialRelation_of_ambient_map_at_target
    X n degree r hr u s hus hx hy
  let f := lambdaPowerBocksteinCSSMap X n
  let FC := unboundedUnderlyingComplex f degree
  have hmap : FC.d 1 = f.aMap degree := by
    simp [FC, unboundedUnderlyingComplex, underlyingComplex,
      twoTermDiff, twoTermObj]
  change xl ≫ (FC.fil u 1).arrow ≫ FC.d 1 = yl ≫ (FC.fil s 0).arrow
  rw [hmap]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply ((synAdamsConvergence Syn
    ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X))).abutmentEquiv
        degree).injective
  exact ((synAdamsFunctoriality Syn).abutment_naturality
    (syn_functorial_cofiber.cofibδ (lambdaPow n X)) degree
    (((lambdaPowerBocksteinSourceCSS X n).F.F u degree).arrow.hom
      (xl.hom a))).trans (hboundary a)

/-- Capping a specified relative source constructs an element of the actual
boundary ESS abutment complex. The map defining that ESS sends it to the
specified divided boundary included from the deeper stage. This is a
homotopy-representative statement; identifying its Adams page classes still
requires the geometric realization of the Adams differential. -/
theorem lambdaPowerBockstein_exists_capped_abutment {A Y : Syn}
    (j : Y ⟶ A) (n : ℕ) (degree : ℤ × ℤ)
    (x : Smn degree.1 degree.2 ⟶ syn_functorial_cofiber.cofib j)
    (y : Smn degree.1 degree.2 ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj Y))
    (hxy : x ≫ syn_functorial_cofiber.cofibδ j =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n Y)) :
    ∃ (c : Smn degree.1 degree.2 ⟶ LambdaCofiberGeometry.commonCone j n)
      (z : (lambdaPowerBocksteinSourceCSS A n).A degree),
      c ≫ LambdaCofiberGeometry.toRelative j n = x ∧
      c ≫ LambdaCofiberGeometry.toQuotient j n =
        (synAdamsConvergence Syn (XModLambdaN A n)).abutmentEquiv degree z ∧
      ((lambdaPowerBocksteinCSSMap A n).aMap degree).hom z =
        ((synAdamsConvergence Syn
          ((shiftFunctor Syn (1 : ℤ)).obj
            ((SyntheticCategory.biShift (0, -(n : ℤ))).obj A))).abutmentEquiv
              degree).symm
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            ((SyntheticCategory.biShift (0, -(n : ℤ))).map j)) := by
  obtain ⟨c, z, hx, hz, _, hb⟩ :=
    LambdaCofiberGeometry.exists_cap_of_relative_boundary j n x y hxy
  refine ⟨c, ((synAdamsConvergence Syn (XModLambdaN A n)).abutmentEquiv
    degree).symm z, hx, ?_, ?_⟩
  · rw [AddEquiv.apply_symm_apply]
    exact hz
  · apply ((synAdamsConvergence Syn
      ((shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj A))).abutmentEquiv
          degree).injective
    rw [AddEquiv.apply_symm_apply]
    exact ((synAdamsFunctoriality Syn).abutment_naturality
      (X := XModLambdaN A n)
      (syn_functorial_cofiber.cofibδ (lambdaPow n A)) degree _).trans (by
        rw [AddEquiv.apply_symm_apply]
        exact hb)

/-- Existence of a boundary ESS relation from cofiber exactness. The source
class and its filtration degree are existentially chosen; in particular the
relation may represent zero on its page. This theorem does not identify a
specified Adams differential or assert essentiality.

The source filtration is assumed exhaustive at one layer in the fixed
bidegree. -/
theorem lambdaPowerBockstein_differential_formula
    (X : Syn) (n : ℕ) (degree : ℤ × ℤ)
    (hsource : ∃ u₀ : ℤ,
      (lambdaPowerBocksteinSourceCSS X n).F.F u₀ degree = ⊤)
    (s : ℤ) {T : AddCommGrpCat.{0}} [Projective T]
    (y : T ⟶ ((lambdaPowerBocksteinTargetCSS X n).E.ssData
      ((lambdaPowerBocksteinTargetCSS X n).conv.reindexEquiv.symm
        (s, degree))).eInfty)
    (hy : LambdaPowerBocksteinPermanentRepresentative X n degree s y) :
    ∃ (u : ℤ) (_hu : u ≤ s)
      (x : T ⟶ ((lambdaPowerBocksteinSourceCSS X n).E.ssData
        ((lambdaPowerBocksteinSourceCSS X n).conv.reindexEquiv.symm
          (u, degree))).eInfty),
      DifferentialRelation
        (ExtensionSpectralSequence.{1, 0, 0, 0}
          (lambdaPowerBocksteinCSSMap X n) degree)
        (s - u) (u, 1) x
        (Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
          (show
            ((ExtensionSpectralSequence.{1, 0, 0, 0}
                (lambdaPowerBocksteinCSSMap X n) degree).ssData
              ((u, 1) +
                (ExtensionSpectralSequence.{1, 0, 0, 0}
                  (lambdaPowerBocksteinCSSMap X n) degree).diffDeg
                    (s - u))).V =
              (unboundedExtensionSSData.{1, 0, 0, 0}
                (lambdaPowerBocksteinCSSMap X n) degree (s, 0)).V by
              have hus : u + (s - u) = s := by omega
              rw [ExtensionSpectralSequence_diffDeg]
              simp only [Prod.mk_add_mk, hus]
              rfl)) y) := by
  classical
  let V₁ := lambdaPowerBocksteinSourceCSS X n
  let V₂ := lambdaPowerBocksteinTargetCSS X n
  let V₃ := lambdaPowerBocksteinAfterCSS X
  let f := lambdaPowerBocksteinCSSMap X n
  let g := lambdaPowerBocksteinShiftLambdaCSSMap X n
  rcases hy with ⟨yl, hyl, hyg⟩
  have hylf : (unboundedUnderlyingComplex f degree).IsLift s 0 yl
      (y ≫ (unboundedExtensionVComplexIso f degree s 0).hom) := by
    unfold FilteredComplex.IsLift at hyl ⊢
    rw [unboundedExtensionVComplexIso_target_source_hom_eq f g degree s]
    exact hyl
  rcases lambdaPowerBockstein_abutment_exact X n degree with ⟨hfg, hex⟩
  let yA : T ⟶ V₂.A degree := yl ≫ (V₂.F.F s degree).arrow
  have hyA_zero : yA ≫ g.aMap degree = 0 := hyg
  have hker : (kernelSubobject (g.aMap degree)).Factors yA :=
    kernelSubobject_factors (g.aMap degree) yA hyA_zero
  have himage : imageSubobject (f.aMap degree) =
      kernelSubobject (g.aMap degree) :=
    (ShortComplex.exact_iff_image_eq_kernel _).1 hex
  have himageFactor : (imageSubobject (f.aMap degree)).Factors yA := by
    rw [himage]
    exact hker
  let yI := (imageSubobject (f.aMap degree)).factorThru yA himageFactor
  let xA := Projective.factorThru yI
    (factorThruImageSubobject (f.aMap degree))
  have hxA : xA ≫ f.aMap degree = yA := by
    calc
      xA ≫ f.aMap degree =
          (xA ≫ factorThruImageSubobject (f.aMap degree)) ≫
            (imageSubobject (f.aMap degree)).arrow := by
              rw [Category.assoc, imageSubobject_arrow_comp]
      _ = yI ≫ (imageSubobject (f.aMap degree)).arrow := by
            rw [Projective.factorThru_comp]
      _ = yA :=
        (imageSubobject (f.aMap degree)).factorThru_arrow yA himageFactor
  rcases hsource with ⟨u₀, hu₀⟩
  let u := min u₀ s
  have hu : u ≤ s := min_le_right _ _
  have hutop : V₁.F.F u degree = ⊤ := by
    apply top_unique
    have hle : V₁.F.F u₀ degree ≤ V₁.F.F u degree :=
      V₁.F.mono_of_le (min_le_left _ _) degree
    rwa [hu₀] at hle
  let FC := unboundedUnderlyingComplex f degree
  let ylFC : T ⟶ Subobject.underlying.obj (FC.fil s 0) := yl
  have hylfFC : FC.IsLift s 0 ylFC
      (y ≫ (unboundedExtensionVComplexIso f degree s 0).hom) := hylf
  have hutopFC : FC.fil u 1 = ⊤ := by
    change (lambdaPowerBocksteinSourceCSS X n).F.F u degree = ⊤
    dsimp only [V₁] at hutop
    exact hutop
  have hxAFactor : (FC.fil u 1).Factors xA := by
    rw [hutopFC]
    exact Subobject.top_factors xA
  let xl : T ⟶ Subobject.underlying.obj (FC.fil u 1) :=
    (FC.fil u 1).factorThru xA hxAFactor
  have hxl : xl ≫ (FC.fil u 1).arrow = xA :=
    (FC.fil u 1).factorThru_arrow xA hxAFactor
  let x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      f degree (u, 1)).V :=
    (xl ≫ FC.filToAssocGraded u 1) ≫
      (unboundedExtensionVComplexIso f degree u 1).inv
  have hxlift : FC.IsLift u 1 xl
      (x ≫ (unboundedExtensionVComplexIso f degree u 1).hom) := by
    unfold FilteredComplex.IsLift
    dsimp only [x]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ha : xl ≫ (FC.fil u 1).arrow ≫ f.aMap degree =
      ylFC ≫ (FC.fil s 0).arrow := by
    calc
      xl ≫ (FC.fil u 1).arrow ≫ f.aMap degree =
          xA ≫ f.aMap degree := by
            rw [← Category.assoc, hxl]
      _ = yA := hxA
      _ = ylFC ≫ (FC.fil s 0).arrow := rfl
  have hmap : FC.d 1 = f.aMap degree := by
    simp [FC, unboundedUnderlyingComplex, underlyingComplex,
      twoTermDiff, twoTermObj]
  have haFC : xl ≫ (FC.fil u 1).arrow ≫ FC.d 1 =
      ylFC ≫ (FC.fil s 0).arrow := by
    rw [hmap]
    exact ha
  refine ⟨u, hu, x, ?_⟩
  exact lambdaPowerBocksteinDifferentialRelation_of_ambient_map_at_target
    X n degree (s - u) (by omega) u s (by omega)
    (T := T) (x := x) (y := y) (xl := xl) (yl := ylFC)
    hxlift hylfFC haFC

/-- The `n = 1` boundary-relation existence statement. Exactness produces
some source class and some nonnegative differential length. Neither a
specified Adams source nor nonzero survival on that page is asserted. -/
theorem lambdaBockstein_differential_formula
    (X : Syn) (degree : ℤ × ℤ)
    (hboundedBelow : ∃ u₀ : ℤ,
      (lambdaBocksteinSourceCSS X).F.F u₀ degree = ⊤)
    (s : ℤ) {T : AddCommGrpCat.{0}} [Projective T]
    (y : T ⟶ ((lambdaBocksteinTargetCSS X).E.ssData
      ((lambdaBocksteinTargetCSS X).conv.reindexEquiv.symm
        (s, degree))).eInfty)
    (hy : LambdaBocksteinPermanentRepresentative X degree s y) :
    ∃ (u : ℤ) (_hu : u ≤ s)
      (x : T ⟶ ((lambdaBocksteinSourceCSS X).E.ssData
        ((lambdaBocksteinSourceCSS X).conv.reindexEquiv.symm
          (u, degree))).eInfty),
      DifferentialRelation
        (ExtensionSpectralSequence.{1, 0, 0, 0}
          (lambdaBocksteinCSSMap X) degree)
        (s - u) (u, 1) x
        (Eq.mpr (congrArg (fun A : AddCommGrpCat.{0} => T ⟶ A)
          (show
            ((ExtensionSpectralSequence.{1, 0, 0, 0}
                (lambdaBocksteinCSSMap X) degree).ssData
              ((u, 1) +
                (ExtensionSpectralSequence.{1, 0, 0, 0}
                  (lambdaBocksteinCSSMap X) degree).diffDeg
                    (s - u))).V =
              (unboundedExtensionSSData.{1, 0, 0, 0}
                (lambdaBocksteinCSSMap X) degree (s, 0)).V by
              have hus : u + (s - u) = s := by omega
              rw [ExtensionSpectralSequence_diffDeg]
              simp only [Prod.mk_add_mk, hus]
              rfl)) y) := by
  classical
  let V₁ := lambdaBocksteinSourceCSS X
  let V₂ := lambdaBocksteinTargetCSS X
  let V₃ := lambdaBocksteinAfterCSS X
  let f := lambdaBocksteinCSSMap X
  let g := lambdaBocksteinShiftLambdaCSSMap X
  rcases hy with ⟨yl, hyl, hyg⟩
  have hylf : (unboundedUnderlyingComplex f degree).IsLift s 0 yl
      (y ≫ (unboundedExtensionVComplexIso f degree s 0).hom) := by
    unfold FilteredComplex.IsLift at hyl ⊢
    rw [unboundedExtensionVComplexIso_target_source_hom_eq f g degree s]
    exact hyl
  rcases lambdaBockstein_abutment_exact X degree with ⟨hfg, hex⟩
  let yA : T ⟶ V₂.A degree := yl ≫ (V₂.F.F s degree).arrow
  have hyA_zero : yA ≫ g.aMap degree = 0 := by
    exact hyg
  have hker : (kernelSubobject (g.aMap degree)).Factors yA :=
    kernelSubobject_factors (g.aMap degree) yA hyA_zero
  have himage : imageSubobject (f.aMap degree) =
      kernelSubobject (g.aMap degree) :=
    (ShortComplex.exact_iff_image_eq_kernel _).1 hex
  have himageFactor : (imageSubobject (f.aMap degree)).Factors yA := by
    rw [himage]
    exact hker
  let yI := (imageSubobject (f.aMap degree)).factorThru yA himageFactor
  let xA := Projective.factorThru yI
    (factorThruImageSubobject (f.aMap degree))
  have hxA : xA ≫ f.aMap degree = yA := by
    calc
      xA ≫ f.aMap degree =
          (xA ≫ factorThruImageSubobject (f.aMap degree)) ≫
            (imageSubobject (f.aMap degree)).arrow := by
              rw [Category.assoc, imageSubobject_arrow_comp]
      _ = yI ≫ (imageSubobject (f.aMap degree)).arrow := by
            rw [Projective.factorThru_comp]
      _ = yA :=
        (imageSubobject (f.aMap degree)).factorThru_arrow yA himageFactor
  rcases hboundedBelow with ⟨u₀, hu₀⟩
  let u := min u₀ s
  have hu : u ≤ s := min_le_right _ _
  have hutop : V₁.F.F u degree = ⊤ := by
    apply top_unique
    have hle : V₁.F.F u₀ degree ≤ V₁.F.F u degree :=
      V₁.F.mono_of_le (min_le_left _ _) degree
    rwa [hu₀] at hle
  let FC := unboundedUnderlyingComplex f degree
  let ylFC : T ⟶ Subobject.underlying.obj (FC.fil s 0) := yl
  have hylfFC : FC.IsLift s 0 ylFC
      (y ≫ (unboundedExtensionVComplexIso f degree s 0).hom) := by
    exact hylf
  have hutopFC : FC.fil u 1 = ⊤ := by
    change (lambdaBocksteinSourceCSS X).F.F u degree = ⊤
    dsimp only [V₁] at hutop
    exact hutop
  have hxAFactor : (FC.fil u 1).Factors xA := by
    rw [hutopFC]
    exact Subobject.top_factors xA
  let xl : T ⟶ Subobject.underlying.obj (FC.fil u 1) :=
    (FC.fil u 1).factorThru xA hxAFactor
  have hxl : xl ≫ (FC.fil u 1).arrow = xA := by
    exact (FC.fil u 1).factorThru_arrow xA hxAFactor
  let x : T ⟶ (unboundedExtensionSSData.{1, 0, 0, 0}
      f degree (u, 1)).V :=
    (xl ≫ FC.filToAssocGraded u 1) ≫
      (unboundedExtensionVComplexIso f degree u 1).inv
  have hxlift : FC.IsLift u 1 xl
      (x ≫ (unboundedExtensionVComplexIso f degree u 1).hom) := by
    unfold FilteredComplex.IsLift
    dsimp only [x]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ha : xl ≫ (FC.fil u 1).arrow ≫ f.aMap degree =
      ylFC ≫ (FC.fil s 0).arrow := by
    calc
      xl ≫ (FC.fil u 1).arrow ≫ f.aMap degree =
          xA ≫ f.aMap degree := by
            rw [← Category.assoc, hxl]
      _ = yA := hxA
      _ = ylFC ≫ (FC.fil s 0).arrow := rfl
  have hmap : FC.d 1 = f.aMap degree := by
    simp [FC, unboundedUnderlyingComplex, underlyingComplex,
      twoTermDiff, twoTermObj]
  have haFC : xl ≫ (FC.fil u 1).arrow ≫ FC.d 1 =
      ylFC ≫ (FC.fil s 0).arrow := by
    rw [hmap]
    exact ha
  refine ⟨u, hu, x, ?_⟩
  exact lambdaPowerBocksteinDifferentialRelation_of_ambient_map_at_target
    X 1 degree (s - u) (by omega) u s (by omega)
    (T := T) (x := x) (y := y) (xl := xl) (yl := ylFC)
    hxlift hylfFC haFC

@[simp]
theorem lambdaBocksteinESS_r₀ (X : Syn)
    (data : LambdaBocksteinData X) (degree : ℤ × ℤ) :
    (lambdaBocksteinESS X data degree).r₀ = 0 :=
  rfl

@[simp]
theorem lambdaBocksteinESS_diffDeg (X : Syn)
    (data : LambdaBocksteinData X) (degree : ℤ × ℤ) (r : ℤ) :
    (lambdaBocksteinESS X data degree).diffDeg r = (r, -1) :=
  rfl

/-- The source column on the raw zeroth λ-boundary ESS page identifies
with E₂ of `νX/λ`, by the proved degeneration of the quotient Adams SS.
This does not yet compare the target column or the later ESS differentials. -/
noncomputable def lambdaBocksteinESSSourceE0Iso
    (𝒮 : Type*) [StableHomotopy.StableHomotopyCategory 𝒮] (X : 𝒮)
    (data : LambdaBocksteinData ((nu 𝒮 Syn).obj X))
    (s : ℤ) (degree : ℤ × ℤ) :
    (lambdaBocksteinESS ((nu 𝒮 Syn).obj X) data degree).Page 0 (s, 1) ≅
      (SynAdamsSS Syn (XModLambdaN ((nu 𝒮 Syn).obj X) 1)).Page 2
        (syntheticAdamsIndex s degree) :=
  data.e0SourceIso s degree ≪≫
    synAdams_mod_lambda_one_eInftyIso 𝒮 Syn X (syntheticAdamsIndex s degree)

/-- An affine index matching the formal differential degrees of the boundary
ESS and synthetic Adams at the same integer page. This arithmetic map alone
does not identify their page objects or the shifted abutment degrees. -/
def lambdaBocksteinAdamsIndex (degree : ℤ × ℤ) (sk : ℤ × ℤ) :
    ℤ × ℤ × ℤ :=
  (sk.1, degree.1 + sk.1 + sk.2 - 1, degree.2)

/-- The affine index sends a Bockstein differential of degree `(r,-1)` to
a synthetic Adams differential of degree `(r,r-1,0)`. -/
theorem lambdaBocksteinAdamsIndex_add_diff (degree : ℤ × ℤ)
    (sk : ℤ × ℤ) (r : ℤ) :
    lambdaBocksteinAdamsIndex degree (sk + (r, -1)) =
      lambdaBocksteinAdamsIndex degree sk + (r, r - 1, 0) := by
  rcases degree with ⟨stem, weight⟩
  rcases sk with ⟨s, k⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · dsimp [lambdaBocksteinAdamsIndex]
      omega
    · simp [lambdaBocksteinAdamsIndex]

/-- The homotopy bidegree in which the mod-λ generator of a synthetic Adams
class of bidegree `(s,t)` lives.  Its weight is `t`; lower synthetic weights
are obtained by multiplication by λ. -/
def lambdaBocksteinGeneratorDegree (s t : ℤ) : ℤ × ℤ :=
  (t - s, t)

@[simp] theorem lambdaBocksteinAdamsIndex_generator
    (s t : ℤ) :
    lambdaBocksteinAdamsIndex (lambdaBocksteinGeneratorDegree s t) (s, 1) =
      (s, t, t) := by
  ext <;> simp [lambdaBocksteinAdamsIndex,
    lambdaBocksteinGeneratorDegree]

/-- Lowering the weight of the diagonal generator by the indicated power of
`λ` gives the requested synthetic Adams tridegree. -/
theorem lambdaBocksteinGenerator_lambdaIndex
    (s t w : ℤ) (hw : w ≤ t) :
    SynAdamsLambdaModule.lambdaIndex (t - w).toNat (s, t, t) =
      (s, t, w) := by
  rw [SynAdamsLambdaModule.lambdaIndex_eq]
  have hcast : ((t - w).toNat : ℤ) = t - w := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hw)
  rw [hcast]
  ext <;> dsimp <;> omega

/-- The affine image of a length-`r` λ-Bockstein target has exactly the
synthetic Adams target tridegree. -/
theorem lambdaBocksteinAdamsIndex_differentialTarget
    (s t r : ℤ) :
    lambdaBocksteinAdamsIndex (lambdaBocksteinGeneratorDegree s t)
        ((s, 1) + (r, -1)) =
      (s + r, t + r - 1, t) := by
  rw [lambdaBocksteinAdamsIndex_add_diff,
    lambdaBocksteinAdamsIndex_generator]
  ext <;> dsimp <;> omega

/-- For `r ≥ 1`, the formal Adams target index is the target diagonal
generator lowered by `λ^(r-1)`. This only describes
`lambdaBocksteinAdamsIndex`; removing the actual boundary suspension raises
weight by one, as recorded by `LambdaPowerBoundary.targetHomEquiv`.
Consequently the actual boundary target at filtration `s+r` has exponent
`r-2`, and one more λ-step gives this formal Adams target index. -/
theorem lambdaBocksteinDifferentialTarget_lambdaIndex
    (s t r : ℤ) (hr : 1 ≤ r) :
    SynAdamsLambdaModule.lambdaIndex (r - 1).toNat
        (s + r, t + r - 1, t + r - 1) =
      lambdaBocksteinAdamsIndex (lambdaBocksteinGeneratorDegree s t)
        ((s, 1) + (r, -1)) := by
  rw [lambdaBocksteinAdamsIndex_differentialTarget,
    SynAdamsLambdaModule.lambdaIndex_eq]
  have hcast : (((r - 1).toNat : ℕ) : ℤ) = r - 1 := by
    exact Int.toNat_of_nonneg (by omega)
  rw [hcast]
  ext <;> dsimp <;> omega

/-- After removing the actual boundary suspension, a source in bidegree
`(t-s,t)` has target homotopy bidegree `(t-s-1,t+1)`. At Adams filtration
`s+r` this would have the following tridegree. This arithmetic statement
does not assert suspension compatibility of the specified Adams filtrations. -/
theorem lambdaBockstein_actual_target_index (s t r : ℤ) :
    syntheticAdamsIndex (s + r) (t - s - 1, t + 1) =
      (s + r, t + r - 1, t + 1) := by
  ext <;> simp [syntheticAdamsIndex] <;> omega

/-- The actual unsuspended boundary target has λ exponent `r-2`.
This is one smaller than the exponent in the synthetic Adams differential. -/
theorem lambdaBockstein_actual_target_lambdaIndex
    (s t r : ℤ) (hr : 2 ≤ r) :
    SynAdamsLambdaModule.lambdaIndex (r - 2).toNat
        (s + r, t + r - 1, t + r - 1) =
      syntheticAdamsIndex (s + r) (t - s - 1, t + 1) := by
  rw [SynAdamsLambdaModule.lambdaIndex_eq,
    lambdaBockstein_actual_target_index]
  have hcast : (((r - 2).toNat : ℕ) : ℤ) = r - 2 :=
    Int.toNat_of_nonneg (by omega)
  rw [hcast]
  ext <;> dsimp <;> omega

/-- One λ-step sends the unsuspended boundary target index to the
synthetic Adams differential target index. -/
theorem lambdaBockstein_actual_target_lambda_step (s t r : ℤ) :
    syntheticAdamsIndex (s + r) (t - s - 1, t + 1) + (0, 0, -1) =
      lambdaBocksteinAdamsIndex (lambdaBocksteinGeneratorDegree s t)
        ((s, 1) + (r, -1)) := by
  rw [lambdaBockstein_actual_target_index,
    lambdaBocksteinAdamsIndex_differentialTarget]
  ext <;> dsimp <;> omega

/-- On the generator diagonal, the initial λ-Bockstein source is the
synthetic Adams E₂-term through the actual quotient `νX ⟶ νX/λ`. -/
noncomputable def canonicalLambdaBocksteinE0SourceIsoSynAdamsE2Diagonal
    (𝒮 : Type*) [StableHomotopy.StableHomotopyCategory 𝒮] (X : 𝒮)
    (s t : ℤ) :
    (canonicalLambdaPowerBocksteinESS ((nu 𝒮 Syn).obj X) 1
      (t - s, t)).Page 0 (s, 1) ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page 2 (s, t, t) :=
  canonicalLambdaPowerSuccBocksteinE0SourceIsoSynAdamsPage
    (Syn := Syn) 𝒮 X 0 s t

/-- The raw source term for a class `(s,t,w)` is first identified with the
diagonal E₂-term by the actual quotient map `νX ⟶ νX/λ`.  The remaining
weight change is the canonical free-λ identification.  In particular, this
comparison is compatible with maps of finite λ-quotients; no independently
chosen E₂-equivalence is used. -/
noncomputable def canonicalLambdaBocksteinE0SourceIsoSynAdamsE2
    (𝒮 : Type*) [StableHomotopy.StableHomotopyCategory 𝒮] (X : 𝒮)
    (s t w : ℤ) (hw : w ≤ t) :
    (canonicalLambdaBocksteinESS ((nu 𝒮 Syn).obj X)
      (lambdaBocksteinGeneratorDegree s t)).Page 0 (s, 1) ≅
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page 2 (s, t, w) := by
  let qIso := canonicalLambdaBocksteinE0SourceIsoSynAdamsE2Diagonal
    (Syn := Syn) 𝒮 X s t
  let R := rigidity_free_lambda_pages 𝒮 Syn X
  exact qIso ≪≫ R.componentIso 2 (by omega) s t t (by omega) ≪≫
    (R.componentIso 2 (by omega) s t w (by omega)).symm

end KIPBase.Synthetic
