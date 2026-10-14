import KIPBase.Synthetic.AdamsBocksteinMorphism
import KIPBase.SpectralSequence.UnboundedCommutativity

/-!
# Finite lambda lifts and actual extension spectral sequence relations

The same finite-quotient representative supplies the direct Bockstein cycle
and the restriction ESS relation. Its literal connecting-map composite
supplies the obstruction ESS relation. No identification of these distinct
spectral sequences is assumed.
-/
namespace KIPBase.Synthetic
open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence
universe u v
noncomputable section
variable {Syn : Type u} [Category.{0} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The filtered representative of an actual homotopy class, with the
integer test group used by the ESS differential-relation API. -/
def homotopyFiltrationRepresentative {X : Syn} (m w s : ℤ)
    (a : Smn (Syn := Syn) m w ⟶ X)
    (ha : a ∈ synAdamsFiltration Syn X m w s) :
    AddCommGrpCat.of ℤ ⟶ Subobject.underlying.obj
      ((synAdamsConvergence Syn X).filtration.F s (m,w)) :=
  AddCommGrpCat.ofHom
    { toFun := fun z => z • ((synAdamsConvergence Syn X).filtrationEquiv s (m,w)).symm ⟨a,ha⟩
      map_zero' := zero_zsmul _
      map_add' := fun p q => add_zsmul _ p q }

/-- The actual source endpoint in the map ESS, detected by `a`. -/
def homotopyESSSource {X Y : Syn} (f : X ⟶ Y) (m w s : ℤ)
    (a : Smn (Syn := Syn) m w ⟶ X)
    (ha : a ∈ synAdamsFiltration Syn X m w s) :
    AddCommGrpCat.of ℤ ⟶
      (unboundedExtensionSSData.{1,0,0,0} (synAdamsConvergingMap f) (m,w) (s,1)).V :=
  UnboundedExtensionClass.{1,0,0,0} (synAdamsConvergingMap f) (m,w) s 1
    (homotopyFiltrationRepresentative m w s a ha ≫
      (unboundedUnderlyingComplex (synAdamsConvergingMap f) (m,w)).filToAssocGraded s 1)

/-- The actual target endpoint in the map ESS, detected by `b`. -/
def homotopyESSTarget {X Y : Syn} (f : X ⟶ Y) (m w s : ℤ)
    (b : Smn (Syn := Syn) m w ⟶ Y)
    (hb : b ∈ synAdamsFiltration Syn Y m w s) :
    AddCommGrpCat.of ℤ ⟶
      (unboundedExtensionSSData.{1,0,0,0} (synAdamsConvergingMap f) (m,w) (s,0)).V :=
  UnboundedExtensionClass.{1,0,0,0} (synAdamsConvergingMap f) (m,w) s 0
    (homotopyFiltrationRepresentative m w s b hb ≫
      (unboundedUnderlyingComplex (synAdamsConvergingMap f) (m,w)).filToAssocGraded s 0)

/-- A literal homotopy map equation gives the actual ESS relation on the
classes detected by the two representatives. -/
theorem homotopy_map_to_ess_relation {X Y : Syn} (f : X ⟶ Y)
    (m w s r : ℤ) (hr : 0 ≤ r)
    (a : Smn (Syn := Syn) m w ⟶ X) (b : Smn (Syn := Syn) m w ⟶ Y)
    (ha : a ∈ synAdamsFiltration Syn X m w s)
    (hb : b ∈ synAdamsFiltration Syn Y m w (s+r)) (hab : a ≫ f = b) :
    DifferentialRelation (ExtensionSpectralSequence.{1,0,0,0} (synAdamsConvergingMap f) (m,w))
      r (s,1) (homotopyESSSource f m w s a ha)
        (homotopyESSTarget f m w (s+r) b hb) := by
  let cm := (synAdamsFunctoriality Syn).convergenceMap f
  let xl := homotopyFiltrationRepresentative m w s a ha
  let yl := homotopyFiltrationRepresentative m w (s+r) b hb
  apply unboundedDifferentialRelation_of_ambient_map.{1,0,0,0} cm (m,w) r hr s (s+r) rfl xl yl
  · simp [xl, cm, synAdamsConvergingMap, synAdamsConvergingSS, homotopyESSSource, UnboundedExtensionClass, UnboundedExtensionIsLift,
      FilteredComplex.IsLift, Category.assoc] <;> rfl
  · simp [yl, cm, synAdamsConvergingMap, synAdamsConvergingSS, homotopyESSTarget, UnboundedExtensionClass, UnboundedExtensionIsLift,
      FilteredComplex.IsLift, Category.assoc] <;> rfl
  · apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    apply ((synAdamsConvergence Syn Y).abutmentEquiv (m,w)).injective
    change (synAdamsConvergence Syn Y).abutmentEquiv (m,w)
      ((cm.aMap (m,w)).hom
        (((synAdamsConvergence Syn X).filtration.F s (m,w)).arrow.hom (xl.hom z))) =
      (synAdamsConvergence Syn Y).abutmentEquiv (m,w)
        (((synAdamsConvergence Syn Y).filtration.F (s+r) (m,w)).arrow.hom (yl.hom z))
    dsimp only [cm, synAdamsConvergingMap, synAdamsConvergingSS]
    rw [(synAdamsFunctoriality Syn).abutment_naturality]
    change (synAdamsConvergence Syn X).abutmentEquiv (m,w)
        (((synAdamsConvergence Syn X).filtration.F s (m,w)).arrow.hom
          (z • ((synAdamsConvergence Syn X).filtrationEquiv s (m,w)).symm ⟨a,ha⟩)) ≫ f =
      (synAdamsConvergence Syn Y).abutmentEquiv (m,w)
        (((synAdamsConvergence Syn Y).filtration.F (s+r) (m,w)).arrow.hom
          (z • ((synAdamsConvergence Syn Y).filtrationEquiv (s+r) (m,w)).symm ⟨b,hb⟩))
    rw [map_zsmul, map_zsmul, map_zsmul, map_zsmul,
      SynAdamsConvergenceData.filtrationEquiv_comm,
      SynAdamsConvergenceData.filtrationEquiv_comm,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    simpa only [Preadditive.zsmul_comp] using congrArg (fun q => z • q) hab

/-- One finite quotient representative gives both the direct Bockstein
cycle and its actual restriction-ESS relation. -/
theorem lambdaLiftBockstein_lift_to_rhoESS {X : Syn}
    (Q : FiniteLambdaQuotientTower X) (m w s r : ℤ) (hr : 0 ≤ r) (i : ℕ)
    (a : Smn (Syn := Syn) m w ⟶ XModLambdaN X (i+1))
    (ha : a ∈ synAdamsFiltration Syn (XModLambdaN X (i+1)) m w s)
    (hx : lambdaLiftBocksteinLift Q (Smn (Syn := Syn) m w) i a ∈
      synAdamsFiltration Syn (XModLambdaN X 1) m w (s+r)) :
    lambdaLiftBocksteinLift Q (Smn (Syn := Syn) m w) i a ∈ lambdaLiftBocksteinZ Q (Smn (Syn := Syn) m w) i ∧
    DifferentialRelation
      (ExtensionSpectralSequence.{1,0,0,0}
        (synAdamsConvergingMap (Q.rho 1 (i+1) (by omega))) (m,w)) r (s,1)
      (homotopyESSSource (Q.rho 1 (i+1) (by omega)) m w s a ha)
      (homotopyESSTarget (Q.rho 1 (i+1) (by omega)) m w (s+r)
        (lambdaLiftBocksteinLift Q (Smn (Syn := Syn) m w) i a) hx) := by
  refine ⟨⟨a,rfl⟩, ?_⟩
  exact homotopy_map_to_ess_relation _ m w s r hr a _ ha hx rfl

/-- The literal connecting map followed by reduction used by the direct
Bockstein differential. This is a map of synthetic spectra, so it has its
own ordinary map ESS. -/
def lambdaLiftObstructionMap (X : Syn) (i : ℕ) :
    XModLambdaN X (i+1) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((i+1 : ℕ) : ℤ))).obj (XModLambdaN X 1)) :=
  syn_functorial_cofiber.cofibδ (lambdaPow (i+1) X) ≫
    (shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -((i+1 : ℕ) : ℤ))).map
        (syn_functorial_cofiber.cofibι (lambdaPow 1 X)))

/-- The direct Bockstein obstruction is the target-exponent-one case of
    the actual finite boundary used by the Mahowald cap construction. -/
theorem lambdaLiftObstructionMap_eq_finiteBoundary (X : Syn) (i : ℕ) :
    lambdaLiftObstructionMap X i = lambdaFiniteBoundary X (i + 1) 1 := rfl

/-- The direct Bockstein obstruction is detected by the ESS of its actual
boundary-and-reduction map, using exactly the same finite quotient lift. -/
theorem lambdaLiftBockstein_obstruction_to_ess {X : Syn}
    (m w s r : ℤ) (hr : 0 ≤ r) (i : ℕ)
    (a : Smn (Syn := Syn) m w ⟶ XModLambdaN X (i+1))
    (ha : a ∈ synAdamsFiltration Syn (XModLambdaN X (i+1)) m w s)
    (hb : lambdaLiftBocksteinObstruction X (Smn (Syn := Syn) m w) i a ∈
      synAdamsFiltration Syn _ m w (s+r)) :
    DifferentialRelation
      (ExtensionSpectralSequence.{1,0,0,0}
        (synAdamsConvergingMap (lambdaLiftObstructionMap X i)) (m,w)) r (s,1)
      (homotopyESSSource (lambdaLiftObstructionMap X i) m w s a ha)
      (homotopyESSTarget (lambdaLiftObstructionMap X i) m w (s+r)
        (lambdaLiftBocksteinObstruction X (Smn (Syn := Syn) m w) i a) hb) :=
  homotopy_map_to_ess_relation _ m w s r hr a _ ha hb rfl

/-- Equality modulo the direct Bockstein boundary group is literally
indistinguishability on its page, not an independently chosen ESS ambiguity. -/
theorem lambdaLiftBockstein_same_page_iff_boundary
    {X : Syn} (Q : FiniteLambdaQuotientTower X) (m w : ℤ) (i : ℕ)
    (x y : lambdaLiftBocksteinZ Q (Smn (Syn := Syn) m w) i) :
    (QuotientAddGroup.mk x : lambdaLiftBocksteinPage Q m w i) =
      QuotientAddGroup.mk y ↔
        x.val - y.val ∈ lambdaLiftBocksteinBoundaryAt X m w i := by
  rw [QuotientAddGroup.eq]
  change -x.val + y.val ∈ lambdaLiftBocksteinBoundaryAt X m w i ↔ _
  constructor
  · intro h
    convert (lambdaLiftBocksteinBoundaryAt X m w i).neg_mem h using 1 <;> abel
  · intro h
    convert (lambdaLiftBocksteinBoundaryAt X m w i).neg_mem h using 1 <;> abel

/-- The boundary ambiguity in the linked Bockstein page is exactly the
existence of one incoming finite lambda-boundary representing the difference. -/
theorem lambdaLiftBockstein_same_page_iff_incoming_target
    {X : Syn} (Q : FiniteLambdaQuotientTower X) (m w : ℤ)
    (i : ℕ) (hi : 0 < i)
    (x y : lambdaLiftBocksteinZ Q (Smn (Syn := Syn) m w) i) :
    (QuotientAddGroup.mk x : lambdaLiftBocksteinPage Q m w i) =
      QuotientAddGroup.mk y ↔
      ∃ a : Smn (Syn := Syn) (m+1) (w-(i : ℤ)) ⟶ XModLambdaN X i,
        lambdaLiftBocksteinIncomingTargetValue X m w i a = x.val-y.val := by
  have h := lambdaLiftBocksteinPage_eq_zero_iff_exists_differential_target
    Q m w i hi (x-y)
  simpa only [QuotientAddGroup.mk_sub, sub_eq_zero, AddSubgroup.coe_sub] using h

/-! ### The common Mahowald quotient representative in the direct Bockstein

The actual finite quotient class produced by the Mahowald diagram is used
once: its reduction supplies the direct Bockstein cycle, and its image
under the normalized map supplies the map ESS relation. This does not
identify the map ESS with the lambda-tower Bockstein.
-/
section DirectBocksteinLink
variable {Syn₀ : Type u} [Category.{0} Syn₀] [Preadditive Syn₀]
    [HasZeroObject Syn₀] [HasShift Syn₀ ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn₀ n)]
    [MonoidalCategory Syn₀] [Pretriangulated Syn₀] [SyntheticCategory Syn₀]

/-- Read both conclusions from the same actual Mahowald quotient lift.
The map may in particular be the finite normalized `fHat` map in the
Mahowald diagram. Filtration hypotheses record the detected ESS degrees. -/
theorem mahowaldQuotientLift_to_directBockstein_and_ess
    {X Y : Syn₀} (Q : FiniteLambdaQuotientTower X)
    (i : ℕ) (g : XModLambdaN X (i+1) ⟶ Y)
    (m w s n : ℤ) (hn : 0 ≤ n)
    (u : Smn (Syn := Syn₀) m w ⟶ XModLambdaN X (i+1))
    (x : lambdaLiftBocksteinV X (Smn (Syn := Syn₀) m w))
    (y : Smn (Syn := Syn₀) m w ⟶ Y)
    (hρ : lambdaLiftBocksteinLift Q (Smn (Syn := Syn₀) m w) i u = x)
    (hg : u ≫ g = y)
    (hu : u ∈ synAdamsFiltration Syn₀ (XModLambdaN X (i+1)) m w s)
    (hy : y ∈ synAdamsFiltration Syn₀ Y m w (s+n)) :
    x ∈ lambdaLiftBocksteinZ Q (Smn (Syn := Syn₀) m w) i ∧
      DifferentialRelation
        (ExtensionSpectralSequence.{1,0,0,0} (synAdamsConvergingMap g) (m,w))
        n (s,1) (homotopyESSSource g m w s u hu)
          (homotopyESSTarget g m w (s+n) y hy) := by
  exact ⟨⟨u,hρ⟩, homotopy_map_to_ess_relation g m w s n hn u y hu hy hg⟩

/-- The direct Bockstein boundary congruence has a concrete
finite-quotient witness in the direct Bockstein, for these same page classes. -/
theorem mahowald_directBockstein_target_congruence
    {X : Syn₀} (Q : FiniteLambdaQuotientTower X) (m w : ℤ)
    (i : ℕ) (hi : 0 < i)
    (x y : lambdaLiftBocksteinZ Q (Smn (Syn := Syn₀) m w) i) :
    (QuotientAddGroup.mk x : lambdaLiftBocksteinPage Q m w i) =
      QuotientAddGroup.mk y ↔
      ∃ a : Smn (Syn := Syn₀) (m+1) (w-(i : ℤ)) ⟶ XModLambdaN X i,
        lambdaLiftBocksteinIncomingTargetValue X m w i a = x.val-y.val :=
  lambdaLiftBockstein_same_page_iff_incoming_target Q m w i hi x y
end DirectBocksteinLink

section AdamsFiniteBoundary
universe uS vS
variable {𝒮 : Type uS} [StableHomotopy.StableHomotopyCategory.{uS,vS} 𝒮]
    [SyntheticModelRealizationWitness Syn]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Adams differential supplies representatives for the ESS of
its literal finite boundary. The source is the restricted cap, and the target
is its actual finite boundary, with canonical Adams filtrations on both. -/
theorem adamsDifferential_to_finiteBoundary_ess
    {X : 𝒮} {M : NuSynAdamsGeometricModel 𝒮 Syn X}
    (C : NuSynAdamsGeometricComparison 𝒮 Syn X M)
    (s k d n : ℕ) (t : ℤ)
    (x : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
      ((k + d + 2 : ℕ) : ℤ) ((s : ℤ), t, t))
    (b : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page
      ((k + d + 2 : ℕ) : ℤ)
        ((s : ℤ) + ((k + d + 2 : ℕ) : ℤ),
          t + ((k + d + 2 : ℕ) : ℤ) - 1, t))
    (hdb : (synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X)
      ((k + d + 2 : ℕ) : ℤ) (s : ℤ) t t).hom x = b) :
    ∃ (z : M.input.Representative
        (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t) s (k + d + 2))
      (c : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        LambdaCofiberGeometry.commonCone
          (M.input.transition s (s + (k + d + 2)) (Nat.le_add_right s (k + d + 2)))
          (k + d + 1))
      (yStage : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (M.input.boundaryTarget (k + d + 1)).stage (s + (k + d + 2)))
      (y : NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t ⟶
        (shiftFunctor Syn (1 : ℤ)).obj
          ((SyntheticCategory.biShift (0, -((k + d + 1 : ℕ) : ℤ))).obj
            (M.input.layer (s + (k + d + 2)))))
      (a : Smn (Syn := Syn) (t - (s : ℤ)) t ⟶
        XModLambdaN ((nu 𝒮 Syn).obj X) (k + 1))
      (ha : a ∈ synAdamsFiltration Syn
        (XModLambdaN ((nu 𝒮 Syn).obj X) (k + 1))
        (t - (s : ℤ)) t (s : ℤ))
      (hb : a ≫ lambdaFiniteBoundary ((nu 𝒮 Syn).obj X) (k + 1) n ∈
        synAdamsFiltration Syn _ (t - (s : ℤ)) t
          ((s : ℤ) + ((k + d + 2 : ℕ) : ℤ))),
      c ≫ LambdaCofiberGeometry.toRelative
          (M.input.transition s (s + (k + d + 2)) (Nat.le_add_right s (k + d + 2)))
          (k + d + 1) = z ∧
      QuotientAddGroup.mk
        (⟨M.input.source (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
          s (k + d + 2) (by omega) z, ⟨z, rfl⟩⟩ :
          M.input.sourceCycles (NuSynAdamsGeometricModel.SourceSphere (Syn := Syn) s t)
            s (k + d + 2) (by omega)) =
        C.sourceEquiv s (k + d + 2) (by omega) t x ∧
      C.targetEquiv s (k + d + 2) (by omega) t b =
        QuotientAddGroup.mk (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (k + d + 1) (M.input.layer (s + (k + d + 2))))) ∧
      a = (NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
        (((c ≫ LambdaCofiberGeometry.toQuotient
          (M.input.transition s (s + (k + d + 2)) (Nat.le_add_right s (k + d + 2)))
          (k + d + 1)) ≫ XModLambdaN.map (M.input.toBase s) (k + d + 1)) ≫
            XModLambdaN.restrict ((nu 𝒮 Syn).obj X) k d) ∧
      yStage ≫ M.input.dividedLayerProjection (k + d + 1) (s + (k + d + 2)) = y ∧
      a ≫ lambdaFiniteBoundary ((nu 𝒮 Syn).obj X) (k + 1) n =
        (NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t).inv ≫
          ((yStage ≫ (shiftFunctor Syn (1 : ℤ)).map
            ((lambdaPowerRestrictionNatTrans k d).app
              (M.input.stage (s + (k + d + 2))))) ≫
              (M.input.boundaryTarget (k + 1)).toBase (s + (k + d + 2))) ≫
          (shiftFunctor Syn (1 : ℤ)).map
            ((SyntheticCategory.biShift (0, -((k + 1 : ℕ) : ℤ))).map
              (syn_functorial_cofiber.cofibι (lambdaPow n ((nu 𝒮 Syn).obj X)))) ∧
      DifferentialRelation
        (ExtensionSpectralSequence.{1,0,0,0}
          (synAdamsConvergingMap
            (lambdaFiniteBoundary ((nu 𝒮 Syn).obj X) (k + 1) n))
          (t - (s : ℤ), t))
        ((k + d + 2 : ℕ) : ℤ) ((s : ℤ), 1)
        (homotopyESSSource _ (t - (s : ℤ)) t (s : ℤ) a ha)
        (homotopyESSTarget _ (t - (s : ℤ)) t
          ((s : ℤ) + ((k + d + 2 : ℕ) : ℤ))
          (a ≫ lambdaFiniteBoundary ((nu 𝒮 Syn).obj X) (k + 1) n) hb) := by
  obtain ⟨z, yStage, y, c, q, a, b0, hz, ht, hy, hc, hq, ha,
      hab, hstage, hAFa, hAFb, hfinite⟩ :=
    C.exists_finitePower_restriction_boundary_of_differential s k d t x b hdb
  let e := NuSynAdamsGeometricModel.sourceSphereIso (Syn := Syn) s t
  have ha' : (M.input.quotient (k + 1)).AFGe (e.inv ≫ a) s := by
    obtain ⟨aStage, h⟩ := hAFa
    refine ⟨e.inv ≫ aStage, ?_⟩
    change aStage ≫ (M.input.quotient (k + 1)).toBase s = a at h
    change (e.inv ≫ aStage) ≫ (M.input.quotient (k + 1)).toBase s = e.inv ≫ a
    rw [Category.assoc, h]
  have hb' : (M.input.boundaryTarget (k + 1)).AFGe (e.inv ≫ b0)
      (s + (k + d + 2)) := by
    obtain ⟨bStage, h⟩ := hAFb
    refine ⟨e.inv ≫ bStage, ?_⟩
    change bStage ≫ (M.input.boundaryTarget (k + 1)).toBase (s + (k + d + 2)) = b0 at h
    change (e.inv ≫ bStage) ≫
      (M.input.boundaryTarget (k + 1)).toBase (s + (k + d + 2)) = e.inv ≫ b0
    rw [Category.assoc, h]
  have haCanonical := (M.quotient_afGe_iff_synAdamsFiltration
    (k + 1) s (t - (s : ℤ)) t (e.inv ≫ a)).mp ha'
  have hbCanonical := (M.boundaryTarget_afGe_iff_synAdamsFiltration
    (k + 1) (s + (k + d + 2)) (t - (s : ℤ)) t (e.inv ≫ b0)).mp hb'
  have htarget := synAdamsFiltration_postcomp
    ((shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -((k + 1 : ℕ) : ℤ))).map
        (syn_functorial_cofiber.cofibι (lambdaPow n ((nu 𝒮 Syn).obj X)))))
    (t - (s : ℤ)) t ((s + (k + d + 2) : ℕ) : ℤ) (e.inv ≫ b0) hbCanonical
  have hfiniteEq := (hfinite n).1
  have hbFinite : (e.inv ≫ a) ≫
      lambdaFiniteBoundary ((nu 𝒮 Syn).obj X) (k + 1) n ∈
      synAdamsFiltration Syn _ (t - (s : ℤ)) t
        ((s : ℤ) + ((k + d + 2 : ℕ) : ℤ)) := by
    simpa only [Category.assoc, hfiniteEq, Nat.cast_add, XModLambdaN] using htarget
  refine ⟨z, c, yStage, y, e.inv ≫ a, haCanonical, hbFinite, hc, hz, ht, ?_, hy, ?_, ?_⟩
  · dsimp only [e]
    rw [hq, ha]
  · dsimp only [e]
    simp only [Category.assoc, hfiniteEq, hstage]
  · exact homotopy_map_to_ess_relation _ (t - (s : ℤ)) t (s : ℤ)
      ((k + d + 2 : ℕ) : ℤ) (by positivity) _ _ haCanonical hbFinite rfl
end AdamsFiniteBoundary

end
end KIPBase.Synthetic
