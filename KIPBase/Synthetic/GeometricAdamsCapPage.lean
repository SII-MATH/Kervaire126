import KIPBase.Synthetic.GeometricAdamsBoundaryComparison
import KIPBase.Synthetic.GeometricAdamsPageShift
import KIPBase.Synthetic.GeometricAdamsCofiber

/-!
# Pages represented by actual lambda caps

The source is the group of maps into the common cofiber, modulo caps whose
adjacent-layer source is an incoming boundary. The target is the divided
layer group modulo the inverse image of shorter boundaries under actual
lambda multiplication. Both quotients are defined before the comparison.

Freeness and the geometric realization in step 2 prove that every geometric
Adams page class has a cap. The resulting additive page equivalence commutes
with the connecting-map differential and reflects its nonzero condition.
These are geometric pages; no identification with the independently specified
legacy `SynAdamsSS` or its abutment filtration is asserted here.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits

universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

namespace FreeLambdaHomotopy

end FreeLambdaHomotopy

namespace GeometricAdams.Input

variable {X : Syn}

/-- Actual common-cofiber representatives, with a fixed length and lambda power. -/
noncomputable abbrev CapRepresentatives (G : Input X) (S : Syn) (s r n : ℕ) :=
  S ⟶ LambdaCofiberGeometry.commonCone
    (G.transition s (s + r) (Nat.le_add_right s r)) n

/-- The adjacent-layer source read from the actual cap. -/
noncomputable def capLayerSource (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    G.CapRepresentatives S s r n →+ (S ⟶ G.layer s) :=
  (G.source S s r hr).comp
    (postcompose S (LambdaCofiberGeometry.toRelative
      (G.transition s (s + r) (Nat.le_add_right s r)) n))

/-- The source of every cap is an actual relative cycle. -/
noncomputable def capCycleSource (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    G.CapRepresentatives S s r n →+ G.sourceCycles S s r hr where
  toFun c := ⟨G.capLayerSource S s r hr n c, ⟨_, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ c d)

/-- The additive map to the geometric Adams page induced by cap sources. -/
noncomputable def capSourceHom (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    G.CapRepresentatives S s r n →+ G.PageGroup S s r hr :=
  (QuotientAddGroup.mk' _).comp (G.capCycleSource S s r hr n)

@[simp] theorem capSourceHom_apply (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) (c : G.CapRepresentatives S s r n) :
    G.capSourceHom S s r hr n c = G.capSourceClass S s r hr n c := rfl

/-- Relations on caps are specified in the adjacent layer: precisely those
whose sources belong to the actual incoming-boundary subgroup. -/
noncomputable def capRelations (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    AddSubgroup (G.CapRepresentatives S s r n) :=
  (G.incomingBoundaries S s r hr).comap (G.capLayerSource S s r hr n)

/-- The relations agree with the kernel of the source page map. -/
theorem capRelations_eq_ker (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    G.capRelations S s r hr n = (G.capSourceHom S s r hr n).ker := by
  ext c
  change G.capLayerSource S s r hr n c ∈ G.incomingBoundaries S s r hr ↔
    (QuotientAddGroup.mk (G.capCycleSource S s r hr n c) :
      G.PageGroup S s r hr) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- The page represented by actual caps, modulo the explicit source relations. -/
noncomputable abbrev CapPage (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :=
  G.CapRepresentatives S s r n ⧸ G.capRelations S s r hr n

/-- At the generator weight every geometric page class has a cap. The
divided target is obtained by surjectivity of actual lambda on the free layer. -/
theorem capSourceHom_surjective (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ) :
    Function.Surjective
      (G.capSourceHom (Smn m (m + s)) s r (by omega) (r - 1)) := by
  intro x
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (G.targetAmbiguity (Smn m (m + s)) s r (by omega))
      (G.pageObstruction (Smn m (m + s)) s r (by omega) x)
  obtain ⟨y, hy⟩ := (R (s + r)).shiftMulHom_surjective m (m + s)
    (r - 1) (by dsimp; omega) z
  have hxy : G.pageObstruction (Smn m (m + s)) s r (by omega) x =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow (r - 1) (G.layer (s + r)))) := by
    exact hz.symm.trans (congrArg QuotientAddGroup.mk hy.symm)
  obtain ⟨z', y', hsource, _, hboundary⟩ :=
    A.dividedBoundary s r hr m x y hxy
  obtain ⟨c, hc, _⟩ := LambdaCofiberGeometry.exists_commonLift_of_relative_boundary
    (G.transition s (s + r) (Nat.le_add_right s r)) (r - 1) z' y' hboundary
  exact ⟨c, by simpa only [capSourceHom_apply, capSourceClass, hc] using hsource⟩

/-- A proved additive equivalence from cap quotients to geometric Adams pages.
No page equivalence is part of the geometric realization input. -/
noncomputable def capPageEquiv (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ) :
    G.CapPage (Smn m (m + s)) s r (by omega) (r - 1) ≃+
      G.PageGroup (Smn m (m + s)) s r (by omega) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (G.capRelations_eq_ker (Smn m (m + s)) s r (by omega) (r - 1))).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _
        (G.capSourceHom_surjective R A s r hr m))

@[simp] theorem capPageEquiv_mk (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (c : G.CapRepresentatives (Smn m (m + s)) s r (r - 1)) :
    G.capPageEquiv R A s r hr m (QuotientAddGroup.mk c) =
      G.capSourceClass (Smn m (m + s)) s r (by omega) (r - 1) c := rfl

/-- The divided layer group in which the cap connecting map takes values. -/
noncomputable abbrev DividedLayer (G : Input X) (S : Syn) (s r n : ℕ) :=
  S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
    ((SyntheticCategory.biShift (0, -(n : ℤ))).obj (G.layer (s + r)))

/-- Shorter target boundaries, pulled back by actual lambda multiplication. -/
noncomputable def dividedTargetBoundaries (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) : AddSubgroup (G.DividedLayer S s r n) :=
  (G.targetAmbiguity S s r hr).comap
    (LambdaPowerBoundary.shiftMulHom S (G.layer (s + r)) n)

noncomputable abbrev DividedTargetPage (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :=
  G.DividedLayer S s r n ⧸ G.dividedTargetBoundaries S s r hr n

/-- Read the divided adjacent target by the actual connecting map. -/
noncomputable def capDividedTargetHom (G : Input X) (S : Syn) (s r n : ℕ) :
    G.CapRepresentatives S s r n →+ G.DividedLayer S s r n :=
  (postcompose S (G.dividedLayerProjection n (s + r))).comp
    (postcompose S (syn_functorial_cofiber.cofibδ
      (lambdaPow n (G.stage (s + r)) ≫
        G.transition s (s + r) (Nat.le_add_right s r))))

/-- Source relations map into shorter target boundaries. Thus the boundary
formula descends to quotients independently of any choice of cap. -/
theorem capDividedTargetHom_mem (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (c : G.CapRepresentatives S s r n) (hc : c ∈ G.capRelations S s r hr n) :
    G.capDividedTargetHom S s r n c ∈ G.dividedTargetBoundaries S s r hr n := by
  have hz : G.capSourceClass S s r hr n c = 0 := by
    change G.capSourceHom S s r hr n c = 0
    rw [G.capRelations_eq_ker S s r hr n] at hc
    exact hc
  have h := G.pageObstruction_capSourceClass S s r hr n c
  rw [hz, map_zero] at h
  change G.capDividedTarget S s r n c ≫
    (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.layer (s + r))) ∈
      G.targetAmbiguity S s r hr
  exact (QuotientAddGroup.eq_zero_iff _).mp h.symm

/-- The cap differential is induced by the actual connecting map, not
defined by transport from the Adams differential. -/
noncomputable def capDifferential (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    G.CapPage S s r hr n →+ G.DividedTargetPage S s r hr n :=
  QuotientAddGroup.map _ _ (G.capDividedTargetHom S s r n)
    (G.capDividedTargetHom_mem S s r hr n)

/-- A cap differential is zero exactly when its divided target is a shorter
target boundary after multiplication by the prescribed λ-power.  This is
the target-side kernel statement used to turn a zero Adams differential
into a zero-source λ-Bockstein relation. -/
theorem capDifferential_mk_eq_zero_iff (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (c : G.CapRepresentatives S s r n) :
    G.capDifferential S s r hr n (QuotientAddGroup.mk c) = 0 ↔
      G.capDividedTargetHom S s r n c ∈
        G.dividedTargetBoundaries S s r hr n := by
  change QuotientAddGroup.mk (G.capDividedTargetHom S s r n c) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]

/-- Expanded form of the zero cap differential criterion.  The witness is a
relative representative with zero source whose target is the prescribed
λ-multiple of the divided target. -/
theorem capDifferential_mk_eq_zero_iff_exists_zero_source
    (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (c : G.CapRepresentatives S s r n) :
    G.capDifferential S s r hr n (QuotientAddGroup.mk c) = 0 ↔
      ∃ z : G.Representative S s r,
        G.source S s r hr z = 0 ∧
        G.target S s r z =
          G.capDividedTargetHom S s r n c ≫
            (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.layer (s + r))) := by
  rw [G.capDifferential_mk_eq_zero_iff S s r hr n c]
  change _ ∈ G.targetAmbiguity S s r hr ↔ _
  constructor
  · rintro ⟨z, hz, htarget⟩
    change G.source S s r hr z = 0 at hz
    exact ⟨z, hz, htarget⟩
  · rintro ⟨z, hz, htarget⟩
    refine ⟨z, ?_, htarget⟩
    change G.source S s r hr z = 0
    exact hz

/-- A divided target whose λ-multiple is zero in the Adams target quotient
has a cap with zero source page class and that same divided target.  The
construction is the corrected-boundary construction applied to the zero
source class, followed by the common-cone lift.  Thus the cap belongs to
the explicit source-relation subgroup. -/
theorem exists_capRelation_of_dividedTarget_page_zero
    (G : Input X) (R : G.FreeLayers) (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (y : Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj
        (G.layer (s + r))))
    (hzero : (QuotientAddGroup.mk
      (y ≫ (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPow (r - 1) (G.layer (s + r)))) :
        (Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
          (G.layer (s + r))) ⧸ G.targetAmbiguity
            (Smn m (m + s)) s r (by omega)) = 0) :
    ∃ c : G.CapRepresentatives (Smn m (m + s)) s r (r - 1),
      c ∈ G.capRelations (Smn m (m + s)) s r (by omega) (r - 1) ∧
      G.capDividedTarget (Smn m (m + s)) s r (r - 1) c = y := by
  have hxy : G.pageObstruction (Smn m (m + s)) s r (by omega)
      (0 : G.PageGroup (Smn m (m + s)) s r (by omega)) =
      QuotientAddGroup.mk
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.layer (s + r)))) := by
    simpa using hzero.symm
  obtain ⟨c, hcsource, hctarget⟩ :=
    (G.capRealizes_iff_pageObstruction R A s r hr m
      (0 : G.PageGroup (Smn m (m + s)) s r (by omega)) y).mpr hxy
  refine ⟨c, ?_, hctarget⟩
  rw [G.capRelations_eq_ker (Smn m (m + s)) s r (by omega) (r - 1)]
  simpa only [AddMonoidHom.mem_ker, capSourceHom_apply] using hcsource

/-- A cap has zero divided-target page class exactly when its divided target
is also realized by a cap relation.  This packages the zero-source disk and
the cone attachment into the form used by the λ-Bockstein source quotient. -/
theorem capDifferential_mk_eq_zero_iff_exists_capRelation_same_dividedTarget
    (G : Input X) (R : G.FreeLayers) (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (c : G.CapRepresentatives (Smn m (m + s)) s r (r - 1)) :
    G.capDifferential (Smn m (m + s)) s r (by omega) (r - 1)
        (QuotientAddGroup.mk c) = 0 ↔
      ∃ d : G.CapRepresentatives (Smn m (m + s)) s r (r - 1),
        d ∈ G.capRelations (Smn m (m + s)) s r (by omega) (r - 1) ∧
        G.capDividedTarget (Smn m (m + s)) s r (r - 1) d =
          G.capDividedTarget (Smn m (m + s)) s r (r - 1) c := by
  constructor
  · intro hzero
    have hboundary : G.capDividedTargetHom (Smn m (m + s)) s r (r - 1) c ∈
        G.dividedTargetBoundaries (Smn m (m + s)) s r (by omega) (r - 1) :=
      (G.capDifferential_mk_eq_zero_iff
        (Smn m (m + s)) s r (by omega) (r - 1) c).mp hzero
    have hquotient : (QuotientAddGroup.mk
        (G.capDividedTarget (Smn m (m + s)) s r (r - 1) c ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (G.layer (s + r)))) :
          (Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
            (G.layer (s + r))) ⧸ G.targetAmbiguity
              (Smn m (m + s)) s r (by omega)) = 0 := by
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      change G.capDividedTargetHom (Smn m (m + s)) s r (r - 1) c ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.layer (s + r))) ∈
        G.targetAmbiguity (Smn m (m + s)) s r (by omega)
      exact hboundary
    obtain ⟨d, hd, htarget⟩ :=
      G.exists_capRelation_of_dividedTarget_page_zero R A s r hr m
        (G.capDividedTarget (Smn m (m + s)) s r (r - 1) c) hquotient
    exact ⟨d, hd, htarget⟩
  · rintro ⟨d, hd, htarget⟩
    apply (G.capDifferential_mk_eq_zero_iff
      (Smn m (m + s)) s r (by omega) (r - 1) c).mpr
    change G.capDividedTarget (Smn m (m + s)) s r (r - 1) c ∈
      G.dividedTargetBoundaries (Smn m (m + s)) s r (by omega) (r - 1)
    rw [← htarget]
    change G.capDividedTargetHom (Smn m (m + s)) s r (r - 1) d ∈
      G.dividedTargetBoundaries (Smn m (m + s)) s r (by omega) (r - 1)
    exact G.capDividedTargetHom_mem (Smn m (m + s)) s r (by omega) (r - 1) d hd

/-- Actual lambda multiplication gives the comparison on the target quotient. -/
noncomputable def dividedTargetEquiv (G : Input X) (R : G.FreeLayers)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ) :
    G.DividedTargetPage (Smn m (m + s)) s r (by omega) (r - 1) ≃+
      ((Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) ⧸
        G.targetAmbiguity (Smn m (m + s)) s r (by omega)) :=
  quotientAddEquivOfAddEquiv
    (AddEquiv.ofBijective
      (LambdaPowerBoundary.shiftMulHom (Smn m (m + s)) (G.layer (s + r)) (r - 1))
      ⟨(R (s + r)).shiftMulHom_injective m (m + s) (r - 1),
        (R (s + r)).shiftMulHom_surjective m (m + s) (r - 1) (by dsimp; omega)⟩)
    _ _ (fun _ => Iff.rfl)

/-- The page equivalences intertwine the geometric Adams obstruction with
the differential induced by the actual cap boundary. -/
theorem capPageEquiv_comm_d (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (x : G.CapPage (Smn m (m + s)) s r (by omega) (r - 1)) :
    G.pageObstruction (Smn m (m + s)) s r (by omega)
        (G.capPageEquiv R A s r hr m x) =
      G.dividedTargetEquiv R s r hr m
        (G.capDifferential (Smn m (m + s)) s r (by omega) (r - 1) x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c => exact G.pageObstruction_capSourceClass (Smn m (m + s)) s r (by omega) (r - 1) c

/-- Nonzero is tested in the target page quotient, so the comparison also
preserves and reflects essential differentials. -/
theorem capDifferential_ne_zero_iff (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (x : G.CapPage (Smn m (m + s)) s r (by omega) (r - 1)) :
    G.capDifferential (Smn m (m + s)) s r (by omega) (r - 1) x ≠ 0 ↔
      G.pageObstruction (Smn m (m + s)) s r (by omega)
        (G.capPageEquiv R A s r hr m x) ≠ 0 := by
  rw [G.capPageEquiv_comm_d R A s r hr m x,
    (G.dividedTargetEquiv R s r hr m).map_ne_zero_iff]

/-! ## Actual quotient classes and their boundaries -/

/-- The homotopy class in the finite lambda quotient determined by the same
cap used in the page comparison. -/
noncomputable def capQuotientClass (G : Input X) (S : Syn) (s r n : ℕ) :
    G.CapRepresentatives S s r n →+ (S ⟶ XModLambdaN X n) :=
  (postcompose S (XModLambdaN.map (G.toBase s) n)).comp
    (postcompose S (LambdaCofiberGeometry.toQuotient
      (G.transition s (s + r) (Nat.le_add_right s r)) n))

/-- Before projecting to the layer, the cap boundary is an actual map into
the specified deep stage. -/
noncomputable def capStageBoundary (G : Input X) (S : Syn) (s r n : ℕ) :
    G.CapRepresentatives S s r n →+
      (S ⟶ (G.boundaryTarget n).stage (s + r)) :=
  postcompose S (syn_functorial_cofiber.cofibδ
    (lambdaPow n (G.stage (s + r)) ≫
      G.transition s (s + r) (Nat.le_add_right s r)))

theorem capQuotientClass_mem_filtration (G : Input X) (S : Syn) (s r n : ℕ)
    (c : G.CapRepresentatives S s r n) :
    (G.quotient n).AFGe (G.capQuotientClass S s r n c) s := by
  refine ⟨c ≫ LambdaCofiberGeometry.toQuotient
    (G.transition s (s + r) (Nat.le_add_right s r)) n, ?_⟩
  change (_ ≫ _) ≫ (G.quotient n).toBase s = _
  exact congrArg (fun f => (c ≫ LambdaCofiberGeometry.toQuotient
    (G.transition s (s + r) (Nat.le_add_right s r)) n) ≫ f)
      (G.map_toBase (XModLambdaN.functor n) s)

/-- The actual finite-cofiber boundary is the deep-stage representative
whose adjacent-layer projection defines `capDifferential`. -/
theorem capQuotientClass_boundary (G : Input X) (S : Syn) (s r n : ℕ)
    (c : G.CapRepresentatives S s r n) :
    G.capQuotientClass S s r n c ≫
        syn_functorial_cofiber.cofibδ (lambdaPow n X) =
      G.capStageBoundary S s r n c ≫ (G.boundaryTarget n).toBase (s + r) := by
  change ((c ≫ LambdaCofiberGeometry.toQuotient
      (G.transition s (s + r) _) n) ≫ XModLambdaN.map (G.toBase s) n) ≫ _ = _
  rw [Category.assoc, XModLambdaN.proj_naturality,
    ← Category.assoc, Category.assoc c,
    LambdaCofiberGeometry.toQuotient_boundary]
  dsimp only [capStageBoundary, postcompose, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [show (G.boundaryTarget n).toBase (s + r) =
    (shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -(n : ℤ))).map (G.toBase (s + r))) from
    G.map_toBase
      (SyntheticCategory.biShift (0, -(n : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ)) (s + r)]
  change (c ≫ (_ ≫ (shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -(n : ℤ))).map
        (G.transition s (s + r) _)))) ≫
      (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(n : ℤ))).map (G.toBase s)) = _
  rw [Category.assoc, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, G.transition_toBase]
  exact (Category.assoc _ _ _).symm

theorem capQuotientClass_boundary_mem_filtration (G : Input X) (S : Syn)
    (s r n : ℕ) (c : G.CapRepresentatives S s r n) :
    (G.boundaryTarget n).AFGe
      (G.capQuotientClass S s r n c ≫
        syn_functorial_cofiber.cofibδ (lambdaPow n X)) (s + r) :=
  ⟨G.capStageBoundary S s r n c, (G.capQuotientClass_boundary S s r n c).symm⟩

/-- The differential representative is the layer projection of the very
same stage representative that computes the actual quotient boundary. -/
theorem capStageBoundary_layer (G : Input X) (S : Syn) (s r n : ℕ)
    (c : G.CapRepresentatives S s r n) :
    G.capStageBoundary S s r n c ≫ G.dividedLayerProjection n (s + r) =
      G.capDividedTargetHom S s r n c := rfl

/-- If the divided layer component of a cap boundary vanishes, its actual
boundary map factors through the next stage of the lambda-boundary tower.
This is the geometric passage from a zero target class to the next Adams
filtration; it is obtained from cofiber exactness, without choosing a page
representative. -/
theorem capStageBoundary_lifts_of_capDividedTarget_eq_zero
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    (G : Input X) (S : Syn) (s r n : ℕ)
    (c : G.CapRepresentatives S s r n)
    (hzero : G.capDividedTargetHom S s r n c = 0) :
    ∃ y' : S ⟶ (G.boundaryTarget n).stage (s + r + 1),
      y' ≫ (G.boundaryTarget n).transition (s + r) (s + r + 1)
        (Nat.le_succ _) = G.capStageBoundary S s r n c := by
  let W : Syn ⥤ Syn := SyntheticCategory.biShift (0, -(n : ℤ))
  let H := G.map W
  let f := H.transition (s + r) (s + r + 1) (Nat.le_succ _)
  let a := G.capStageBoundary S s r n c
  have hlayer : a ≫
      (shiftFunctor Syn (1 : ℤ)).map
        (W.map (syn_functorial_cofiber.cofibι
          (G.transition (s + r) (s + r + 1) (Nat.le_succ _)))) = 0 := by
    change G.capStageBoundary S s r n c ≫
      G.dividedLayerProjection n (s + r) = 0
    rw [G.capStageBoundary_layer]
    exact hzero
  let e := G.mapRelativeIso W (s + r) (s + r + 1) (Nat.le_succ _)
  have hz : a ≫ (shiftFunctor Syn (1 : ℤ)).map
      (syn_functorial_cofiber.cofibι f) = 0 := by
    apply (cancel_mono ((shiftFunctor Syn (1 : ℤ)).map e.hom)).mp
    rw [Category.assoc, ← Functor.map_comp]
    change a ≫ (shiftFunctor Syn (1 : ℤ)).map
      (syn_functorial_cofiber.cofibι
        ((G.map W).transition (s + r) (s + r + 1) (Nat.le_succ _)) ≫
          (G.mapRelativeIso W (s + r) (s + r + 1) (Nat.le_succ _)).hom) =
        0 ≫ (shiftFunctor Syn (1 : ℤ)).map e.hom
    rw [G.mapRelativeIso_incl, Limits.zero_comp]
    exact hlayer
  let T := chosenCofiberTriangle f
  let Ts := (shiftFunctor (Pretriangulated.Triangle Syn) (1 : ℤ)).obj T
  have hTs : Ts ∈ distTriang Syn :=
    Pretriangulated.Triangle.shift_distinguished T
      (syn_functorial_cofiber.cofib_distinguished f) (1 : ℤ)
  have hzTs : a ≫ Ts.mor₂ = 0 := by
    simpa [Ts, T, Pretriangulated.Triangle.shiftFunctor, chosenCofiberTriangle] using hz
  obtain ⟨y', hy'⟩ := Pretriangulated.Triangle.coyoneda_exact₂ Ts hTs a hzTs
  refine ⟨-y', ?_⟩
  have hm : Ts.mor₁ = -((shiftFunctor Syn (1 : ℤ)).map f) := by
    simp [Ts, T, Pretriangulated.Triangle.shiftFunctor, chosenCofiberTriangle]
  rw [hm] at hy'
  change (-y') ≫ (shiftFunctor Syn (1 : ℤ)).map f = a
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using hy'.symm

/-- Caps with the same divided target have λ-boundary representatives whose
difference factors through the next boundary-tower stage.  Consequently,
their single-λ boundaries differ by one higher Adams filtration step. -/
theorem exists_nextStage_of_capStageBoundary_sub_of_same_dividedTarget
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    (G : Input X) (S : Syn) (s r n : ℕ)
    (c d : G.CapRepresentatives S s r n)
    (hdivided : G.capDividedTarget S s r n c =
      G.capDividedTarget S s r n d) :
    ∃ y' : S ⟶ (G.boundaryTarget n).stage (s + r + 1),
      y' ≫ (G.boundaryTarget n).transition (s + r) (s + r + 1)
        (Nat.le_succ _) =
          G.capStageBoundary S s r n c - G.capStageBoundary S s r n d := by
  have hzero : G.capDividedTarget S s r n (c - d) = 0 := by
    change ((c - d) ≫ syn_functorial_cofiber.cofibδ
      (lambdaPow n (G.stage (s + r)) ≫
        G.transition s (s + r) (Nat.le_add_right s r))) ≫
          G.dividedLayerProjection n (s + r) = 0
    rw [Preadditive.sub_comp, Preadditive.sub_comp]
    change G.capDividedTarget S s r n c -
      G.capDividedTarget S s r n d = 0
    exact sub_eq_zero.mpr hdivided
  obtain ⟨y', hy'⟩ :=
    G.capStageBoundary_lifts_of_capDividedTarget_eq_zero S s r n (c - d) hzero
  refine ⟨y', ?_⟩
  simpa only [map_sub] using hy'

/-- The remaining-power map from `λ^(n+1)` to `λ` is compatible with one
transition of the boundary towers. -/
theorem boundaryTarget_transition_lambdaPowerToOne
    (G : Input X) (n b : ℕ) :
    (G.boundaryTarget (n + 1)).transition b (b + 1) (Nat.le_succ b) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne (G.stage b) n) =
      (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne (G.stage (b + 1)) n) ≫
        (G.boundaryTarget 1).transition b (b + 1) (Nat.le_succ b) := by
  change (shiftFunctor Syn (1 : ℤ)).map
      ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).map
        (G.transition b (b + 1) (Nat.le_succ b))) ≫
      (shiftFunctor Syn (1 : ℤ)).map
        (lambdaPowerToOne (G.stage b) n) =
    (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne (G.stage (b + 1)) n) ≫
      (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, (-1 : ℤ))).map
          (G.transition b (b + 1) (Nat.le_succ b)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((shiftFunctor Syn (1 : ℤ)).map)
    ((lambdaPowerToOneNatTrans n).naturality
      (G.transition b (b + 1) (Nat.le_succ b)))

/-- After restriction to the first quotient, the actual lambda boundary
retains the remaining power at the deep stage. For an Adams differential
of length `n+2` this power is `n`, i.e. length minus two. -/
theorem capQuotientClass_toOne_boundary (G : Input X) (S : Syn) (s r n : ℕ)
    (c : G.CapRepresentatives S s r (n + 1)) :
    (G.capQuotientClass S s r (n + 1) c ≫ XModLambdaN.toOne X n) ≫
        lambdaBocksteinConnecting X =
      (G.capStageBoundary S s r (n + 1) c ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne (G.stage (s + r)) n)) ≫
            (G.boundaryTarget 1).toBase (s + r) :=
  G.toOne_boundary_formula n S (s + r) _ _
    (G.capQuotientClass_boundary S s r (n + 1) c)

/-- Equal divided targets give equal single-λ boundary classes on the
current associated graded: their difference belongs to the next target
filtration. -/
theorem capToOne_boundary_sub_mem_next_of_same_dividedTarget
    [SyntheticShiftCofiberCompatibility (Syn := Syn)]
    (G : Input X) (S : Syn) (s r n : ℕ)
    (c d : G.CapRepresentatives S s r (n + 1))
    (hdivided : G.capDividedTarget S s r (n + 1) c =
      G.capDividedTarget S s r (n + 1) d) :
    (G.boundaryTarget 1).AFGe
      ((G.capQuotientClass S s r (n + 1) c ≫ XModLambdaN.toOne X n) ≫
          lambdaBocksteinConnecting X -
        (G.capQuotientClass S s r (n + 1) d ≫ XModLambdaN.toOne X n) ≫
          lambdaBocksteinConnecting X)
      (s + r + 1) := by
  obtain ⟨y', hy'⟩ :=
    G.exists_nextStage_of_capStageBoundary_sub_of_same_dividedTarget
      S s r (n + 1) c d hdivided
  let e := (shiftFunctor Syn (1 : ℤ)).map
    (lambdaPowerToOne (G.stage (s + r + 1)) n)
  refine ⟨y' ≫ e, ?_⟩
  have hnatural := G.boundaryTarget_transition_lambdaPowerToOne n (s + r)
  have hc := G.capQuotientClass_toOne_boundary S s r n c
  have hd := G.capQuotientClass_toOne_boundary S s r n d
  calc
    (y' ≫ e) ≫ (G.boundaryTarget 1).toBase (s + r + 1) =
        y' ≫ e ≫ ((G.boundaryTarget 1).transition (s + r) (s + r + 1)
          (Nat.le_succ _) ≫ (G.boundaryTarget 1).toBase (s + r)) := by
          rw [(G.boundaryTarget 1).transition_toBase]
          simp only [Category.assoc]
    _ = y' ≫ ((G.boundaryTarget (n + 1)).transition (s + r) (s + r + 1)
          (Nat.le_succ _) ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPowerToOne (G.stage (s + r)) n)) ≫
          (G.boundaryTarget 1).toBase (s + r) := by
          have h := congrArg
            (fun f => y' ≫ f ≫ (G.boundaryTarget 1).toBase (s + r))
            hnatural.symm
          simpa only [Category.assoc, e] using h
    _ = (G.capStageBoundary S s r (n + 1) c -
        G.capStageBoundary S s r (n + 1) d) ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPowerToOne (G.stage (s + r)) n) ≫
          (G.boundaryTarget 1).toBase (s + r) := by
            have h := congrArg
              (fun f => f ≫ (shiftFunctor Syn (1 : ℤ)).map
                (lambdaPowerToOne (G.stage (s + r)) n) ≫
                  (G.boundaryTarget 1).toBase (s + r)) hy'
            simpa only [Category.assoc] using h
    _ = _ := by
      simpa only [Preadditive.sub_comp, Category.assoc] using
        (congrArg₂ (fun f g => f - g) hc hd).symm

/-- Equality of source page classes gives equality of the divided boundary
classes. This is independence of the chosen geometric filling. -/
theorem capDividedTargets_eq_of_sources_eq (G : Input X) (R : G.FreeLayers)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (c d : G.CapRepresentatives (Smn m (m + s)) s r (r - 1))
    (h : G.capSourceClass (Smn m (m + s)) s r (by omega) (r - 1) c =
      G.capSourceClass (Smn m (m + s)) s r (by omega) (r - 1) d) :
    (QuotientAddGroup.mk (G.capDividedTargetHom (Smn m (m + s)) s r (r - 1) c) :
      G.DividedTargetPage (Smn m (m + s)) s r (by omega) (r - 1)) =
        QuotientAddGroup.mk (G.capDividedTargetHom (Smn m (m + s)) s r (r - 1) d) := by
  apply (G.dividedTargetEquiv R s r hr m).injective
  exact (G.pageObstruction_capSourceClass (Smn m (m + s)) s r (by omega) (r - 1) c).symm.trans
    ((congrArg (G.pageObstruction (Smn m (m + s)) s r (by omega)) h).trans
      (G.pageObstruction_capSourceClass (Smn m (m + s)) s r (by omega) (r - 1) d))

/-! ## Compatibility with passage to the next page -/

/-- The comparison restricts to the actual kernels of the two differentials. -/
noncomputable def capKernelEquiv (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ) :
    (G.capDifferential (Smn m (m + s)) s r (by omega) (r - 1)).ker ≃+
      (G.pageObstruction (Smn m (m + s)) s r (by omega)).ker where
  toFun x := ⟨G.capPageEquiv R A s r hr m x, by
    change G.pageObstruction (Smn m (m + s)) s r (by omega)
      (G.capPageEquiv R A s r hr m x.val) = 0
    rw [G.capPageEquiv_comm_d R A s r hr m, x.property, map_zero]⟩
  invFun y := ⟨(G.capPageEquiv R A s r hr m).symm y, by
    apply (G.dividedTargetEquiv R s r hr m).injective
    rw [map_zero, ← G.capPageEquiv_comm_d R A s r hr m, AddEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- Incoming boundaries in cap cycles are determined by the tower's
next incoming-boundary group via the proved kernel equivalence. -/
noncomputable def capIncomingInKernel (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ) :
    AddSubgroup (G.capDifferential (Smn m (m + s)) s r (by omega) (r - 1)).ker :=
  (G.newBoundariesInKernel (Smn m (m + s)) s r (by omega)).comap
    (G.capKernelEquiv R A s r hr m).toAddMonoidHom

/-- Taking cycles modulo the new incoming boundaries gives the next cap
page. This uses the tower's previously proved kernel and image rules. -/
noncomputable def capNextPageHomologyEquiv (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ) :
    ((G.capDifferential (Smn m (m + s)) s r
        (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 1)) hr) (r - 1)).ker ⧸
      G.capIncomingInKernel R A s r hr m) ≃+
        G.CapPage (Smn m (m + s)) s (r + 1) (by omega) (r + 1 - 1) :=
  (quotientAddEquivOfAddEquiv (G.capKernelEquiv R A s r hr m)
    _ _ (fun _ => Iff.rfl)).trans
      ((G.nextPageHomologyEquiv (Smn m (m + s)) s r (by omega)).trans
        (G.capPageEquiv R A s (r + 1) (by omega) m).symm)

end GeometricAdams.Input
end KIPBase.Synthetic
