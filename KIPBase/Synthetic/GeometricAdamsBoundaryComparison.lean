import KIPBase.Synthetic.GeometricAdamsPending

/-!
# Actual boundary formulas after the two deferred geometric steps

No placeholder occurs in this file. The common cone retains the specified
source page class, and its connecting map gives the divided target. The
converse is proved as well, so the capping condition characterizes the
geometric page differential, including its nonzero condition.

This is a comparison of actual geometric representatives. Identification
of these representatives with the legacy Adams/ESS filtrations is separate.
-/

namespace KIPBase.Synthetic.GeometricAdams.Input

open CategoryTheory CategoryTheory.Limits

universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]
    {X : Syn}

/-- Projection of a divided stage target to its divided adjacent layer. -/
noncomputable def dividedLayerProjection (G : Input X) (n b : ℕ) :
    (G.boundaryTarget n).stage b ⟶
      (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -(n : ℤ))).obj (G.layer b)) :=
  (shiftFunctor Syn (1 : ℤ)).map
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map
      (syn_functorial_cofiber.cofibι (G.transition b (b + 1) (Nat.le_succ b))))

/-- Multiplication and the adjacent-layer projection commute. This uses
the actual natural transformation λ, not a page action with the same name. -/
theorem dividedLayerProjection_lambda (G : Input X) (n b : ℕ) :
    G.dividedLayerProjection n b ≫
        (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.layer b)) =
      (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.stage b)) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (syn_functorial_cofiber.cofibι
            (G.transition b (b + 1) (Nat.le_succ b))) := by
  dsimp only [dividedLayerProjection]
  rw [← Functor.map_comp, lambdaPow_naturality, Functor.map_comp]

/-- The source page class retained by a common-cone representative. -/
noncomputable def capSourceClass (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (c : S ⟶ LambdaCofiberGeometry.commonCone
      (G.transition s (s + r) (Nat.le_add_right s r)) n) :
    G.PageGroup S s r hr :=
  QuotientAddGroup.mk
    (⟨G.source S s r hr
        (c ≫ LambdaCofiberGeometry.toRelative
          (G.transition s (s + r) (Nat.le_add_right s r)) n),
      ⟨_, rfl⟩⟩ : G.sourceCycles S s r hr)

/-- Read the divided layer target from the actual common-cone boundary. -/
noncomputable def capDividedTarget (G : Input X) (S : Syn) (s r n : ℕ)
    (c : S ⟶ LambdaCofiberGeometry.commonCone
      (G.transition s (s + r) (Nat.le_add_right s r)) n) :
    S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj (G.layer (s + r))) :=
  (c ≫ syn_functorial_cofiber.cofibδ
    (lambdaPow n (G.stage (s + r)) ≫
      G.transition s (s + r) (Nat.le_add_right s r))) ≫
    G.dividedLayerProjection n (s + r)

/-- The geometric Adams differential of a cap is λ^n times its divided
target. The formula is proved on the actual page quotient. -/
theorem pageObstruction_capSourceClass (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (c : S ⟶ LambdaCofiberGeometry.commonCone
      (G.transition s (s + r) (Nat.le_add_right s r)) n) :
    G.pageObstruction S s r hr (G.capSourceClass S s r hr n c) =
      QuotientAddGroup.mk
        (G.capDividedTarget S s r n c ≫
          (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.layer (s + r)))) := by
  rw [capSourceClass, pageObstruction_mk, obstruction_source]
  apply congrArg QuotientAddGroup.mk
  change (c ≫ LambdaCofiberGeometry.toRelative _ n) ≫
      (G.boundary s (s + r) _ ≫ _) =
    ((c ≫ _) ≫ G.dividedLayerProjection n (s + r)) ≫ _
  dsimp only [boundary]
  rw [Category.assoc, ← Category.assoc
    (LambdaCofiberGeometry.toRelative _ n),
    LambdaCofiberGeometry.toRelative_boundary]
  rw [Category.assoc, Category.assoc, Category.assoc,
    G.dividedLayerProjection_lambda]

/-- A capping witness specifies both the source page class and the divided
adjacent-layer target. This definition contains only actual cofiber maps. -/
def CapRealizes (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) (n : ℕ)
    (x : G.PageGroup S s r hr)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj (G.layer (s + r)))) : Prop :=
  ∃ c : S ⟶ LambdaCofiberGeometry.commonCone
      (G.transition s (s + r) (Nat.le_add_right s r)) n,
    G.capSourceClass S s r hr n c = x ∧ G.capDividedTarget S s r n c = y

/-- Every cap gives the specified page differential. This direction has
no dependency on either deferred step. -/
theorem CapRealizes.pageObstruction {G : Input X} {S : Syn}
    {s r : ℕ} {hr : 1 ≤ r} {n : ℕ} {x y}
    (h : G.CapRealizes S s r hr n x y) :
    G.pageObstruction S s r hr x = QuotientAddGroup.mk
      (y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.layer (s + r)))) := by
  obtain ⟨c, rfl, rfl⟩ := h
  exact G.pageObstruction_capSourceClass S s r hr n c

/-- After step 2, the common-cone capping condition is equivalent to the
specified geometric page differential. The target is the prescribed layer
class, so no existentially chosen replacement target is substituted. -/
theorem capRealizes_iff_pageObstruction (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (x : G.PageGroup (Smn m (m + s)) s r (by omega))
    (y : Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj (G.layer (s + r)))) :
    G.CapRealizes (Smn m (m + s)) s r (by omega) (r - 1) x y ↔
      G.pageObstruction (Smn m (m + s)) s r (by omega) x =
        QuotientAddGroup.mk
          (y ≫
            (shiftFunctor Syn (1 : ℤ)).map
              (lambdaPow (r - 1) (G.layer (s + r)))) := by
  constructor
  · exact CapRealizes.pageObstruction
  · intro hxy
    obtain ⟨z, y', hz, hy', hzy⟩ :=
      Deferred.correctedBoundary G R A s r hr m x y hxy
    obtain ⟨c, hc, hcy⟩ := LambdaCofiberGeometry.exists_commonLift_of_relative_boundary
      (G.transition s (s + r) (Nat.le_add_right s r)) (r - 1) z y' hzy
    refine ⟨c, ?_, ?_⟩
    · simpa only [capSourceClass, hc] using hz
    · change (c ≫ _) ≫ G.dividedLayerProjection (r - 1) (s + r) = _
      rw [hcy]
      exact hy'

/-- Nonzero geometric differentials correspond exactly to caps whose
multiplied target is not a shorter incoming boundary. This tests nonzero
on the page quotient, rather than just on a chosen layer representative. -/
theorem essential_cap_iff (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
    (x : G.PageGroup (Smn m (m + s)) s r (by omega))
    (y : Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj (G.layer (s + r)))) :
    (G.pageObstruction (Smn m (m + s)) s r (by omega) x =
        QuotientAddGroup.mk
          (y ≫
            (shiftFunctor Syn (1 : ℤ)).map
              (lambdaPow (r - 1) (G.layer (s + r)))) ∧
      G.pageObstruction (Smn m (m + s)) s r (by omega) x ≠ 0) ↔
    (G.CapRealizes (Smn m (m + s)) s r (by omega) (r - 1) x y ∧
      (y ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.layer (s + r)))) ∉
        G.suspendedBoundaries (Smn m (m + s)) (s + 1) (s + r) (by omega)) := by
  have hne : (QuotientAddGroup.mk
      (y ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.layer (s + r)))) :
      _ ⧸ G.targetAmbiguity (Smn m (m + s)) s r (by omega)) ≠ 0 ↔
      (y ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.layer (s + r)))) ∉
        G.suspendedBoundaries (Smn m (m + s)) (s + 1) (s + r) (by omega) := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, G.targetAmbiguity_eq_suspendedBoundaries]
  constructor
  · rintro ⟨hxy, hn⟩
    exact ⟨(G.capRealizes_iff_pageObstruction R A s r hr m x y).mpr hxy,
      hne.mp (hxy ▸ hn)⟩
  · rintro ⟨hc, hn⟩
    have hxy := hc.pageObstruction
    exact ⟨hxy, hxy.symm ▸ hne.mpr hn⟩

/-- Read the actual single-λ boundary of the cap associated to a given
geometric differential. The source page class and source filtration are
retained, and the boundary lies in the specified deeper target filtration.
The length is `n+2`, so the remaining target exponent is `n = r-2`. -/
theorem exists_singleBoundary_of_pageObstruction (G : Input X) (R : G.FreeLayers)
    (A : G.SyntheticAdamsGeometricRealization R)
    (s n : ℕ) (m : ℤ)
    (x : G.PageGroup (Smn m (m + s)) s (n + 2) (by omega))
    (y : Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).obj (G.layer (s + (n + 2)))))
    (hxy : G.pageObstruction (Smn m (m + s)) s (n + 2) (by omega) x =
      QuotientAddGroup.mk
        (y ≫
          (shiftFunctor Syn (1 : ℤ)).map (lambdaPow (n + 1) (G.layer (s + (n + 2)))))) :
    ∃ (c : Smn m (m + s) ⟶ LambdaCofiberGeometry.commonCone
        (G.transition s (s + (n + 2)) (Nat.le_add_right s (n + 2))) (n + 1))
      (y' : Smn m (m + s) ⟶ (G.boundaryTarget (n + 1)).stage (s + (n + 2)))
      (w : Smn m (m + s) ⟶ XModLambdaN X 1),
      G.capSourceClass (Smn m (m + s)) s (n + 2) (by omega) (n + 1) c = x ∧
      (((c ≫ LambdaCofiberGeometry.toQuotient
        (G.transition s (s + (n + 2)) (Nat.le_add_right s (n + 2))) (n + 1)) ≫
          XModLambdaN.map (G.toBase s) (n + 1)) ≫ XModLambdaN.toOne X n) = w ∧
      y' ≫ G.dividedLayerProjection (n + 1) (s + (n + 2)) = y ∧
      (G.quotient 1).AFGe w s ∧
      w ≫ lambdaBocksteinConnecting X =
        (y' ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne (G.stage (s + (n + 2))) n)) ≫
            (G.boundaryTarget 1).toBase (s + (n + 2)) ∧
      (G.boundaryTarget 1).AFGe (w ≫ lambdaBocksteinConnecting X) (s + (n + 2)) := by
  obtain ⟨z, y', hz, hy', hzy⟩ :=
    Deferred.correctedBoundary G R A s (n + 2) (by omega) m x y hxy
  obtain ⟨c, w, hc, hcw, hw, hb, hbf⟩ :=
    G.exists_singleCap (Smn m (m + s)) s (n + 2) n z y' hzy
  exact ⟨c, y', w, by simpa only [capSourceClass, hc] using hz,
    hcw, hy', hw, hb, hbf⟩

end KIPBase.Synthetic.GeometricAdams.Input
