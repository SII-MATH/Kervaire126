import KIPBase.Synthetic.LambdaBoundary

/-!
# Geometric entry for synthetic Adams

The input is an actual tower with its bottom identified with the object.
Relative representatives, their source classes, and their boundary targets
are constructed from cofibers. No spectral sequence, comparison isomorphism,
or realization theorem is an input field.

This module constructs relative representatives, the page quotients, their
boundary-induced obstruction maps, the next-cycle and incoming-image rules,
the kernel-modulo-boundaries description of the next page, and actual tower
naturality (including lambda). It does not yet assemble these groups into
the existing integer-graded `SpectralSequence` structure or identify them
with the legacy `SynAdamsSS`.
-/

namespace KIPBase.Synthetic.GeometricAdams

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {Syn : Type u} [Category.{v} Syn]

/-- An actual tower over an object, the geometric input for the construction.
An arbitrary tower is not asserted to be an Adams resolution. -/
structure Input (X : Syn) where
  tower : SyntheticCofiberTower Syn
  baseIso : tower.stage 0 ≅ X

namespace Input

variable {X : Syn}

/-- Use a supplied tower directly, with its own stage zero as base. -/
def ofTower (T : SyntheticCofiberTower Syn) : Input (T.stage 0) :=
  ⟨T, Iso.refl _⟩

abbrev stage (G : Input X) (s : ℕ) : Syn := G.tower.stage s

abbrev transition (G : Input X) (a b : ℕ) (h : a ≤ b) :
    G.stage b ⟶ G.stage a := G.tower.transition a b h

/-- The actual map from a stage to the specified base object. -/
def toBase (G : Input X) (s : ℕ) : G.stage s ⟶ X :=
  G.transition 0 s (Nat.zero_le s) ≫ G.baseIso.hom

@[reassoc] theorem transition_toBase (G : Input X) (a b : ℕ) (h : a ≤ b) :
    G.transition a b h ≫ G.toBase a = G.toBase b := by
  dsimp only [toBase, transition]
  rw [← Category.assoc, SyntheticCofiberTower.transition_comp]

/-- Apply an actual functor to every stage and the base identification. -/
def map (G : Input X) (F : Syn ⥤ Syn) : Input (F.obj X) :=
  ⟨G.tower ⋙ F, F.mapIso G.baseIso⟩

@[simp] theorem map_toBase (G : Input X) (F : Syn ⥤ Syn) (s : ℕ) :
    (G.map F).toBase s = F.map (G.toBase s) := by
  exact (F.map_comp _ _).symm

section Additive
variable [Preadditive Syn]

/-- Filtration by actual factorizations through the named stage. -/
def filtration (G : Input X) (S : Syn) (s : ℕ) : AddSubgroup (S ⟶ X) :=
  AddMonoidHom.range
    { toFun := fun f : S ⟶ G.stage s => f ≫ G.toBase s
      map_zero' := zero_comp
      map_add' := fun _ _ => by simp only [Preadditive.add_comp] }

theorem mem_filtration (G : Input X) (S : Syn) (s : ℕ) (f : S ⟶ X) :
    f ∈ G.filtration S s ↔ ∃ g : S ⟶ G.stage s, g ≫ G.toBase s = f := Iff.rfl

theorem filtration_antitone (G : Input X) (S : Syn) :
    Antitone (G.filtration S) := by
  intro a b hab f hf
  obtain ⟨g, rfl⟩ := hf
  refine ⟨g ≫ G.transition a b hab, ?_⟩
  change (g ≫ G.transition a b hab) ≫ G.toBase a = g ≫ G.toBase b
  rw [Category.assoc, G.transition_toBase]

/-- The bottom filtration is exhaustive by the supplied base isomorphism. -/
theorem filtration_zero (G : Input X) (S : Syn) : G.filtration S 0 = ⊤ := by
  apply top_unique
  intro f _
  refine ⟨f ≫ G.baseIso.inv, ?_⟩
  simp [toBase, transition, SyntheticCofiberTower.transition_self]

/-- Filtration at least `s` is a proposition, not a numerical function. -/
def AFGe (G : Input X) {S : Syn} (f : S ⟶ X) (s : ℕ) : Prop :=
  f ∈ G.filtration S s

/-- Exact filtration is defined from the two successive lower bounds. -/
def AFEq (G : Input X) {S : Syn} (f : S ⟶ X) (s : ℕ) : Prop :=
  G.AFGe f s ∧ ¬ G.AFGe f (s + 1)

theorem afGe_antitone (G : Input X) {S : Syn} (f : S ⟶ X)
    {a b : ℕ} (h : a ≤ b) (hf : G.AFGe f b) : G.AFGe f a :=
  G.filtration_antitone S h hf

end Additive

variable [Preadditive Syn] [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn]

/-- The relative object of two actual stages. -/
noncomputable abbrev relative (G : Input X) (a b : ℕ) (h : a ≤ b) : Syn :=
  syn_functorial_cofiber.cofib (G.transition a b h)

/-- An adjacent layer of the tower. -/
noncomputable abbrev layer (G : Input X) (s : ℕ) : Syn :=
  G.relative s (s + 1) (Nat.le_succ s)

/-- A stage class whose image in the adjacent layer is zero lifts to the
next stage.  This is the cofiber exactness step that turns a zero layer
target into membership in the next filtration. -/
theorem exists_stageLift_of_layer_zero (G : Input X) (S : Syn) (s : ℕ)
    (a : S ⟶ G.stage s)
    (ha : a ≫ syn_functorial_cofiber.cofibι
      (G.transition s (s + 1) (Nat.le_succ s)) = 0) :
    ∃ a' : S ⟶ G.stage (s + 1),
      a' ≫ G.transition s (s + 1) (Nat.le_succ s) = a := by
  obtain ⟨a', ha'⟩ := Triangle.coyoneda_exact₂ _
    (syn_functorial_cofiber.cofib_distinguished
      (G.transition s (s + 1) (Nat.le_succ s))) a ha
  exact ⟨a', ha'.symm⟩

/-- Projection of a relative representative to its adjacent source layer. -/
noncomputable def sourceProjection (G : Input X) (s b : ℕ) (h : s + 1 ≤ b) :
    G.relative s b (by omega) ⟶ G.layer s :=
  syn_functorial_cofiber.cofibMap (G.transition s b (by omega))
    (G.transition s (s + 1) (Nat.le_succ s))
    (G.transition (s + 1) b h) (𝟙 (G.stage s))
    (by simpa only [Category.comp_id] using
      G.tower.transition_comp s (s + 1) b (Nat.le_succ s) h)

/-- Restrict a relative representative to a shallower endpoint. -/
noncomputable def relativeRestriction (G : Input X) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    G.relative a c (hab.trans hbc) ⟶ G.relative a b hab :=
  syn_functorial_cofiber.cofibMap (G.transition a c (hab.trans hbc))
    (G.transition a b hab) (G.transition b c hbc) (𝟙 (G.stage a))
    (by simpa only [Category.comp_id] using G.tower.transition_comp a b c hab hbc)

/-- Restriction of representatives preserves their adjacent-layer source. -/
@[reassoc] theorem relativeRestriction_sourceProjection
    (G : Input X) (s b c : ℕ) (hab : s + 1 ≤ b) (hbc : b ≤ c) :
    G.relativeRestriction s b c (by omega) hbc ≫ G.sourceProjection s b hab =
      G.sourceProjection s c (hab.trans hbc) := by
  dsimp only [relativeRestriction, sourceProjection]
  rw [syn_functorial_cofiber.cofibMap_comp]
  congr 1
  · exact G.tower.transition_comp (s + 1) b c hab hbc
  · simp

@[simp] theorem sourceProjection_self (G : Input X) (s : ℕ) :
    G.sourceProjection s (s + 1) le_rfl = 𝟙 (G.layer s) := by
  calc
    G.sourceProjection s (s + 1) le_rfl =
        syn_functorial_cofiber.cofibMap
          (G.transition s (s + 1) (Nat.le_succ s))
          (G.transition s (s + 1) (Nat.le_succ s))
          (𝟙 _) (𝟙 _) (by simp) := by
      dsimp only [sourceProjection]
      congr 1
      exact G.tower.transition_self (s + 1)
    _ = _ := syn_functorial_cofiber.cofibMap_id _

/-- The actual relative connecting map, before passage to page quotients. -/
noncomputable def boundary (G : Input X) (s b : ℕ) (h : s ≤ b) :
    G.relative s b h ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.stage b) :=
  syn_functorial_cofiber.cofibδ (G.transition s b h)

/-- Projection of the relative boundary to the target adjacent layer. -/
noncomputable def targetProjection (G : Input X) (s b : ℕ) (h : s ≤ b) :
    G.relative s b h ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer b) :=
  G.boundary s b h ≫ (shiftFunctor Syn (1 : ℤ)).map
    (syn_functorial_cofiber.cofibι (G.transition b (b + 1) (Nat.le_succ b)))

/-- Source projection preserves the actual boundary after inclusion
from the deeper stage. -/
@[reassoc] theorem sourceProjection_boundary
    (G : Input X) (s b : ℕ) (h : s + 1 ≤ b) :
    G.sourceProjection s b h ≫ G.boundary s (s + 1) (Nat.le_succ s) =
      G.boundary s b (by omega) ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.transition (s + 1) b h) :=
  syn_functorial_cofiber.cofibMap_δ _ _ _ _ _

/-- Restriction between relative objects respects their actual boundaries. -/
@[reassoc] theorem relativeRestriction_boundary (G : Input X) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    G.relativeRestriction a b c hab hbc ≫ G.boundary a b hab =
      G.boundary a c (hab.trans hbc) ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.transition b c hbc) :=
  syn_functorial_cofiber.cofibMap_δ _ _ _ _ _

/-- Lift a specified relative class to a deeper endpoint when its boundary
lifts there. Exactness first constructs the boundary lift; a correction
from the shallow stage restores the specified relative class itself. -/
theorem exists_relativeLift (G : Input X) (S : Syn) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c)
    (z : S ⟶ G.relative a b hab)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.stage c))
    (hzy : z ≫ G.boundary a b hab =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (G.transition b c hbc)) :
    ∃ z' : S ⟶ G.relative a c (hab.trans hbc),
      z' ≫ G.relativeRestriction a b c hab hbc = z ∧
      z' ≫ G.boundary a c (hab.trans hbc) = y := by
  have hzero : G.boundary a b hab ≫
      (shiftFunctor Syn (1 : ℤ)).map (G.transition a b hab) = 0 :=
    comp_distTriang_mor_zero₃₁ _
      (syn_functorial_cofiber.cofib_distinguished (G.transition a b hab))
  have hy : y ≫ (shiftFunctor Syn (1 : ℤ)).map
      (G.transition a c (hab.trans hbc)) = 0 := by
    have hcomp : G.transition b c hbc ≫ G.transition a b hab =
        G.transition a c (hab.trans hbc) := G.tower.transition_comp a b c hab hbc
    rw [← hcomp, Functor.map_comp,
      ← Category.assoc, ← hzy, Category.assoc, hzero, comp_zero]
  obtain ⟨z', hz'⟩ := Triangle.coyoneda_exact₁ _
    (syn_functorial_cofiber.cofib_distinguished
      (G.transition a c (hab.trans hbc))) y hy
  change S ⟶ G.relative a c (hab.trans hbc) at z'
  change y = z' ≫ G.boundary a c (hab.trans hbc) at hz'
  have hz : (z - z' ≫ G.relativeRestriction a b c hab hbc) ≫
      G.boundary a b hab = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, G.relativeRestriction_boundary,
      ← Category.assoc, ← hz', hzy, sub_self]
  obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₃ _
    (syn_functorial_cofiber.cofib_distinguished (G.transition a b hab)) _ hz
  change S ⟶ G.stage a at q
  change z - z' ≫ G.relativeRestriction a b c hab hbc =
    q ≫ syn_functorial_cofiber.cofibι (G.transition a b hab) at hq
  have hi : syn_functorial_cofiber.cofibι (G.transition a c (hab.trans hbc)) ≫
      G.relativeRestriction a b c hab hbc =
        syn_functorial_cofiber.cofibι (G.transition a b hab) := by
    exact (syn_functorial_cofiber.cofibMap_ι _ _ _ _ _).symm.trans
      (Category.id_comp _)
  refine ⟨z' + q ≫ syn_functorial_cofiber.cofibι
    (G.transition a c (hab.trans hbc)), ?_, ?_⟩
  · rw [Preadditive.add_comp, Category.assoc, hi, ← hq]
    abel
  · have hiδ : syn_functorial_cofiber.cofibι (G.transition a c (hab.trans hbc)) ≫
        G.boundary a c (hab.trans hbc) = 0 :=
      comp_distTriang_mor_zero₂₃ _
        (syn_functorial_cofiber.cofib_distinguished (G.transition a c (hab.trans hbc)))
    rw [Preadditive.add_comp, Category.assoc, hiδ, comp_zero, add_zero]
    exact hz'.symm

/-- Relative classes representing a differential of length `r`.
The actual Adams bidegrees are supplied by choosing `S` to be a sphere. -/
abbrev Representative (G : Input X) (S : Syn) (s r : ℕ) :=
  S ⟶ G.relative s (s + r) (Nat.le_add_right s r)

/-- Read the source of a geometric representative. -/
noncomputable def source (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    G.Representative S s r →+ (S ⟶ G.layer s) where
  toFun z := z ≫ G.sourceProjection s (s + r) (by omega)
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- Read its differential target by taking the actual relative boundary. -/
noncomputable def target (G : Input X) (S : Syn) (s r : ℕ) :
    G.Representative S s r →+
      (S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) where
  toFun z := z ≫ G.targetProjection s (s + r) (Nat.le_add_right s r)
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- The geometric representative relation. Page quotients still have to
be constructed; this is not an assertion about the legacy page differential. -/
def RepresentativeRelation (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : S ⟶ G.layer s)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) : Prop :=
  ∃ z : G.Representative S s r,
    G.source S s r hr z = x ∧ G.target S s r z = y

/-- Every relative representative supplies both sides of its relation. -/
theorem representativeRelation (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (z : G.Representative S s r) :
    G.RepresentativeRelation S s r hr
      (G.source S s r hr z) (G.target S s r z) := ⟨z, rfl, rfl⟩

/-- A representative whose actual relative boundary vanishes has zero target. -/
theorem target_zero_of_boundary_zero (G : Input X) (S : Syn) (s r : ℕ)
    (z : G.Representative S s r)
    (hz : z ≫ G.boundary s (s + r) (Nat.le_add_right s r) = 0) :
    G.target S s r z = 0 := by
  change z ≫ (G.boundary s (s + r) _ ≫ _) = 0
  rw [← Category.assoc, hz, zero_comp]

/-- Taking the next connecting map kills the boundary target. This is
the geometric zero-composite used to construct page differentials. -/
theorem target_comp_next_boundary (G : Input X) (S : Syn) (s r : ℕ)
    (z : G.Representative S s r) :
    G.target S s r z ≫ (shiftFunctor Syn (1 : ℤ)).map
      (G.boundary (s + r) (s + r + 1) (Nat.le_succ (s + r))) = 0 := by
  have h : syn_functorial_cofiber.cofibι
      (G.transition (s + r) (s + r + 1) (Nat.le_succ _)) ≫
      G.boundary (s + r) (s + r + 1) (Nat.le_succ _) = 0 :=
    comp_distTriang_mor_zero₂₃ _ (syn_functorial_cofiber.cofib_distinguished _)
  change (z ≫ (G.boundary s (s + r) _ ≫ _)) ≫ _ = 0
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, h,
    Functor.map_zero, comp_zero, comp_zero]

/-! ### A well-defined obstruction from relative representatives -/

/-- Vanishing of the actual target is precisely the condition for lifting
the same relative representative one stage further. The forward direction
uses the rotated cofiber triangle and the source-preserving correction. -/
theorem target_eq_zero_iff_relativeLift (G : Input X) (S : Syn) (s r : ℕ)
    (z : G.Representative S s r) :
    G.target S s r z = 0 ↔
      ∃ z' : G.Representative S s (r + 1),
        z' ≫ G.relativeRestriction s (s + r) (s + r + 1)
          (Nat.le_add_right s r) (Nat.le_succ _) = z := by
  let j := G.transition (s + r) (s + r + 1) (Nat.le_succ _)
  constructor
  · intro hz
    have hz' : (z ≫ G.boundary s (s + r) (Nat.le_add_right s r)) ≫
        (shiftFunctor Syn (1 : ℤ)).map (syn_functorial_cofiber.cofibι j) = 0 := by
      change z ≫ (G.boundary s (s + r) _ ≫ _) = 0 at hz
      exact (Category.assoc _ _ _).trans hz
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₁ _
      (rot_of_distTriang _ (syn_functorial_cofiber.cofib_distinguished j)) _ hz'
    change S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.stage (s + r + 1)) at y
    change z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
      y ≫ (-(shiftFunctor Syn (1 : ℤ)).map j) at hy
    have hy' : z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
        (-y) ≫ (shiftFunctor Syn (1 : ℤ)).map j := by
      exact hy.trans
        ((Preadditive.comp_neg y ((shiftFunctor Syn (1 : ℤ)).map j)).trans
          (Preadditive.neg_comp y ((shiftFunctor Syn (1 : ℤ)).map j)).symm)
    obtain ⟨z', hz', _⟩ := G.exists_relativeLift S s (s + r) (s + r + 1)
      (Nat.le_add_right s r) (Nat.le_succ _) z (-y) hy'
    exact ⟨z', hz'⟩
  · rintro ⟨z', rfl⟩
    have hj : j ≫ syn_functorial_cofiber.cofibι j = 0 :=
      comp_distTriang_mor_zero₁₂ _ (syn_functorial_cofiber.cofib_distinguished j)
    change (z' ≫ G.relativeRestriction s (s + r) (s + r + 1) _ _) ≫
      (G.boundary s (s + r) _ ≫ (shiftFunctor Syn (1 : ℤ)).map
        (syn_functorial_cofiber.cofibι j)) = 0
    rw [← Category.assoc, Category.assoc z', G.relativeRestriction_boundary,
      Category.assoc, Category.assoc, ← Functor.map_comp, hj,
      Functor.map_zero, comp_zero, comp_zero]

/-- Adjacent-layer classes admitting a representative over `r` stages. -/
noncomputable def sourceCycles (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    AddSubgroup (S ⟶ G.layer s) := (G.source S s r hr).range

/-- Longer relative lifts give a decreasing sequence of source cycles. -/
theorem sourceCycles_antitone (G : Input X) (S : Syn) (s a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b) :
    G.sourceCycles S s b hb ≤ G.sourceCycles S s a ha := by
  intro x hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z ≫ G.relativeRestriction s (s + a) (s + b)
    (Nat.le_add_right s a) (by omega), ?_⟩
  change (z ≫ G.relativeRestriction s (s + a) (s + b) _ _) ≫
    G.sourceProjection s (s + a) _ = x
  rw [Category.assoc, G.relativeRestriction_sourceProjection]
  exact hz

/-- At the initial relative stage every adjacent-layer class is a source. -/
theorem sourceCycles_one (G : Input X) (S : Syn) (s : ℕ) :
    G.sourceCycles S s 1 le_rfl = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨x, ?_⟩
  change x ≫ G.sourceProjection s (s + 1) _ = x
  rw [G.sourceProjection_self, Category.comp_id]

/-- Exactly the target changes caused by changing a representative without
changing its source. -/
noncomputable def targetAmbiguity (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    AddSubgroup (S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :=
  ((G.source S s r hr).ker).map (G.target S s r)

/-- The boundary target descends through the kernel of the source map. -/
noncomputable def obstructionOnQuotient (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    (G.Representative S s r ⧸ (G.source S s r hr).ker) →+
      ((S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) ⧸
        G.targetAmbiguity S s r hr) :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' _).comp (G.target S s r)) (by
      intro z hz
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      exact ⟨z, hz, rfl⟩)

/-- The geometric obstruction map on source classes, with the target
ambiguity proved and quotiented out. This is not yet an entire `E_r` page:
incoming boundaries at the source remain to be accounted for. -/
noncomputable def obstruction (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    G.sourceCycles S s r hr →+
      ((S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) ⧸
        G.targetAmbiguity S s r hr) :=
  (G.obstructionOnQuotient S s r hr).comp
    (QuotientAddGroup.quotientKerEquivRange (G.source S s r hr)).symm.toAddMonoidHom

/-- Computing the obstruction uses the actual boundary of the same
relative representative; no comparison or chosen page map is assumed. -/
theorem obstruction_source (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (z : G.Representative S s r) :
    G.obstruction S s r hr ⟨G.source S s r hr z, ⟨z, rfl⟩⟩ =
      QuotientAddGroup.mk (G.target S s r z) := by
  let e := QuotientAddGroup.quotientKerEquivRange (G.source S s r hr)
  have he : e (QuotientAddGroup.mk z) = ⟨G.source S s r hr z, ⟨z, rfl⟩⟩ := rfl
  have hinv := e.symm_apply_apply (QuotientAddGroup.mk z)
  rw [he] at hinv
  change G.obstructionOnQuotient S s r hr (e.symm _) = _
  exact congrArg (G.obstructionOnQuotient S s r hr) hinv

/-- This is the full ambiguity statement, in both directions: a target
represents the obstruction exactly when the same source has a relative
representative with that precise target. -/
theorem obstruction_eq_iff_relation (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.sourceCycles S s r hr)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :
    G.obstruction S s r hr x = QuotientAddGroup.mk y ↔
      G.RepresentativeRelation S s r hr x.val y := by
  obtain ⟨z, hz⟩ := x.property
  have hx : (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr) = x :=
    Subtype.ext hz
  rw [← hx, G.obstruction_source]
  constructor
  · intro h
    obtain ⟨w, hw, hwy⟩ := (QuotientAddGroup.eq_iff_sub_mem.mp h)
    change G.source S s r hr w = 0 at hw
    change G.target S s r w = G.target S s r z - y at hwy
    refine ⟨z - w, ?_, ?_⟩
    · change G.source S s r hr (z - w) = G.source S s r hr z
      rw [map_sub, hw, sub_zero]
    · rw [map_sub, hwy]
      abel
  · rintro ⟨w, hw, rfl⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨z - w, ?_, ?_⟩
    · change G.source S s r hr (z - w) = 0
      change G.source S s r hr w = G.source S s r hr z at hw
      rw [map_sub, hw, sub_self]
    · exact map_sub _ _ _

/-- The kernel of the well-defined obstruction consists exactly of the
source classes lifting one stage further. This proves the next-cycle rule
directly for the abstract tower and its actual relative cofibers. -/
theorem obstruction_eq_zero_iff_next_sourceCycle (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.sourceCycles S s r hr) :
    G.obstruction S s r hr x = 0 ↔
      x.val ∈ G.sourceCycles S s (r + 1) (by omega) := by
  have hrel := G.obstruction_eq_iff_relation S s r hr x 0
  rw [show (QuotientAddGroup.mk (0 : S ⟶
    (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :
      _ ⧸ G.targetAmbiguity S s r hr) = 0 from rfl] at hrel
  rw [hrel]
  constructor
  · rintro ⟨z, hsource, htarget⟩
    obtain ⟨z', hz'⟩ := (G.target_eq_zero_iff_relativeLift S s r z).mp htarget
    refine ⟨z', ?_⟩
    change z' ≫ G.sourceProjection s (s + (r + 1)) _ = x.val
    change z ≫ G.sourceProjection s (s + r) _ = x.val at hsource
    rw [← hz', Category.assoc, G.relativeRestriction_sourceProjection] at hsource
    exact hsource
  · rintro ⟨z', hz'⟩
    let z := z' ≫ G.relativeRestriction s (s + r) (s + r + 1)
      (Nat.le_add_right s r) (Nat.le_succ _)
    refine ⟨z, ?_, (G.target_eq_zero_iff_relativeLift S s r z).mpr ⟨z', rfl⟩⟩
    change (z' ≫ G.relativeRestriction s (s + r) (s + r + 1) _ _) ≫
      G.sourceProjection s (s + r) _ = x.val
    rw [Category.assoc, G.relativeRestriction_sourceProjection]
    exact hz'

/-! ### Incoming boundaries and the page quotient -/

/-- Postcomposition on represented homotopy groups. -/
def postcompose {A B : Syn} (S : Syn) (f : A ⟶ B) : (S ⟶ A) →+ (S ⟶ B) where
  toFun x := x ≫ f
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- Project a class at a stage to its adjacent layer. -/
noncomputable def stageProjection (G : Input X) (S : Syn) (s : ℕ) :
    (S ⟶ G.stage s) →+ (S ⟶ G.layer s) :=
  postcompose S (syn_functorial_cofiber.cofibι (G.transition s (s + 1) (Nat.le_succ s)))

/-- Every class represented in the stage itself lifts over arbitrarily
many layers. This is the permanence used for incoming boundaries. -/
theorem stageProjection_mem_sourceCycles (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (a : S ⟶ G.stage s) :
    G.stageProjection S s a ∈ G.sourceCycles S s r hr := by
  refine ⟨a ≫ syn_functorial_cofiber.cofibι
    (G.transition s (s + r) (Nat.le_add_right s r)), ?_⟩
  have hi : syn_functorial_cofiber.cofibι (G.transition s (s + r) _) ≫
      G.sourceProjection s (s + r) (by omega) =
        syn_functorial_cofiber.cofibι (G.transition s (s + 1) (Nat.le_succ s)) :=
    (syn_functorial_cofiber.cofibMap_ι _ _ _ _ _).symm.trans (Category.id_comp _)
  change (a ≫ _) ≫ _ = a ≫ _
  rw [Category.assoc, hi]

/-- Incoming boundaries at stage `s` are actual stage classes which
become zero at stage `max 0 (s-r+1)`, projected to the adjacent layer. -/
noncomputable def incomingBoundaries (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) : AddSubgroup (S ⟶ G.layer s) :=
  ((postcompose S (G.transition (s + 1 - r) s (by omega))).ker).map
    (G.stageProjection S s)

/-- Incoming boundaries grow with the page number. -/
theorem incomingBoundaries_mono (G : Input X) (S : Syn)
    (s a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b) :
    G.incomingBoundaries S s a ha ≤ G.incomingBoundaries S s b hb := by
  rintro x ⟨u, hu, hux⟩
  refine ⟨u, ?_, hux⟩
  change u ≫ G.transition (s + 1 - a) s _ = 0 at hu
  change u ≫ G.transition (s + 1 - b) s _ = 0
  have ht : G.transition (s + 1 - a) s (by omega) ≫
      G.transition (s + 1 - b) (s + 1 - a) (by omega) =
        G.transition (s + 1 - b) s (by omega) :=
    G.tower.transition_comp _ _ _ (by omega) (by omega)
  rw [← ht, ← Category.assoc, hu, zero_comp]

/-- There are no incoming boundaries on the initial adjacent-layer page. -/
theorem incomingBoundaries_one (G : Input X) (S : Syn) (s : ℕ) :
    G.incomingBoundaries S s 1 le_rfl = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨u, hu, rfl⟩
  have hzero : u = 0 := by
    change u ≫ G.transition s s le_rfl = 0 at hu
    have hi : G.transition s s le_rfl = 𝟙 (G.stage s) := G.tower.transition_self s
    rw [hi, Category.comp_id] at hu
    exact hu
  change G.stageProjection S s u = 0
  rw [hzero, map_zero]

/-- Incoming boundaries are cycles at every length, since they are
represented by actual maps into the stage. -/
theorem incomingBoundaries_le_sourceCycles (G : Input X) (S : Syn)
    (s r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q) :
    G.incomingBoundaries S s r hr ≤ G.sourceCycles S s q hq := by
  rintro x ⟨a, _, rfl⟩
  exact G.stageProjection_mem_sourceCycles S s q hq a

/-- The shifted incoming boundary subgroup with a specified shallower
endpoint. It is an image of the actual kernel of a tower transition. -/
noncomputable def suspendedBoundaries (G : Input X) (S : Syn)
    (a b : ℕ) (hab : a ≤ b) :
    AddSubgroup (S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer b)) :=
  ((postcompose S ((shiftFunctor Syn (1 : ℤ)).map (G.transition a b hab))).ker).map
    (postcompose S ((shiftFunctor Syn (1 : ℤ)).map
      (syn_functorial_cofiber.cofibι (G.transition b (b + 1) (Nat.le_succ b)))))

/-- The full range of the actual relative target is the new incoming
boundary subgroup. This is the geometric image rule for the page step. -/
theorem target_range_eq_suspendedBoundaries (G : Input X) (S : Syn) (s r : ℕ) :
    (G.target S s r).range =
      G.suspendedBoundaries S s (s + r) (Nat.le_add_right s r) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z ≫ G.boundary s (s + r) (Nat.le_add_right s r), ?_, ?_⟩
    · change (z ≫ G.boundary s (s + r) _) ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.transition s (s + r) _) = 0
      have hz : G.boundary s (s + r) (Nat.le_add_right s r) ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (G.transition s (s + r) (Nat.le_add_right s r)) = 0 :=
        comp_distTriang_mor_zero₃₁ _ (syn_functorial_cofiber.cofib_distinguished
          (G.transition s (s + r) (Nat.le_add_right s r)))
      rw [Category.assoc, hz, comp_zero]
    · exact Category.assoc _ _ _
  · rintro ⟨a, ha, rfl⟩
    change a ≫ (shiftFunctor Syn (1 : ℤ)).map (G.transition s (s + r) _) = 0 at ha
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁ _
      (syn_functorial_cofiber.cofib_distinguished
        (G.transition s (s + r) (Nat.le_add_right s r))) a ha
    change S ⟶ G.relative s (s + r) (Nat.le_add_right s r) at z
    change a = z ≫ G.boundary s (s + r) _ at hz
    refine ⟨z, ?_⟩
    change z ≫ (G.boundary s (s + r) _ ≫ _) = a ≫ _
    rw [← Category.assoc, ← hz]

/-- All ambiguity at the target comes precisely from shorter incoming
boundaries, not from an independently chosen equivalence relation. -/
theorem targetAmbiguity_eq_suspendedBoundaries (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    G.targetAmbiguity S s r hr =
      G.suspendedBoundaries S (s + 1) (s + r) (by omega) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change G.source S s r hr z = 0 at hz
    refine ⟨z ≫ G.boundary s (s + r) (Nat.le_add_right s r), ?_, ?_⟩
    · change (z ≫ G.boundary s (s + r) _) ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.transition (s + 1) (s + r) _) = 0
      rw [Category.assoc, ← G.sourceProjection_boundary, ← Category.assoc]
      change G.source S s r hr z ≫ _ = 0
      rw [hz, zero_comp]
    · exact Category.assoc _ _ _
  · rintro ⟨a, ha, hay⟩
    change a ≫ (shiftFunctor Syn (1 : ℤ)).map
      (G.transition (s + 1) (s + r) (by omega)) = 0 at ha
    have hcomp : G.transition (s + 1) (s + r) (by omega) ≫
        G.transition s (s + 1) (Nat.le_succ s) =
      G.transition s (s + r) (Nat.le_add_right s r) :=
      G.tower.transition_comp s (s + 1) (s + r) (Nat.le_succ s) (by omega)
    have ha' : a ≫ (shiftFunctor Syn (1 : ℤ)).map
        (G.transition s (s + r) (Nat.le_add_right s r)) = 0 := by
      rw [← hcomp, Functor.map_comp, ← Category.assoc, ha, zero_comp]
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁ _
      (syn_functorial_cofiber.cofib_distinguished
        (G.transition s (s + r) (Nat.le_add_right s r))) a ha'
    change S ⟶ G.relative s (s + r) (Nat.le_add_right s r) at z
    change a = z ≫ G.boundary s (s + r) _ at hz
    have hs : (z ≫ G.sourceProjection s (s + r) (by omega)) ≫
        G.boundary s (s + 1) (Nat.le_succ s) = 0 := by
      rw [Category.assoc, G.sourceProjection_boundary, ← Category.assoc, ← hz, ha]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₃ _
      (syn_functorial_cofiber.cofib_distinguished
        (G.transition s (s + 1) (Nat.le_succ s))) _ hs
    change S ⟶ G.stage s at q
    change z ≫ G.sourceProjection s (s + r) _ =
      q ≫ syn_functorial_cofiber.cofibι (G.transition s (s + 1) _) at hq
    have hi : syn_functorial_cofiber.cofibι (G.transition s (s + r) _) ≫
        G.sourceProjection s (s + r) (by omega) =
          syn_functorial_cofiber.cofibι (G.transition s (s + 1) (Nat.le_succ s)) :=
      (syn_functorial_cofiber.cofibMap_ι _ _ _ _ _).symm.trans (Category.id_comp _)
    have hiδ : syn_functorial_cofiber.cofibι (G.transition s (s + r) _) ≫
        G.boundary s (s + r) (Nat.le_add_right s r) = 0 :=
      comp_distTriang_mor_zero₂₃ _ (syn_functorial_cofiber.cofib_distinguished _)
    refine ⟨z - q ≫ syn_functorial_cofiber.cofibι
      (G.transition s (s + r) (Nat.le_add_right s r)), ?_, ?_⟩
    · change (z - q ≫ _) ≫ G.sourceProjection s (s + r) _ = 0
      rw [Preadditive.sub_comp, Category.assoc, hi, ← hq, sub_self]
    · change (z - q ≫ _) ≫ (G.boundary s (s + r) _ ≫ _) = y
      rw [← Category.assoc, Preadditive.sub_comp, Category.assoc,
        hiδ, comp_zero, sub_zero, ← hz]
      exact hay

/-- Incoming boundaries regarded as a subgroup of the current source
cycles. The inclusion into cycles was proved above. -/
noncomputable def pageBoundaries (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    AddSubgroup (G.sourceCycles S s r hr) :=
  (G.incomingBoundaries S s r hr).comap (G.sourceCycles S s r hr).subtype

/-- The actual quotient of relative cycles by incoming boundaries. -/
noncomputable abbrev PageGroup (G : Input X) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :=
  G.sourceCycles S s r hr ⧸ G.pageBoundaries S s r hr

/-- The relative obstruction descends through incoming boundaries. Its
target is written as the adjacent-layer group modulo shorter boundaries;
the next-cycle and image rules below identify its kernel and image. -/
noncomputable def pageObstruction (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    G.PageGroup S s r hr →+
      ((S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) ⧸
        G.targetAmbiguity S s r hr) :=
  QuotientAddGroup.lift _ (G.obstruction S s r hr) (by
    intro x hx
    apply (G.obstruction_eq_zero_iff_next_sourceCycle S s r hr x).mpr
    exact G.incomingBoundaries_le_sourceCycles S s r (r + 1) hr (by omega) hx)

/-- The quotient differential is still computed by the boundary of the
same specified relative representative. -/
theorem pageObstruction_mk (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.sourceCycles S s r hr) :
    G.pageObstruction S s r hr (QuotientAddGroup.mk x) = G.obstruction S s r hr x :=
  rfl

/-- Even after dividing the source by incoming boundaries, its value is
characterized by actual representatives with the specified source. -/
theorem pageObstruction_eq_iff_relation (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.sourceCycles S s r hr)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) :
    G.pageObstruction S s r hr (QuotientAddGroup.mk x) = QuotientAddGroup.mk y ↔
      G.RepresentativeRelation S s r hr x.val y :=
  G.obstruction_eq_iff_relation S s r hr x y

/-- A differential equation on the actual page quotient produces its
relative representative. The caller gives the page class, not a chosen
cycle lift or a geometric realization hypothesis. The prescribed target
representative is recovered exactly in the adjacent target layer. -/
theorem exists_representative_of_pageObstruction (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.PageGroup S s r hr)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r)))
    (hxy : G.pageObstruction S s r hr x = QuotientAddGroup.mk y) :
    ∃ z : G.Representative S s r,
      QuotientAddGroup.mk
        (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr) = x ∧
      G.target S s r z = y := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (G.pageBoundaries S s r hr) x
  obtain ⟨z, hsource, htarget⟩ :=
    (G.pageObstruction_eq_iff_relation S s r hr a y).mp hxy
  refine ⟨z, ?_, htarget⟩
  exact congrArg (fun a : G.sourceCycles S s r hr =>
    (QuotientAddGroup.mk a : G.PageGroup S s r hr)) (Subtype.ext hsource)

/-- When a specified stage class detects the page target, the actual
relative boundary differs from it by a map through the next deeper stage.
Both the relative representative and this correction are constructed.
This keeps the distinction between a layer equality and a stage equality
explicit when applying the lambda cap formula. -/
theorem exists_boundaryCorrection_of_pageObstruction (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (x : G.PageGroup S s r hr)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.stage (s + r)))
    (hxy : G.pageObstruction S s r hr x = QuotientAddGroup.mk
      (y ≫ (shiftFunctor Syn (1 : ℤ)).map
        (syn_functorial_cofiber.cofibι
          (G.transition (s + r) (s + r + 1) (Nat.le_succ _))))) :
    ∃ (z : G.Representative S s r)
      (u : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.stage (s + r + 1))),
      QuotientAddGroup.mk
        (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr) = x ∧
      z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
        y + u ≫ (shiftFunctor Syn (1 : ℤ)).map
          (G.transition (s + r) (s + r + 1) (Nat.le_succ _)) := by
  obtain ⟨z, hsource, htarget⟩ :=
    G.exists_representative_of_pageObstruction S s r hr x _ hxy
  let j := G.transition (s + r) (s + r + 1) (Nat.le_succ _)
  have hz : (z ≫ G.boundary s (s + r) (Nat.le_add_right s r) - y) ≫
      (shiftFunctor Syn (1 : ℤ)).map (syn_functorial_cofiber.cofibι j) = 0 := by
    rw [Preadditive.sub_comp, Category.assoc]
    change G.target S s r z - y ≫ _ = 0
    rw [htarget, sub_self]
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₁ _
    (rot_of_distTriang _ (syn_functorial_cofiber.cofib_distinguished j)) _ hz
  change S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.stage (s + r + 1)) at u
  change z ≫ G.boundary s (s + r) _ - y =
    u ≫ (-(shiftFunctor Syn (1 : ℤ)).map j) at hu
  have hu' : z ≫ G.boundary s (s + r) _ - y =
      (-u) ≫ (shiftFunctor Syn (1 : ℤ)).map j :=
    hu.trans ((Preadditive.comp_neg u ((shiftFunctor Syn (1 : ℤ)).map j)).trans
      (Preadditive.neg_comp u ((shiftFunctor Syn (1 : ℤ)).map j)).symm)
  refine ⟨z, -u, hsource, ?_⟩
  change z ≫ G.boundary s (s + r) _ = y + (-u) ≫ (shiftFunctor Syn (1 : ℤ)).map j
  rw [← hu']
  abel

/-- Include next-step cycles in the current page quotient. -/
noncomputable def nextCycleToPage (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    G.sourceCycles S s (r + 1) (by omega) →+ G.PageGroup S s r hr :=
  (QuotientAddGroup.mk' _).comp
    (AddSubgroup.inclusion (G.sourceCycles_antitone S s r (r + 1) hr
      (by omega) (Nat.le_succ r)))

/-- The kernel on the page quotient is exactly the image of next-step
cycles. This includes the source boundary quotient, unlike the earlier
representative-level kernel formula. -/
theorem pageObstruction_ker (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    (G.pageObstruction S s r hr).ker = (G.nextCycleToPage S s r hr).range := by
  ext a
  constructor
  · intro ha
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (G.pageBoundaries S s r hr) a
    have hx : x.val ∈ G.sourceCycles S s (r + 1) (by omega) :=
      (G.obstruction_eq_zero_iff_next_sourceCycle S s r hr x).mp ha
    exact ⟨⟨x.val, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    change G.obstruction S s r hr
      (AddSubgroup.inclusion (G.sourceCycles_antitone S s r (r + 1) hr
        (by omega) (Nat.le_succ r)) x) = 0
    exact (G.obstruction_eq_zero_iff_next_sourceCycle S s r hr _).mpr x.property

/-- The image of the page obstruction is the new incoming boundary
subgroup modulo the old one. Both subgroups were computed from actual
tower transitions and cofiber exactness. -/
theorem pageObstruction_range (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    (G.pageObstruction S s r hr).range =
      (G.suspendedBoundaries S s (s + r) (Nat.le_add_right s r)).map
        (QuotientAddGroup.mk' (G.targetAmbiguity S s r hr)) := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (G.pageBoundaries S s r hr) p
    obtain ⟨z, hz⟩ := x.property
    have hx : (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr) = x :=
      Subtype.ext hz
    refine ⟨G.target S s r z, ?_, ?_⟩
    · rw [← G.target_range_eq_suspendedBoundaries S s r]
      exact ⟨z, rfl⟩
    · change QuotientAddGroup.mk (G.target S s r z) = G.obstruction S s r hr x
      rw [← hx, G.obstruction_source]
  · rintro ⟨y, hy, rfl⟩
    rw [← G.target_range_eq_suspendedBoundaries S s r] at hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨QuotientAddGroup.mk
      (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr), ?_⟩
    exact G.obstruction_source S s r hr z

/-- A represented differential is nonzero on the page precisely when its
actual target is not a shorter incoming boundary. -/
theorem pageObstruction_nonzero_iff (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) (z : G.Representative S s r) :
    G.pageObstruction S s r hr (QuotientAddGroup.mk
      (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr)) ≠ 0 ↔
      G.target S s r z ∉ G.suspendedBoundaries S (s + 1) (s + r) (by omega) := by
  rw [G.pageObstruction_mk, G.obstruction_source]
  rw [Ne, QuotientAddGroup.eq_zero_iff, G.targetAmbiguity_eq_suspendedBoundaries]

/-- The old incoming boundaries, now regarded inside next-step cycles. -/
noncomputable def oldBoundariesInNextCycles (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) : AddSubgroup (G.sourceCycles S s (r + 1) (by omega)) :=
  (G.incomingBoundaries S s r hr).comap (G.sourceCycles S s (r + 1) (by omega)).subtype

/-- The inclusion of next-step cycles kills exactly the old boundaries. -/
theorem nextCycleToPage_ker (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    (G.nextCycleToPage S s r hr).ker = G.oldBoundariesInNextCycles S s r hr := by
  ext x
  change (QuotientAddGroup.mk
    (AddSubgroup.inclusion (G.sourceCycles_antitone S s r (r + 1) hr
      (by omega) (Nat.le_succ r)) x) : G.PageGroup S s r hr) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- Next-step cycles modulo the old boundaries are the actual kernel of
the current quotient differential. -/
noncomputable def nextCyclesQuotientEquivKernel (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    (G.sourceCycles S s (r + 1) (Nat.succ_le_succ (Nat.zero_le r)) ⧸
      G.oldBoundariesInNextCycles S s r hr) ≃+
        (G.pageObstruction S s r hr).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (G.nextCycleToPage_ker S s r hr).symm).trans
    ((QuotientAddGroup.quotientKerEquivRange (G.nextCycleToPage S s r hr)).trans
      (AddEquiv.addSubgroupCongr (G.pageObstruction_ker S s r hr).symm))

/-- The newly enlarged incoming boundary group inside the kernel of the
current page differential. -/
noncomputable def newBoundariesInKernel (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) : AddSubgroup (G.pageObstruction S s r hr).ker :=
  (G.pageBoundaries S s (r + 1) (by omega)).map
    ((G.nextCyclesQuotientEquivKernel S s r hr).toAddMonoidHom.comp
      (QuotientAddGroup.mk' (G.oldBoundariesInNextCycles S s r hr)))

/-- The next page is the kernel of the current quotient differential
modulo the new incoming boundaries. The kernel and boundary-image rules
above were proved using actual relative cofiber maps. -/
noncomputable def nextPageHomologyEquiv (G : Input X) (S : Syn)
    (s r : ℕ) (hr : 1 ≤ r) :
    ((G.pageObstruction S s r hr).ker ⧸ G.newBoundariesInKernel S s r hr) ≃+
      G.PageGroup S s (r + 1) (by omega) := by
  let B := G.oldBoundariesInNextCycles S s r hr
  let B' := G.pageBoundaries S s (r + 1) (by omega)
  let e := G.nextCyclesQuotientEquivKernel S s r hr
  have hBB' : B ≤ B' := by
    intro x hx
    exact G.incomingBoundaries_mono S s r (r + 1) hr (by omega) (Nat.le_succ r) hx
  have hmap : (B'.map (QuotientAddGroup.mk' B)).map e.toAddMonoidHom =
      G.newBoundariesInKernel S s r hr := by
    rw [AddSubgroup.map_map]
    rfl
  exact (QuotientAddGroup.congr _ _ e hmap).symm.trans
    (QuotientAddGroup.quotientQuotientEquivQuotient B B' hBB')

/-! ### Naturality of the actual relative differential -/

omit [Preadditive Syn] [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] in
/-- Naturality of a morphism of towers, in transition-map notation. -/
theorem towerMap_transition {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (a b : ℕ) (hab : a ≤ b) :
    φ.app (Opposite.op b) ≫ H.transition a b hab =
      G.transition a b hab ≫ φ.app (Opposite.op a) :=
  (φ.naturality (homOfLE hab).op).symm

/-- The map on actual relative objects induced by a morphism of towers. -/
noncomputable def relativeMap {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (a b : ℕ) (hab : a ≤ b) :
    G.relative a b hab ⟶ H.relative a b hab :=
  syn_functorial_cofiber.cofibMap (G.transition a b hab) (H.transition a b hab)
    (φ.app (Opposite.op b)) (φ.app (Opposite.op a))
    (G.towerMap_transition H φ a b hab)

/-- The actual map on adjacent layers. -/
noncomputable abbrev layerMap {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (s : ℕ) : G.layer s ⟶ H.layer s :=
  G.relativeMap H φ s (s + 1) (Nat.le_succ s)

@[reassoc] theorem relativeMap_boundary {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (a b : ℕ) (hab : a ≤ b) :
    G.relativeMap H φ a b hab ≫ H.boundary a b hab =
      G.boundary a b hab ≫ (shiftFunctor Syn (1 : ℤ)).map (φ.app (Opposite.op b)) :=
  syn_functorial_cofiber.cofibMap_δ _ _ _ _ _

@[reassoc] theorem relativeMap_sourceProjection {Y : Syn}
    (G : Input X) (H : Input Y) (φ : G.tower ⟶ H.tower)
    (s b : ℕ) (hsb : s + 1 ≤ b) :
    G.relativeMap H φ s b (by omega) ≫ H.sourceProjection s b hsb =
      G.sourceProjection s b hsb ≫ G.layerMap H φ s := by
  dsimp only [relativeMap, sourceProjection, layerMap]
  rw [syn_functorial_cofiber.cofibMap_comp, syn_functorial_cofiber.cofibMap_comp]
  congr 1
  · exact G.towerMap_transition H φ (s + 1) b hsb
  · simp

@[reassoc] theorem stageMap_layerProjection {Y : Syn}
    (G : Input X) (H : Input Y) (φ : G.tower ⟶ H.tower) (s : ℕ) :
    φ.app (Opposite.op s) ≫
        syn_functorial_cofiber.cofibι (H.transition s (s + 1) (Nat.le_succ s)) =
      syn_functorial_cofiber.cofibι (G.transition s (s + 1) (Nat.le_succ s)) ≫
        G.layerMap H φ s :=
  syn_functorial_cofiber.cofibMap_ι _ _ _ _ _

@[reassoc] theorem relativeMap_targetProjection {Y : Syn}
    (G : Input X) (H : Input Y) (φ : G.tower ⟶ H.tower)
    (s b : ℕ) (hsb : s ≤ b) :
    G.relativeMap H φ s b hsb ≫ H.targetProjection s b hsb =
      G.targetProjection s b hsb ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.layerMap H φ b) := by
  dsimp only [targetProjection]
  rw [← Category.assoc, G.relativeMap_boundary, Category.assoc,
    ← Functor.map_comp, G.stageMap_layerProjection, Functor.map_comp, Category.assoc]

/-- A tower morphism sends the same representative's source and target
to the source and target of its actual image. -/
theorem representativeRelation_map {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : S ⟶ G.layer s)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r)))
    (h : G.RepresentativeRelation S s r hr x y) :
    H.RepresentativeRelation S s r hr (x ≫ G.layerMap H φ s)
      (y ≫ (shiftFunctor Syn (1 : ℤ)).map (G.layerMap H φ (s + r))) := by
  obtain ⟨z, hx, hy⟩ := h
  refine ⟨z ≫ G.relativeMap H φ s (s + r) (Nat.le_add_right s r), ?_, ?_⟩
  · change (z ≫ _) ≫ H.sourceProjection s (s + r) _ = x ≫ _
    rw [Category.assoc, G.relativeMap_sourceProjection, ← Category.assoc]
    change G.source S s r hr z ≫ _ = x ≫ _
    rw [hx]
  · change (z ≫ _) ≫ H.targetProjection s (s + r) _ = y ≫ _
    rw [Category.assoc, G.relativeMap_targetProjection, ← Category.assoc]
    change G.target S s r z ≫ _ = y ≫ _
    rw [hy]

/-- The induced additive map on actual source cycles. -/
noncomputable def cycleMap {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    G.sourceCycles S s r hr →+ H.sourceCycles S s r hr :=
  ((postcompose S (G.layerMap H φ s)).comp (G.sourceCycles S s r hr).subtype).codRestrict
    (H.sourceCycles S s r hr) (by
      rintro ⟨x, z, hz⟩
      refine ⟨z ≫ G.relativeMap H φ s (s + r) (Nat.le_add_right s r), ?_⟩
      change (z ≫ _) ≫ H.sourceProjection s (s + r) _ = x ≫ _
      rw [Category.assoc, G.relativeMap_sourceProjection, ← Category.assoc]
      exact congrArg (fun a => a ≫ G.layerMap H φ s) hz)

/-- Tower morphisms preserve incoming boundaries by actual transition
naturality, so the induced cycle map descends to the page quotient. -/
theorem cycleMap_preserves_boundaries {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : G.sourceCycles S s r hr) (hx : x ∈ G.pageBoundaries S s r hr) :
    G.cycleMap H φ S s r hr x ∈ H.pageBoundaries S s r hr := by
  obtain ⟨a, ha, hax⟩ := hx
  refine ⟨a ≫ φ.app (Opposite.op s), ?_, ?_⟩
  · change (a ≫ φ.app (Opposite.op s)) ≫ H.transition (s + 1 - r) s _ = 0
    change a ≫ G.transition (s + 1 - r) s _ = 0 at ha
    rw [Category.assoc, G.towerMap_transition, ← Category.assoc, ha, zero_comp]
  · change (a ≫ φ.app (Opposite.op s)) ≫
      syn_functorial_cofiber.cofibι (H.transition s (s + 1) _) = x.val ≫ _
    rw [Category.assoc, G.stageMap_layerProjection, ← Category.assoc]
    exact congrArg (fun b => b ≫ G.layerMap H φ s) hax

/-- The page map induced by an actual morphism of towers. -/
noncomputable def pageMap {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    G.PageGroup S s r hr →+ H.PageGroup S s r hr :=
  QuotientAddGroup.map _ _ (G.cycleMap H φ S s r hr)
    (fun x hx => G.cycleMap_preserves_boundaries H φ S s r hr x hx)

/-- The map on the target modulo shorter boundaries, induced by the
same tower morphism used on the source page. -/
noncomputable def targetQuotientMap {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    ((S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (G.layer (s + r))) ⧸
        G.targetAmbiguity S s r hr) →+
      ((S ⟶ (shiftFunctor Syn (1 : ℤ)).obj (H.layer (s + r))) ⧸
        H.targetAmbiguity S s r hr) :=
  QuotientAddGroup.map _ _
    (postcompose S ((shiftFunctor Syn (1 : ℤ)).map (G.layerMap H φ (s + r)))) (by
      rintro y ⟨z, hz, hzy⟩
      change G.source S s r hr z = 0 at hz
      have hrel := G.representativeRelation_map H φ S s r hr 0 y ⟨z, hz, hzy⟩
      obtain ⟨z', hz', hy'⟩ := hrel
      refine ⟨z', ?_, hy'⟩
      change H.source S s r hr z' = 0
      simpa only [zero_comp] using hz')

/-- Naturality holds for the quotient differential itself, using the
actual relative maps and their cofiber boundary squares. -/
theorem pageObstruction_naturality {Y : Syn} (G : Input X) (H : Input Y)
    (φ : G.tower ⟶ H.tower) (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : G.PageGroup S s r hr) :
    H.pageObstruction S s r hr (G.pageMap H φ S s r hr x) =
      G.targetQuotientMap H φ S s r hr (G.pageObstruction S s r hr x) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (G.pageBoundaries S s r hr) x
  obtain ⟨z, hz⟩ := a.property
  have ha : (⟨G.source S s r hr z, ⟨z, rfl⟩⟩ : G.sourceCycles S s r hr) = a :=
    Subtype.ext hz
  have hrel : G.RepresentativeRelation S s r hr a.val (G.target S s r z) :=
    ⟨z, hz, rfl⟩
  have himage := G.representativeRelation_map H φ S s r hr _ _ hrel
  have hvalue := (H.obstruction_eq_iff_relation S s r hr
    (G.cycleMap H φ S s r hr a) _).mpr himage
  change H.obstruction S s r hr (G.cycleMap H φ S s r hr a) =
    G.targetQuotientMap H φ S s r hr (G.obstruction S s r hr a)
  rw [hvalue, ← ha, G.obstruction_source]
  rfl

variable [SyntheticCategory Syn]

/-- Multiplication by the actual λ power is a morphism of the whole
shifted tower. Its naturality is inherited from `lambdaPowNatTrans`. -/
noncomputable def lambdaTowerMap (G : Input X) (n : ℕ) :
    (G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).tower ⟶ G.tower where
  app i := lambdaPow n (G.tower.obj i)
  naturality _ _ f := lambdaPow_naturality n (G.tower.map f)

/-- The actual λ action on the quotient pages of the abstract tower. -/
noncomputable def lambdaPageMap (G : Input X) (n : ℕ)
    (S : Syn) (s r : ℕ) (hr : 1 ≤ r) :
    (G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).PageGroup S s r hr →+
      G.PageGroup S s r hr :=
  (G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).pageMap G
    (G.lambdaTowerMap n) S s r hr

/-- Multiplication by λ commutes with the quotient differential because
both are induced by the actual tower and its relative boundary maps. -/
theorem pageObstruction_lambda_naturality (G : Input X) (n : ℕ)
    (S : Syn) (s r : ℕ) (hr : 1 ≤ r)
    (x : (G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).PageGroup S s r hr) :
    G.pageObstruction S s r hr (G.lambdaPageMap n S s r hr x) =
      (G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).targetQuotientMap G
        (G.lambdaTowerMap n) S s r hr
          ((G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).pageObstruction S s r hr x) :=
  (G.map (SyntheticCategory.biShift (0, -(n : ℤ)))).pageObstruction_naturality G
    (G.lambdaTowerMap n) S s r hr x

/-- The finite quotient of the entire input tower. -/
noncomputable def quotient (G : Input X) (n : ℕ) : Input (XModLambdaN X n) :=
  G.map (XModLambdaN.functor n)

/-- Target tower of the actual finite-power connecting morphism. -/
noncomputable def boundaryTarget (G : Input X) (n : ℕ) :
    Input ((shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)) :=
  G.map (SyntheticCategory.biShift (0, -(n : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ))

/-- The cofiber inclusion gives an actual morphism into the quotient
tower; applying `pageMap` gives its map on every geometric page. -/
noncomputable def quotientTowerMap (G : Input X) (n : ℕ) :
    G.tower ⟶ (G.quotient n).tower where
  app i := (XModLambdaN.inclNatTrans n).app (G.tower.obj i)
  naturality _ _ f := (XModLambdaN.inclNatTrans n).naturality (G.tower.map f)

/-- The λ-power boundary itself is a morphism from the quotient tower to
the shifted target tower, with the cofiber naturality square as its law. -/
noncomputable def boundaryTowerMap (G : Input X) (n : ℕ) :
    (G.quotient n).tower ⟶ (G.boundaryTarget n).tower where
  app i := syn_functorial_cofiber.cofibδ (lambdaPow n (G.tower.obj i))
  naturality _ _ f := XModLambdaN.proj_naturality (G.tower.map f) n

/-- The actual λ boundary commutes with the relative page differential.
This uses one morphism of towers for both source and target maps. -/
theorem pageObstruction_boundary_naturality (G : Input X) (n : ℕ)
    (S : Syn) (s r : ℕ) (hr : 1 ≤ r) (x : (G.quotient n).PageGroup S s r hr) :
    (G.boundaryTarget n).pageObstruction S s r hr
        ((G.quotient n).pageMap (G.boundaryTarget n) (G.boundaryTowerMap n) S s r hr x) =
      (G.quotient n).targetQuotientMap (G.boundaryTarget n) (G.boundaryTowerMap n)
        S s r hr ((G.quotient n).pageObstruction S s r hr x) :=
  (G.quotient n).pageObstruction_naturality (G.boundaryTarget n)
    (G.boundaryTowerMap n) S s r hr x

/-- The actual lambda boundary preserves the tower factorization filtration. -/
theorem boundary_preserves_filtration (G : Input X) (n : ℕ) (S : Syn) (s : ℕ)
    (z : S ⟶ XModLambdaN X n) (hz : (G.quotient n).AFGe z s) :
    (G.boundaryTarget n).AFGe
      (z ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X)) s := by
  obtain ⟨a, ha⟩ := hz
  change S ⟶ XModLambdaN (G.stage s) n at a
  change a ≫ (G.quotient n).toBase s = z at ha
  refine ⟨a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n (G.stage s)), ?_⟩
  have hs : (G.quotient n).toBase s = XModLambdaN.map (G.toBase s) n :=
    G.map_toBase (XModLambdaN.functor n) s
  have ht : (G.boundaryTarget n).toBase s =
      (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(n : ℤ))).map (G.toBase s)) :=
    G.map_toBase _ s
  change (a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n (G.stage s))) ≫
    (G.boundaryTarget n).toBase s = z ≫ _
  have ha' : a ≫ XModLambdaN.map (G.toBase s) n = z :=
    (congrArg (fun f => a ≫ f) hs).symm.trans ha
  exact (congrArg (fun f =>
    (a ≫ syn_functorial_cofiber.cofibδ (lambdaPow n (G.stage s))) ≫ f) ht).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => a ≫ f)
        (XModLambdaN.proj_naturality (G.toBase s) n).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X)) ha'))))

/-- Reducing a finite quotient representative to the first quotient
preserves its actual tower filtration. -/
theorem toOne_preserves_filtration (G : Input X) (n : ℕ) (S : Syn) (s : ℕ)
    (z : S ⟶ XModLambdaN X (n + 1)) (hz : (G.quotient (n + 1)).AFGe z s) :
    (G.quotient 1).AFGe (z ≫ XModLambdaN.toOne X n) s := by
  obtain ⟨a, ha⟩ := hz
  change S ⟶ XModLambdaN (G.stage s) (n + 1) at a
  change a ≫ (G.quotient (n + 1)).toBase s = z at ha
  have hq := G.map_toBase (XModLambdaN.functor (n + 1)) s
  have hq1 := G.map_toBase (XModLambdaN.functor 1) s
  refine ⟨a ≫ XModLambdaN.toOne (G.stage s) n, ?_⟩
  have ha' : a ≫ XModLambdaN.map (G.toBase s) (n + 1) = z :=
    (congrArg (fun f => a ≫ f) hq).symm.trans ha
  change (a ≫ XModLambdaN.toOne (G.stage s) n) ≫ (G.quotient 1).toBase s = _
  exact (congrArg (fun f => (a ≫ XModLambdaN.toOne (G.stage s) n) ≫ f) hq1).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => a ≫ f)
        (XModLambdaN.toOne_naturality (G.toBase s) n).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ XModLambdaN.toOne X n) ha'))))

/-- A computed finite-power boundary determines the actual single-lambda
boundary after restriction. The remaining lambda power stays at the named
deep stage, so its filtration factorization is retained. -/
theorem toOne_boundary_formula (G : Input X) (n : ℕ) (S : Syn) (b : ℕ)
    (z : S ⟶ XModLambdaN X (n + 1))
    (y : S ⟶ (G.boundaryTarget (n + 1)).stage b)
    (hz : z ≫ syn_functorial_cofiber.cofibδ (lambdaPow (n + 1) X) =
      y ≫ (G.boundaryTarget (n + 1)).toBase b) :
    (z ≫ XModLambdaN.toOne X n) ≫ lambdaBocksteinConnecting X =
      (y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne (G.stage b) n)) ≫
        (G.boundaryTarget 1).toBase b := by
  have ht := G.map_toBase
    (SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ)) b
  have ht1 := G.map_toBase
    (SyntheticCategory.biShift (0, -(1 : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ)) b
  have hn : (SyntheticCategory.biShift (0, -((n + 1 : ℕ) : ℤ))).map (G.toBase b) ≫
      lambdaPowerToOne X n = lambdaPowerToOne (G.stage b) n ≫
        (SyntheticCategory.biShift (0, (-1 : ℤ))).map (G.toBase b) :=
    (lambdaPowerToOneNatTrans n).naturality (G.toBase b)
  have hstage : (G.boundaryTarget (n + 1)).toBase b ≫
      (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne X n) =
      (shiftFunctor Syn (1 : ℤ)).map (lambdaPowerToOne (G.stage b) n) ≫
        (G.boundaryTarget 1).toBase b := by
    rw [show (G.boundaryTarget (n + 1)).toBase b = _ from ht,
      show (G.boundaryTarget 1).toBase b = _ from ht1]
    change (shiftFunctor Syn (1 : ℤ)).map _ ≫ (shiftFunctor Syn (1 : ℤ)).map _ =
      (shiftFunctor Syn (1 : ℤ)).map _ ≫ (shiftFunctor Syn (1 : ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp, hn]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => z ≫ f) (XModLambdaN.toOne_boundary X n)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne X n)) hz).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => y ≫ f) hstage).trans (Category.assoc _ _ _).symm)))))

/-- A lambda-divisible actual relative boundary gives a cap over the base.
The common-cone witness retains the specified relative source, and the
source filtration is proved from the stage where the cap was made. -/
theorem exists_cap (G : Input X) (S : Syn) (s r n : ℕ)
    (z : G.Representative S s r)
    (y : S ⟶ (shiftFunctor Syn (1 : ℤ)).obj
      ((SyntheticCategory.biShift (0, -(n : ℤ))).obj (G.stage (s + r))))
    (hzy : z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow n (G.stage (s + r)))) :
    ∃ (c : S ⟶ LambdaCofiberGeometry.commonCone
        (G.transition s (s + r) (Nat.le_add_right s r)) n)
      (w : S ⟶ XModLambdaN X n),
      c ≫ LambdaCofiberGeometry.toRelative
        (G.transition s (s + r) (Nat.le_add_right s r)) n = z ∧
      (c ≫ LambdaCofiberGeometry.toQuotient
        (G.transition s (s + r) (Nat.le_add_right s r)) n) ≫
          XModLambdaN.map (G.toBase s) n = w ∧
      (G.quotient n).AFGe w s ∧
      w ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X) =
        y ≫ (G.boundaryTarget n).toBase (s + r) ∧
      (G.boundaryTarget n).AFGe
        (w ≫ syn_functorial_cofiber.cofibδ (lambdaPow n X)) (s + r) := by
  obtain ⟨c, w, hc, hcw, _, hw⟩ :=
    LambdaCofiberGeometry.exists_cap_of_relative_boundary
      (G.transition s (s + r) (Nat.le_add_right s r)) n z y hzy
  have hbase : (w ≫ XModLambdaN.map (G.toBase s) n) ≫
      syn_functorial_cofiber.cofibδ (lambdaPow n X) =
      y ≫ (G.boundaryTarget n).toBase (s + r) := by
    have ht := G.map_toBase
      (SyntheticCategory.biShift (0, -(n : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ))
      (s + r)
    change (G.boundaryTarget n).toBase (s + r) =
      (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(n : ℤ))).map (G.toBase (s + r))) at ht
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => w ≫ f)
        (XModLambdaN.proj_naturality (G.toBase s) n)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ (shiftFunctor Syn (1 : ℤ)).map
            ((SyntheticCategory.biShift (0, -(n : ℤ))).map (G.toBase s))) hw).trans
            (by rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
              G.transition_toBase, ← ht]))))
  refine ⟨c, w ≫ XModLambdaN.map (G.toBase s) n, hc,
    congrArg (fun f => f ≫ XModLambdaN.map (G.toBase s) n) hcw, ?_, hbase, ?_⟩
  · refine ⟨w, ?_⟩
    exact congrArg (fun f => w ≫ f) (G.map_toBase (XModLambdaN.functor n) s)
  · exact ⟨y, hbase.symm⟩

/-- The actual single-lambda cap of a specified relative representative.
Both the source filtration and the deeper target filtration are derived
from the input tower, and the common cone retains the original source. -/
theorem exists_singleCap (G : Input X) (S : Syn) (s r n : ℕ)
    (z : G.Representative S s r)
    (y : S ⟶ (G.boundaryTarget (n + 1)).stage (s + r))
    (hzy : z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
      y ≫ (shiftFunctor Syn (1 : ℤ)).map (lambdaPow (n + 1) (G.stage (s + r)))) :
    ∃ (c : S ⟶ LambdaCofiberGeometry.commonCone
        (G.transition s (s + r) (Nat.le_add_right s r)) (n + 1))
      (w : S ⟶ XModLambdaN X 1),
      c ≫ LambdaCofiberGeometry.toRelative
        (G.transition s (s + r) (Nat.le_add_right s r)) (n + 1) = z ∧
      (((c ≫ LambdaCofiberGeometry.toQuotient
        (G.transition s (s + r) (Nat.le_add_right s r)) (n + 1)) ≫
          XModLambdaN.map (G.toBase s) (n + 1)) ≫ XModLambdaN.toOne X n) = w ∧
      (G.quotient 1).AFGe w s ∧
      w ≫ lambdaBocksteinConnecting X =
        (y ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPowerToOne (G.stage (s + r)) n)) ≫
            (G.boundaryTarget 1).toBase (s + r) ∧
      (G.boundaryTarget 1).AFGe (w ≫ lambdaBocksteinConnecting X) (s + r) := by
  obtain ⟨c, w, hc, hcw, hw, hb, _⟩ := G.exists_cap S s r (n + 1) z y hzy
  have hb1 := G.toOne_boundary_formula n S (s + r) w y hb
  refine ⟨c, w ≫ XModLambdaN.toOne X n, hc,
    congrArg (fun f => f ≫ XModLambdaN.toOne X n) hcw,
    G.toOne_preserves_filtration n S s w hw, hb1, ?_⟩
  exact ⟨y ≫ (shiftFunctor Syn (1 : ℤ)).map
    (lambdaPowerToOne (G.stage (s + r)) n), hb1.symm⟩

end Input
end KIPBase.Synthetic.GeometricAdams
