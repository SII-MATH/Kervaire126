/-
  KIPBase.Synthetic.GeometricAdamsShift
  Shift invariance of the actual tower-factorization filtration.
-/
import KIPBase.Synthetic.GeometricAdams
import KIPBase.Synthetic.ShiftCofiber
import KIPBase.Synthetic.WeightwiseShift

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The suspension/weight-shift functor on the lambda-boundary edge is an
equivalence, as a composite of a synthetic bidegree shift and suspension. -/
noncomputable instance lambdaBoundaryShiftFunctor_isEquivalence (n : ℕ) :
    (lambdaBoundaryShiftFunctor (Syn := Syn) n).IsEquivalence := by
  dsimp only [lambdaBoundaryShiftFunctor]
  infer_instance

/-- The shift used on the bottom lambda-boundary edge is additive. -/
noncomputable instance lambdaBoundaryShiftFunctor_additive (n : ℕ) :
    Functor.Additive (lambdaBoundaryShiftFunctor (Syn := Syn) n) := by
  dsimp only [lambdaBoundaryShiftFunctor]
  infer_instance

namespace GeometricAdams.Input

variable {X : Syn}

omit [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn] in
/-- Applying an equivalence to an actual tower preserves, and reflects, the
property that a map factors through a specified stage.  This is the geometric
filtration compatibility needed before comparing shifted Adams pages. -/
theorem map_AFGe_iff (G : GeometricAdams.Input X)
    (F : Syn ⥤ Syn) [F.IsEquivalence]
    {S : Syn} (f : S ⟶ X) (s : ℕ) :
    (G.map F).AFGe (F.map f) s ↔ G.AFGe f s := by
  change (∃ a : F.obj S ⟶ (G.map F).stage s,
      a ≫ (G.map F).toBase s = F.map f) ↔
    ∃ a : S ⟶ G.stage s, a ≫ G.toBase s = f
  constructor
  · rintro ⟨a, ha⟩
    change F.obj S ⟶ F.obj (G.stage s) at a
    obtain ⟨a, rfl⟩ := F.map_surjective a
    refine ⟨a, ?_⟩
    apply F.map_injective
    rw [F.map_comp, ← G.map_toBase]
    exact ha
  · rintro ⟨a, rfl⟩
    refine ⟨F.map a, ?_⟩
    change F.map a ≫ (G.map F).toBase s = F.map (a ≫ G.toBase s)
    rw [G.map_toBase, F.map_comp]

omit [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn] in
/-- Exact tower filtration is invariant under equivalences as well. -/
theorem map_AFEq_iff (G : GeometricAdams.Input X)
    (F : Syn ⥤ Syn) [F.IsEquivalence]
    {S : Syn} (f : S ⟶ X) (s : ℕ) :
    (G.map F).AFEq (F.map f) s ↔ G.AFEq f s := by
  simp only [GeometricAdams.Input.AFEq, G.map_AFGe_iff F]

/-- Tower filtration is invariant under every synthetic bidegree shift. -/
theorem biShift_AFGe_iff (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) {S : Syn} (f : S ⟶ X) (s : ℕ) :
    (G.map (SyntheticCategory.biShift p)).AFGe
      ((SyntheticCategory.biShift p).map f) s ↔ G.AFGe f s :=
  G.map_AFGe_iff _ f s

/-- Exact tower filtration is invariant under every synthetic bidegree shift. -/
theorem biShift_AFEq_iff (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) {S : Syn} (f : S ⟶ X) (s : ℕ) :
    (G.map (SyntheticCategory.biShift p)).AFEq
      ((SyntheticCategory.biShift p).map f) s ↔ G.AFEq f s :=
  G.map_AFEq_iff _ f s

/-- The actual filtration used on the bottom lambda-boundary tower is exactly
the transported filtration of the original tower. -/
theorem lambdaBoundaryShift_AFGe_iff (G : GeometricAdams.Input X)
    (n : ℕ) {S : Syn} (f : S ⟶ X) (s : ℕ) :
    (G.map (lambdaBoundaryShiftFunctor (Syn := Syn) n)).AFGe
      ((lambdaBoundaryShiftFunctor (Syn := Syn) n).map f) s ↔ G.AFGe f s :=
  G.map_AFGe_iff _ f s

/-- Exact filtration is preserved on the bottom lambda-boundary tower. -/
theorem lambdaBoundaryShift_AFEq_iff (G : GeometricAdams.Input X)
    (n : ℕ) {S : Syn} (f : S ⟶ X) (s : ℕ) :
    (G.map (lambdaBoundaryShiftFunctor (Syn := Syn) n)).AFEq
      ((lambdaBoundaryShiftFunctor (Syn := Syn) n).map f) s ↔ G.AFEq f s :=
  G.map_AFEq_iff _ f s

section CofiberCompatibility

variable [SyntheticShiftCofiberCompatibility (Syn := Syn)]

/-- Applying a compatible bidegree shift before or after forming any relative
object of the tower gives canonically isomorphic objects. -/
noncomputable def relativeShiftIso (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (a b : ℕ) (h : a ≤ b) :
    (SyntheticCategory.biShift p).obj (G.relative a b h) ≅
      (G.map (SyntheticCategory.biShift p)).relative a b h :=
  SyntheticShiftCofiberCompatibility.biShiftCofibIso p (G.transition a b h)

/-- The preceding comparison on adjacent layers. -/
noncomputable abbrev layerShiftIso (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (s : ℕ) :
    (SyntheticCategory.biShift p).obj (G.layer s) ≅
      (G.map (SyntheticCategory.biShift p)).layer s :=
  G.relativeShiftIso p s (s + 1) (Nat.le_succ s)

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
/-- The relative/layer comparisons commute with the actual source projection.
This is the first coherence needed to transport geometric page cycles. -/
theorem relativeShiftIso_sourceProjection (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (s b : ℕ) (hsb : s + 1 ≤ b) :
    (SyntheticCategory.biShift p).map (G.sourceProjection s b hsb) ≫
        (G.layerShiftIso p s).hom =
      (G.relativeShiftIso p s b (by omega)).hom ≫
        (G.map (SyntheticCategory.biShift p)).sourceProjection s b hsb := by
  have H := SyntheticShiftCofiberCompatibility.map_cofibMap p
      (G.transition s b (by omega))
      (G.transition s (s + 1) (Nat.le_succ s))
      (G.transition (s + 1) b hsb) (𝟙 (G.stage s))
      (by simpa only [Category.comp_id] using
        G.tower.transition_comp s (s + 1) b (Nat.le_succ s) hsb)
  dsimp only [sourceProjection, relativeShiftIso, layerShiftIso,
    SyntheticShiftCofiberCompatibility.biShiftCofibIso,
    chosenCofiberTriangle, GeometricAdams.Input.relative,
    GeometricAdams.Input.layer,
    GeometricAdams.Input.map, GeometricAdams.Input.transition,
    SyntheticCofiberTower.transition, Functor.comp_map, Functor.comp_obj] at H ⊢
  simp only [Functor.mapIso_hom, Pretriangulated.Triangle.π₃] at H ⊢
  rw [H]
  congr 2
  exact (SyntheticCategory.biShift p).map_id (G.stage s)

/-- The relative comparison also commutes with the projected connecting map.
Together with `relativeShiftIso_sourceProjection`, this transports both ends
of every geometric differential representative. -/
theorem relativeShiftIso_targetProjection (G : GeometricAdams.Input X)
    (p : ℤ × ℤ) (s b : ℕ) (hsb : s ≤ b) :
    (SyntheticCategory.biShift p).map (G.targetProjection s b hsb) ≫
        ((SyntheticCategory.biShift p).commShiftIso (1 : ℤ)).hom.app (G.layer b) ≫
        (shiftFunctor Syn (1 : ℤ)).map (G.layerShiftIso p b).hom =
      (G.relativeShiftIso p s b hsb).hom ≫
        (G.map (SyntheticCategory.biShift p)).targetProjection s b hsb := by
  let F := SyntheticCategory.biShift (Syn := Syn) p
  let f := G.transition s b hsb
  let j := G.transition b (b + 1) (Nat.le_succ b)
  change F.map
        (syn_functorial_cofiber.cofibδ f ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (syn_functorial_cofiber.cofibι j)) ≫
        (F.commShiftIso (1 : ℤ)).hom.app (syn_functorial_cofiber.cofib j) ≫
        (shiftFunctor Syn (1 : ℤ)).map
          (SyntheticShiftCofiberCompatibility.biShiftCofibIso p j).hom =
      (SyntheticShiftCofiberCompatibility.biShiftCofibIso p f).hom ≫
        (syn_functorial_cofiber.cofibδ (F.map f) ≫
          (shiftFunctor Syn (1 : ℤ)).map
            (syn_functorial_cofiber.cofibι (F.map j)))
  rw [F.map_comp, Category.assoc,
    F.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp,
    SyntheticShiftCofiberCompatibility.biShiftCofibIso_ι]
  rw [← Category.assoc,
    ← SyntheticShiftCofiberCompatibility.biShiftCofibIso_δ]
  dsimp only [F]
  simp only [Category.assoc]

end CofiberCompatibility

end GeometricAdams.Input

end

end KIPBase.Synthetic
