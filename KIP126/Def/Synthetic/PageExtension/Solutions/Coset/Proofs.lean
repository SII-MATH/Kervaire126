import KIP126.Def.Synthetic.PageExtension.Solutions.Proofs
import KIP126.Def.Synthetic.PageExtension.Relation.Proofs

namespace KIP126.Synthetic.PageExtension

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.Core.SpectralSequence

universe u v w

/-- Once one differential target is known, its full boundary coset consists
exactly of the other targets of the same source. -/
theorem mem_targetCoset_iff_differentialRelation
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (n : ℤ) (p : ℤ × ℤ) {T : ModuleCat.{v} ℤ}
    {x : T ⟶ (E.ssData p).V}
    {y z : T ⟶ (E.ssData (p + E.diffDeg n)).V}
    (h : DifferentialRelation E n p x y) :
    z ∈ targetCoset E n p y ↔ DifferentialRelation E n p x z := by
  constructor
  · intro hz
    rcases h with ⟨xZ, hx, yZ, hy, hrel⟩
    let D := E.ssData (p + E.diffDeg n)
    let q : WithTop ℕ := ↑(n - E.r₀).toNat
    let i := Subobject.ofLE (D.B q) (D.Z q) (D.B_le_Z q)
    let b := (D.B q).factorThru (y - z) hz
    have hb : b ≫ (D.B q).arrow = y - z :=
      Subobject.factorThru_arrow _ _ hz
    refine ⟨xZ, hx, yZ - b ≫ i, ?_, ?_⟩
    · rw [Preadditive.sub_comp, Category.assoc, Subobject.ofLE_arrow, hy, hb]
      abel
    · change xZ ≫ (E.ssData p).pageπ q ≫ E.d n p =
        (yZ - b ≫ i) ≫ cokernel.π i
      rw [Preadditive.sub_comp, Category.assoc, cokernel.condition, comp_zero, sub_zero]
      exact hrel
  · exact related_target_mem_targetCoset E n p h

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- Membership in the complete finite target coset is equivalent to an
actual solution fiber for the witness's fixed source representative. -/
theorem FiniteExtensionWitness.mem_targetCoset_iff_solutions
    {P : NormalizedPageFamily H N F f} {r : ℕ} {n s t : ℤ}
    {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y)
    (z : PageRepresentatives.cycles H Y (r - 1 - P.lambdaExponent n : ℕ)
      (s + n, t + n)) :
    z ∈ W.targetCoset ↔
      Nonempty (P.FiniteSolutions (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)
        n s t W.exponent_le_length W.exponent_lt_quotient W.sourceCycle z) := by
  change elementMap (P.finiteTargetMap (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)
      n s t W.exponent_le_length W.exponent_lt_quotient z) ∈
    KIP126.Synthetic.PageExtension.targetCoset _ n (s, 1) _ ↔ _
  rw [mem_targetCoset_iff_differentialRelation _ _ _ W.relation]
  exact finiteRelation_iff_solutions _ _ _ _ _ _ _ _ _ _

/-- The infinite target coset likewise records exactly the nonempty fibers
of the untruncated normalized map, with the same fixed source cycle. -/
theorem InfiniteExtensionWitness.mem_targetCoset_iff_solutions
    {P : NormalizedPageFamily H N F f} {n s t : ℤ}
    {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y)
    (z : PageRepresentatives.permanentCycles H Y (s + n, t + n)) :
    z ∈ W.targetCoset ↔
      Nonempty (P.InfiniteSolutions n s t W.exponent_le_length W.sourceCycle z) := by
  change elementMap (P.infiniteTargetMap n s t W.exponent_le_length z) ∈
    KIP126.Synthetic.PageExtension.targetCoset _ n (s, 1) _ ↔ _
  rw [mem_targetCoset_iff_differentialRelation _ _ _ W.relation]
  exact infiniteRelation_iff_solutions _ _ _ _ _ _ _

end KIP126.Synthetic.PageExtension
