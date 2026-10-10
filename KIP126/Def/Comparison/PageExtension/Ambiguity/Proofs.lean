import KIP126.Def.Comparison.PageExtension.Ambiguity.Predicates
import KIP126.Def.Synthetic.PageExtension.Ambiguity.Proofs

namespace KIP126.Def.Comparison.StageInterfaces
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Synthetic.PageExtension KIP126.Classical.Adams.PageRepresentatives

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}
  {P : NormalizedPageFamily H N F f}

theorem finitePageExtensionTargetCoset (I : Challenge2.PageExtensionAmbiguityInterface P)
    {r : ℕ} {n s t : ℤ} {x : Ambient H X (s, t)} {y : Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y) :
    W.targetCoset =
      {z | W.targetCycle - z ∈ W.ordinaryBoundaries ⊔ W.shorterImages} :=
  W.targetCoset_eq (I.finite_kernel W) (I.finite_shorter W)

theorem finitePageExtensionEssential (I : Challenge2.PageExtensionAmbiguityInterface P)
    {r : ℕ} {n s t : ℤ} {x : Ambient H X (s, t)} {y : Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y) :
    W.Essential ↔ W.targetCycle ∉ W.ordinaryBoundaries ⊔ W.shorterImages :=
  W.essential_iff_not_mem_ambiguity (I.finite_kernel W) (I.finite_shorter W)

theorem infinitePageExtensionTargetCoset (I : Challenge2.PageExtensionAmbiguityInterface P)
    {n s t : ℤ} {x : Ambient H X (s, t)} {y : Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y) :
    W.targetCoset =
      {z | W.targetCycle - z ∈ W.ordinaryBoundaries ⊔ W.shorterImages} :=
  W.targetCoset_eq (I.infinite_kernel W) (I.infinite_shorter W)

theorem infinitePageExtensionEssential (I : Challenge2.PageExtensionAmbiguityInterface P)
    {n s t : ℤ} {x : Ambient H X (s, t)} {y : Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y) :
    W.Essential ↔ W.targetCycle ∉ W.ordinaryBoundaries ⊔ W.shorterImages :=
  W.essential_iff_not_mem_ambiguity (I.infinite_kernel W) (I.infinite_shorter W)

end KIP126.Def.Comparison.StageInterfaces
