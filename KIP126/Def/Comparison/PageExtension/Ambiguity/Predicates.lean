import KIP126.Def.Synthetic.PageExtension.Ambiguity.Predicates
/-!
# Page-extension ambiguity conditions

These are parameterized mathematical definitions, independent of fixed program data
and stage witnesses. Existing public declaration names are preserved.
-/

namespace KIP126.Challenge2

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams Core.SpectralSequence

universe u v w

section PageExtensionAmbiguity

open StableHomotopy StableHomotopy.Cohomology Synthetic.Context Synthetic.SpectralSequence
open Synthetic.PageExtension Classical.Adams.PageRepresentatives

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- am6 的剩余模型绑定义务，逐一量化同一比较家族中的实际 extension。
kernel 是经典 Adams boundaries；shorterImages 是同一映射实际较短扩张目标
的 span。两条等式足以派生经典 target coset 与 essential 判据，但尚未由
任意 NormalizedPageFamily 自动构造。infinite 仍保留该家族的有界收敛前提。 -/
structure PageExtensionAmbiguityInterface (P : NormalizedPageFamily H N F f) : Prop where
  finite_kernel : ∀ {r : ℕ} {n s t : ℤ} {x : Ambient H X (s, t)}
    {y : Ambient H Y (s + n, t + n)} (W : FiniteExtensionWitness P r n s t x y),
    W.ClassicalBoundaryKernel
  finite_shorter : ∀ {r : ℕ} {n s t : ℤ} {x : Ambient H X (s, t)}
    {y : Ambient H Y (s + n, t + n)} (W : FiniteExtensionWitness P r n s t x y),
    W.ShorterImagesCompatible
  infinite_kernel : ∀ {n s t : ℤ} {x : Ambient H X (s, t)}
    {y : Ambient H Y (s + n, t + n)} (W : InfiniteExtensionWitness P n s t x y),
    W.ClassicalBoundaryKernel
  infinite_shorter : ∀ {n s t : ℤ} {x : Ambient H X (s, t)}
    {y : Ambient H Y (s + n, t + n)} (W : InfiniteExtensionWitness P n s t x y),
    W.ShorterImagesCompatible

end PageExtensionAmbiguity

end KIP126.Challenge2
