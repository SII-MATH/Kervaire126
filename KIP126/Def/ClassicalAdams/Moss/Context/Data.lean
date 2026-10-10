import KIP126.Def.ClassicalAdams.Moss.Statement.Predicates
/-!
# Moss pairing and convergence context

These are parameterized mathematical definitions, independent of fixed program data
and stage witnesses. Existing public declaration names are preserved.
-/

namespace KIP126.Challenge2

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams Core.SpectralSequence

universe u v w

section Moss

open StableHomotopy StableHomotopy.Cohomology Classical.Adams.Moss

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  [∀ A : C, (tensorLeft A).CommShift ℤ]

/-- am8/am15：同一映射 Adams 塔上的配对、检测、收敛和不定性上下文。
这些项目构造与性质不归为外部 Moss 定理；定理结论由 LiteratureInterface 单列。
`objects` 指定应用范围；不要求任意谱的 Adams SS 收敛到未完备同伦群。
配对的每个值由实际长层代表元约束，收敛端使用实际塔像滤过。
Massey 关系使用 E_(r−1) 的 defining system，因此范围是 r ≥ 3。
来源：MainPaper:2537–2545；Moss Theorem 1.2。现代 crossing/weak-convergence
表述另见 Belmont–Kong, arXiv:2112.08689v2, Definitions 2.3–2.4。
此类型提出模型交付义务，不是对任意背景都已有该结构的证明。 -/
structure MossContext {ι : Type w} (objects : ι → C) where
  composition : CompositionPairing H R
  coherent : composition.Coherent H R
  convergence : ∀ X Y : ι, MappingAdamsConvergence H.unit (objects X) (objects Y)
  weak_convergence : ∀ X Y : ι, MappingAdamsTower H.unit (objects X) (objects Y)
  detection : ∀ X Y Z : ι,
    composition.DetectionCompatible H R (objects X) (objects Y) (objects Z)
      (convergence X Y) (convergence Y Z) (convergence X Z)
  indeterminacy : ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : ι) (i j k : ℤ × ℤ)
    (a : (mappingSequence H.unit (objects W) (objects X)).Page r i)
    (b : (mappingSequence H.unit (objects X) (objects Y)).Page r j)
    (c : (mappingSequence H.unit (objects Y) (objects Z)).Page r k)
    (x₀ x : (mappingSequence H.unit (objects W) (objects Z)).Page r
      (PageMassey.degree r i j k)),
    PageMassey.Relation H R composition r hr x₀ a b c →
      (PageMassey.Relation H R composition r hr x a b c ↔
        PageMassey.Indeterminacy H R composition r (j := j) a c (x - x₀))

end Moss

end KIP126.Challenge2
