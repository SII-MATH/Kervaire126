module

public import KIP126.Def.Topology.SequentialColimit.BasedHomotopy.Data

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ TopCat.{u}) (x₀ : F.obj 0) (c : Cocone F) (hc : IsColimit c)

include hc

/-- Actual based cubical loops in the colimit already occur at a finite stage,
with the basepoint and the entire cube boundary retained exactly. -/
theorem natColimitLoopInclusion_jointly_surjective
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (r : ℕ)
    (p : GenLoop (Fin r) c.pt (c.ι.app 0 x₀)) :
    ∃ (n : ℕ) (q : GenLoop (Fin r) (F.obj n) (natColimitStagePoint F x₀ n)),
      natColimitLoopInclusion F x₀ c n r q = p := by
  obtain ⟨n, q, hq⟩ := continuousMap_factor_nat_colimit F c hc hF p.val
  have hpoint : c.ι.app n (natColimitStagePoint F x₀ n) = c.ι.app 0 x₀ :=
    ConcreteCategory.congr_hom (c.w (homOfLE (Nat.zero_le n))) x₀
  have hboundary (t) (ht : t ∈ Cube.boundary (Fin r)) :
      q t = natColimitStagePoint F x₀ n := by
    apply (isClosedEmbedding_nat_colimit F c hc hF n).injective
    exact (hq t).trans ((p.property t ht).trans hpoint.symm)
  refine ⟨n, ⟨q, hboundary⟩, ?_⟩
  exact GenLoop.ext _ _ hq

/-- Two actual loops from one stage become based homotopic in the colimit
exactly when they become based homotopic at a finite later stage. -/
theorem natColimitLoopInclusion_homotopic_iff
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (n r : ℕ)
    (p q : GenLoop (Fin r) (F.obj n) (natColimitStagePoint F x₀ n)) :
    GenLoop.Homotopic (natColimitLoopInclusion F x₀ c n r p)
      (natColimitLoopInclusion F x₀ c n r q) ↔
        ∃ (m : ℕ) (h : n ≤ m),
          GenLoop.Homotopic (natColimitLoopTransition F x₀ h r p)
            (natColimitLoopTransition F x₀ h r q) :=
  homotopicRel_nat_colimit_iff F c hc hF n p.val q.val (Cube.boundary (Fin r))

/-- Actual cubical homotopy sets, including degree zero, commute with actual
sequential colimits of closed embeddings of T1 spaces. This is the categorical
colimit universal property for the original homotopy quotients. -/
noncomputable def natColimitHomotopyCocone_isColimit
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (r : ℕ) :
    IsColimit (natColimitHomotopyCocone F x₀ c r) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro p
    induction p using Quotient.inductionOn with
    | h p =>
        obtain ⟨n, q, hq⟩ := natColimitLoopInclusion_jointly_surjective F x₀ c hc hF r p
        exact ⟨n, ⟦q⟧, congrArg Quotient.mk'' hq.symm⟩
  · intro n p q
    induction p using Quotient.inductionOn with
    | h p =>
        induction q using Quotient.inductionOn with
        | h q =>
            intro hpq
            have hh := Quotient.exact hpq
            obtain ⟨m, h, hhom⟩ :=
              (natColimitLoopInclusion_homotopic_iff F x₀ c hc hF n r p q).mp hh
            exact ⟨m, homOfLE h, Quotient.sound hhom⟩

end KIP126.Topology
