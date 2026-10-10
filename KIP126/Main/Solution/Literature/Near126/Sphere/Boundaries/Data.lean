import KIP126.Main.Solution.Literature.Near126.Sphere.Predicates


namespace KIP126.Computation.Near126
open KIP126.LinE2 KIP126.Classical.Adams KIP126.Core.SpectralSequence


attribute [local irreducible] KIP126.LinE2.homogeneousPart

/-- The two d₂-image facts consumed in the proof of prop:state5false,
MainPaper/main.tex:2716 and 2726. Sources have degrees (10,136) and (11,137),
but their coordinates are not guessed. These are explicit input propositions,
not consequences of E₂ multiplication or of later whole-page vanishing.
The pinned CSV witnesses and algebra certificates have now been independently
checked by scripts/check-near126-product-boundaries.py; their locators and the
remaining archive-to-actual-differential comparison are recorded in
docs/NEAR126_R10_CERTIFICATE.md. That script does not populate this structure.

Only boundary membership is retained: the consumer does not require a separate
nonzero claim for the product. This weaker consequence of the paper's stated
nonzero hits also handles zero and linear combinations correctly. The synthetic
filtration consequences and P/Q candidate exhaustion are separate obligations. -/
structure SphereBoundaryFacts where
  p_h2_d2_boundary :
    (IsPageBoundary sphereAdamsData 2 (10, 136)
      (linToSphereE2 12 137 (by decide) (mulAt P (atom .h2))))
  q_h2_d2_boundary :
    (IsPageBoundary sphereAdamsData 2 (11, 137)
      (linToSphereE2 13 138 (by decide) (mulAt Q (atom .h2))))

end KIP126.Computation.Near126
