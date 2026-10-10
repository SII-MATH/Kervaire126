import KIP126.Interface.Challenge.Literature.Delivery
import KIP126.Interface.Challenge.Computation.Delivery

/-! Challenge2 has exactly two correlated deliveries on Def's fixed model.
Literature includes source statements and source-to-model comparisons;
computation includes program interpretations and their mathematical certificates.
Internal applications and the paper's conclusions are derived in Main. -/
namespace KIP126

/-- The Interface construction goal. Computation uses the same sources and
labels as literature, on the one mathematical background fixed in Def. -/
structure Challenge2 where
  literature : Challenge2.LiteratureInterface
  computation : Challenge2.ComputationInterface literature

end KIP126
