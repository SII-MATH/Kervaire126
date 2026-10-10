import KIP126.LinProgram.Model.E2.Data
import KIP126.LinProgram.Compute.E2.Data

namespace KIP126.LinE2

/-- Interpret the calculator's sparse output in the actual quotient algebra.
This only interprets a polynomial; it does not certify reduction soundness. -/
noncomputable def interpretComputedPolynomial (p : Compute.PolynomialF2) : E2 :=
  (p.map fun m => projection
    (polynomialOfPowers (m.flatMap fun (i, a) => [i, a]))).sum

end KIP126.LinE2
