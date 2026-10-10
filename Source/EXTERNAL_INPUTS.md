# Archived external references

This is a reading guide to the archived sources, not a second input ledger.
The canonical record is [external-inputs.json](../docs/external-inputs.json).
It also includes supplemental and bibliography-only sources whose primary
texts are unavailable or unverified, and connects mathematical inputs to Lean
declarations and Blueprint nodes.

Lean interfaces state mathematics directly. Citation and artifact metadata are
maintained in the manifest. If primary text is unavailable, the actual secondary
locator must be explicit; metadata checks do not establish that a cited result
entails the Lean statement.

| Source | External input represented in Lean |
| --- | --- |
| `Browder` | The Kervaire-invariant criterion relating survival of \(h_j^2\) to a nonzero Kervaire class, used for the conditional geometric conclusions. |
| `MahowaldTangora` | Earlier Adams differentials and the \(h_4^2\) survival input used in the lower-dimensional Kervaire package. |
| `BJMtheta5` | The \(h_5^2\) survival / dimension-62 input used to supply a \(\theta_5\). |
| `BJMinduction` | The Barratt–Jones–Mahowald inductive criterion for passing from \(\theta_j\) to \(\theta_{j+1}\). |
| `Maythesis` | May's low-page Adams-survival results used by the lower-dimensional external package. |
| `HHR` | Nonexistence of Kervaire-invariant-one classes in the forbidden higher dimensions. |
| `Xu` | Dimension-62 stable-stem and order-two facts for \(\theta_5\). |
| `IWX` | Stable-stem and \(\theta_5\)-indeterminacy/order-two facts used in the final reduction. |
| `tmf` | The Hurewicz-detection input for the possible \(\lambda^{20}g^4\Delta h_1g\) class. |
| `Pst` | Synthetic spectra, the functor \(\nu\), and the deformation/localization interfaces. |
| `BHS` | Rigidity, synthetic Adams/Bockstein comparison, and the extension interfaces. |
| `BHSmot` | The \(E_\infty\)-structure on the \(\lambda^n\)-quotients used by the synthetic constructions. |
| `BurklundXu` | The synthetic extension of the BJM criterion (Proposition 7.19) and the \(\lambda\eta\theta_5^2\) differential relation. |
| `May01` | The triangulated pullback lemma used in the generalized Leibniz argument. |
| `Moss` | The no-crossing/Toda-bracket criterion used in the final extension contradiction. |
| `BR21` | The manually supplied \(tmf\) Adams differential \(d_3(v_2^{16})=\beta^5g\). |
| `LWXMachine` | Lin–Wang–Xu paper, Zenodo proofs/data, `SSeqCpp`, and plots supplying all Appendix table facts and computed differential/extension evidence. |

Conditional final theorems expose the corresponding mathematical hypotheses.
The current Main development uses one disclosed Challenge2 witness axiom,
which must be replaced by its proved construction before final acceptance.
