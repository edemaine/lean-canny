import LeanCanny.Connectivity.Encoding
import LeanCanny.Connectivity.FormulaPathCover
import LeanCanny.Connectivity.EndpointValidation

/-! # Connectivity development

Checked input encodings, finite closed path covers, and native polynomial-space
implicit-graph algorithms. Canonical input recognition is polynomial time;
singleton endpoint validation is in native PSPACE on all bitstrings. For
supplied formula-defined covers, ETR supplies the validity and intersection
tests. The effective semialgebraic roadmap
construction is not yet supplied. In particular, neither
`Connectivity.pointLanguage` nor `Connectivity.connectedLanguage` has a PSPACE
membership theorem here.
-/
