import LeanCanny.Connectivity.Encoding
import LeanCanny.Connectivity.FormulaPathCover

/-! # Connectivity development

Checked input encodings, finite closed path covers, and native polynomial-space
implicit-graph algorithms. For supplied formula-defined covers, ETR supplies
the validity and intersection tests. The effective semialgebraic roadmap
construction is not yet supplied. In particular, neither
`Connectivity.pointLanguage` nor `Connectivity.connectedLanguage` has a PSPACE
membership theorem here.
-/
