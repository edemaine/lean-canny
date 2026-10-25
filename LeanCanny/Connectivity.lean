import LeanCanny.Connectivity.Encoding
import LeanCanny.Connectivity.FormulaPathCover
import LeanCanny.Connectivity.EndpointValidation
import LeanCanny.Connectivity.AccessibleArc
import LeanCanny.Geometry.RootBranchLocal

/-! # Connectivity development

Checked input encodings, finite closed path covers, frontier incidence, and native polynomial-space
implicit-graph algorithms. Canonical input recognition is polynomial time;
singleton endpoint validation is in native PSPACE on all bitstrings. For
supplied formula-defined covers, ETR supplies the validity and intersection
tests. Regular root systems have local continuous branches; bounded continuous
algebraic branches extend to their finite endpoints, giving the accessibility
needed for frontier-incidence graphs. The effective semialgebraic roadmap
construction is not yet supplied. In particular, neither
`Connectivity.pointLanguage` nor `Connectivity.connectedLanguage` has a PSPACE
membership theorem here.
-/
