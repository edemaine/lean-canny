/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparableSpace

/-! # Reindexing certified original polynomial families -/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open LeanCanny.Encoding LeanCanny.Computation

noncomputable abbrev Family.reindex (F : Family) (input : List Bool → List Bool) : Family :=
  CertifiedPolynomial.Family.reindex F input

abbrev reindexQuery := CertifiedPolynomial.reindexQuery

theorem reindexQuery_FP (input : List Bool → List Bool) (hi : input ∈ FP) : reindexQuery input ∈ FP :=
  CertifiedPolynomial.reindexQuery_FP input hi

noncomputable def Readers.reindex {F : Family} (A : Readers F) (input : List Bool → List Bool) (hi : input ∈ FP) :
    Readers (F.reindex input) where
  toReaders := A.toReaders.reindex input hi
  toExactDegree := A.toExactDegree.reindex input hi

end LeanCanny.Algebra.SeparableBits
