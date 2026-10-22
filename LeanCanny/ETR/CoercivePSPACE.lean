/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveCoordinatePairReaders
public import LeanCanny.ETR.CoerciveParameterAccess
public import LeanCanny.ETR.CoerciveClearedQueryCoefficient

/-! # Canny's polynomial-space upper bound for the existential theory of the reals

The prepared parameter and cleared sign-query programs include the costs of
constructing their annihilators, preparation tables, symbolic squarefree leaves,
resultant trees, and rational coordinate paths. Their native polynomial-space
certificates close the effective coercive sampling and infinitesimal sign proof.
-/

@[expose] public section
namespace LeanCanny.ETR
open LeanCanny.Computation

/-- The actual prepared parameter and final sign-query programs. -/
noncomputable def coerciveReaders : CoerciveInfinitesimalFamily.Readers :=
  CoerciveClearedQueryCoefficient.readers CoerciveCoordinatePairReaders.readers
    CoerciveParameterAccess.access CoerciveParameterAccess.evaluator

/-- Encoded existential real feasibility belongs to native deterministic PSPACE. -/
theorem etr_mem_PSPACE : language ∈ PSPACE :=
  CoerciveInfinitesimalFamily.etr_mem_PSPACE_of_readers coerciveReaders

/-- Every language polynomial-time reducible to ETR belongs to PSPACE. -/
theorem existsReal_subset_PSPACE : ExistsReal ⊆ PSPACE :=
  LeanCanny.existsReal_subset_PSPACE_of_etr etr_mem_PSPACE

end LeanCanny.ETR
