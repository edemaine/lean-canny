/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitSource
public import LeanCanny.Algebra.FermatLevelFramedTiltedSyntax
/-! # Concrete tilted original sources for canonical changing-source records

The original term fixes the spatial Fermat degree once. Each record changes
only the frozen count, tilt coordinate and implicit level exponent. The
constructor proves the actual LOW degree and unit leading coefficient,
including malformed coordinate indices (finite-polynomial clipping remains
literal). Geometric use additionally supplies the usual coordinate scopes.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalTiltedSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory MvPolynomial

noncomputable def low (n k u E : ℕ) (t : ETR.Term) : MvPolynomial (Fin (n+1)) ℤ :=
  rename Fin.castSucc ((FixedLeadingTiltedSource.lowTerm k t.toData.size u t).finitePolynomial n)-
    C ((2:ℤ)^E)*X (Fin.last n)

theorem low_degree (n k u E : ℕ) (t : ETR.Term) :
    (low n k u E t).totalDegree<FixedLeadingTiltedSource.degree t.toData.size := by
  unfold low
  apply (totalDegree_sub _ _).trans_lt
  apply max_lt
  · exact (totalDegree_rename_le _ _).trans_lt
      ((ETR.Term.totalDegree_finitePolynomial _ _).trans_lt
        (FixedLeadingTiltedSource.lowTerm_degree k t.toData.size u t t.degreeBound_le_dataSize))
  · apply (totalDegree_mul _ _).trans_lt
    simp only [totalDegree_C,totalDegree_X,zero_add,FixedLeadingTiltedSource.degree]
    omega

noncomputable def source (n k u E : ℕ) (t : ETR.Term) : SpatialSource n where
  low := low n k u E t
  leading := 1
  degree := FixedLeadingTiltedSource.degree t.toData.size
  degree_two := by simp only [FixedLeadingTiltedSource.degree]; omega
  low_degree := low_degree n k u E t
  leading_ne_zero := one_ne_zero

theorem source_geometry {n : ℕ} (k E : ℕ) (u : Fin n) (t : ETR.Term) :
    source (n+1) k u.val E t=
      FermatLevelLift.source (FixedLeadingTiltedSource.source k t.toData.size u t t.degreeBound_le_dataSize) ((2:ℤ)^E) := rfl

noncomputable def originals (P : Parameters) (t : List Bool → ETR.Term)
    (k u E : List Bool → ℕ → ℕ)
    (hd : ∀ root, FixedLeadingTiltedSource.degree (t root).toData.size=P.degree root) :
    IntegralMixedCanonicalUnitSourceBits.Originals P :=
  IntegralMixedCanonicalUnitSourceBits.ofSources P
    (fun root b => source (P.ambient root) (k root b) (u root b) (E root b) (t root))
    (fun root _ => hd root)

theorem source_originals (P : Parameters) (t : List Bool → ETR.Term)
    (k u E : List Bool → ℕ → ℕ)
    (hd : ∀ root, FixedLeadingTiltedSource.degree (t root).toData.size=P.degree root)
    (root : List Bool) (b : ℕ) :
    IntegralMixedCanonicalUnitSourceBits.source P (originals P t k u E hd) root b=
      source (P.ambient root) (k root b) (u root b) (E root b) (t root) :=
  IntegralMixedCanonicalUnitSourceBits.source_ofSources P _ (fun root _ => hd root) (fun _ _ => rfl) root b

theorem low_saved (P : Parameters) (t : List Bool → ETR.Term)
    (k u E : List Bool → ℕ → ℕ)
    (hd : ∀ root, FixedLeadingTiltedSource.degree (t root).toData.size=P.degree root)
    (index : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedCanonicalUnitSourceBits.source P (originals P t k u E hd) (pairFst key) (index key)).low=
      FermatLevelFramedTiltedSyntax.low P (fun z => t (pairFst z))
        (fun z => k (pairFst z) (index z)) (fun z => u (pairFst z) (index z))
        (fun z => E (pairFst z) (index z)) key := rfl

end LeanCanny.Algebra.IntegralMixedCanonicalTiltedSourceBits
