module
import LeanCanny.Connectivity.NativeConnectivityPSPACE
open LeanCanny LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR Set
open scoped Classical
namespace ConnectivityPSPACERegression

example : connectedLanguage ∈ PSPACE := connectedLanguage_mem_PSPACE
example : pointLanguage ∈ PSPACE := pointLanguage_mem_PSPACE

/-- Every malformed point encoding is rejected, independently of its payload. -/
example (b : List Bool) (h : ¬Input.IsPoint b) : b ∉ pointLanguage := by
  rintro ⟨q,rfl,_⟩
  exact h ((Input.isPoint_iff _).mpr ⟨q,rfl⟩)

/-- Nonunique or inconsistent endpoint formulas are rejected. -/
example (q : PointQuery) (h : ¬∃x : Fin q.space.dimension → ℝ,Denotes q.space.dimension q.source x) :
    (Input.point q).encode ∉ pointLanguage := by
  rw [point_encode_mem_iff]
  rintro ⟨_,x,_,hx,_,_⟩
  exact h ⟨x,hx⟩

/-- Whole-space connectivity accepts the empty set, including dimension zero. -/
example : (Input.whole ⟨0,Formula.falsum⟩).encode ∈ connectedLanguage := by
  rw [whole_encode_mem_iff]
  refine ⟨by change 0 ≤ 0; exact le_rfl,?_⟩
  change IsPreconnected {x : Fin 0 → ℝ | False}
  simpa only [ofPred_false] using (isPreconnected_empty : IsPreconnected (∅ : Set (Fin 0 → ℝ)))

#print axioms connectedLanguage_mem_PSPACE
#print axioms pointLanguage_mem_PSPACE
#print axioms FormulaSignSlotRadialGuardedFeasibilityNative.word_decider
#print axioms FormulaSignSlotRadialGuardedFeasibilityNative.feasible_mem_PSPACE
#print axioms FormulaSignSlotRadialGuardedFeasibility.language_iff_feasible
#print axioms CanonicalAuxiliaryNativeFrontier.edge_eq
end ConnectivityPSPACERegression
