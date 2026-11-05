/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # Bounded native coefficient guards preserve their whole conjunction -/
@[expose] public section
namespace LeanCanny.Computation.FiniteCoefficientGuardTransport
open LeanCanny.Encoding LeanCanny.Algebra FiniteCoefficientSignScan
set_option backward.isDefEq.respectTransparency false

/-- The leading and lower-choice requests fit the same literal finite range;
no higher coefficient is discarded at the stored degree. -/
theorem guards_iff (s t h h' : List Bool → List Bool)
    (K D C K' D' C' : List Bool → ℕ) (q r : List Bool)
    (hK : K q = K' r) (hD : D q = D' r) (hC : C q = C' r)
    (hd : D q ≤ C q)
    (hs : ∀ e ≤ C q, ∀ k ≤ K q, s (query q e k) = t (query r e k))
    (hh : h q = h' r) : Guards s h K D C q ↔ Guards t h' K' D' C' r := by
  have hz (e k : ℕ) (he : e ≤ C q) (hl : k ≤ K q) : FiniteCoefficientSignScan.Zero s q e k ↔ FiniteCoefficientSignScan.Zero t r e k := by
    unfold FiniteCoefficientSignScan.Zero
    rw [hs e he k hl]
  unfold Guards
  rw [← hK, ← hD, ← hC, hh]
  constructor
  · rintro ⟨lower, leading, higher, head⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hl e he
      exact (hz e k (by omega) hl.le).mp (lower k hl e he)
    · exact fun hzero => leading ((hz (D q) (K q) hd le_rfl).mpr hzero)
    · intro e he hde
      exact (hz e (K q) (by omega) le_rfl).mp (higher e he hde)
    · exact head.imp id ((hz 0 (K q) (Nat.zero_le _) le_rfl).mp)
  · rintro ⟨lower, leading, higher, head⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hl e he
      exact (hz e k (by omega) hl.le).mpr (lower k hl e he)
    · exact fun hzero => leading ((hz (D q) (K q) hd le_rfl).mp hzero)
    · intro e he hde
      exact (hz e (K q) (by omega) le_rfl).mpr (higher e he hde)
    · exact head.imp id ((hz 0 (K q) (Nat.zero_le _) le_rfl).mpr)

end LeanCanny.Computation.FiniteCoefficientGuardTransport
