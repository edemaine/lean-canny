/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ScalarRootTransport
public import LeanCanny.Encoding.FixedWidthNatVector

/-! # Fixed-width ordinal records for coordinate-grid branches

One distinct-root ordinal per coordinate identifies a grid point. These
records are constant along continuous branches on a retained interval and
have exactly n*W bits when every coordinate degree is at most 2^W. Empty
coordinate families and width-zero records are included. Nonzero specialized
coordinates also give distinct records at singular endpoint fibers. Native
computation of retained interval samples remains required.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateBranchOrdinals
open Set LeanCanny.Algebra LeanCanny.Geometry
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical
variable {n : ℕ}

noncomputable def ordinal (p : Fin n → Polynomial Coefficient) (t : ℝ) (x : Fin n → ℝ) (i : ℕ) : ℕ :=
  if hi : i < n then ScalarRootTransport.rank (p ⟨i, hi⟩) t (x ⟨i, hi⟩) else 0

noncomputable def word (W : ℕ) (p : Fin n → Polynomial Coefficient) (t : ℝ) (x : Fin n → ℝ) : List Bool :=
  FixedWidthNatVector.encode n W (ordinal p t x)

theorem length_word (W : ℕ) (p : Fin n → Polynomial Coefficient) (t : ℝ) (x : Fin n → ℝ) :
    (word W p t x).length = n * W := FixedWidthNatVector.length_encode _ _ _

theorem decode_word_of_ne_zero (W : ℕ) (p : Fin n → Polynomial Coefficient) (t : ℝ) (x : Fin n → ℝ)
    (ht : ∀ i, (p i).map (scalarEvaluation t) ≠ 0)
    (hdeg : ∀ i, (p i).natDegree ≤ 2 ^ W)
    (hx : ∀ i, (p i).eval₂ (scalarEvaluation t) (x i) = 0) (i : Fin n) :
    Nat.fromBitsLE (((word W p t x).drop (i.val * W)).take W) = ScalarRootTransport.rank (p i) t (x i) := by
  have hfit : ordinal p t x i.val < 2 ^ W := by
    rw [ordinal, dite_eq_left i.isLt]
    exact (ScalarRootTransport.rank_lt_degree_of_ne_zero (p i) t (x i) (ht i) (hx i)).trans_le (hdeg i)
  have h := FixedWidthNatVector.decode_block n W (ordinal p t x) i.val i.isLt hfit
  simpa only [word, ordinal, dite_eq_left i.isLt] using h

theorem decode_word (W : ℕ) (p : Fin n → Polynomial Coefficient) (t : ℝ) (x : Fin n → ℝ)
    (ht : ∀ i, scalarEvaluation t (exceptional (p i)) ≠ 0)
    (hdeg : ∀ i, (p i).natDegree ≤ 2 ^ W)
    (hx : ∀ i, (p i).eval₂ (scalarEvaluation t) (x i) = 0) (i : Fin n) :
    Nat.fromBitsLE (((word W p t x).drop (i.val * W)).take W) = ScalarRootTransport.rank (p i) t (x i) :=
  decode_word_of_ne_zero W p t x (fun i => ScalarRootTransport.specialized_ne_zero (p i) t (ht i)) hdeg hx i

theorem word_injective_of_ne_zero (W : ℕ) (p : Fin n → Polynomial Coefficient) (t : ℝ)
    (ht : ∀ i, (p i).map (scalarEvaluation t) ≠ 0)
    (hdeg : ∀ i, (p i).natDegree ≤ 2 ^ W) (x y : Fin n → ℝ)
    (hx : ∀ i, (p i).eval₂ (scalarEvaluation t) (x i) = 0)
    (hy : ∀ i, (p i).eval₂ (scalarEvaluation t) (y i) = 0)
    (he : word W p t x = word W p t y) : x = y := by
  funext i
  have hh := congrArg (fun z : List Bool => Nat.fromBitsLE ((z.drop (i.val * W)).take W)) he
  rw [decode_word_of_ne_zero W p t x ht hdeg hx i, decode_word_of_ne_zero W p t y ht hdeg hy i] at hh
  exact congrArg Subtype.val (ScalarRootTransport.rank_injective_of_ne_zero (p i) t (ht i)
    (a₁ := ⟨x i, hx i⟩) (a₂ := ⟨y i, hy i⟩) hh)

theorem word_injective (W : ℕ) (p : Fin n → Polynomial Coefficient) (t : ℝ)
    (ht : ∀ i, scalarEvaluation t (exceptional (p i)) ≠ 0)
    (hdeg : ∀ i, (p i).natDegree ≤ 2 ^ W) (x y : Fin n → ℝ)
    (hx : ∀ i, (p i).eval₂ (scalarEvaluation t) (x i) = 0)
    (hy : ∀ i, (p i).eval₂ (scalarEvaluation t) (y i) = 0)
    (he : word W p t x = word W p t y) : x = y :=
  word_injective_of_ne_zero W p t (fun i => ScalarRootTransport.specialized_ne_zero (p i) t (ht i)) hdeg x y hx hy he

/-- The anchor record denotes the same coordinate roots at every retained
sample, so no permutation of root ordinals has to be supplied. -/
theorem word_eq (W : ℕ) (p : Fin n → Polynomial Coefficient) {a b : ℝ}
    (havoid : ∀ t ∈ Ioo a b, ∀ i, scalarEvaluation t (exceptional (p i)) ≠ 0)
    (f : C(Ioo a b, Fin n → ℝ))
    (hf : ∀ t i, (p i).eval₂ (scalarEvaluation t.val) (f t i) = 0) (s t : Ioo a b) :
    word W p s.val (f s) = word W p t.val (f t) := by
  unfold word
  congr 1
  funext i
  by_cases hi : i < n
  · simp only [ordinal, dite_eq_left hi]
    let fi : C(Ioo a b, Fin 1 → ℝ) :=
      ⟨fun u _ => f u ⟨i, hi⟩, continuous_pi (fun _ => (continuous_apply (⟨i, hi⟩ : Fin n)).comp f.continuous)⟩
    exact ScalarRootTransport.rank_eq (p ⟨i, hi⟩) (fun u hu => havoid u hu ⟨i, hi⟩)
      fi (fun u => hf u ⟨i, hi⟩) s t
  · simp [ordinal, hi]

end LeanCanny.Encoding.CoordinateBranchOrdinals
