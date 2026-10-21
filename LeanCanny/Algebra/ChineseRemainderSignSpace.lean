/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderSignBit
public import LeanCanny.Algebra.DyadicSumSpace

/-!
# Certified sign evaluation from local CRT preparation

The remaining algorithmic input is a space-bounded routine returning one
locally reduced CRT numerator and its modulus. FP count/precision writers and
the proved CRT magnitude/precision bounds then supply a complete sign evaluator
and PSPACE decision procedure. Zero is included without a separate oracle.
Constructing the local preparation routine from residue access remains separate.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

theorem signEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count precision : List Bool → List Bool) (hc : count ∈ FP) (hp : precision ∈ FP)
    (F : (c : List Bool) → System (Fin (Nat.fromBitsLE (count c))))
    (r : (c : List Bool) → Fin (Nat.fromBitsLE (count c)) → ℕ) (z : List Bool → ℤ)
    (hres : ∀ c i, (r c i : ZMod ((F c).modulus i)) = z c)
    (hmag : ∀ c, 2 * (z c).natAbs < (F c).product)
    (hprecision : ∀ c, 0 < Nat.fromBitsLE (precision c) ∧
      2 * Nat.fromBitsLE (count c) * (F c).product < 2 ^ Nat.fromBitsLE (precision c))
    (hprep : ∀ c (i : Fin (Nat.fromBitsLE (count c))),
      f (pair c (BinaryNatCode.encode i.val)) =
        pair (BinaryNatCode.encode ((F c).numerator (r c) i)) (BinaryNatCode.encode ((F c).modulus i - 1))) :
    SpaceFunction (fun c => if z c < 0 then [true] else []) := by
  let A := fun c i => if h : i < Nat.fromBitsLE (count c) then (F c).numerator (r c) ⟨i, h⟩ else 0
  let M := fun c i => if h : i < Nat.fromBitsLE (count c) then (F c).modulus ⟨i, h⟩ else 1
  have hprep' : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = pair (BinaryNatCode.encode (A c i)) (BinaryNatCode.encode (M c i - 1)) := by
    intro c i hi
    simpa only [A, M, dite_eq_left hi] using hprep c ⟨i, hi⟩
  have hm : ∀ c i, i < Nat.fromBitsLE (count c) → 0 < M c i := by
    intro c i hi
    simpa only [M, dite_eq_left hi] using (F c).positive ⟨i, hi⟩
  have ha : ∀ c i, i < Nat.fromBitsLE (count c) → A c i < M c i := by
    intro c i hi
    simpa only [A, M, dite_eq_left hi] using (F c).numerator_lt (r c) ⟨i, hi⟩
  have hi := mem_FP_comp hp BinaryNat.pred_mem_FP
  let E' := DyadicSumBits.evaluator E count precision (BinaryNat.pred ∘ precision) hc hp hi A M hprep' hm ha
  refine E'.congr (funext fun c => ?_)
  have hsum : (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)),
      2 ^ Nat.fromBitsLE (precision c) * A c i / M c i) =
      (F c).truncatedSum (r c) (2 ^ Nat.fromBitsLE (precision c)) := by
    rw [Finset.sum_range]
    unfold System.truncatedSum
    apply Finset.sum_congr rfl
    intro i _
    simp only [A, M, dite_eq_left i.is_lt]
  have hidx : Nat.fromBitsLE ((BinaryNat.pred ∘ precision) c) = Nat.fromBitsLE (precision c) - 1 := by
    simp only [Function.comp_apply, BinaryNat.pred_eq_bits, Nat.fromBitsLE_bits]
  have hpos := (hprecision c).1
  have he : Nat.fromBitsLE (precision c) - 1 + 1 = Nat.fromBitsLE (precision c) := by omega
  have hpr : 2 * Fintype.card (Fin (Nat.fromBitsLE (count c))) * (F c).product <
      2 ^ (Nat.fromBitsLE (precision c) - 1 + 1) := by
    simpa only [he, Fintype.card_fin] using (hprecision c).2
  have hsign := (F c).negative_iff_truncated_bit (r c) (z c) (hres c) (hmag c) _ hpr
  rw [he] at hsign
  rw [hsum, hidx]
  simp only [← hsign]

/-- A count writer can describe a separately named index cardinality. This
avoids transporting the dependent modulus family by hand at each application. -/
theorem signEvaluatorOfCount {f : List Bool → List Bool} (E : SpaceFunction f)
    (count precision : List Bool → List Bool) (hc : count ∈ FP) (hp : precision ∈ FP)
    (N : List Bool → ℕ) (hcount : ∀ c, Nat.fromBitsLE (count c) = N c)
    (F : (c : List Bool) → System (Fin (N c))) (r : (c : List Bool) → Fin (N c) → ℕ) (z : List Bool → ℤ)
    (hres : ∀ c i, (r c i : ZMod ((F c).modulus i)) = z c)
    (hmag : ∀ c, 2 * (z c).natAbs < (F c).product)
    (hprecision : ∀ c, 0 < Nat.fromBitsLE (precision c) ∧
      2 * N c * (F c).product < 2 ^ Nat.fromBitsLE (precision c))
    (hprep : ∀ c (i : Fin (N c)), f (pair c (BinaryNatCode.encode i.val)) =
      pair (BinaryNatCode.encode ((F c).numerator (r c) i)) (BinaryNatCode.encode ((F c).modulus i - 1))) :
    SpaceFunction (fun c => if z c < 0 then [true] else []) := by
  have he : (fun c => Nat.fromBitsLE (count c)) = N := funext hcount
  subst N
  exact signEvaluator E count precision hc hp F r z hres hmag hprecision hprep

theorem negativeLanguage_mem_PSPACE {f : List Bool → List Bool} (E : SpaceFunction f)
    (count precision : List Bool → List Bool) (hc : count ∈ FP) (hp : precision ∈ FP)
    (F : (c : List Bool) → System (Fin (Nat.fromBitsLE (count c))))
    (r : (c : List Bool) → Fin (Nat.fromBitsLE (count c)) → ℕ) (z : List Bool → ℤ)
    (hres : ∀ c i, (r c i : ZMod ((F c).modulus i)) = z c)
    (hmag : ∀ c, 2 * (z c).natAbs < (F c).product)
    (hprecision : ∀ c, 0 < Nat.fromBitsLE (precision c) ∧
      2 * Nat.fromBitsLE (count c) * (F c).product < 2 ^ Nat.fromBitsLE (precision c))
    (hprep : ∀ c (i : Fin (Nat.fromBitsLE (count c))),
      f (pair c (BinaryNatCode.encode i.val)) =
        pair (BinaryNatCode.encode ((F c).numerator (r c) i)) (BinaryNatCode.encode ((F c).modulus i - 1))) :
    {c | z c < 0} ∈ PSPACE := by
  have E' := signEvaluator E count precision hc hp F r z hres hmag hprecision hprep
  have hb : (fun w : List Bool => [w[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply (E'.decider (fun w => w[0]?.getD false) hb ?_).mem_PSPACE
  intro c
  by_cases hz : z c < 0 <;> simp [hz]

end LeanCanny.Algebra.ChineseRemainder
