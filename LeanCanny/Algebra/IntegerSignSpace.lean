/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CRTPreparationSpace
public import LeanCanny.Algebra.ChineseRemainderSignSpace

/-!
# Integer sign recovery from certified small-residue access

An FP writer supplies a magnitude-bit budget, which may itself be exponential.
The routine constructs indexed CRT moduli, their local inverse weights, and
the truncated-quotient sum bit. Thus a uniform space-bounded residue routine
suffices for a certified integer sign evaluator. Full integer values, combined
CRT moduli, dyadic precision words, and quotient sums are never stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerSignBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Algebra.ChineseRemainder

def bound (budget : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.add (pair (budget c) (budget c))) (BinaryNatCode.encode 6))
def count (budget : List Bool → List Bool) : List Bool → List Bool := BinaryNat.succ ∘ bound budget
def precision (budget : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.mul (pair
    (BinaryNat.add (pair (bound budget c) (BinaryNatCode.encode 2)))
    (BinaryNatCode.encode (bound budget c).length))) (BinaryNatCode.encode 2))

theorem bound_mem_FP {budget : List Bool → List Bool} (hb : budget ∈ FP) : bound budget ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair hb hb) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP (BinaryNatCode.encode 6))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := bound budget) h ?_
  intro c
  simp only [Function.comp_apply, bound]

theorem count_mem_FP {budget : List Bool → List Bool} (hb : budget ∈ FP) : count budget ∈ FP :=
  mem_FP_comp (bound_mem_FP hb) BinaryNat.succ_mem_FP

theorem precision_mem_FP {budget : List Bool → List Bool} (hb : budget ∈ FP) : precision budget ∈ FP := by
  have hN := bound_mem_FP hb
  have hs : (fun c => BinaryNatCode.encode (bound budget c).length) ∈ FP := bits_mem_FP (UnaryFn.length hN)
  have hp := mem_FP_comp (mem_FP_pair hN (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.add_mem_FP
  have hm := mem_FP_comp (mem_FP_pair hp hs) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := precision budget) h ?_
  intro c
  simp only [Function.comp_apply, precision]

theorem bound_code (budget : List Bool → List Bool) (c : List Bool) :
    bound budget c = BinaryNatCode.encode (2 * Nat.fromBitsLE (budget c) + 6) := by
  simp only [bound, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  omega

theorem precision_code (budget : List Bool → List Bool) (c : List Bool) :
    precision budget c = BinaryNatCode.encode (precisionBits (2 * Nat.fromBitsLE (budget c) + 6)) := by
  simp only [precision, bound_code, BinaryNat.add_pair, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len, precisionBits]

theorem evaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    SpaceFunction (fun c => if z c < 0 then [true] else []) := by
  let N := fun c => Nat.fromBitsLE (bound budget c)
  let F := fun c => indexedSystem (N c)
  let r := fun c (i : Fin (N c + 1)) => (z c : ZMod ((F c).modulus i)).val
  have hN (c : List Bool) : N c = 2 * Nat.fromBitsLE (budget c) + 6 := by
    simp only [N, bound_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hcount (c : List Bool) : Nat.fromBitsLE (count budget c) = N c + 1 := by
    simp only [count, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, N]
  have hp (c : List Bool) : Nat.fromBitsLE (precision budget c) = precisionBits (N c) := by
    simp only [precision_code, BinaryNatCode.encode, Nat.fromBitsLE_bits, hN]
  let P := PreparationBits.evaluator R (bound budget) (bound_mem_FP hb)
  refine signEvaluatorOfCount P (count budget) (precision budget) (count_mem_FP hb) (precision_mem_FP hb)
    (fun c => N c + 1) hcount F r z ?_ ?_ ?_ ?_
  · intro c i
    have : NeZero ((F c).modulus i) := ⟨(F c).positive i |>.ne'⟩
    exact ZMod.natCast_zmod_val _
  · intro c
    change 2 * (z c).natAbs < (indexedSystem (N c)).product
    rw [hN]
    exact indexed_magnitude_bound (z c) _ (hbudget c)
  · intro c
    rw [hp]
    constructor
    · dsimp only [precisionBits]
      omega
    · simpa only [F, Fintype.card_fin] using indexed_precision_sufficient (N c)
  · intro c i
    exact PreparationBits.value_pair (bound budget) rho c (z c) (hres c) i

theorem negativeLanguage_mem_PSPACE {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    {c | z c < 0} ∈ PSPACE := by
  have E := evaluator R budget hb z hbudget hres
  have ha : (fun w : List Bool => [w[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply (E.decider (fun w => w[0]?.getD false) ha ?_).mem_PSPACE
  intro c
  by_cases hz : z c < 0 <;> simp [hz]

end LeanCanny.Algebra.IntegerSignBits
