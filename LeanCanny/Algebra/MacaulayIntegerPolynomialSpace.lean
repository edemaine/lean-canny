/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayPolynomialBinarySpace

/-! # Native modular entries of implicit integer polynomial Macaulay matrices

The modulus is retained in every source query. Binary source degrees use the
same entry program and correctness theorem as the unary backend.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayIntegerPolynomialBits
open LeanCanny.Encoding LeanCanny.Computation MacaulayBits MatrixPower
open scoped Classical

def modularLayout (L : Layout) : Layout where
  arity := L.arity ∘ pairFst
  width := L.width ∘ pairFst
  degree z i := L.degree (pairFst z) i

theorem modularLayout_binary {L : Layout} (h : L.BinaryPolyTime) : (modularLayout L).BinaryPolyTime := by
  refine ⟨h.arity.comp pairFst_mem_FP, h.width.comp pairFst_mem_FP, ?_⟩
  refine BinaryFn.of_eq (h.degree.comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)) ?_
  intro q
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, modularLayout]

def dimension (L : Layout) (c : List Bool) : ℕ := FixedWidthPolynomial.count (L.arity c) (L.width c)

noncomputable def matrix (L : Layout)
    (Q : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) (Polynomial ℤ)) (c : List Bool) :=
  Macaulay.matrix (Q c) (Degrees L c) (L.width c)

def entry (L : Layout) (reader : List Bool → List Bool) : List Bool → List Bool :=
  entryWithIdentity (modularLayout L) (reader ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ pairSnd)) ∘ PolynomialMoment.augmentedInput

theorem entry_evaluator {L : Layout} (h : L.BinaryPolyTime) {reader : List Bool → List Bool}
    (E : SpaceFunction reader) : SpaceFunction (entry L reader) :=
  (entryWithIdentityBinaryEvaluator (modularLayout_binary h)
    (E.precompose MacaulayPolynomial.sourceInput MacaulayPolynomial.sourceInput_mem_FP)
    (MacaulayPolynomial.constantEntry_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP))).precompose
      PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

theorem raw_entry_packet (L : Layout)
    (Q : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) (Polynomial ℤ))
    (reader : List Bool → List Bool)
    (hc : ∀ z (i : Fin (L.arity (pairFst z))) r k,
      reader (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode k)))) =
        residueBits (((((Q (pairFst z) i).coeff
          (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst z)) (FixedWidthPolynomial.entry (L.width (pairFst z)) r))).coeff k) : ℤ) :
            ZMod (Nat.fromBitsLE (pairSnd z) + 1)))
    (z : List Bool) (i j : Fin (dimension L (pairFst z))) (k : ℕ) :
    entry L reader (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
      residueBits ((((matrix L Q (pairFst z) i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd z) + 1)) := by
  simp only [entry, Function.comp_apply, PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair]
  change entryWithIdentity (modularLayout L) (reader ∘ MacaulayPolynomial.sourceInput)
    (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ pairSnd))
      (packet (pair z (BinaryNatCode.encode k)) i.val j.val) = _
  have H := entryWithIdentity_packet (R := Polynomial ℤ) (modularLayout L)
    (reader ∘ MacaulayPolynomial.sourceInput) (MacaulayPolynomial.constantEntry (BinaryNat.succ ∘ pairSnd))
    (pair z (BinaryNatCode.encode k))
  dsimp only [Indices, modularLayout, Function.comp_apply] at H
  rw [pairFst_pair] at H
  refine H (Q (pairFst z)) (fun p => residueBits ((p.coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd z) + 1)))
    (by simp [residueBits, BinaryNatCode.encode]) ?_ i j ?_
  · intro s r
    rw [MacaulayPolynomial.sourceInput_packet]
    exact hc z s r k
  · have hid : ((((if i.val = j.val then 1 else 0) : Polynomial ℤ).coeff k : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd z) + 1)) =
        ((if i.val = j.val then 1 else 0) : Polynomial (ZMod (Nat.fromBitsLE (pairSnd z) + 1))).coeff k := by
      by_cases hij : i.val = j.val <;> by_cases hk : k = 0 <;> simp [hij, hk, Polynomial.coeff_one]
    rw [hid]
    exact MacaulayPolynomial.constantEntry_packet (BinaryNat.succ ∘ pairSnd) z
      (Nat.fromBitsLE (pairSnd z) + 1) k i.val j.val (BinaryNat.succ_eq_bits _)

theorem entry_packet (L : Layout)
    (Q : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) (Polynomial ℤ))
    (reader : List Bool → List Bool)
    (hc : ∀ z (i : Fin (L.arity (pairFst z))) r k,
      reader (pair z (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode k)))) =
        residueBits (((((Q (pairFst z) i).coeff
          (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst z)) (FixedWidthPolynomial.entry (L.width (pairFst z)) r))).coeff k) : ℤ) :
            ZMod (Nat.fromBitsLE (pairSnd z) + 1)))
    (c m : List Bool) (i j : Fin (dimension L c)) (k : ℕ) :
    entry L reader (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k)))) =
        residueBits ((((matrix L Q c i j).coeff k) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair c m = z
  have hctx : pairFst z = c := by rw [← hz, pairFst_pair]
  have hm : pairSnd z = m := by rw [← hz, pairSnd_pair]
  subst c
  subst m
  exact raw_entry_packet L Q reader hc z i j k

end LeanCanny.Algebra.MacaulayIntegerPolynomialBits
