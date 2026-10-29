/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthLinearCoefficientSpace
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Computation.SpaceFunctionSelect

/-! # Native coefficients of weighted linear heights

A bounded exponent scan selects the scalar summands contributing to a queried
monomial. Their signed residues are streamed through a modular sum. Variable
selections may coincide, so collected coefficients include every contribution.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (A N : List Bool → ℕ)
    (a : (c : List Bool) → Fin (N c) → ℤ) (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (c : List Bool) : MvPolynomial (Fin (A c)) ℤ := ∑ i, C (a c i) * X (f c i)

noncomputable def summand (A W selected : List Bool → ℕ)
    (target reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  if FixedWidthLinearCoefficientBits.Matches (A ∘ pairFst) (W ∘ pairFst) selected (target ∘ pairFst) q
    then reader q else []

theorem summand_evaluator {A W selected : List Bool → ℕ} {target reader : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (ht : target ∈ FP)
    (hr : SpaceFunction reader) : SpaceFunction (summand A W selected target reader) := by
  have hb := FixedWidthLinearCoefficientBits.matches_FP (A ∘ pairFst) (W ∘ pairFst) selected (target ∘ pairFst)
    (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) hs (mem_FP_comp pairFst_mem_FP ht)
  exact (SpaceFunction.branch _ hb.flag_mem_FP hr (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun _ => by simp only [summand, decide_eq_true_eq])

noncomputable def value (A N W : List Bool → ℕ)
    (a : (c : List Bool) → Fin (N c) → ℤ) (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((polynomial A N a f c).coeff
    (nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c)))

theorem evaluator_of_summand {A N W selected : List Bool → ℕ}
    {target modulus reader : List Bool → List Bool}
    (hN : UnaryFn N) (hm : modulus ∈ FP)
    (hr : SpaceFunction (summand A W selected target reader))
    (a : (c : List Bool) → Fin (N c) → ℤ) (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (hselected : ∀ c i, selected (pair c (BinaryNatCode.encode i.val)) = (f c i).val)
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hreader : ∀ c i, reader (pair c (BinaryNatCode.encode i.val)) =
      residueBits ((a c i : ℤ) : ZMod (Nat.fromBitsLE (modulus c)))) :
    SpaceFunction (value A N W a f target modulus) := by
  let E (c : List Bool) := nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))
  let term (c : List Bool) (i : ℕ) : ZMod (Nat.fromBitsLE (modulus c)) :=
    if hi : i < N c then (((C (a c ⟨i, hi⟩) * X (f c ⟨i, hi⟩) : MvPolynomial (Fin (A c)) ℤ).coeff (E c) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c))) else 0
  have hp (c : List Bool) (i : ℕ) (hi : i < N c) :
      summand A W selected target reader (pair c (BinaryNatCode.encode i)) = residueBits (term c i) := by
    let j : Fin (N c) := ⟨i, hi⟩
    have hsel : selected (pair c (BinaryNatCode.encode i)) = (f c j).val := hselected c j
    have hmch : FixedWidthLinearCoefficientBits.Matches (A ∘ pairFst) (W ∘ pairFst) selected
        (target ∘ pairFst) (pair c (BinaryNatCode.encode i)) ↔ E c = Finsupp.single (f c j) 1 := by
      have hval (v : Fin (A c)) : E c v = FixedWidthQuery.coordinate W target c v.val :=
        FixedWidthBlockRenameBits.entry_bits _ _ _
      simp only [FixedWidthLinearCoefficientBits.Matches, Function.comp_apply, pairFst_pair, hsel]
      constructor
      · rintro ⟨_, h⟩
        ext v
        rw [hval]
        simpa only [FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, hsel, Finsupp.single_apply, Fin.ext_iff, eq_comm] using h v.val v.isLt
      · intro h
        refine ⟨(f c j).isLt, ?_⟩
        intro v hv
        have he := congrArg (fun m : Fin (A c) →₀ ℕ => m ⟨v, hv⟩) h
        simpa only [hval, FixedWidthQuery.coordinate, Function.comp_apply, pairFst_pair, hsel, Finsupp.single_apply, Fin.ext_iff, eq_comm] using he
    rw [summand, hmch]
    rw [show reader (pair c (BinaryNatCode.encode i)) =
      residueBits ((a c j : ℤ) : ZMod (Nat.fromBitsLE (modulus c))) from hreader c j]
    have hterm : term c i = (((C (a c j) * X (f c j) : MvPolynomial (Fin (A c)) ℤ).coeff (E c) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c))) := by
      simp only [term, dite_eq_left hi]
      rfl
    rw [hterm]
    by_cases he : E c = Finsupp.single (f c j) 1
    · simp only [he, ite_true, coeff_C_mul, coeff_X, mul_one]
    · simp only [he, ite_false, coeff_C_mul, coeff_X, Ne.symm he, mul_zero,
        Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
      rfl
  have H := ModularSum.evaluatorWithModulus hr
    (BinaryNatCode.encode ∘ N) modulus (BinaryFn.ofUnary hN).bits_mem_FP hm
    (fun c => Nat.fromBitsLE (modulus c)) rfl term hpos (by
      intro c i hi
      simp only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi
      exact hp c i hi)
  refine H.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits, value, polynomial,
    coeff_sum, Int.cast_sum, Finset.sum_range]
  apply congrArg residueBits
  apply Finset.sum_congr rfl
  intro i _
  simp only [term, dite_eq_left i.isLt]
  rfl

theorem evaluator {A N W selected : List Bool → ℕ}
    {target modulus reader : List Bool → List Bool}
    (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W) (hs : BinaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (hr : SpaceFunction reader)
    (a : (c : List Bool) → Fin (N c) → ℤ) (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (hselected : ∀ c i, selected (pair c (BinaryNatCode.encode i.val)) = (f c i).val)
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hreader : ∀ c i, reader (pair c (BinaryNatCode.encode i.val)) =
      residueBits ((a c i : ℤ) : ZMod (Nat.fromBitsLE (modulus c)))) :
    SpaceFunction (value A N W a f target modulus) :=
  evaluator_of_summand hN hm (summand_evaluator hA hW hs ht hr) a f hselected hpos hreader

/-- A space-bounded variable selector can depend on an ancestral level record. -/
theorem summand_evaluator_space {A W selected : List Bool → ℕ} {target reader : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) (hr : SpaceFunction reader)
    (hs : SpaceFunction (BinaryNatCode.encode ∘ selected)) :
    SpaceFunction (summand A W selected target reader) := by
  let old := pairFst ∘ pairFst
  let test (z : List Bool) := decide (FixedWidthLinearCoefficientBits.Matches
    (A ∘ old) (W ∘ old) (fun z => Nat.fromBitsLE (pairSnd z)) (target ∘ old) z)
  have ho : old ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hb := FixedWidthLinearCoefficientBits.matches_FP (A ∘ old) (W ∘ old)
    (fun z => Nat.fromBitsLE (pairSnd z)) (target ∘ old) (hA.comp ho) (hW.comp ho)
    (BinaryFn.fromBits pairSnd_mem_FP) (mem_FP_comp ho ht)
  have hp : SpaceFunction (fun q => [decide (FixedWidthLinearCoefficientBits.Matches
      (A ∘ pairFst) (W ∘ pairFst) selected (target ∘ pairFst) q)]) := by
    have H := hs.withInput.postcompose (fun z => [test z]) hb.flag_mem_FP
    refine H.congr (funext fun q => ?_)
    simp only [test, FixedWidthLinearCoefficientBits.Matches, old, FixedWidthQuery.coordinate,
      Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    apply congrArg List.singleton
    apply decide_eq_decide.mpr
    rfl
  exact (SpaceFunction.select hp hr (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun q => by simp only [summand, List.getElem?_cons_zero, Option.getD_some, decide_eq_true_eq])

theorem evaluator_space {A N W selected : List Bool → ℕ}
    {target modulus reader : List Bool → List Bool}
    (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W)
    (hs : SpaceFunction (BinaryNatCode.encode ∘ selected))
    (ht : target ∈ FP) (hm : modulus ∈ FP) (hr : SpaceFunction reader)
    (a : (c : List Bool) → Fin (N c) → ℤ) (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (hselected : ∀ c i, selected (pair c (BinaryNatCode.encode i.val)) = (f c i).val)
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hreader : ∀ c i, reader (pair c (BinaryNatCode.encode i.val)) =
      residueBits ((a c i : ℤ) : ZMod (Nat.fromBitsLE (modulus c)))) :
    SpaceFunction (value A N W a f target modulus) :=
  evaluator_of_summand hN hm (summand_evaluator_space hA hW ht hr hs) a f hselected hpos hreader

end LeanCanny.Algebra.FixedWidthHeightBits
