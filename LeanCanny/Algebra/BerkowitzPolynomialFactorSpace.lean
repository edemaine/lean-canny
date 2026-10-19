/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialFactor

/-!
# Space-certified polynomial factor coefficient selection

The requested degree accompanies the original layered-entry query. FP guards
select a coefficient of one, a negative diagonal coefficient, a negative
moment coefficient, or zero. Negation retains the query's modulus context.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Berkowitz
open Polynomial Matrix

def negative {F : ModularFamily} (a : ModularAccess F) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (a.modulus (pairFst (pairFst (pairFst z)))) (pairSnd z))

theorem negative_mem_FP {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) : negative a ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) ha.modulus
  have h := mem_FP_comp (mem_FP_pair hc pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq (g := negative a) h ?_
  intro z
  simp only [Function.comp_apply, negative]

theorem negative_pair {F : ModularFamily} (a : ModularAccess F) (p : List Bool)
    (x : ZMod (F.modulus (pairFst (pairFst p)))) : negative a (pair p (residueBits x)) = residueBits (-x) := by
  let : NeZero (F.modulus (pairFst (pairFst p))) := ⟨F.modulus_ne_zero (pairFst (pairFst p))⟩
  simp only [negative, pairFst_pair, pairSnd_pair, a.modulus_eq]
  exact ArithmeticBits.negate_residueBits _ x

def oneCoefficient {F : ModularFamily} (a : ModularAccess F) (p : List Bool) : List Bool :=
  if BinaryNat.normalize (pairSnd p) = [] then ArithmeticBits.one (a.modulus (pairFst (pairFst p))) else []

theorem oneCoefficient_mem_FP {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    oneCoefficient a ∈ FP := by
  have hk := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) ha.modulus
  have ho := mem_FP_comp hm ArithmeticBits.one_mem_FP
  have h := (stringEq_fppred hk (constFn_mem_FP [])).ite_mem_FP ho (constFn_mem_FP [])
  refine mem_FP_of_eq (g := oneCoefficient a) h ?_
  intro p
  simp only [Function.comp_apply, oneCoefficient]

theorem oneCoefficient_correct {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    oneCoefficient a p = residueBits ((1 : (ZMod (F.modulus (pairFst (pairFst p))))[X]).coeff
      (Nat.fromBitsLE (pairSnd p))) := by
  let : NeZero (F.modulus (pairFst (pairFst p))) := ⟨F.modulus_ne_zero (pairFst (pairFst p))⟩
  simp only [oneCoefficient, a.modulus_eq, ArithmeticBits.one_residueBits,
    BinaryNat.normalize_eq_bits, BinaryNat.bits_eq_nil_iff, Polynomial.coeff_one]
  split_ifs <;> simp [residueBits, BinaryNatCode.encode]

def diagonalInput {F : ModularFamily} (a : ModularAccess F) (p : List Bool) : List Bool :=
  attachDegree (pair (EntryAccess.diagonalInput a.dimension (pairFst p)) (pairSnd p))

theorem diagonalInput_mem_FP {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    diagonalInput a ∈ FP := by
  have hd := mem_FP_comp pairFst_mem_FP (EntryAccess.diagonalInput_mem_FP ha.dimension)
  have h := mem_FP_comp (mem_FP_pair hd pairSnd_mem_FP) attachDegree_mem_FP
  refine mem_FP_of_eq (g := diagonalInput a) h ?_
  intro p
  simp only [Function.comp_apply, diagonalInput]

def mode {F : ModularFamily} (a : ModularAccess F) (tag p : List Bool) : Bool :=
  decide (QueryBits.selector a.dimension (pairFst p) = tag)

theorem mode_mem_FP {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) (tag : List Bool) :
    (fun p => [mode a tag p]) ∈ FP :=
  (stringEq_fppred (mem_FP_comp pairFst_mem_FP (QueryBits.selector_mem_FP ha.dimension))
    (constFn_mem_FP tag)).flag_mem_FP

noncomputable def factorValue {F : ModularFamily} (a : ModularAccess F) (p : List Bool) : List Bool :=
  if QueryBits.selector a.dimension (pairFst p) = [true] then oneCoefficient a p
  else if QueryBits.selector a.dimension (pairFst p) = [false, true] then
    negative a (pair p (a.entry (diagonalInput a p)))
  else if QueryBits.selector a.dimension (pairFst p) = [true, true] then
    negative a (pair p ((momentFamily F).value p))
  else []

noncomputable def factorEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceFunction (factorValue a) := by
  have hn := negative_mem_FP a ha
  have ED := ((E.precompose (diagonalInput a) (diagonalInput_mem_FP a ha)).withInput).postcompose (negative a) hn
  have EM := ((momentEvaluator a ha E).withInput).postcompose (negative a) hn
  have EZ := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have EO := SpaceFunction.ofFP (oneCoefficient a) (oneCoefficient_mem_FP a ha)
  have RM := SpaceFunction.branch (mode a [true, true]) (mode_mem_FP a ha _) EM EZ
  have RD := SpaceFunction.branch (mode a [false, true]) (mode_mem_FP a ha _) ED RM
  have R := SpaceFunction.branch (mode a [true]) (mode_mem_FP a ha _) EO RD
  refine R.congr ?_
  funext p
  simp only [factorValue, mode, Function.comp_apply, decide_eq_true_eq]

def controlAccess {F : ModularFamily} (a : ModularAccess F) : FactorChild.Access where
  dimension := a.dimension
  modulus := a.modulus
  entry := fun _ => []

set_option backward.isDefEq.respectTransparency false in
theorem factorValue_correct {F : ModularFamily} (a : ModularAccess F) (q : List Bool)
    (s t d k D : ℕ) (hq : FactorChild.DecodedAt a.controlAccess q s t d k) :
    factorValue a (pair q (BinaryNatCode.encode D)) =
      residueBits ((FactorChild.value (F.matrix (pairFst q)) s t d k).coeff D) := by
  let : NeZero (F.modulus (pairFst q)) := ⟨F.modulus_ne_zero (pairFst q)⟩
  have hsel := FactorChild.selector_code a.controlAccess q (F.dimension (pairFst q)) s t d k
    (a.dimension_eq (pairFst q)) hq
  change QueryBits.selector a.dimension q = QueryBits.select (F.dimension (pairFst q)) s t d k at hsel
  have hstage : stage F q = s := BinaryNatCode.encode_injective ((stage_code a q).symm.trans hq.sourceLayer)
  have hexp : momentExponent F q = k - (d + 1) :=
    BinaryNatCode.encode_injective ((momentExponent_code a q).symm.trans
      (FactorChild.exponent_code a.controlAccess q s t d k hq))
  subst s
  by_cases hedge : stage F q + 1 = t
  · by_cases hs : stage F q < F.dimension (pairFst q)
    · by_cases hshift : k + 1 = d
      · have hm : QueryBits.selector a.dimension q = [true] := by
          rw [hsel]
          simp only [QueryBits.select, hedge, hs, hshift, ↓reduceIte]
        rw [factorValue, pairFst_pair, ite_eq_left hm, oneCoefficient_correct]
        rw [pairFst_pair]
        simp only [pairSnd_pair, QueryBits.code_value, FactorChild.value, hedge, hs,
          ↓reduceIte, ↓reduceDIte, coefficientKernel_cases, hshift]
      · by_cases hdiag : k = d
        · have hm : QueryBits.selector a.dimension q = [false, true] := by
            rw [hsel]
            exact (QueryBits.select_diagonal_iff _ _ _ _ _).mpr ⟨hedge, hs, hdiag⟩
          have hnot : QueryBits.selector a.dimension q ≠ [true] := by rw [hm]; decide
          have he : a.entry (diagonalInput a (pair q (BinaryNatCode.encode D))) =
              residueBits ((F.matrix (pairFst q) ⟨stage F q, hs⟩ ⟨stage F q, hs⟩).coeff D) := by
            simp only [diagonalInput, pairFst_pair, pairSnd_pair,
              EntryAccess.diagonalInput_code a.dimension q (stage F q) hq.sourceLayer, attachDegree]
            exact a.entry_eq (pairFst q) ⟨stage F q, hs⟩ ⟨stage F q, hs⟩ D
          rw [factorValue, pairFst_pair, ite_eq_right hnot, ite_eq_left hm, he]
          simp only [negative, pairFst_pair, pairSnd_pair, a.modulus_eq]
          rw [ArithmeticBits.negate_residueBits]
          simp [FactorChild.value, hedge, hs, coefficientKernel_cases, hdiag, principalBlock]
        · by_cases hmoment : d < k ∧ k ≤ F.dimension (pairFst q) - stage F q - 1
          · have hm : QueryBits.selector a.dimension q = [true, true] := by
              rw [hsel]
              exact (QueryBits.select_moment_iff _ _ _ _ _).mpr ⟨hedge, hs, hmoment.1, hmoment.2⟩
            have hnot1 : QueryBits.selector a.dimension q ≠ [true] := by rw [hm]; decide
            have hnot2 : QueryBits.selector a.dimension q ≠ [false, true] := by rw [hm]; decide
            have hsp : stage F (pairFst (pair q (BinaryNatCode.encode D))) <
                F.dimension (pairFst (pairFst (pair q (BinaryNatCode.encode D)))) := by
              simpa only [pairFst_pair] using hs
            rw [factorValue, pairFst_pair, ite_eq_right hnot1, ite_eq_right hnot2, ite_eq_left hm,
              moment_value_eq _ hsp]
            revert hsp
            rw [pairFst_pair]
            intro hsp
            simp only [negative, pairFst_pair, pairSnd_pair, a.modulus_eq]
            rw [ArithmeticBits.negate_residueBits]
            simp only [QueryBits.code_value, hexp, FactorChild.value,
              hedge, hs, ↓reduceIte, ↓reduceDIte, coefficientKernel_cases, hshift, hdiag, hmoment,
              and_self, Polynomial.coeff_neg]
          · have hm : QueryBits.selector a.dimension q = [] := by
              rw [hsel]
              simp only [QueryBits.select, hedge, hs, hshift, hdiag, ↓reduceIte]
              split_ifs <;> simp_all
            simp [factorValue, hm, FactorChild.value, hedge, hs, coefficientKernel_cases, hshift, hdiag, hmoment,
              residueBits, BinaryNatCode.encode]
    · have hm : QueryBits.selector a.dimension q = [] := by rw [hsel]; simp only [QueryBits.select, hedge, hs, ↓reduceIte]
      simp [factorValue, hm, FactorChild.value, hedge, hs, residueBits, BinaryNatCode.encode]
  · have hm : QueryBits.selector a.dimension q = [] := by rw [hsel]; simp only [QueryBits.select, hedge, ↓reduceIte]
    simp [factorValue, hm, FactorChild.value, hedge, residueBits, BinaryNatCode.encode]

theorem factorValue_packet {F : ModularFamily} (a : ModularAccess F) (c : List Bool)
    (i j : Fin ((F.dimension c + 1) * (F.dimension c + 1))) (D : ℕ) :
    factorValue a (pair (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
      (BinaryNatCode.encode D)) = residueBits ((powerMatrix (F.matrix c) i j).coeff D) := by
  have hq := FactorChild.decoded_packet a.controlAccess c (F.dimension c) i.val j.val (a.dimension_eq c)
  have h := factorValue_correct a _ _ _ _ _ D hq
  rw [pairFst_pair] at h
  change factorValue a _ = residueBits
    ((FactorChild.value (F.matrix c) i.divNat.val j.divNat.val i.modNat.val j.modNat.val).coeff D) at h
  rw [FactorChild.value_eq_powerMatrix] at h
  exact h

end LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess
