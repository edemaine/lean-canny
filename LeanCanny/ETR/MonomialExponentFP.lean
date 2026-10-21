/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderFP
public import LeanCanny.ETR.MonomialExponentAtom
public import LeanCanny.ETR.TermView

/-!
# Uniform FP access to indexed source exponents

The term, monomial index, and variable index are FP input fields. Both indices
stay binary. The traversal counts selected variable leaves, retains the original
input, and has a polynomial bound for the complete stack and accumulator.
Malformed terms use the validated zero expression.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding

def exponentRead (term index varIndex : List Bool → List Bool) : List Bool → List Bool :=
  evaluate (exponentAtom varIndex) (TermView.normalize ∘ term) index (fun _ => [])

theorem exponentRead_correct (term index varIndex : List Bool → List Bool) (c : List Bool) :
    exponentRead term index varIndex c = BinaryNatCode.encode
      ((TermView.term (term c)).monomialExponent (Nat.fromBitsLE (index c)) (Nat.fromBitsLE (varIndex c))) := by
  have he := evaluate_eq (R := fun _ => Multiplicative ℕ) (fun _ v => BinaryNatCode.encode v.toAdd)
    (fun _ _ => Multiplicative.ofAdd 0)
    (fun c j => Multiplicative.ofAdd (if Nat.fromBitsLE (varIndex c) = j then 1 else 0))
    (fun c => TermView.term (term c)) (TermView.normalize ∘ term) index (fun _ => []) (exponentAtom varIndex)
    (fun c => TermView.normalize_eq_term (term c)) (fun _ => rfl)
    (exponentAtom_const varIndex) (exponentAtom_var varIndex) c
  simpa only [exponentRead, fold_exponent] using he

theorem exponentRead_mem_FP {term index varIndex : List Bool → List Bool}
    (ht : term ∈ FP) (hi : index ∈ FP) (hv : varIndex ∈ FP) : exponentRead term index varIndex ∈ FP := by
  have hn := mem_FP_comp ht TermView.normalize_mem_FP
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hn
  have H := reader_mem_FP (R := fun _ => Multiplicative ℕ) (fun _ v => BinaryNatCode.encode v.toAdd)
    (fun _ _ => Multiplicative.ofAdd 0)
    (fun c j => Multiplicative.ofAdd (if Nat.fromBitsLE (varIndex c) = j then 1 else 0))
    (fun c => TermView.term (term c)) (TermView.normalize ∘ term) index (fun _ => []) (exponentAtom varIndex)
    (fun c => TermView.normalize_eq_term (term c)) (fun _ => rfl)
    (exponentAtom_const varIndex) (exponentAtom_var varIndex) hn hi (constFn_mem_FP []) (exponentAtom_mem_FP hv) p (by
      intro c k hk
      have hvalue := exponent_iterate_value_le (Nat.fromBitsLE (varIndex c))
        (⟨[⟨TermView.term (term c), Nat.fromBitsLE (index c)⟩], 1⟩ : State (Multiplicative ℕ)) k
      have hsmall : (((step (fun _ => Multiplicative.ofAdd 0)
          (fun j => Multiplicative.ofAdd (if Nat.fromBitsLE (varIndex c) = j then 1 else 0)))^[k])
            ⟨[⟨TermView.term (term c), Nat.fromBitsLE (index c)⟩], 1⟩).value.toAdd ≤ k := by simpa using hvalue
      rw [BinaryNatCode.length_encode]
      exact (Nat.size_le.mpr (hsmall.trans_lt (hk.trans_lt Nat.lt_two_pow_self))).trans (hp c))
  refine mem_FP_of_eq (g := exponentRead term index varIndex) H ?_
  intro c
  rw [exponentRead_correct, fold_exponent]

def sourceExponent (source : List Bool → List Bool) : List Bool → List Bool :=
  exponentRead (source ∘ pairFst) (pairFst ∘ pairSnd) (pairSnd ∘ pairSnd)

theorem sourceExponent_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : sourceExponent source ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP hs
  have hr := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  exact exponentRead_mem_FP ht hr hi

theorem sourceExponent_packet (source : List Bool → List Bool) (c : List Bool) (r i : ℕ) :
    sourceExponent source (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) =
      BinaryNatCode.encode ((TermView.term (source c)).monomialExponent r i) := by
  rw [sourceExponent, exponentRead_correct]
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.ETR.MonomialReader
