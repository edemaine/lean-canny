/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignStatisticSpace
public import LeanCanny.Algebra.PseudoRemainderQuery

/-! # Descending principal-sign scans and the integer Tarski formula

This composition accepts a certified signed-principal-coefficient sign reader.
Instantiating that reader from original polynomial coefficients and retaining
computed actual degrees are separate obligations.
-/

@[expose] public section

namespace LeanCanny.Algebra.SignStatisticBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open PrincipalSubresultant

theorem descending_range {α : Type*} (a : ℕ → α) (d : ℕ) :
    (List.range (d + 1)).map (fun i => a (d - i)) = (List.range (d + 1)).reverse.map a := by
  rw [List.range_eq_range', List.reverse_range']
  simp only [Nat.zero_add, Nat.add_sub_cancel, List.map_map, Function.comp_def]
  rw [← List.range_eq_range']

def reverseQuery (degree : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNat.sub (pair (degree (pairFst q)) (pairSnd q)))

theorem reverseQuery_mem_FP {degree : List Bool → List Bool} (hd : degree ∈ FP) :
    reverseQuery degree ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hd) pairSnd_mem_FP) BinaryNat.sub_mem_FP)
  refine mem_FP_of_eq (g := reverseQuery degree) h ?_
  intro q
  simp only [reverseQuery, Function.comp_apply]

/-- Read indices in descending order without retaining a list of signs. -/
theorem descendingEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (degree : List Bool → List Bool) (hd : degree ∈ FP) (a : List Bool → ℕ → ℤ)
    (hsign : ∀ c i, f (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.tag (a c i)) :
    SpaceFunction (fun c => integerCode (permanencesMinusVariations
      ((List.range (Nat.fromBitsLE (degree c) + 1)).reverse.map (a c)))) := by
  let R := E.precompose (reverseQuery degree) (reverseQuery_mem_FP hd)
  let b := fun c i => SignType.sign (a c (Nat.fromBitsLE (degree c) - i))
  have hr : ∀ c i, (f ∘ reverseQuery degree) (pair c (BinaryNatCode.encode i)) =
      InfinitesimalSign.encode (b c i) := by
    intro c i
    simp only [Function.comp_apply, reverseQuery, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (hsign c _).trans (InfinitesimalSign.tag_eq_encode _)
  let Q := evaluator R (BinaryNat.succ ∘ degree) (mem_FP_comp hd BinaryNat.succ_mem_FP) b hr
  refine Q.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  congr 1
  rw [← descending_range]
  simpa only [List.map_map, Function.comp_def, b] using
    permanencesMinusVariations_map_sign ((List.range (Nat.fromBitsLE (degree c) + 1)).map
      (fun i => a c (Nat.fromBitsLE (degree c) - i)))

/-- Given the principal-sign reader, the scan returns the actual real-root
query. The head-degree writer here must encode the actual positive degree. -/
theorem tarskiEvaluator {r : List Bool → List Bool} (E : SpaceFunction r)
    (degree : List Bool → List Bool) (hd : degree ∈ FP)
    (p f : List Bool → ℤ[X]) (D : List Bool → ℕ)
    (hdegree : ∀ c, (p c).natDegree = Nat.fromBitsLE (degree c))
    (hpositive : ∀ c, 0 < Nat.fromBitsLE (degree c))
    (hD : ∀ c, (f c * (p c).derivative).natDegree ≤ D c)
    (hsign : ∀ c i, r (pair c (BinaryNatCode.encode i)) = InfinitesimalSign.tag
      (signedPsc (p c) (PseudoRemainder.seed (p c) (f c) (Nat.fromBitsLE (degree c)) (D c))
        (Nat.fromBitsLE (degree c))
        (PseudoRemainder.seed (p c) (f c) (Nat.fromBitsLE (degree c)) (D c)).natDegree i)) :
    SpaceFunction (fun c => integerCode (RootSignQueries.tarskiQuery
      ((p c).map (algebraMap ℤ ℝ)) ((f c).map (algebraMap ℤ ℝ)))) := by
  let Q := descendingEvaluator E degree hd _ hsign
  refine Q.congr (funext fun c => ?_)
  rw [RootSignQueries.tarskiQuery_pseudo_int (p c) (f c) _ (D c)
    (hdegree c) (hpositive c) (hD c)]
  rfl

end LeanCanny.Algebra.SignStatisticBits
