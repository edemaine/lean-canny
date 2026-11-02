/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PoweredPrefixProduct
/-! # Powered products preserve an independently stated semantic modulus -/
@[expose] public section
namespace LeanCanny.Algebra.PoweredPrefixProductModulus
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators

theorem value (count exponent pred : List Bool → ℕ) (task answer : List Bool → List Bool)
    (m : List Bool → ℕ) (hm : (fun q => pred q+1)=m) (q : List Bool)
    (a : ℕ → ZMod (m q)) (last : ZMod (m q))
    (ha : ∀ i<count q, answer (task (pair q (BinaryNatCode.encode i)))=residueBits (a i))
    (hlast : answer (task (pair q (BinaryNatCode.encode (count q))))=residueBits last) :
    (PoweredPrefixProduct.program count exponent pred task).value answer q =
      residueBits ((∏ i ∈ Finset.range (count q), a i)^exponent q * last) := by
  subst m
  exact PoweredPrefixProduct.value count exponent pred task answer q a last ha hlast

theorem partial_value (count exponent pred : List Bool → ℕ) (task answer : List Bool → List Bool)
    (m : List Bool → ℕ) (hm : (fun q => pred q+1)=m) (q : List Bool)
    (a : ℕ → ZMod (m q)) (last : ZMod (m q))
    (ha : ∀ i<count q, answer (task (pair q (BinaryNatCode.encode i)))=residueBits (a i))
    (hlast : answer (task (pair q (BinaryNatCode.encode (count q))))=residueBits last)
    (k : ℕ) (hk : k≤count q+1) :
    (PoweredPrefixProduct.program count exponent pred task).partialValue answer q k =
      residueBits (∏ i ∈ Finset.range k, if i<count q then a i^exponent q else last) := by
  subst m
  let b : ℕ → ZMod (pred q+1) := fun i => if i<count q then a i^exponent q else last
  have HB (i : ℕ) (hi : i<count q+1) :
      TransformedRecursiveProduct.mapped task (PoweredPrefixProduct.transform count exponent pred) answer
        (pair q (BinaryNatCode.encode i))=residueBits (b i) := by
    unfold TransformedRecursiveProduct.mapped
    by_cases h : i<count q
    · rw [ha i h, PoweredPrefixProduct.transform_packet, ite_eq_left h]
      simp only [b, ite_eq_left h]
    · have HI : i=count q := by omega
      subst i
      rw [hlast, PoweredPrefixProduct.transform_packet, ite_eq_right (Nat.lt_irrefl _), pow_one]
      simp only [b, Nat.lt_irrefl, ite_false]
  exact TransformedRecursiveProduct.partialValueWithModulus (fun q => count q+1)
    (fun q => BinaryNatCode.encode (pred q+1)) task (PoweredPrefixProduct.transform count exponent pred) answer
    (fun q => pred q+1) (funext fun r => Nat.fromBitsLE_bits _) q b (by omega) HB k hk

theorem orbit_length (count exponent pred : List Bool → ℕ) (task answer : List Bool → List Bool)
    (m : List Bool → ℕ) (hm : (fun q => pred q+1)=m) (q : List Bool) (hpos : m q≠0)
    (a : ℕ → ZMod (m q)) (last : ZMod (m q))
    (ha : ∀ i<count q, answer (task (pair q (BinaryNatCode.encode i)))=residueBits (a i))
    (hlast : answer (task (pair q (BinaryNatCode.encode (count q))))=residueBits last) (t : ℕ) :
    (RecursiveFold.encState (((PoweredPrefixProduct.program count exponent pred task).controller.reference answer)^[t]
      ((PoweredPrefixProduct.program count exponent pred task).initial q))).length ≤
      2*q.length+2*(Turing.MultiTapeTM.encNat (count q+1)).length+(m q).size+2 := by
  let : NeZero (m q) := ⟨hpos⟩
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [partial_value count exponent pred task answer m hm q a last ha hlast k hk]
  exact residueBits_length_le _ _

end LeanCanny.Algebra.PoweredPrefixProductModulus
