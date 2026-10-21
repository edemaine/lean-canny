/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Computation.BoundedFoldTidy
public import LeanCanny.Computation.SpaceFunctionTidy

/-! # Modular sums using tidy space composition

The summand need only be polynomial-space computable. The same binary fields,
canonical residues, and sum correctness theorem as the legacy implementation
are retained, while the new composition carries no controller or child clock.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularSum

open Complexity LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
open scoped BigOperators

theorem update_computable {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolySpace f encBits encBits)
    (modulus : List Bool → List Bool) (hm : modulus ∈ FP) :
    ComputableTidilyInPolySpace (update modulus f) encBits encBits := by
  have hfinish :=
    (TidyFP.of_mem_FP (finish_mem_FP hm)).comp
      (TidyFP.pair (ComputableTidilyInPolyTime.fst encBits encBits)
        (ComputableTidilyInPolyTime.snd encBits encBits))
  have h := (ComputableTidilyInPolySpace.of_polyTime hfinish).comp
    (ComputableTidilyInPolySpace.id'.prod
      (hf.comp (ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP query_mem_FP))))
  exact h.congr fun p => by simp only [update, Function.comp_apply]

theorem computable {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolySpace f encBits encBits)
    (count modulus : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hvalue : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    ComputableTidilyInPolySpace
      (fun c => residueBits (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i))
      encBits encBits := by
  let p := Classical.choose (Cobham.output_length_poly_of_mem_FP hm)
  have hp : ∀ c, (modulus c).length ≤ p.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hm)
  have hstate : ∀ c k, k ≤ Nat.fromBitsLE (count c) →
      (BoundedFold.fold (update modulus f) (fun _ => []) c k).length ≤ p.eval c.length := by
    intro c k hk
    let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨(hpos c).ne'⟩
    rw [fold_eq_sum modulus f c _ (a c) (hpos c) (hvalue c) k hk,
      residueBits, BinaryNatCode.length_encode]
    apply (Nat.size_le.mpr ?_).trans (hp c)
    exact (ZMod.val_lt (∑ i ∈ Finset.range k, a c i)).trans
      (Nat.fromBitsLE_lt_pow_length (modulus c))
  have h := BoundedFold.computable (update_computable hf modulus hm) count (fun _ => [])
    hc (constFn_mem_FP []) p hstate
  exact h.congr fun c => fold_eq_sum modulus f c _ (a c) (hpos c) (hvalue c) _ le_rfl

end LeanCanny.Algebra.ModularSum
