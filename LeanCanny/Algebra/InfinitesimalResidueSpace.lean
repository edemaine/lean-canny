/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSignSpace
public import LeanCanny.Algebra.IntegerSignumSpace

/-!
# Infinitesimal signs from coefficient residues

The residue routine receives `pair (pair context coefficientIndex) (m-1)`.
FP binary degree and coefficient-bit-budget writers, with their correctness
contracts, give a full sign evaluator for a sufficiently small positive
parameter. Neither the polynomial nor a complete coefficient is stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalSign
open Complexity
open Polynomial
open LeanCanny.Computation

noncomputable def evaluatorOfResidues {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (degree budget : List Bool → List Bool) (hd : degree ∈ FP) (hb : budget ∈ FP)
    (p : List Bool → ℤ[X]) (hdegree : ∀ c, (p c).natDegree ≤ Nat.fromBitsLE (degree c))
    (hbudget : ∀ q, ((p (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))).natAbs.size ≤
      Nat.fromBitsLE (budget q))
    (hres : ∀ q (m : ℕ), 0 < m →
      rho (pair q (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode
        ((((p (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))) : ZMod m).val)) :
    SpaceFunction (fun c => tag (p c).trailingCoeff) := by
  let a := fun q => (p (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))
  have E := IntegerSignumBits.evaluator R budget hb a hbudget hres
  refine evaluator E degree hd p hdegree ?_
  intro c i
  simp only [a, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, tag]

end LeanCanny.Algebra.InfinitesimalSign
