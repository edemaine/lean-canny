/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.MonotoneGateSourceBounds
public import LeanCanny.ETR.EquationSize
/-! # One native original-input degree budget for the gate source -/
@[expose] public section
namespace LeanCanny.Encoding.MonotoneGateSource
open LeanCanny.Computation ETR
open scoped BigOperators

def atomMass (F : Family) (c : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (F.count c), (F.atom (pair c (List.replicate i true))).toData.size

theorem atomMass_unary (F : Family) (hF : Access F) : UnaryFn (atomMass F) := by
  have HM : UnaryFn (fun q => (F.atom q).toData.size) :=
    (UnaryFn.length hF.atom).of_eq (fun q => LeanCanny.Data.length_toBits (F.atom q).toData)
  exact hF.count.sum HM

theorem atom_degree_mass (F : Family) (c : List Bool) (i : ℕ) (hi : i < F.count c) :
    (F.atom (pair c (List.replicate i true))).degreeBound≤atomMass F c := by
  apply (F.atom (pair c (List.replicate i true))).degreeBound_le_dataSize.trans
  unfold atomMass
  exact Finset.single_le_sum (f := fun j => (F.atom (pair c (List.replicate j true))).toData.size)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

def degreeBudget (F : Family) (c : List Bool) : ℕ := 2*max (atomMass F c) 2

theorem degreeBudget_unary (F : Family) (hF : Access F) : UnaryFn (degreeBudget F) :=
  (UnaryFn.const 2).mul ((atomMass_unary F hF).max (UnaryFn.const 2))

theorem polynomial_degree_budget (F : Family) (c : List Bool) :
    (polynomial F c).degreeBound≤degreeBudget F c :=
  polynomial_degree F c (atomMass F c) (atom_degree_mass F c)

theorem polynomial_totalDegree_budget (F : Family) (c : List Bool) :
    (polynomial F c).toPolynomial.totalDegree≤degreeBudget F c :=
  (polynomial F c).totalDegree_toPolynomial_le.trans (polynomial_degree_budget F c)

end LeanCanny.Encoding.MonotoneGateSource
