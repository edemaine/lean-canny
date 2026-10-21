/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DerivativeProductSpace
public import LeanCanny.Algebra.PseudoRemainderSpace

/-! # Integer-style Tarski seeds from the two original coefficient routines

The derivative product, reduction matrix, and fixed even power are supplied
internally. The reduction bound is the sum of the original degree bounds.
Formal bounds are preserved under modular degree drops.
-/

@[expose] public section

namespace LeanCanny.Algebra.TarskiSeedBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

structure Family where
  source : DerivativeProductBits.Family
  degree : List Bool → ℕ
  queryBound : List Bool → ℕ
  selected : (c : List Bool) → Fin (degree c + queryBound c + 1)
  degree_pos : ∀ c, 0 < degree c
  head_degree : ∀ c, (source.head c).natDegree ≤ degree c
  query_degree : ∀ c, (source.query c).natDegree ≤ queryBound c

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits ((PseudoRemainder.seed (F.source.head c) (F.source.query c)
    (F.degree c) (F.degree c + F.queryBound c)).coeff (F.selected c).val)

noncomputable def Family.reduction (F : Family) : PseudoRemainderBits.Family where
  modulus := F.source.modulus
  head := F.source.head
  input c := F.source.query c * (F.source.head c).derivative
  degree := F.degree
  bound c := F.degree c + F.queryBound c
  selected := F.selected
  modulus_ne_zero := F.source.modulus_ne_zero
  degree_pos := F.degree_pos
  degree_le c := Nat.le_add_right _ _
  head_degree := F.head_degree
  input_degree c := by
    have hp := ((natDegree_derivative_le (F.source.head c)).trans (Nat.sub_le _ _)).trans (F.head_degree c)
    exact natDegree_mul_le.trans (by have := F.query_degree c; omega)

theorem Family.reduction_value (F : Family) (c : List Bool) : F.reduction.value c = F.value c := rfl

structure Access (F : Family) where
  source : DerivativeProductBits.Access F.source
  degree : List Bool → List Bool
  queryBound : List Bool → List Bool
  selected : List Bool → List Bool
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)
  queryBound_eq : ∀ c, queryBound c = BinaryNatCode.encode (F.queryBound c)
  selected_eq : ∀ c, selected c = BinaryNatCode.encode (F.selected c).val

structure Access.ControlsPolyTime {F : Family} (a : Access F) : Prop where
  modulus : a.source.modulus ∈ FP
  degree : a.degree ∈ FP
  queryBound : a.queryBound ∈ FP
  selected : a.selected ∈ FP

namespace Access

def bound {F : Family} (a : Access F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.degree c) (a.queryBound c))

theorem bound_mem_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : bound a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.degree ha.queryBound) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := bound a) h ?_
  intro c
  simp only [bound, Function.comp_apply]

theorem bound_code {F : Family} (a : Access F) (c : List Bool) :
    bound a c = BinaryNatCode.encode (F.degree c + F.queryBound c) := by
  simp only [bound, a.degree_eq, a.queryBound_eq, BinaryNat.add_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits]

set_option backward.isDefEq.respectTransparency false in
noncomputable def reduction {F : Family} (a : Access F) : PseudoRemainderBits.DataAccess F.reduction where
  source := {
    headDegree := a.degree
    modulus := a.source.modulus
    coefficient := a.source.headCoefficient }
  bound := bound a
  selected := a.selected
  inputCoefficient := F.source.value
  degree_eq := a.degree_eq
  modulus_eq := a.source.modulus_eq
  bound_eq := bound_code a
  selected_eq := a.selected_eq
  head_eq := a.source.head_eq
  input_eq c k := F.source.value_packet c k

theorem evaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.source.headCoefficient) (Q : SpaceFunction a.source.queryCoefficient) :
    SpaceFunction F.value := by
  have hc : a.reduction.ControlsPolyTime := by
    constructor
    · simpa only [reduction] using ha.degree
    · simpa only [reduction] using ha.modulus
    · simpa only [reduction] using bound_mem_FP a ha
    · simpa only [reduction] using ha.selected
  let G := DerivativeProductBits.Access.evaluator a.source ha.modulus P Q
  let E := PseudoRemainderBits.DataAccess.evaluator a.reduction hc P G
  exact E.congr (funext F.reduction_value)

end Access
end LeanCanny.Algebra.TarskiSeedBits
