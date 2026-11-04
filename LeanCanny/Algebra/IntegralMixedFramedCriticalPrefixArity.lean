/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLayout
/-! # Exact physical arity growth across a critical interval of headers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedCommandHeaderBits (lookup)
open scoped BigOperators

theorem prefixArity_critical_interval (P :Parameters) (T :Tables) (key :List Bool)
    (a b :ℕ) (hab :a≤b)
    (hc :∀j,a≤j→j<b→(lookup (T.commands (pairFst key)) j).context=1):
    prefixArity P T (pair key (List.replicate b true))=
      prefixArity P T (pair key (List.replicate a true))+
        (2*P.ambient (pairFst key)+4)*(b-a):=by
  simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate]
  conv_lhs=>rw [show b=a+(b-a) by omega,Finset.sum_range_add]
  congr 1
  calc
    (∑j∈Finset.range (b-a),span P T (pair key (List.replicate (a+j) true)))=
        ∑_j∈Finset.range (b-a),(2*P.ambient (pairFst key)+4):=by
      apply Finset.sum_congr rfl
      intro j hj
      have HJ :j<b-a:=Finset.mem_range.mp hj
      simp only [span,pairFst_pair,pairSnd_pair,List.length_replicate,
        hc (a+j) (by omega) (by omega),ite_true,block]
      omega
    _=(2*P.ambient (pairFst key)+4)*(b-a):=by simp [Nat.mul_comm]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
