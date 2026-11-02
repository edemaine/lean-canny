/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankProducts
/-! # Streamed products are the literal actual bank cofactors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankProductBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankDenominatorBits (count state)
open scoped Classical BigOperators

theorem masked_product {m : ℕ} (f : Fin m → ℤ) (i : Fin m) :
    (∏ j : Fin m,if j.val=i.val then 1 else f j)=CommonIntegerDenominator.denominator (Finset.univ.erase i) f := by
  have HE : (Finset.univ.erase i : Finset (Fin m))=Finset.univ.filter (fun j => j≠i) := by
    ext j
    simp only [Finset.mem_erase,Finset.mem_univ,true_and,Finset.mem_filter,and_true]
  unfold CommonIntegerDenominator.denominator
  rw [HE,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i
  · subst j
    simp only [ite_true,ne_eq,not_true_eq_false,ite_false]
  · have HJ : j.val≠i.val := fun h => hj (Fin.ext h)
    rw [ite_eq_right HJ,ite_eq_left hj]

theorem integer_cofactor (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) (i : Fin (count P D H q)) (hi : skip q=i.val) :
    integer P D H skip q=CommonIntegerDenominator.denominator (Finset.univ.erase i) (state P D H q).bank.denominator := by
  exact (integer_fin P D H skip q).trans
    ((congrArg (fun k : ℕ => ∏ j : Fin (count P D H q), if j.val=k then 1 else (state P D H q).bank.denominator j) hi).trans
      (masked_product _ i))

theorem common_split (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (skip : List Bool → ℕ) (q : List Bool) (i : Fin (count P D H q)) (hi : skip q=i.val) :
    IntegralMixedHistory.commonDenominator (state P D H q)=
      (state P D H q).bank.denominator i*integer P D H skip q := by
  rw [integer_cofactor P D H skip q i hi]
  exact CommonIntegerDenominator.denominator_split Finset.univ _ i (Finset.mem_univ _)

end LeanCanny.Algebra.IntegralMixedFramedBankProductBits
