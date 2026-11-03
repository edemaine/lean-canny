/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardSpace
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # Original-root degree and mass for sparse physical correlation tests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedStepHeight (familyHeight FamilyInputs)
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

def degree (P : Parameters) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :=
  max (scalarPower P key stage q) (physicalPower P key stage q)
def mass (P : Parameters) (L F C : List Bool→ℕ) (key : List Bool→List Bool) (q : List Bool) :=familyHeight P L F C (key q)+1

theorem degree_binary (P : Parameters) (a : Access P) (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (hk : key∈FP) (hj : UnaryFn stage) : BinaryFn (degree P key stage) := by
  have HS:=scalarPower_binary P a key stage hk hj
  have HP:=physicalPower_binary P a key stage hk hj
  exact (BinaryFn.ite (HS.le HP) HP HS).of_eq (fun q=>by simp only [degree,max_def])
theorem mass_binary (P : Parameters) (a : Access P) (L F C : List Bool→ℕ) (key : List Bool→List Bool)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) (hk : key∈FP): BinaryFn (mass P L F C key) := by
  have HG : BinaryFn (fun q=>familyHeight P L F C (key q)) := (IntegralMixedFramedStepHeight.familyHeight_binary P a hL hF hC).comp hk
  exact HG.add (BinaryFn.const 1)

private theorem monomial_degree (A selected power : List Bool→ℕ) (a : List Bool→ℤ) (q : List Bool) :
    (FixedWidthMonomialBits.polynomial A selected power a q).totalDegree≤power q := by
  unfold FixedWidthMonomialBits.polynomial
  split_ifs
  · exact (totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp only [totalDegree_zero,Nat.zero_le]
private theorem monomial_mass (A selected power : List Bool→ℕ) (a : List Bool→ℤ) (q : List Bool) :
    MvMass.mass (FixedWidthMonomialBits.polynomial A selected power a q)≤(a q).natAbs := by
  unfold FixedWidthMonomialBits.polynomial
  split_ifs
  · exact (MvMass.monomial _ _).le
  · simp only [MvMass.zero,Nat.zero_le]

theorem polynomial_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool) :
    (polynomial P D H T key stage q).totalDegree≤degree P key stage q := by
  unfold polynomial
  split_ifs
  · exact (totalDegree_sub _ _).trans (max_le_max (monomial_degree _ _ _ _ _) (monomial_degree _ _ _ _ _))
  · exact Nat.zero_le _

theorem polynomial_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (key : List Bool→List Bool) (stage L F C : List Bool→ℕ)
    (hs : FamilyInputs P D L F C) (q : List Bool) :
    MvMass.mass (polynomial P D H T key stage q)≤2^mass P L F C key q := by
  have HD : (denominator P D H key stage q).natAbs≤2^familyHeight P L F C (key q) := by
    unfold denominator atKey
    split_ifs with hi
    · exact (IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs (key q)).denominator _
    · exact Nat.zero_le _
  unfold polynomial
  split_ifs
  · have HB:=MvMass.sub_le
      (FixedWidthMonomialBits.polynomial (count P T key) (scalar P T key stage) (scalarPower P key stage) (fun _=>1) q)
      (FixedWidthMonomialBits.polynomial (count P T key) (physical P T key stage) (physicalPower P key stage) (denominator P D H key stage) q)
    have HM:=HB.trans (Nat.add_le_add (monomial_mass _ _ _ _ _) (monomial_mass _ _ _ _ _))
    change MvMass.mass (rawPolynomial P D H T key stage q)≤_ at HM
    have HP : 1≤2^familyHeight P L F C (key q):=Nat.one_le_two_pow
    change _≤2^(familyHeight P L F C (key q)+1)
    rw [pow_succ]
    exact HM.trans (by simp only [Int.natAbs_one]; omega)
  · exact Nat.zero_le _
end LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
