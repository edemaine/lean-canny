/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiAccess
public import LeanCanny.Algebra.FixedWidthTarskiMass
/-! # Original degree/mass ceilings for zero-specialized principal tests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedZeroTarskiBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical BigOperators

private theorem ternary_mass {σ : Type*} (p : Polynomial (MvPolynomial σ ℤ)) (M : ℕ)
    (hd : p.natDegree≤1) (hm : ∀i,MvMass.mass (p.coeff i)≤2^M) (e : Fin 3) (i : ℕ) :
    MvMass.mass ((p^e.val).coeff i)≤2^(2*M+2) :=by
  by_cases h0 :e.val=0
  · rw [h0,pow_zero,Polynomial.coeff_one]
    split_ifs
    · simp only [MvMass.one];exact Nat.one_le_two_pow
    · simp
  · by_cases h1 :e.val=1
    · rw [h1,pow_one]
      exact (hm i).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · have h2 :e.val=2:=by have H:=e.isLt;omega
      rw [h2]
      by_cases hi :i≤2
      · rw [pow_two,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply (MvMass.sum_le _ _).trans
        calc
          _≤∑_k∈Finset.range (i+1),2^(2*M):=Finset.sum_le_sum (fun k _=>
            (MvMass.mul_le _ _).trans ((Nat.mul_le_mul (hm k) (hm (i-k))).trans_eq (by rw [←pow_add,two_mul])))
          _=(i+1)*2^(2*M):=by simp
          _≤4*2^(2*M):=Nat.mul_le_mul_right _ (by omega)
          _=_:=by rw [pow_add];ring
      · have HD :(p^2).natDegree≤2:=Polynomial.natDegree_pow_le.trans (by omega)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (HD.trans_lt (by omega)),MvMass.zero]
        exact Nat.zero_le _

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e selected : List Bool→ℕ)

noncomputable def headHeight :=IntegralMixedFramedCoordinatePackedBits.headMassBound P D H L F C parent e
noncomputable def queryHeight (c : List Bool) :=2*(2*IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)+1)+2
noncomputable def principalHeight (c : List Bool) :=(arity P D H terminal c+2)*width P D H L F C hs parent terminal d e selected c+
  FixedWidthTarskiMass.principalMass (degree d c) (seedDegree d c) (inputBound d c) (d c) 2
    (headHeight P D H L F C parent e c) (queryHeight P D H L F C terminal c)

include hs in
theorem head_coefficient_mass (hF :∀root,1≤F root)
    (hf :∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key) (c : List Bool) (y : ℕ) :
    MvMass.mass ((head P D H parent terminal d e c).coeff y)≤2^headHeight P D H L F C parent e c :=
  (FixedWidthBivariateZeroLiftBits.mass _ _ c y).trans
    (IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_mass P D H L F C hs hF hf parent terminal d e c y)

theorem query_coefficient_mass (power : List Bool→Fin 3) (negative : Bool) (c : List Bool) (y : ℕ) :
    MvMass.mass ((query P D H L F C hs terminal selected power negative c).coeff y)≤2^queryHeight P D H L F C terminal c :=by
  apply ternary_mass _ _ (baseQuery_outer_degree P D H L F C hs terminal selected negative c) _ (power c) y
  intro i
  exact (FixedWidthBivariateZeroLiftBits.epsilon_mass _ _ c i).trans
    (IntegralMixedFramedWindowQuery.coefficient_mass P D H L F C hs terminal selected negative c i)

theorem principal_mass (hF :∀root,1≤F root)
    (hf :∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : List Bool→Fin 3) (negative : Bool) (c : List Bool) (j : ℕ) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial (family P D H L F C hs parent terminal d e selected power negative) c j)≤
      2^principalHeight P D H L F C hs parent terminal d e selected c :=by
  let MF:=family P D H L F C hs parent terminal d e selected power negative
  have HD :(MF.head c).natDegree≤d c:=head_outer_degree P D H parent terminal d e c
  have HQ :(MF.query c).natDegree≤2:=query_outer_degree P D H L F C hs terminal selected power negative c
  have HP :∀i,MvMass.mass ((MF.head c).coeff i)≤2^headHeight P D H L F C parent e c:=head_coefficient_mass P D H L F C hs parent terminal d e hF hf c
  have HQQ :∀i,MvMass.mass ((MF.query c).coeff i)≤2^queryHeight P D H L F C terminal c:=query_coefficient_mass P D H L F C hs terminal selected power negative c
  have Hdeg :=principal_degree P D H L F C hs parent terminal d e selected power negative c j
  have HW :wholeBound P D H L F C hs parent terminal d e selected c<2^MF.width c:=Nat.lt_size_self _
  exact FixedWidthTarskiMass.principal_mass MF c j (d c) 2
    (headHeight P D H L F C parent e c) (queryHeight P D H L F C terminal c)
    (wholeBound P D H L F C hs parent terminal d e selected c) HD HQ HP HQQ Hdeg HW

theorem principalHeight_binary (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn selected) :
    BinaryFn (principalHeight P D H L F C hs parent terminal d e selected) :=by
  have HD:=degree_binary d hd
  have HH:=IntegralMixedFramedCoordinatePackedBits.headMassBound_binary P a D H L F C hL hF hC I parent hp e he
  have HC :BinaryFn (fun c=>IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)):=
    (IntegralMixedFramedBankTermBits.coordinateMass_binary P a D H hL hF hC).comp ht
  have HQ:=(BinaryFn.const 2).mul (((BinaryFn.const 2).mul HC).add (BinaryFn.const 1))
  have HQuery:=(HQ.add (BinaryFn.const 2))
  have HM:=FixedWidthTarskiMass.principalMass_binary HD (HD.sub (BinaryFn.const 1)) (HD.add (BinaryFn.const 2)) hd (BinaryFn.const 2) HH HQuery
  have HA :UnaryFn (arity P D H terminal):=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  exact ((BinaryFn.ofUnary (HA.add (UnaryFn.const 2))).mul
    (BinaryFn.ofUnary (width_unary P D H L F C hs parent terminal d e selected a hp ht hd he hi))).add HM

end LeanCanny.Algebra.IntegralMixedFramedZeroTarskiBits
