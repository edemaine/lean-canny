/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalAccess
public import LeanCanny.Algebra.FixedWidthTarskiMass
/-! # Original-only mass for full relative-factor interval principals -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical BigOperators

private theorem square_coefficient_mass {σ : Type*} (q : Polynomial (MvPolynomial σ ℤ)) (H : ℕ)
    (hd : q.natDegree≤1) (hM : ∀ i,MvMass.mass (q.coeff i)≤2^H) (i : ℕ) :
    MvMass.mass ((q^2).coeff i)≤2^(2*H+2) :=by
  by_cases hi : i≤2
  · rw [pow_two,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply (MvMass.sum_le _ _).trans
    calc
      _≤∑_k∈Finset.range (i+1),2^(2*H):=Finset.sum_le_sum (fun k _=>
        (MvMass.mul_le _ _).trans ((Nat.mul_le_mul (hM k) (hM (i-k))).trans_eq
          (by rw [←pow_add,two_mul])))
      _=(i+1)*2^(2*H):=by simp
      _≤4*2^(2*H):=Nat.mul_le_mul_right _ (by omega)
      _=_:=by rw [pow_add];ring
  · have HD : (q^2).natDegree≤2:=Polynomial.natDegree_pow_le.trans (by omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (HD.trans_lt (by omega)),MvMass.zero]
    exact Nat.zero_le _

private theorem ternary_coefficient_mass {σ : Type*} (q : Polynomial (MvPolynomial σ ℤ)) (H : ℕ)
    (hd : q.natDegree≤1) (hM : ∀ i,MvMass.mass (q.coeff i)≤2^H) (e : Fin 3) (i : ℕ) :
    MvMass.mass ((q^e.val).coeff i)≤2^(2*H+2) :=by
  by_cases h0 : e.val=0
  · rw [h0,pow_zero,Polynomial.coeff_one]
    split_ifs
    · simp only [MvMass.one]
      exact Nat.one_le_two_pow
    · simp
  · by_cases h1 : e.val=1
    · rw [h1,pow_one]
      exact (hM i).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · have h2 : e.val=2:=by have HH:=e.isLt;omega
      rw [h2]
      exact square_coefficient_mass q H hd hM i

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d selected : List Bool→ℕ)

noncomputable def headHeight :=IntegralMixedFramedFullCutHead.headMass P D H parent L F C
noncomputable def queryHeight (c : List Bool) :=2*(2*IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)+1)+2
noncomputable def principalHeight (c : List Bool) :=(1+(arity P D H terminal c+1))*
  width P D H L F C hs parent terminal d selected c+FixedWidthTarskiMass.principalMass
    (degree d c) (seedDegree d c) (inputBound d c) (d c) 2
    (headHeight P D H L F C parent c) (queryHeight P D H L F C terminal c)

include hs in
theorem head_coefficient_mass (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (c : List Bool) (y : ℕ) :
    MvMass.mass ((head P D H parent terminal d c).coeff y)≤
      2^headHeight P D H L F C parent c :=
  (FixedWidthBivariateParameterPairBits.mass true _ _ c y).trans
    (IntegralMixedFramedFullCutTerminalHead.coefficient_mass P D H parent terminal d L F C hs hF hf c y)

theorem query_coefficient_mass (power : List Bool→Fin 3) (negative : Bool) (c : List Bool) (y : ℕ) :
    MvMass.mass ((query P D H L F C hs terminal selected power negative c).coeff y)≤
      2^queryHeight P D H L F C terminal c :=by
  have HD : (baseQuery P D H L F C hs terminal selected negative c).natDegree≤1 :=
    Polynomial.natDegree_map_le.trans (RationalMonomialWindowQuery.degree _ negative c)
  apply ternary_coefficient_mass _ _ HD _ (power c) y
  intro i
  exact (FixedWidthBivariateParameterPairBits.mass false _ _ c i).trans
    (IntegralMixedFramedWindowQuery.coefficient_mass P D H L F C hs terminal selected negative c i)

theorem principal_mass (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (power : List Bool→Fin 3) (negativeEpsilon : Bool) (c : List Bool) (j : ℕ) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial
      (family P D H L F C hs parent terminal d selected power negativeEpsilon) c j)≤
        2^principalHeight P D H L F C hs parent terminal d selected c :=by
  let MF:=family P D H L F C hs parent terminal d selected power negativeEpsilon
  have HD : (MF.head c).natDegree≤d c:=head_outer_degree P D H parent terminal d c
  have HQ : (MF.query c).natDegree≤2:=query_outer_degree P D H L F C hs terminal selected power negativeEpsilon c
  have HP : ∀ i,MvMass.mass ((MF.head c).coeff i)≤2^headHeight P D H L F C parent c:=
    head_coefficient_mass P D H L F C hs parent terminal d hF hf c
  have HQQ : ∀ i,MvMass.mass ((MF.query c).coeff i)≤2^queryHeight P D H L F C terminal c:=
    query_coefficient_mass P D H L F C hs terminal selected power negativeEpsilon c
  have HDeg : (FixedWidthTarskiPrincipalBits.polynomial MF c j).totalDegree≤
      wholeBound P D H L F C hs parent terminal d selected c:=
    principal_degree P D H L F C hs parent terminal d selected power negativeEpsilon c j
  have HW : wholeBound P D H L F C hs parent terminal d selected c<2^MF.width c :=by
    unfold MF family
    unfold IntegralMixedFramedFullCutIntervalFamily.width
    dsimp only [FixedWidthTarskiPrincipalBits.Family.width]
    exact Nat.lt_size_self (wholeBound P D H L F C hs parent terminal d selected c)
  have HE:=FixedWidthTarskiMass.principal_mass MF c j (d c) 2
    (headHeight P D H L F C parent c) (queryHeight P D H L F C terminal c)
    (wholeBound P D H L F C hs parent terminal d selected c) HD HQ HP HQQ HDeg HW
  unfold principalHeight
  simpa only [MF,family] using HE


theorem principalHeight_binary (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (hi : BinaryFn selected) :
    BinaryFn (principalHeight P D H L F C hs parent terminal d selected) :=by
  have HD : BinaryFn (degree d):=
    (BinaryFn.ite ((BinaryFn.const 1).le hd) hd (BinaryFn.const 1)).of_eq (fun _=>by simp only [degree,max_def])
  have HHead : BinaryFn (headHeight P D H L F C parent):=
    IntegralMixedFramedFullCutHead.headMass_binary P D H parent a L F C hL hF hC hp
  have HCoord : BinaryFn (fun c=>IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)):=
    (IntegralMixedFramedBankTermBits.coordinateMass_binary P a D H hL hF hC).comp ht
  have HQuery : BinaryFn (queryHeight P D H L F C terminal):=
    ((BinaryFn.const 2).mul (((BinaryFn.const 2).mul HCoord).add (BinaryFn.const 1))).add (BinaryFn.const 2)
  have HM:=FixedWidthTarskiMass.principalMass_binary HD (HD.sub (BinaryFn.const 1))
    (HD.add (BinaryFn.const 2)) hd (BinaryFn.const 2) HHead HQuery
  have HA : UnaryFn (arity P D H terminal):=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  exact ((BinaryFn.ofUnary ((UnaryFn.const 1).add (HA.add (UnaryFn.const 1)))).mul
    (BinaryFn.ofUnary (width_unary P D H L F C hs parent terminal d selected a hp ht hd hi))).add HM

end LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
