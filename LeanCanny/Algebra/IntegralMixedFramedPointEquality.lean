/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBounds
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardSpace
/-! # Sparse equality of two actual powered physical blocks

Each creating birth uses its own physical power. The coordinate selector is
an arbitrary ambient index, independent of the command's selected scalar.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPointEqualityBits
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial MatrixPower
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedCriticalGuardBits (count packet Active physicalPower)
open IntegralMixedFramedPhysicalIndex (prefixArity)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (T : Tables) (key : List Bool→List Bool)
  (left right coordinate : List Bool→ℕ)

def column (stage : List Bool→ℕ) (q : List Bool) :=prefixArity P T (packet key stage q)+coordinate q
theorem column_binary (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (stage : List Bool→ℕ) (hk : key∈FP) (hs : UnaryFn stage) (hi : BinaryFn coordinate) :
    BinaryFn (column P T key coordinate stage) :=
  (BinaryFn.ofUnary ((IntegralMixedFramedPhysicalIndex.prefixArity_unary P a T hT).comp
    (IntegralMixedFramedCriticalGuardBits.packet_FP hk hs))).add hi

def Admissible (q : List Bool) :=Active P T key left q ∧ Active P T key right q ∧
  coordinate q<P.ambient (pairFst (key q))+1
theorem admissible_FP (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hk : key∈FP) (hl : UnaryFn left) (hr : UnaryFn right) (hi : BinaryFn coordinate) :
    FPPred (Admissible P T key left right coordinate) :=
  (IntegralMixedFramedCriticalGuardBits.active_FP P a T hT key left hk hl).and
    ((IntegralMixedFramedCriticalGuardBits.active_FP P a T hT key right hk hr).and
      (hi.lt (BinaryFn.ofUnary ((a.ambient.comp (mem_FP_comp hk pairFst_mem_FP)).add (UnaryFn.const 1)))))

theorem column_lt (stage : List Bool→ℕ) (q : List Bool)
    (ha : Active P T key stage q) (hi : coordinate q<P.ambient (pairFst (key q))+1) :
    column P T key coordinate stage q<count P T key q :=by
  let K:=key q
  let j:=stage q
  let m:=IntegralMixedFramedHistoryFamilyBits.prefixLength P K
  change coordinate q<P.ambient (pairFst K)+1 at hi
  have HS : prefixArity P T (pair K (List.replicate (j+1) true))=
      prefixArity P T (pair K (List.replicate j true))+IntegralMixedFramedPhysicalIndex.block (P.ambient (pairFst K))+1 :=by
    simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate,Finset.sum_range_succ]
    have HH : IntegralMixedFramedPhysicalIndex.span P T (pair K (List.replicate j true))=
        IntegralMixedFramedPhysicalIndex.block (P.ambient (pairFst K))+1 :=by
      unfold IntegralMixedFramedPhysicalIndex.span
      simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
      exact ite_eq_left ha.2
    rw [HH]
    omega
  have HL : prefixArity P T (pair K (List.replicate (j+1) true))≤prefixArity P T (pair K (List.replicate m true)) :=by
    simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt ha.1))
  unfold column count packet
  change prefixArity P T (pair K (List.replicate j true))+coordinate q<
    prefixArity P T (pair K (List.replicate m true))
  unfold IntegralMixedFramedPhysicalIndex.block at HS
  omega

noncomputable def polynomial (q : List Bool) : MvPolynomial (Fin (count P T key q)) ℤ :=
  FixedWidthMonomialBits.polynomial (count P T key) (column P T key coordinate left)
    (physicalPower P key left) (fun _=>1) q-
  FixedWidthMonomialBits.polynomial (count P T key) (column P T key coordinate right)
    (physicalPower P key right) (fun _=>1) q
def degree (q : List Bool) :=max (physicalPower P key left q) (physicalPower P key right q)
theorem degree_binary (a : Access P) (hk : key∈FP) (hl : UnaryFn left) (hr : UnaryFn right) :
    BinaryFn (degree P key left right) :=by
  have HL:=IntegralMixedFramedCriticalGuardBits.physicalPower_binary P a key left hk hl
  have HR:=IntegralMixedFramedCriticalGuardBits.physicalPower_binary P a key right hk hr
  exact (BinaryFn.ite (HL.le HR) HR HL).of_eq (fun q=>by simp only [degree,max_def])

private theorem monomial_degree (A c e : List Bool→ℕ) (q : List Bool) :
    (FixedWidthMonomialBits.polynomial A c e (fun _=>1) q).totalDegree≤e q :=by
  unfold FixedWidthMonomialBits.polynomial
  split_ifs
  · exact (totalDegree_monomial_le _ _).trans_eq (by simp)
  · exact Nat.zero_le _
private theorem monomial_mass (A c e : List Bool→ℕ) (q : List Bool) :
    MvMass.mass (FixedWidthMonomialBits.polynomial A c e (fun _=>1) q)≤1 :=by
  unfold FixedWidthMonomialBits.polynomial
  split_ifs
  · simpa only [Int.natAbs_one] using (MvMass.monomial (Finsupp.single _ (e q)) (1:ℤ)).le
  · exact Nat.zero_le _
theorem polynomial_degree (q : List Bool) :
    (polynomial P T key left right coordinate q).totalDegree≤degree P key left right q :=
  (totalDegree_sub _ _).trans (max_le_max (monomial_degree _ _ _ _) (monomial_degree _ _ _ _))
theorem polynomial_mass (q : List Bool) : MvMass.mass (polynomial P T key left right coordinate q)≤2^1 :=
  (MvMass.sub_le _ _).trans (Nat.add_le_add (monomial_mass _ _ _ _) (monomial_mass _ _ _ _))

private theorem one_evaluator (modulus : List Bool→List Bool) (hm : modulus∈FP) :
    SpaceFunction (fun q=>residueBits (1 : ZMod (Nat.fromBitsLE (modulus q)+1))) :=by
  have HM:BinaryFn (fun q=>Nat.fromBitsLE (modulus q)+1):=(BinaryFn.fromBits hm).add (BinaryFn.const 1)
  apply SpaceFunction.ofFP
  apply mem_FP_of_eq (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)
  intro q
  exact ArithmeticBits.one_residueBits _
theorem coefficient_evaluator (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T)
    (W : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hk : key∈FP) (hl : UnaryFn left) (hr : UnaryFn right) (hi : BinaryFn coordinate)
    (hW : UnaryFn W) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (count P T key) W (polynomial P T key left right coordinate) target modulus) :=by
  have HA:=IntegralMixedFramedCriticalGuardBits.count_unary P a T hT key hk
  have E (stage : List Bool→ℕ) (hs : UnaryFn stage) :=
    FixedWidthMonomialBits.coefficient_evaluator (count P T key) W (column P T key coordinate stage)
      (physicalPower P key stage) target (fun _=>1) modulus
      (fun q=>residueBits (1 : ZMod (Nat.fromBitsLE (modulus q)+1))) (one_evaluator modulus hm)
      (fun _=>rfl) HA hW (column_binary P T key coordinate a hT stage hk hs hi)
      (IntegralMixedFramedCriticalGuardBits.physicalPower_binary P a key stage hk hs) ht
  exact FixedWidthRowBits.sub_evaluator _ W _ _ target modulus hm (E left hl) (E right hr)

noncomputable def point (stage : List Bool→ℕ) (q : List Bool) (ha : Active P T key stage q)
    (z : Fin (count P T key q)→ℝ) (i : Fin (P.ambient (pairFst (key q))+1)) : ℝ :=
  z ⟨prefixArity P T (packet key stage q)+i.val,
    column_lt P T key (fun _=>i.val) stage q ha i.isLt⟩^physicalPower P key stage q

theorem polynomial_eval (q : List Bool) (h : Admissible P T key left right coordinate q)
    (z : Fin (count P T key q)→ℝ) :
    (polynomial P T key left right coordinate q).eval₂ (Int.castRingHom ℝ) z=
      point P T key left q h.1 z ⟨coordinate q,h.2.2⟩-
        point P T key right q h.2.1 z ⟨coordinate q,h.2.2⟩ :=by
  unfold polynomial FixedWidthMonomialBits.polynomial
  rw [dite_eq_left (column_lt P T key coordinate left q h.1 h.2.2),
    dite_eq_left (column_lt P T key coordinate right q h.2.1 h.2.2)]
  rw [←MvPolynomial.X_pow_eq_monomial,←MvPolynomial.X_pow_eq_monomial]
  simp only [MvPolynomial.eval₂_sub,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedPointEqualityBits
