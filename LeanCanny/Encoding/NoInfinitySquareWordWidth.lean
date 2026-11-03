/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.NoInfinitySquareSample
public import LeanCanny.Encoding.SquareSampleCompleteVertices
/-! # Explicit complete-sampler word width from count and row degrees -/
@[expose] public section
namespace LeanCanny.Encoding.NoInfinitySquareWordWidth
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators

def ceiling (count degree : ℕ) :=
  count*((count+3).size+(count+1)*(count*degree+1).size+3)+2

theorem size_pow_add_one (n : ℕ) : (2^n+1).size≤n+2 :=by
  have H : 2^n+1≤2^(n+1):=by
    rw [pow_succ]
    have HP : 1≤2^n:=Nat.one_le_two_pow
    omega
  exact (Nat.size_le_size H).trans_eq (by rw [Nat.size_pow])

theorem size_scaled_power_add_two (a b : ℕ) : (a*2^b+2).size≤a.size+b+3 :=by
  apply Nat.size_le.mpr
  have HA : a*2^b<2^(a.size+b):=by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (Nat.two_pow_pos b)
  have HP : 1≤2^(a.size+b):=Nat.one_le_two_pow
  rw [show a.size+b+3=(a.size+b)+3 by omega,pow_add]
  norm_num
  omega

theorem level_le {n : ℕ} (d : Fin n→ℕ) (D : ℕ) (hd : ∀i,d i≤D) :
    Macaulay.level (AffineBoxGramEliminant.degrees d)≤n*D+1 :=by
  have HS : (∑i : Fin n,(d i-1))≤∑_i : Fin n,D:=
    Finset.sum_le_sum (fun i _=>(Nat.sub_le _ _).trans (hd i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at HS
  simpa only [Macaulay.level,AffineBoxGramEliminant.degrees,Fin.sum_univ_succ,
    Fin.cases_zero,Fin.cases_succ,Nat.sub_self,Nat.zero_add] using Nat.add_le_add_right HS 1

theorem width_exact (F : NoInfinitySquareSample.Family) (u : List Bool) :
    SquareSampleCompleteVertices.width (NoInfinitySquareSample.input F) u=
      (2^((F.count u)*((NoInfinitySquareSample.dimension F u)+2).size)+1).size :=by
  change ((FiniteSourceDegreePreparation.degreeBudget
    (SquareSampleSource.degreeBound (SquareSampleGrid.input (NoInfinitySquareSample.input F))) u)^
      (F.count u)+1).size=_
  simp only [FiniteSourceDegreePreparation.degreeBudget,FiniteSourceDegreePreparation.width,
    SquareSampleSource.degreeBound,SquareSampleGrid.input,NoInfinitySquareSample.input,
    NoInfinitySquareSample.annDegree]
  rw [←pow_mul,Nat.mul_comm]

theorem width_le (F : NoInfinitySquareSample.Family) (u : List Bool) (D : ℕ)
    (hd : ∀i : Fin (F.count u),F.rowDegree u i.val≤D) :
    SquareSampleCompleteVertices.width (NoInfinitySquareSample.input F) u≤ceiling (F.count u) D :=by
  let n:=F.count u
  let W:=AffineFiniteCoordinates.width (fun i : Fin n=>F.rowDegree u i.val)
  have HW : W≤(n*D+1).size:=Nat.size_le_size (level_le _ D hd)
  have HA : NoInfinitySquareSample.dimension F u=(n+3)*2^((n+1)*W):=by
    simp only [NoInfinitySquareSample.dimension,AffineFiniteCoordinates.dimension,
      AffineBoxGramEliminant.dimension,FixedWidthPolynomial.count,←pow_mul,n,W,Nat.mul_comm]
  rw [width_exact]
  apply (size_pow_add_one _).trans
  have HB : (NoInfinitySquareSample.dimension F u+2).size≤
      (n+3).size+(n+1)*(n*D+1).size+3:=by
    rw [HA]
    exact (size_scaled_power_add_two _ _).trans
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left (n+1) HW) _) 3)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n HB) 2

theorem ceiling_mono {n m d e : ℕ} (hn : n≤m) (hd : d≤e) : ceiling n d≤ceiling m e :=by
  unfold ceiling
  have HS : (n*d+1).size≤(m*e+1).size:=
    Nat.size_le_size (Nat.add_le_add_right (Nat.mul_le_mul hn hd) 1)
  have HN : (n+3).size≤(m+3).size:=Nat.size_le_size (Nat.add_le_add_right hn 3)
  exact Nat.add_le_add_right (Nat.mul_le_mul hn (Nat.add_le_add_right
    (Nat.add_le_add HN (Nat.mul_le_mul (Nat.add_le_add_right hn 1) HS)) 3)) 2

theorem ceiling_unary {n d : List Bool→ℕ} (hn : UnaryFn n) (hd : BinaryFn d) :
    UnaryFn (fun q=>ceiling (n q) (d q)) :=by
  have HA : BinaryFn (fun q=>n q*d q+1):=((BinaryFn.ofUnary hn).mul hd).add (BinaryFn.const 1)
  have HS : UnaryFn (fun q=>(n q*d q+1).size):=
    (UnaryFn.length HA.bits_mem_FP).of_eq (fun q=>BinaryNatCode.length_encode _)
  have HN : UnaryFn (fun q=>(n q+3).size):=
    (UnaryFn.length ((BinaryFn.ofUnary hn).add (BinaryFn.const 3)).bits_mem_FP).of_eq
      (fun q=>BinaryNatCode.length_encode _)
  exact (hn.mul ((HN.add ((hn.add (UnaryFn.const 1)).mul HS)).add (UnaryFn.const 3))).add (UnaryFn.const 2)

end LeanCanny.Encoding.NoInfinitySquareWordWidth
