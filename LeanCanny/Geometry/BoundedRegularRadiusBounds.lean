/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedRegularRadiusPolynomial
public import LeanCanny.Encoding.BoundedRegularControls

/-! # Original-only degree and native bit width of the external radius family

The parameter degree can be large, but its binary code has polynomial size.
Neither this bound nor the specialization identity asserts component stability.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularRadius
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

def parameterDegree (n D : ℕ) := regularizationSlope n D+perturbationSlope n D+BoundedZeroSource.powerDegree D+4
def parameterWidth (n D : ℕ) := (parameterDegree n D).size

theorem regularizationSlope_pos (n D : ℕ) : 0<regularizationSlope n D := by
  unfold regularizationSlope
  apply Nat.mul_pos
  · unfold FixedWidthPolynomial.count
    positivity
  · unfold sourceMassSlope
    omega

theorem polynomial_at_zero {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) :
    (polynomial q D b).eval 0=-1 := by
  have H : (powerScalar (ι:=Fin (n+4)) (BoundedRegularSource.regularizationExponent n D b 0)
      (regularizationSlope n D)).eval 0=0 := by
    simp only [powerScalar,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
      zero_pow (ne_of_gt (regularizationSlope_pos n D)),mul_zero]
  unfold polynomial
  rw [Polynomial.eval_sub,Polynomial.eval_mul,H,zero_mul,Polynomial.eval_one,zero_sub]

theorem powerScalar_degree {ι : Type*} (offset slope : ℕ) : (powerScalar (ι:=ι) offset slope).natDegree≤slope := by
  unfold powerScalar
  calc
    _≤(Polynomial.C (MvPolynomial.C ((2 : ℤ)^offset))).natDegree+(Polynomial.X^slope).natDegree := Polynomial.natDegree_mul_le
    _=slope := by simp only [Polynomial.natDegree_C,Polynomial.natDegree_X_pow,zero_add]

theorem sourcePolynomial_degree {n : ℕ} (q : MvPolynomial (Fin n) ℤ) : (sourcePolynomial q).natDegree≤4 := by
  have H (v : MvPolynomial (Fin (n+4)) ℤ) : (Polynomial.C v-Polynomial.X^2).natDegree≤2 := by
    calc
      _≤max (Polynomial.C v).natDegree (Polynomial.X^2).natDegree := Polynomial.natDegree_sub_le _ _
      _=2 := by simp only [Polynomial.natDegree_C,Polynomial.natDegree_X_pow,Nat.zero_max]
  unfold sourcePolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_pow_le).trans
    simpa only [Polynomial.natDegree_C,mul_zero] using (Nat.zero_le 4)
  · exact (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (H _))

private theorem form_degree {A : Type*} [CommRing A] [Nontrivial A] (a b c p : Polynomial A) (v : A)
    (s t u : ℕ) (ha : a.natDegree≤s) (hb : b.natDegree≤t) (hc : c.natDegree≤u) (hp : p.natDegree≤4) :
    (a*(b*p-c+Polynomial.C v)-1).natDegree≤s+t+u+4 := by
  have HB : (b*p).natDegree≤t+4 := Polynomial.natDegree_mul_le.trans (Nat.add_le_add hb hp)
  have HC : (b*p-c).natDegree≤t+u+4 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (HB.trans (by omega)) (hc.trans (by omega)))
  have HV : (b*p-c+Polynomial.C v).natDegree≤t+u+4 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le HC (by rw [Polynomial.natDegree_C]; omega))
  have HA : (a*(b*p-c+Polynomial.C v)).natDegree≤s+t+u+4 :=
    Polynomial.natDegree_mul_le.trans ((Nat.add_le_add ha HV).trans (by omega))
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le HA (by rw [Polynomial.natDegree_one]; omega))

theorem polynomial_degree {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) :
    (polynomial q D b).natDegree≤parameterDegree n D :=
  form_degree _ _ _ _ _ _ _ _ (powerScalar_degree _ _) (powerScalar_degree _ _) (powerScalar_degree _ _) (sourcePolynomial_degree q)

theorem perturbationSlope_binary {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun q=>perturbationSlope (n q) (D q)) := by
  have H1:=BoundedZeroControls.perturbationExponent_binary hn hD (BinaryFn.const 0) (BinaryFn.const 1)
  have H0:=BoundedZeroControls.perturbationExponent_binary hn hD (BinaryFn.const 0) (BinaryFn.const 0)
  apply (H1.sub H0).of_eq
  intro q
  simp only [perturbation_affine (n q) (D q) 0 1,Nat.mul_one,Nat.add_sub_cancel_left]

theorem regularizationSlope_binary {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun q=>regularizationSlope (n q) (D q)) := by
  have H1:=BoundedRegularControls.regularizationExponent_binary hn hD (BinaryFn.const 0) (BinaryFn.const 1)
  have H0:=BoundedRegularControls.regularizationExponent_binary hn hD (BinaryFn.const 0) (BinaryFn.const 0)
  apply (H1.sub H0).of_eq
  intro q
  simp only [regularization_affine (n q) (D q) 0 1,Nat.mul_one,Nat.add_sub_cancel_left]

theorem parameterDegree_binary {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun q=>parameterDegree (n q) (D q)) :=
  (((regularizationSlope_binary hn hD).add (perturbationSlope_binary hn hD)).add
    (BoundedZeroControls.powerDegree_binary hD)).add (BinaryFn.const 4)

theorem parameterWidth_unary {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    UnaryFn (fun q=>parameterWidth (n q) (D q)) :=
  (UnaryFn.length (parameterDegree_binary hn hD).bits_mem_FP).of_eq
    (fun q=>BinaryNatCode.length_encode (parameterDegree (n q) (D q)))

theorem parameterWidth_polynomial {n D : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    ∃ p : Polynomial ℕ,∀ q,parameterWidth (n q) (D q)≤p.eval q.length := by
  obtain ⟨p,HP⟩:=output_length_poly_of_mem_FP (parameterWidth_unary hn hD).mem_FP
  exact ⟨p,fun q=>by simpa only [List.length_replicate] using HP q⟩

end LeanCanny.Geometry.BoundedRegularRadius
