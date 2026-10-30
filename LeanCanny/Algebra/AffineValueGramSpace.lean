/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveValueGramSpace
public import LeanCanny.Algebra.HomogenizationParameterSpace
public import LeanCanny.Algebra.AffineRingCoordinates

/-! # Native value certificates from original affine polynomial rows

The original rows and test retain polynomial coefficients. Homogenization
and the reciprocal Gram backend construct their value annihilator, charging
only the original coefficient reader. Spatial degree allowances are explicit
binary metadata, not assumed computations of actual polynomial degrees.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineValueGramBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open MacaulayFullBoxBits (ctx idx shift uv ctx_FP idx_FP shift_FP uv_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ → ℕ
  testDegree : List Bool → ℕ
  rows : (c : List Bool) → Fin (arity c) → MvPolynomial (Fin (arity c)) (Polynomial ℤ)
  test : (c : List Bool) → MvPolynomial (Fin (arity c)) (Polynomial ℤ)

noncomputable def Family.homogeneous (F : Family) : ProjectiveValueGramBits.Family where
  arity := F.arity
  width := F.width
  degree := F.degree
  testDegree := F.testDegree
  rows c := AffineRingCoordinates.homogeneousRows (F.rows c) (fun i => F.degree c i.val)
  test c := rename AffineCoordinateSystem.layout (WeightedHomogenization.homogenize
    (fun _ => 1) (F.testDegree c) (F.test c))

noncomputable def Family.original (F : Family) (c : List Bool) :
    Fin (F.arity c + 1) → MvPolynomial (Fin (F.arity c)) (Polynomial ℤ) := Fin.cases (F.test c) (F.rows c)

lemma Family.homogeneous_original (F : Family) (c : List Bool) (i : Fin (F.arity c + 1)) :
    F.homogeneous.original c i = rename AffineCoordinateSystem.layout
      (WeightedHomogenization.homogenize (fun _ => 1)
        (F.homogeneous.layout.degree c i.val) (F.original c i)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Family.homogeneous, Family.original, ProjectiveValueGramBits.Family.original,
      ProjectiveValueGramBits.Family.layout]
  · simp only [Family.homogeneous, Family.original, ProjectiveValueGramBits.Family.original,
      ProjectiveValueGramBits.Family.layout, Fin.cases_succ, Fin.val_succ, Nat.add_one_ne_zero,
      ite_false, Nat.add_sub_cancel, AffineRingCoordinates.homogeneousRows]
    rfl

def base (q : List Bool) := pairFst (ctx q)
lemma base_FP : base ∈ FP := mem_FP_comp ctx_FP pairFst_mem_FP

noncomputable def Family.row (F : Family) (q : List Bool) : Fin (F.arity (base q) + 1) :=
  ⟨min (Nat.fromBitsLE (idx q)) (F.arity (base q)), by omega⟩

noncomputable def Family.sourceAt (F : Family) (c : List Bool) (i r u : ℕ) (modulus : List Bool) : List Bool :=
  residueBits (((((F.original c ⟨min i (F.arity c), by omega⟩).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (F.width c) r)).coeff u) : ℤ) :
      ZMod (Nat.fromBitsLE modulus + 1))

noncomputable def Family.sourceCoefficient (F : Family) (q : List Bool) : List Bool :=
  F.sourceAt (base q) (Nat.fromBitsLE (idx q)) (Nat.fromBitsLE (shift q))
    (Nat.fromBitsLE (pairFst (uv q))) (pairSnd (ctx q))

lemma Family.arity_unary (F : Family) (h : F.homogeneous.layout.Controls) : UnaryFn F.arity := by
  have hn : UnaryFn (fun c => F.arity c + 1) := h.arity
  exact (hn.sub (UnaryFn.const 1)).of_eq (fun c => Nat.add_sub_cancel _ _)

lemma Family.row_unary (F : Family) (h : F.homogeneous.layout.Controls) : UnaryFn (fun q => (F.row q).val) :=
  UnaryFn.fromBitsLE_min idx_FP ((F.arity_unary h).comp base_FP)

noncomputable def Family.selected (F : Family) (q : List Bool) :
    MvPolynomial (Fin (F.arity (base q))) (Polynomial ℤ) := F.original (base q) (F.row q)

noncomputable def Family.allowance (F : Family) (q : List Bool) : ℕ :=
  F.homogeneous.layout.degree (base q) (F.row q).val

lemma Family.allowance_binary (F : Family) (h : F.homogeneous.layout.Controls) : BinaryFn F.allowance := by
  apply BinaryFn.of_eq (h.degree.comp (mem_FP_pair base_FP (bits_mem_FP (F.row_unary h))))
  intro q
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits, Family.allowance]

def sourceQuery (z : List Bool) : List Bool :=
  pair (ctx (pairFst z)) (pair (idx (pairFst z)) (pair (pairSnd z) (uv (pairFst z))))

lemma sourceQuery_FP : sourceQuery ∈ FP := by
  have hc : (fun z => ctx (pairFst z)) ∈ FP := mem_FP_comp (f := pairFst) (g := ctx) pairFst_mem_FP ctx_FP
  have hi : (fun z => idx (pairFst z)) ∈ FP := mem_FP_comp (f := pairFst) (g := idx) pairFst_mem_FP idx_FP
  have hu : (fun z => uv (pairFst z)) ∈ FP := mem_FP_comp (f := pairFst) (g := uv) pairFst_mem_FP uv_FP
  exact mem_FP_of_eq (mem_FP_pair hc (mem_FP_pair hi (mem_FP_pair pairSnd_mem_FP hu))) (fun _ => rfl)

def prepare (q : List Bool) : List Bool := pair q (BinaryNat.normalize (shift q))
lemma prepare_FP : prepare ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp shift_FP BinaryNat.normalize_mem_FP)

lemma Family.source_query_eq (F : Family) (z : List Bool) :
    F.sourceCoefficient (sourceQuery z) =
      HomogenizationParameterBits.source (fun q => F.arity (base q)) (fun q => F.width (base q))
        F.selected (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) z := by
  unfold Family.sourceCoefficient base sourceQuery ctx idx shift uv
  simp only [pairFst_pair, pairSnd_pair]
  rfl

lemma Family.homogeneous_query_eq (F : Family) (q : List Bool) :
    HomogenizationParameterBits.value (fun q => F.arity (base q)) (fun q => F.width (base q)) F.allowance
      F.selected (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) (prepare q) =
        F.homogeneous.sourceCoefficient q := by
  rw [prepare, BinaryNat.normalize_eq_bits]
  change HomogenizationParameterBits.value (fun q => F.arity (base q)) (fun q => F.width (base q)) F.allowance
    F.selected (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q))
    (pair q (BinaryNatCode.encode (Nat.fromBitsLE (shift q)))) = _
  rw [HomogenizationParameterBits.value_packet]
  rw [ProjectiveValueGramBits.Family.sourceCoefficient, ProjectiveValueGramBits.Family.source_comp_at]
  unfold ProjectiveValueGramBits.Family.sourceAt
  rw [F.homogeneous_original]
  simp only [HomogenizationParameterBits.polynomial, Family.homogeneous, Family.selected,
    Family.allowance, Family.row, base, FixedWidthPolynomial.nativeExponent_refl, Nat.add_sub_cancel]
  rfl

/-- Native original affine coefficients construct the complete homogeneous
source reader used by the value determinant, with all original costs retained. -/
theorem Family.homogeneousSourceEvaluator (F : Family) (h : F.homogeneous.layout.Controls)
    (E : SpaceFunction F.sourceCoefficient) : SpaceFunction F.homogeneous.sourceCoefficient := by
  have ES := (E.precompose sourceQuery sourceQuery_FP).congr (funext F.source_query_eq)
  have hn : UnaryFn (fun q => F.arity (base q)) := (F.arity_unary h).comp base_FP
  have hw : UnaryFn (fun q => F.width (base q)) := h.width.comp base_FP
  have EH := HomogenizationParameterBits.evaluator hn hw (F.allowance_binary h)
    F.selected (fun q => pairFst (uv q)) (fun q => pairSnd (ctx q)) ES
  exact (EH.precompose prepare prepare_FP).congr (funext F.homogeneous_query_eq)

lemma homogenized_inner_degree {n : ℕ} (p : MvPolynomial (Fin n) (Polynomial ℤ)) (D B : ℕ)
    (hp : ∀ u, (p.coeff u).natDegree ≤ B) (u : Fin (n + 1) →₀ ℕ) :
    ((rename AffineCoordinateSystem.layout (WeightedHomogenization.homogenize (fun _ => 1) D p)).coeff u).natDegree ≤ B := by
  by_cases hz : (rename AffineCoordinateSystem.layout
      (WeightedHomogenization.homogenize (fun _ => 1) D p)).coeff u = 0
  · simp [hz]
  · obtain ⟨v, hv, _⟩ := coeff_rename_ne_zero AffineCoordinateSystem.layout _ u hz
    rw [← hv, coeff_rename_mapDomain _ AffineCoordinateSystem.layout.injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hp _
    · simp

lemma Family.homogeneous_inner_bound (F : Family) (B : List Bool → ℕ)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ B c)
    (c : List Bool) (i : Fin (F.homogeneous.layout.arity c)) (u : Fin (F.arity c + 1) →₀ ℕ) :
    ((F.homogeneous.original c i).coeff u).natDegree ≤ B c := by
  rw [F.homogeneous_original]
  exact homogenized_inner_degree _ _ _ (hbound c i) u

/-- The native value coefficient reader now starts with the actual affine
equations and test, rather than a supplied homogeneous or determinant reader. -/
theorem Family.coefficientEvaluator (F : Family) (h : F.homogeneous.layout.Controls)
    (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ B c)
    (E : SpaceFunction F.sourceCoefficient) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.homogeneous.annihilator) :=
  F.homogeneous.coefficientEvaluator h B hB (F.homogeneous_inner_bound B hbound)
    (F.homogeneousSourceEvaluator h E)

noncomputable def Family.reader (F : Family) (h : F.homogeneous.layout.Controls)
    (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ B c)
    (E : SpaceFunction F.sourceCoefficient) : CertifiedPolynomial.BivariateReader F.homogeneous.annihilator :=
  F.homogeneous.reader h B hB (F.homogeneous_inner_bound B hbound) (F.homogeneousSourceEvaluator h E)

lemma Family.test_homogeneous (F : Family) (c : List Bool) :
    (F.homogeneous.test c).IsHomogeneous (F.testDegree c) := by
  have hw : WeightedHomogenization.weights (fun _ : Fin (F.arity c) => 1) = 1 := by
    funext j; cases j <;> rfl
  apply IsHomogeneous.rename_isHomogeneous
  simpa only [IsHomogeneous, hw] using WeightedHomogenization.homogeneous
    (fun _ : Fin (F.arity c) => 1) (F.testDegree c) (F.test c)

lemma Family.test_eval (F : Family) (c : List Bool) {K : Type*} [Field K]
    (rho : Polynomial ℤ →+* K) (x : Fin (F.arity c) → K)
    (hq : (F.test c).totalDegree ≤ F.testDegree c) :
    (F.homogeneous.test c).eval₂ rho (AffineFiniteCoordinates.point x) = (F.test c).eval₂ rho x := by
  change (rename AffineCoordinateSystem.layout (WeightedHomogenization.homogenize
    (fun _ => 1) (F.testDegree c) (F.test c))).eval₂ rho _ = _
  rw [eval₂_rename]
  have he : AffineFiniteCoordinates.point x ∘ AffineCoordinateSystem.layout =
      fun j => j.elim 1 x := by
    funext j
    simp [AffineFiniteCoordinates.point, AffineCoordinateSystem.layout, AffineFiniteCoordinates.layout]
  rw [he]
  apply WeightedHomogenization.eval_chart
  intro u hu
  exact (WeightedHomogenization.weight_le_degree _ (by simp) u).trans ((le_totalDegree hu).trans hq)

/-- The same polynomial read by the native program retains every affine
root, including singular roots and parameter specializations with degree drops. -/
theorem Family.eval_eq_zero (F : Family) (c : List Bool) {K : Type*} [Field K]
    (rho : Polynomial ℤ →+* K) (x : Fin (F.arity c) → K)
    (hp : ∀ i, (F.rows c i).totalDegree ≤ F.degree c i.val)
    (hq : (F.test c).totalDegree ≤ F.testDegree c)
    (hW : F.homogeneous.layout.level c < 2 ^ F.width c)
    (hx : ∀ i, (F.rows c i).eval₂ rho x = 0) :
    (F.homogeneous.annihilator c).eval₂ rho ((F.test c).eval₂ rho x) = 0 := by
  have h := ProjectiveValueGram.annihilator_eval
    (F.homogeneous.rows c) (F.homogeneous.test c) (fun i => F.degree c i.val)
    (F.testDegree c) (F.width c) hW (AffineRingCoordinates.homogeneous _ _)
    (F.test_homogeneous c) rho (AffineFiniteCoordinates.point x)
    (AffineFiniteCoordinates.point_zero x) (by
      intro i
      exact (AffineRingCoordinates.eval_rows rho (F.rows c) (fun i => F.degree c i.val) hp x i).trans (hx i))
  rwa [F.test_eval c rho x hq] at h

theorem Family.ne_zero (F : Family) (c : List Bool)
    (hd : ∀ i : Fin (F.arity c), 0 < F.degree c i.val) (he : 0 < F.testDegree c)
    (hW : F.homogeneous.layout.level c < 2 ^ F.width c) (rho : Polynomial ℤ →+* ℝ)
    (hinfinity : AffineRingCoordinates.NoInfinity (Complex.ofRealHom.comp rho)
      (F.rows c) (fun i => F.degree c i.val)) : F.homogeneous.annihilator c ≠ 0 :=
  ProjectiveValueGram.annihilator_ne_zero _ _ _ _ _ hW (AffineRingCoordinates.homogeneous _ _)
    (F.test_homogeneous c) hd he rho (AffineRingCoordinates.noInfinity_layout _ _ _ hinfinity)

end LeanCanny.Algebra.AffineValueGramBits
