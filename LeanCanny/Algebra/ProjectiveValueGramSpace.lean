/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveValueSourceSpace
public import LeanCanny.Algebra.BivariateReflectSpace
public import LeanCanny.Algebra.CertifiedPolynomial

/-! # Native complete polynomial-value annihilator coefficients

The canonical nested Gram determinant reads original homogeneous rows and
the polynomial test directly. Binary Macaulay levels permit exponential
coordinate degrees. Fixed-degree reflection gives the actual value
annihilator. All original-row workspace is charged by native composition.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveValueGramBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.sub

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ → ℕ
  testDegree : List Bool → ℕ
  rows : (c : List Bool) → Fin (arity c) → MvPolynomial (Fin (arity c + 1)) (Polynomial ℤ)
  test : (c : List Bool) → MvPolynomial (Fin (arity c + 1)) (Polynomial ℤ)

def Family.layout (F : Family) : MacaulayFullBoxBits.Layout where
  arity c := F.arity c + 1
  width := F.width
  level c := Macaulay.level (ProjectiveValueGram.degrees (fun i : Fin (F.arity c) => F.degree c i.val) (F.testDegree c))
  degree c i := if i = 0 then F.testDegree c else F.degree c (i - 1)

lemma Family.positive (F : Family) (c : List Bool) : 0 < F.layout.arity c := Nat.zero_lt_succ _

noncomputable def Family.original (F : Family) (c : List Bool) :
    Fin (F.layout.arity c) → MvPolynomial (Fin (F.layout.arity c)) (Polynomial ℤ) :=
  Fin.cases (F.test c) (F.rows c)

lemma Family.system_eq (F : Family) (c : List Bool) :
    ProjectiveValueSourceBits.system F.layout F.positive F.original c =
      ProjectiveValueGram.system (F.rows c) (F.test c) (F.testDegree c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [ProjectiveValueSourceBits.system, Family.layout, Family.original, ProjectiveValueGram.system]
  · simp [ProjectiveValueSourceBits.system, Family.original, ProjectiveValueGram.system]
    rfl

lemma Family.degrees_eq (F : Family) (c : List Bool) :
    (fun i : Fin (F.layout.arity c) => F.layout.degree c i.val) =
      ProjectiveValueGram.degrees (fun i : Fin (F.arity c) => F.degree c i.val) (F.testDegree c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Family.layout, ProjectiveValueGram.degrees]

lemma Family.level_eq (F : Family) (c : List Bool) :
    F.layout.level c = Macaulay.level (fun i : Fin (F.layout.arity c) => F.layout.degree c i.val) := by
  rw [F.degrees_eq]
  rfl

noncomputable def Family.polynomial (F : Family) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  ProjectiveValueGram.polynomial (F.rows c) (F.test c)
    (fun i => F.degree c i.val) (F.testDegree c) (F.width c)

noncomputable def Family.annihilator (F : Family) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  ProjectiveValueGram.annihilator (F.rows c) (F.test c)
    (fun i => F.degree c i.val) (F.testDegree c) (F.width c)

noncomputable def Family.value (F : Family) (modulus inner outer : List Bool → List Bool)
    (c : List Bool) : List Bool := MacaulayFullBoxBits.scalar modulus c (Nat.fromBitsLE (inner c))
      (Nat.fromBitsLE (outer c)) (F.polynomial c)

theorem Family.polynomialEvaluator (F : Family) (h : F.layout.Controls)
    (modulus inner outer bound : List Bool → List Bool)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ Nat.fromBitsLE (bound c))
    (hm : modulus ∈ FP) (hi : inner ∈ FP) (ho : outer ∈ FP) (hb : bound ∈ FP)
    (E : SpaceFunction (ProjectiveValueSourceBits.source F.layout F.positive F.original modulus)) :
    SpaceFunction (F.value modulus inner outer) := by
  have R := ProjectiveValueSourceBits.determinantEvaluator F.layout F.positive F.original h
    modulus inner outer bound F.level_eq hbound hm hi ho hb E
  refine R.congr (funext fun c => ?_)
  rw [MacaulayFullBoxBits.determinantValue_eq, F.system_eq, F.degrees_eq]
  rfl

lemma Family.dimension_binary (F : Family) (h : F.layout.Controls) :
    BinaryFn (fun c => ProjectiveValueGram.dimension (F.arity c) (F.width c)) := by
  have hc := BinaryFn.of_bits (mem_FP_of_eq (MacaulayFullBoxBits.columnsCode_FP h)
    (MacaulayFullBoxBits.columnsCode_eq F.layout))
  exact (BinaryFn.ofUnary (h.arity.add (UnaryFn.const 2))).mul hc

/-- Requests of degree zero or above the allowance return zero, including
noncanonical raw index words. No exact-degree reader is an input. -/
theorem Family.annihilatorEvaluator (F : Family) (h : F.layout.Controls)
    (modulus inner outer bound : List Bool → List Bool)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ Nat.fromBitsLE (bound c))
    (hm : modulus ∈ FP) (hi : inner ∈ FP) (ho : outer ∈ FP) (hb : bound ∈ FP)
    (E : SpaceFunction (ProjectiveValueSourceBits.source F.layout F.positive F.original modulus)) :
    SpaceFunction (fun c => MacaulayFullBoxBits.scalar modulus c (Nat.fromBitsLE (inner c))
      (Nat.fromBitsLE (outer c)) (F.annihilator c)) := by
  have hn := F.dimension_binary h
  let reflected := fun c => BinaryNat.sub
    (pair (BinaryNatCode.encode (ProjectiveValueGram.dimension (F.arity c) (F.width c) + 1)) (outer c))
  have hr : reflected ∈ FP := mem_FP_comp (mem_FP_pair (hn.add (BinaryFn.const 1)).bits_mem_FP ho) BinaryNat.sub_mem_FP
  have hv := ((BinaryFn.const 0).lt (BinaryFn.fromBits ho)).and
    ((BinaryFn.fromBits ho).le (hn.add (BinaryFn.const 1)))
  have R := SpaceFunction.branch (fun c => decide (0 < Nat.fromBitsLE (outer c) ∧
      Nat.fromBitsLE (outer c) ≤ ProjectiveValueGram.dimension (F.arity c) (F.width c) + 1))
    hv.flag_mem_FP (F.polynomialEvaluator h modulus inner reflected bound hbound hm hi hr hb E)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine R.congr (funext fun c => ?_)
  simp only [Family.annihilator, ProjectiveValueGram.annihilator, MacaulayFullBoxBits.scalar,
    PolynomialReflectBits.coefficient_eq _ _ (ProjectiveValueGram.degree_le _ _ _ _ _), decide_eq_true_eq]
  by_cases hv : 0 < Nat.fromBitsLE (outer c) ∧
      Nat.fromBitsLE (outer c) ≤ ProjectiveValueGram.dimension (F.arity c) (F.width c) + 1
  · rw [ite_eq_left hv, ite_eq_left hv]
    simp only [Family.value, MacaulayFullBoxBits.scalar, reflected, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.polynomial]
  · rw [ite_eq_right hv, ite_eq_right hv]
    simp [residueBits, BinaryNatCode.encode]

/-- Context changes retain the original equations and all degree metadata. -/
noncomputable def Family.comp (F : Family) (f : List Bool → List Bool) : Family where
  arity c := F.arity (f c)
  width c := F.width (f c)
  degree c := F.degree (f c)
  testDegree c := F.testDegree (f c)
  rows c := F.rows (f c)
  test c := F.test (f c)

lemma Family.original_comp (F : Family) (f : List Bool → List Bool) (c : List Bool)
    (i : Fin ((F.comp f).layout.arity c)) : (F.comp f).original c i = F.original (f c) i := rfl

theorem Family.comp_controls (F : Family) (h : F.layout.Controls)
    (f : List Bool → List Bool) (hf : f ∈ FP) : (F.comp f).layout.Controls := by
  refine ⟨h.arity.comp hf, h.width.comp hf, h.level.comp hf, ?_⟩
  apply BinaryFn.of_eq (h.degree.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP))
  intro q
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]
  rfl

-- The context of an original-row packet is (original input, modulus).
noncomputable def Family.sourceCoefficient (F : Family) : List Bool → List Bool :=
  ProjectiveValueSourceBits.source (F.comp pairFst).layout (F.comp pairFst).positive
    (F.comp pairFst).original pairSnd

noncomputable def Family.sourceAt (F : Family) (c : List Bool) (i r u : ℕ) (modulus : List Bool) : List Bool :=
  residueBits (((((F.original c ⟨min i (F.arity c + 1 - 1), by
    change min i (F.arity c + 1 - 1) < F.arity c + 1
    omega⟩).coeff
    (RationalSubstitution.Indexed.exponentVector (F.arity c + 1) (FixedWidthPolynomial.entry (F.width c) r))).coeff u) : ℤ) :
      ZMod (Nat.fromBitsLE modulus + 1))

lemma Family.source_comp_at (F : Family) (f modulus : List Bool → List Bool) (q : List Bool) :
    ProjectiveValueSourceBits.source (F.comp f).layout (F.comp f).positive (F.comp f).original modulus q =
      F.sourceAt (f (MacaulayFullBoxBits.ctx q)) (Nat.fromBitsLE (MacaulayFullBoxBits.idx q))
        (Nat.fromBitsLE (MacaulayFullBoxBits.shift q))
        (Nat.fromBitsLE (pairFst (MacaulayFullBoxBits.uv q))) (modulus (MacaulayFullBoxBits.ctx q)) := rfl

def sourceQuery (z : List Bool) : List Bool :=
  pair (pairFst (MacaulayFullBoxBits.ctx z)) (pairSnd z)

lemma sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp MacaulayFullBoxBits.ctx_FP pairFst_mem_FP) pairSnd_mem_FP

lemma Family.source_query_eq (F : Family) (z : List Bool) :
    F.sourceCoefficient (sourceQuery z) =
      ProjectiveValueSourceBits.source (F.comp BivariateReflectBits.base).layout
        (F.comp BivariateReflectBits.base).positive (F.comp BivariateReflectBits.base).original
        (fun q => pairSnd (pairFst q)) z := by
  rw [Family.sourceCoefficient, Family.source_comp_at, Family.source_comp_at]
  simp only [sourceQuery, BivariateReflectBits.base, MacaulayFullBoxBits.ctx,
    MacaulayFullBoxBits.idx, MacaulayFullBoxBits.shift, MacaulayFullBoxBits.uv, pairFst_pair, pairSnd_pair]

/-- A canonical coefficient reader for the actual value annihilator. Its only
coefficient premise is the native reader for the original homogeneous rows. -/
theorem Family.coefficientEvaluator (F : Family) (h : F.layout.Controls)
    (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ B c)
    (E : SpaceFunction F.sourceCoefficient) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.annihilator) := by
  have hs := (E.precompose sourceQuery sourceQuery_FP).congr
    (funext (F.source_query_eq))
  have he := (F.comp BivariateReflectBits.base).annihilatorEvaluator
    (F.comp_controls h BivariateReflectBits.base BivariateReflectBits.base_FP)
    (fun q => pairSnd (pairFst q)) BivariateReflectBits.inner BivariateReflectBits.outer
    (fun q => BinaryNatCode.encode (B (BivariateReflectBits.base q)))
    (fun q i u => by
      change ((F.original (BivariateReflectBits.base q) i).coeff u).natDegree ≤
        Nat.fromBitsLE (BinaryNatCode.encode (B (BivariateReflectBits.base q)))
      rw [MacaulayBits.fromBits_encode]
      exact hbound _ i u)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BivariateReflectBits.inner_FP BivariateReflectBits.outer_FP
    (mem_FP_comp BivariateReflectBits.base_FP hB.bits_mem_FP) hs
  refine he.congr (funext fun q => ?_)
  rfl

noncomputable def Family.reader (F : Family) (h : F.layout.Controls)
    (B : List Bool → ℕ) (hB : BinaryFn B)
    (hbound : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ B c)
    (E : SpaceFunction F.sourceCoefficient) : CertifiedPolynomial.BivariateReader F.annihilator where
  coefficient := SymbolicFixedTableEntryBits.coefficient F.annihilator
  evaluator := F.coefficientEvaluator h B hB hbound E
  coefficient_eq q u v := by
    simp only [SymbolicFixedTableEntryBits.coefficient, pairFst_pair, pairSnd_pair,
      MacaulayBits.fromBits_encode]
    rfl

end LeanCanny.Algebra.ProjectiveValueGramBits
