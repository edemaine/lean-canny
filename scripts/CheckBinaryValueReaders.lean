import LeanCanny.Algebra.ProjectiveValueGramSpace

/-! Binary Macaulay levels and actual reciprocal value readers.
Run with `lake env lean -DwarningAsError=true scripts/CheckBinaryValueReaders.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

namespace ExponentialValueReaderRegression
noncomputable section

-- Empty coordinate systems are valid. The zero test is homogeneous of the
-- exponential allowance, giving the nonzero chart row -X₀^(2^|c|).
private noncomputable def F : ProjectiveValueGramBits.Family where
  arity _ := 0
  width c := c.length + 1
  degree _ _ := 0
  testDegree c := 2 ^ c.length
  rows _ i := i.elim0
  test _ := 0

private lemma level (c : List Bool) : F.layout.level c = 2 ^ c.length := by
  have h : 0 < 2 ^ c.length := Nat.two_pow_pos _
  change (∑ i : Fin 1, (ProjectiveValueGram.degrees (fun _ : Fin 0 => 0) (2 ^ c.length) i - 1)) + 1 = _
  rw [Fin.sum_univ_succ]
  simp only [ProjectiveValueGram.degrees, Fin.cases_zero, Fin.sum_univ_zero, add_zero]
  omega

private lemma controls : F.layout.Controls := by
  have hl : UnaryFn (fun c : List Bool => c.length) := UnaryFn.length id_mem_FP
  have he := (BinaryFn.const 2).powUnary hl
  refine ⟨UnaryFn.const 1, hl.add (UnaryFn.const 1), he.of_eq (fun c => (level c).symm), ?_⟩
  have hz := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)
  have hctx : BinaryFn (fun q => 2 ^ (pairFst q).length) := he.comp pairFst_mem_FP
  exact (BinaryFn.ite hz hctx (BinaryFn.const 0)).of_eq (fun _ => rfl)

example : F.layout.level (List.replicate 8 false) = 256 := by rw [level]; rfl

-- Exponential levels still have native exponent-sum and row-activity tests.
example : BinaryFn (MacaulayFullBoxBits.total F.layout) := MacaulayFullBoxBits.total_binary controls
example : FPPred (MacaulayFullBoxBits.active F.layout) := MacaulayFullBoxBits.active_FP controls

private lemma original_zero (c : List Bool) (i : Fin (F.layout.arity c)) : F.original c i = 0 := by
  refine Fin.cases rfl (fun i => i.elim0) i

private lemma source_evaluator (modulus : List Bool → List Bool) :
    SpaceFunction (ProjectiveValueSourceBits.source F.layout F.positive F.original modulus) := by
  have E := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
  refine E.congr (funext fun q => ?_)
  simp [ProjectiveValueSourceBits.source, original_zero, residueBits, BinaryNatCode.encode]

-- The full annihilator reader is derived without any determinant or source
-- oracle, even though the mathematical source degree is exponential.
example (modulus inner outer : List Bool → List Bool)
    (hm : modulus ∈ FP) (hi : inner ∈ FP) (ho : outer ∈ FP) :
    SpaceFunction (fun c => MacaulayFullBoxBits.scalar modulus c (Nat.fromBitsLE (inner c))
      (Nat.fromBitsLE (outer c)) (F.annihilator c)) := by
  apply F.annihilatorEvaluator controls modulus inner outer (fun _ => []) ?_
    hm hi ho (constFn_mem_FP []) (source_evaluator modulus)
  intro c i u
  simp [original_zero]

-- Canonical bivariate access is suitable for the existing trailing-coefficient
-- scan, without changing the modulus or coefficient index conventions.
private lemma canonical_source_evaluator : SpaceFunction F.sourceCoefficient := by
  have E := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
  have hz (c : List Bool) (i : Fin ((F.comp pairFst).layout.arity c)) :
      (F.comp pairFst).original c i = 0 := original_zero (pairFst c) i
  refine E.congr (funext fun q => ?_)
  simp [ProjectiveValueGramBits.Family.sourceCoefficient, ProjectiveValueSourceBits.source,
    hz, residueBits, BinaryNatCode.encode]

example : CertifiedPolynomial.BivariateReader F.annihilator := by
  apply F.reader controls (fun _ => 0) (BinaryFn.const 0) ?_ canonical_source_evaluator
  intro c i u
  simp [original_zero]

-- The mask distinguishes reciprocal degree one from the chart constant.
example (q : List Bool) (hq : (ProjectiveValueSourceBits.row F.layout F.positive q).val = 0)
    (hv : Nat.fromBitsLE (pairSnd (MacaulayFullBoxBits.uv q)) = 0) :
    ¬ProjectiveValueSourceBits.selected F.layout F.positive q := by
  simp [ProjectiveValueSourceBits.selected, hq, hv]

end
end ExponentialValueReaderRegression
