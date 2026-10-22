/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveHomogeneousReaders
public import LeanCanny.ETR.CoerciveHomogeneousRepack

/-! # Native row and parameter-degree branching for homogeneous coefficients -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveHomogeneousRowReader
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveSparseReaders
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

def context (q : List Bool) : List Bool := pairFst q
def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def rank (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def inner (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd q)))
def outer (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd q)))

theorem context_FP : context ∈ FP := pairFst_mem_FP
theorem row_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rank_FP : rank ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem inner_FP : inner ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
theorem outer_FP : outer ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

noncomputable def selected (input : List Bool → List Bool) (q : List Bool) : ℕ :=
  min (Nat.fromBitsLE (row q)) (dimension (input (context q)) + 1) - 1

theorem selected_unary {input : List Bool → List Bool} (hi : input ∈ FP) : UnaryFn (selected input) :=
  (UnaryFn.fromBitsLE_min row_FP (((dimension_unary.comp hi).comp context_FP).add (UnaryFn.const 1))).sub (UnaryFn.const 1)

noncomputable def target (input : List Bool → List Bool) : List Bool → List Bool :=
  CoerciveHomogeneousRepack.target (input ∘ context) rank

theorem target_FP {input : List Bool → List Bool} (hi : input ∈ FP) : target input ∈ FP :=
  CoerciveHomogeneousRepack.target_FP (mem_FP_comp context_FP hi) rank_FP

noncomputable def ordinary (input modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  CoerciveHomogeneousReaders.ordinaryValue (input ∘ context) (selected input) (modulus ∘ context)
    (pair q (BinaryNat.normalize (target input q)))

theorem ordinaryEvaluator {input modulus : List Bool → List Bool} (hi : input ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (ordinary input modulus) :=
  (CoerciveHomogeneousReaders.ordinaryEvaluator (mem_FP_comp context_FP hi)
    (mem_FP_comp context_FP hm) (selected_unary hi)).precompose _
      (mem_FP_pair id_mem_FP (mem_FP_comp (target_FP hi) BinaryNat.normalize_mem_FP))

noncomputable def leading (input modulus : List Bool → List Bool) : List Bool → List Bool :=
  monomialValue (input ∘ context) (target input) (modulus ∘ context) (fun _ => 0)
    (fun q => 2 * degreeAllowance (input (context q)) + 1) (selected input)
    (fun q => 2 * degreeAllowance (input (context q)) + 2)
noncomputable def homogeneousCoordinate (input modulus : List Bool → List Bool) : List Bool → List Bool :=
  monomialValue (input ∘ context) (target input) (modulus ∘ context)
    (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 1)
noncomputable def pointCoordinate (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ) :
    List Bool → List Bool :=
  monomialValue (input ∘ context) (target input) (modulus ∘ context)
    (fun _ => 0) (fun _ => 1) (coordinate ∘ context) (fun _ => 1)

theorem leading_FP {input modulus : List Bool → List Bool} (hi : input ∈ FP) (hm : modulus ∈ FP) :
    leading input modulus ∈ FP :=
  monomialValue_FP (mem_FP_comp context_FP hi) (target_FP hi) (mem_FP_comp context_FP hm)
    (UnaryFn.const 0) (((UnaryFn.const 2).mul ((degreeAllowance_unary.comp hi).comp context_FP)).add (UnaryFn.const 1))
    (selected_unary hi) (((UnaryFn.const 2).mul ((degreeAllowance_unary.comp hi).comp context_FP)).add (UnaryFn.const 2))

theorem homogeneousCoordinate_FP {input modulus : List Bool → List Bool} (hi : input ∈ FP) (hm : modulus ∈ FP) :
    homogeneousCoordinate input modulus ∈ FP :=
  monomialValue_FP (mem_FP_comp context_FP hi) (target_FP hi) (mem_FP_comp context_FP hm)
    (UnaryFn.const 1) (UnaryFn.const 0) (UnaryFn.const 0) (UnaryFn.const 1)

theorem pointCoordinate_FP {input modulus : List Bool → List Bool} {coordinate : List Bool → ℕ}
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn coordinate) :
    pointCoordinate input modulus coordinate ∈ FP :=
  monomialValue_FP (mem_FP_comp context_FP hi) (target_FP hi) (mem_FP_comp context_FP hm)
    (UnaryFn.const 0) (UnaryFn.const 1) (hc.comp context_FP) (UnaryFn.const 1)

noncomputable def phase (s t : ℕ) (q : List Bool) : Prop :=
  Nat.fromBitsLE (outer q) = s ∧ Nat.fromBitsLE (inner q) = t
noncomputable def zeroRow (q : List Bool) : Prop := Nat.fromBitsLE (row q) = 0
noncomputable def valid (input : List Bool → List Bool) (coordinate : List Bool → ℕ) (q : List Bool) : Prop :=
  coordinate (context q) < dimension (input (context q)) ∧
    Nat.fromBitsLE (row q) < dimension (input (context q)) + 1

private theorem code_eq_fppred {word : List Bool → List Bool} (hw : word ∈ FP) (k : ℕ) :
    FPPred (fun q => Nat.fromBitsLE (word q) = k) := by
  have h := (BinaryNat.le_fppred hw (constFn_mem_FP (BinaryNatCode.encode k))).and
    (BinaryNat.le_fppred (constFn_mem_FP (BinaryNatCode.encode k)) hw)
  apply h.of_iff
  intro q
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact le_antisymm_iff.symm

theorem phase_fppred (s t : ℕ) : FPPred (phase s t) :=
  (code_eq_fppred outer_FP s).and (code_eq_fppred inner_FP t)
theorem zeroRow_fppred : FPPred zeroRow := code_eq_fppred row_FP 0

theorem valid_fppred {input : List Bool → List Bool} {coordinate : List Bool → ℕ}
    (hi : input ∈ FP) (hc : UnaryFn coordinate) : FPPred (valid input coordinate) := by
  have hn := (dimension_unary.comp hi).comp context_FP
  have hr := BinaryNat.lt_fppred row_FP (bits_mem_FP (hn.add (UnaryFn.const 1)))
  have hr' : FPPred (fun q => Nat.fromBitsLE (row q) < dimension (input (context q)) + 1) := by
    apply hr.of_iff
    intro q
    simp only [Nat.fromBitsLE_bits]
  exact (FPPred.lt (hc.comp context_FP) hn).and hr'

noncomputable def maskValue (p : List Bool → Prop) (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  if p q then f q else []

private theorem maskEvaluator {p : List Bool → Prop} {f : List Bool → List Bool}
    (hp : FPPred p) (E : SpaceFunction f) : SpaceFunction (maskValue p f) :=
  ModularResidueReaders.maskEvaluator hp E

noncomputable def coordinatePart (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ) :
    List Bool → List Bool :=
  CoerciveQueryCoefficient.addValue (modulus ∘ context)
    (maskValue (phase 0 1) (homogeneousCoordinate input modulus))
    (CoerciveQueryCoefficient.negValue (modulus ∘ context)
      (maskValue (phase 0 0) (pointCoordinate input modulus coordinate)))

noncomputable def gradientPart (input modulus : List Bool → List Bool) : List Bool → List Bool :=
  CoerciveQueryCoefficient.addValue (modulus ∘ context)
    (maskValue (phase 0 0) (ordinary input modulus))
    (maskValue (phase 1 0) (leading input modulus))

noncomputable def value (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ) (q : List Bool) :
    List Bool :=
  if valid input coordinate q then
    if zeroRow q then coordinatePart input modulus coordinate q else gradientPart input modulus q
  else []


theorem coordinateEvaluator {input modulus : List Bool → List Bool} {coordinate : List Bool → ℕ}
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn coordinate) :
    SpaceFunction (coordinatePart input modulus coordinate) :=
  CoerciveQueryCoefficient.addEvaluator (mem_FP_comp context_FP hm)
    (maskEvaluator (phase_fppred 0 1) (SpaceFunction.ofFP _ (homogeneousCoordinate_FP hi hm)))
    (CoerciveQueryCoefficient.negEvaluator (mem_FP_comp context_FP hm)
      (maskEvaluator (phase_fppred 0 0) (SpaceFunction.ofFP _ (pointCoordinate_FP hi hm hc))))

theorem gradientEvaluator {input modulus : List Bool → List Bool} (hi : input ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (gradientPart input modulus) :=
  CoerciveQueryCoefficient.addEvaluator (mem_FP_comp context_FP hm)
    (maskEvaluator (phase_fppred 0 0) (ordinaryEvaluator hi hm))
    (maskEvaluator (phase_fppred 1 0) (SpaceFunction.ofFP _ (leading_FP hi hm)))

theorem evaluator {input modulus : List Bool → List Bool} {coordinate : List Bool → ℕ}
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn coordinate) :
    SpaceFunction (value input modulus coordinate) := by
  have ER := SpaceFunction.branch (fun q => decide (zeroRow q)) zeroRow_fppred.flag_mem_FP
    (coordinateEvaluator hi hm hc) (gradientEvaluator hi hm)
  have E := SpaceFunction.branch (fun q => decide (valid input coordinate q)) (valid_fppred hi hc).flag_mem_FP
    ER (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [value, decide_eq_true_eq])

end LeanCanny.ETR.CoerciveHomogeneousRowReader
