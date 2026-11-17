/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceNormObjectiveEvaluation
public import LeanCanny.CountingHierarchy.QuotientDeterminantEvaluation

/-! # Constructing the final quotient determinant at twenty-one additional levels -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def codedFiniteCriticalDeterminant {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (data : List (ℕ × ℕ)) (e : ℕ) : ℤ :=
  finiteCriticalDeterminant d b F hF (sourceCodedLabel n d data) (sourceNormShift n d e)

@[expose] def sourceNormTraceDegreeBound (n d b : ℕ) : ℕ :=
  (d + 1) ^ n * criticalNormObjectiveDegreeBound n d b + n * d

@[expose] def sourceNormPrimeCutoff (n d b : ℕ) : ℕ :=
  criticalCoefficientPrimeCutoff n d + (d + 1) * (sourceNormTraceDegreeBound n d b + 1) + 1 +
    (d + 1) ^ n + (d + 1) ^ n * (d + 1) ^ n + 6

@[expose] noncomputable def sourceNormDeterminantValue (p n d b e : ℕ) (data : List (ℕ × ℕ))
    (value : List ℕ → ℕ) : ℕ :=
  quotientDeterminantValue p n (d + 1) (sourceNormTraceDegreeBound n d b)
    (fun z => sourceNormObjectiveValue p n d b e z data value)
    (fun z => criticalJacobianValue p n (d + 1) (criticalParameterResidue p n d b) z value)
    (fun i z => criticalLowerValue p n (d + 1) (criticalParameterResidue p n d b) i z value)

variable {α : Type} {enc : α ↪ List Bool}

theorem sourceNormTraceDegreeBound_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => sourceNormTraceDegreeBound (n w) (d w) (b w)) enc encNat :=
  ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn)
      (criticalNormObjectiveDegreeBound_polyTime hn hd hb))
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.unary_to_binary.comp hn) hd)

theorem sourceNormPrimeCutoff_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => sourceNormPrimeCutoff (n w) (d w) (b w)) enc encNat := by
  have hell := ComputableInPolyTime.binary_add' hd (.const 1)
  have hD := ComputableInPolyTime.binary_pow' hell hn
  have hgrid := ComputableInPolyTime.binary_mul' hell
    (ComputableInPolyTime.binary_add' (sourceNormTraceDegreeBound_polyTime hn hd hb) (.const 1))
  have hfirst := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' (criticalCoefficientPrimeCutoff_polyTime hn hd) hgrid) (.const 1)
  exact ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' hfirst hD) (ComputableInPolyTime.binary_mul' hD hD)) (.const 6)

/-- One source evaluator constructs every stage. Neither quotient matrix,
characteristic coefficients, derivatives nor label polynomials are inputs. -/
theorem sourceNormDeterminantValue_mem {a : ℕ}
    (E : Decoder enc) {p n d b e : α → ℕ} {data : α → List (ℕ × ℕ)}
    {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (he : ComputableInPolyTime e enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => sourceNormDeterminantValue (p w) (n w) (d w) (b w) (e w) (data w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 21) enc encNat := by
  have hell := ComputableInPolyTime.binary_add' hd (.const 1)
  have hu := criticalParameterResidue_polyTime hp hn hd hb
  have haccess := criticalEvaluationAccess_mem E hp hn hell hu hv
  have hf := ComputableInPolyTime.fst enc (encList encNat)
  have hz := ComputableInPolyTime.snd enc (encList encNat)
  have hv' := CountingFunction.preprocess
    (input := encPair (encPair enc (encList encNat)) (encList encNat)) hv
    (g := fun q : (α × List ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hobj := sourceNormObjectiveValue_mem (Decoder.pair E (Decoder.list Decoder.nat))
    (hp.comp hf) (hn.comp hf) (hd.comp hf) (hb.comp hf) (he.comp hf) hz (hdata.comp hf) hv'
  have hdet := quotientDeterminantValue_mem E hp hn hell (sourceNormTraceDegreeBound_polyTime hn hd hb)
    hobj (CountingFunction.mono (by omega : a + 1 ≤ a + 13) haccess.2.1)
    (CountingFunction.mono (by omega : a + 1 ≤ a + 13) haccess.2.2)
  simpa only [sourceNormDeterminantValue, Nat.add_assoc, Function.comp_apply] using hdet

end LeanCanny.CountingHierarchy
