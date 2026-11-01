/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualSweepSource
public import LeanCanny.Algebra.IntegralEulerSemanticAccess
public import LeanCanny.Algebra.IntegralCriticalFlatGenericEuler
public import LeanCanny.Algebra.IntegralCriticalFlatDerivative
/-! # Native metadata for the actual virtual nilpotent source

Only original numeric fields are read. The coefficient, height, denominator,
and leading components of the access record are their actual semantic values;
this construction gives none of those components an evaluator certificate.
The backend does not interpret a virtual source as a physical script birth.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedCutSource IntegralMixedVirtualSweepSource
set_option backward.isDefEq.respectTransparency false

structure Metadata (F : Family) (I : Indices F) : Prop where
  ambient : UnaryFn F.ambient
  birth : UnaryFn F.birth
  width : UnaryFn F.width
  offset : UnaryFn (fun q => (F.rule q).critical.offset.val)
  degree : BinaryFn (fun q => (F.spatial q).degree)
  objective : BinaryFn (fun q => (F.rule q).critical.objective)
  target : BinaryFn I.target
  row : BinaryFn (fun q => (I.row q).val)
  col : BinaryFn (fun q => (I.col q).val)
  modulus : BinaryFn I.modulus
  coordinate : BinaryFn (fun q => (I.coordinate q).val)
  coefficientIndex : BinaryFn I.coefficientIndex

theorem rank_binary (F : Family) (I : Indices F) (h : Metadata F I) :
    BinaryFn (fun q => count (F.birth q + 1) (F.width q)) :=
  ((BinaryFn.const 2).powUnary h.width).powUnary (h.birth.add (UnaryFn.const 1))

theorem sourceWidth_unary (F : Family) (I : Indices F) (h : Metadata F I) :
    UnaryFn (fun q => (F.spatial q).degree.size) :=
  (UnaryFn.length h.degree.bits_mem_FP).of_eq (fun _ => Nat.size_eq_bits_len _)

theorem free_unary (F : Family) (I : Indices F) (h : Metadata F I) :
    UnaryFn (fun q => F.ambient q - (F.rule q).critical.offset.val + 1) :=
  (h.ambient.sub h.offset).add (UnaryFn.const 1)

theorem semantic_controls (F : Family) (I : Indices F) (h : Metadata F I) :
    IntegralEulerSemanticBits.Controls (euler F I) where
  arity := h.ambient.add (UnaryFn.const 1)
  free := free_unary F I h
  offset := h.offset
  sourceWidth := sourceWidth_unary F I h
  targetWidth := UnaryFn.const 0
  rank := rank_binary F I h
  allowance := h.degree
  target := h.target
  row := h.row
  col := h.col
  modulus := h.modulus
  degree := h.degree
  objective := h.objective.mod (BinaryFn.ofUnary (free_unary F I h))

noncomputable def access (F : Family) (I : Indices F) (h : Metadata F I) :
    IntegralEulerBits.Access (euler F I) :=
  IntegralEulerSemanticBits.access (euler F I) (semantic_controls F I h)

noncomputable def criticalAccess (F : Family) (I : Indices F) (h : Metadata F I) :
    IntegralClearedCriticalBits.Access (source F I) :=
  IntegralCanonicalCriticalBits.access (euler F I) (access F I h)
    I.coordinate I.coefficientIndex h.coordinate h.coefficientIndex

noncomputable abbrev arithmetic (F : Family) (I : Indices F) := (source F I).toEuler

noncomputable def arithmeticAccess (F : Family) (I : Indices F) (h : Metadata F I) :
    IntegralEulerBits.Access (arithmetic F I) := (criticalAccess F I h).toEuler

theorem denominator_eq (F : Family) (I : Indices F) (h : Metadata F I) (q : List Bool) :
    (arithmeticAccess F I h).denominator q = residueBits (denominator F q : ZMod (I.modulus q)) := rfl

theorem leading_eq (F : Family) (I : Indices F) (h : Metadata F I) (q : List Bool) :
    (arithmeticAccess F I h).leading q = residueBits ((F.spatial q).leading : ZMod (I.modulus q)) := rfl

-- Existing controller certificates accept this backend directly; no physical
-- script, creating-birth guard, or coefficient/height space premise is present.
theorem derivative_certificates (P : IntegralCriticalHistoryTask.Parameters)
    (a : IntegralCriticalHistoryTask.Access P) (F : Family) (I : Indices F) (h : Metadata F I) :
    (IntegralCriticalFlatDerivativeBits.controller P
      (IntegralCriticalFlatDerivativeBits.eulerSource P (arithmetic F I))).Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  IntegralCriticalFlatDerivativeBits.certificates P a _
    (IntegralCriticalFlatDerivativeBits.eulerAccess P a (arithmetic F I) (arithmeticAccess F I h))

theorem lower_controls (P : IntegralCriticalHistoryTask.Parameters)
    (a : IntegralCriticalHistoryTask.Access P) (F : Family) (I : Indices F) (h : Metadata F I) :
    (IntegralCriticalFlatGenericEulerBits.lowerProgram P (arithmetic F I)).Controls :=
  IntegralCriticalFlatGenericEulerBits.lower_controls P a (arithmetic F I) (arithmeticAccess F I h)

theorem objective_certificates (P : IntegralCriticalHistoryTask.Parameters)
    (a : IntegralCriticalHistoryTask.Access P) (F : Family) (I : Indices F) (h : Metadata F I) :
    (IntegralCriticalFlatGenericEulerBits.objectiveProgram P (arithmetic F I)).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralCriticalFlatGenericEulerBits.objective_certificates P a (arithmetic F I) (arithmeticAccess F I h)
end LeanCanny.Algebra.IntegralMixedVirtualNativeBits
