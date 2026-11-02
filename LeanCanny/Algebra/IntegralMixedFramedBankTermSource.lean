/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankSnapshot
public import LeanCanny.ETR.EncodedRationalSubstitution
/-! # Original-root term syntax and fixed coordinate encoding metadata

The arithmetic term is read at the complete original root of a saved key.
Its native syntax size and actual prefix dimensions determine one dense
encoding width. No source degree or coefficient reader is a premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

def wordAt (word : List Bool → List Bool) (key : List Bool) := word (pairFst key)
theorem wordAt_FP (word : List Bool → List Bool) (hw : word∈FP) : wordAt word∈FP :=
  mem_FP_comp pairFst_mem_FP hw
noncomputable def source (word : List Bool → List Bool) := ETR.RationalSubstitutionBits.Source.ofTerm (wordAt word)
noncomputable def size (word : List Bool → List Bool) (key : List Bool) := ((source word).syntax key).toData.size

theorem size_unary (word : List Bool → List Bool) (hw : word∈FP) : UnaryFn (size word) :=
  (UnaryFn.length (mem_FP_comp (wordAt_FP word hw) ETR.TermView.normalize_mem_FP)).of_eq
    (fun key => by simp only [Function.comp_apply,ETR.TermView.normalize_eq_term,Data.length_toBits]; rfl)

noncomputable def maxPower (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :=
  UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key)) ((atKey P D H key).count-1)

theorem maxPower_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    BinaryFn (maxPower P D H) :=
  UniformIntegralPowerSchedule.birth_binary ((a.cap.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (a.width.comp pairFst_mem_FP))
    ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).sub (UnaryFn.const 1))

noncomputable def degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) := size word key*(2*size word key)*maxPower P D H key
theorem degree_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (hw : word∈FP) : BinaryFn (degree P D H word) :=
  ((BinaryFn.ofUnary (size_unary word hw)).mul ((BinaryFn.const 2).mul (BinaryFn.ofUnary (size_unary word hw)))).mul
    (maxPower_binary P a D H)

noncomputable def width (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) := (degree P D H word key).size
theorem width_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (hw : word∈FP) : UnaryFn (width P D H word) :=
  (UnaryFn.length (degree_binary P a D H word hw).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

noncomputable def reverseIndex (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) := (atKey P D H key).count-1-i

noncomputable def numerator (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) (i : ℕ) : Polynomial ℤ :=
  if i<(atKey P D H key).count then
    Polynomial.monomial
      (UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key)) i*
        2^(reverseIndex P D H key i*width P D H word key))
      ((atKey P D H key).cofactor (reverseIndex P D H key i))
  else 0

noncomputable def denominator (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (_i : ℕ) : Polynomial ℤ := Polynomial.C ((atKey P D H key).common)

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits
