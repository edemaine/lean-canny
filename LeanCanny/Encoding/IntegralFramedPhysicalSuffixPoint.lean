/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots

/-! # Full suffix tests read the literal raw scalar tuple once -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem extend_cast {a b d : ℕ} (h : d+a=b) (z : Fin b→ℝ) (i : Fin a) :
    z (Fin.cast h (FixedWidthSuffixLiftBits.shift d i))=IntegralMixedFramedBankObservation.extend z (d+i.val) :=by
  have HI : d+i.val<b :=by have HH:=i.isLt;omega
  unfold IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HI]
  rfl

variable (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
  (R : SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B))
  (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w)

noncomputable def rawTuple : ℕ→ℝ :=IntegralMixedFramedBankObservation.extend
  (IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    B.key B.positive c w hv)

theorem scalar_value (i : Fin (R.arity c d)) :
    (SquareSampleCompleteVertices.candidate (input B) c w hv).val (columns B T hr R c d i)=
      IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hv (Fin.cast (R.dimension c d) (FixedWidthSuffixLiftBits.shift (R.newer c d) i)) :=by
  rw [IntegralFramedPhysicalSquare.scalarTuple_map]
  unfold columns IntegralMixedFramedScalarEmbedding.scalarMap
  rw [IntegralMixedFramedPhysicalIndex.nativeScalarColumn_eq]
  rfl

theorem scalar_value_raw (i : Fin (R.arity c d)) :
    (SquareSampleCompleteVertices.candidate (input B) c w hv).val (columns B T hr R c d i)=
      rawTuple B c w hv (R.newer c d+i.val) :=by
  rw [scalar_value B T hr R c w d hv i]
  exact extend_cast (R.dimension c d) _ i

theorem packet_scalar :
    value B T hr R (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((R.polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
          B.key B.positive c w hv (Fin.cast (R.dimension c d) (FixedWidthSuffixLiftBits.shift (R.newer c d) i))))) :=by
  rw [packet B T hr R c w d hv]
  apply congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v))
  apply congrArg ((R.polynomial c d).eval₂ (Int.castRingHom ℝ))
  funext i
  exact scalar_value B T hr R c w d hv i

theorem packet_raw :
    value B T hr R (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((R.polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>rawTuple B c w hv (R.newer c d+i.val)))) :=by
  rw [packet B T hr R c w d hv]
  apply congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v))
  apply congrArg ((R.polynomial c d).eval₂ (Int.castRingHom ℝ))
  funext i
  exact scalar_value_raw B T hr R c w d hv i

end LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
