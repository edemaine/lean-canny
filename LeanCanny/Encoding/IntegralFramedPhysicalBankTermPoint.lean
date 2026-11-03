/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermSource
public import LeanCanny.Encoding.IntegralFramedPhysicalIntegerLeaves
/-! # Common-cleared term signs on the same full retained-bank point

The raw scalar injection is applied before the clearing polynomial is
evaluated. Thus its original powers occur once, and its positive clearing
factor gives precisely Term.eval on the actual full bank quotients.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalBankTerm
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedPhysicalIndex (nativeScalarColumn)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (B : Bank) (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w)

noncomputable def rawScalar : Fin ((IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count)→ℝ :=
  fun i=>IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv
    (nativeScalarColumn B.parameters B.plan B.data T hr (B.key c) i)
noncomputable def env : ℕ→ℝ :=LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point
  B.parameters B.plan B.data (B.key c) (rawScalar B T hr c w hv)

theorem packet (word : List Bool→List Bool) (d : List Bool) :
    value B T hr word (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (B.key c)).eval (env B T hr c w hv))) :=by
  rw [value,test,SquareSampleCompleteEmbeddedPolynomialTest.packet _ _ _ c w d hv]
  exact congrArg InfinitesimalSign.encode (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.sign
    B.parameters B.plan B.data word (B.key c) (rawScalar B T hr c w hv))

theorem point_rawScalar (i : Fin ((IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count)) :
    LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
      ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).state (B.key c))
      (rawScalar B T hr c w hv) i=
    IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv i :=by
  rw [IntegralFramedPhysicalSquare.point_column B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv T hr i]
  rfl

theorem env_coordinate (i : ℕ) (hi : i<(IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count) :
    env B T hr c w hv i=IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv
      (IntegralFramedPhysicalIntegerLeaves.coordinate B.parameters B.plan B.data B.key B.positive c (BinaryNatCode.encode i)) :=by
  unfold env LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point
  rw [dite_eq_left hi]
  have HE : (⟨IntegralMixedFramedBankTermBits.reverseIndex B.parameters B.plan B.data (B.key c) i,
      IntegralMixedFramedBankTermBits.reverse_lt B.parameters B.plan B.data (B.key c) i hi⟩ :
      Fin ((IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count))=
      IntegralFramedPhysicalIntegerLeaves.coordinate B.parameters B.plan B.data B.key B.positive c (BinaryNatCode.encode i) :=by
    apply Fin.ext
    simp only [IntegralMixedFramedBankTermBits.reverseIndex,IntegralFramedPhysicalIntegerLeaves.coordinate,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rfl
  rw [HE]
  exact point_rawScalar B T hr c w hv _

end LeanCanny.Encoding.IntegralFramedPhysicalBankTerm
