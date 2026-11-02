/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedRegularLowCoefficient
public import LeanCanny.Algebra.IntegralMixedFramedCriticalDispatcher
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves
public import LeanCanny.Algebra.IntegralMixedFramedScalarLeading
/-! # Actual regular-source leaves at the full framed saved key

A literal source snapshot identifies instructions, including defaults, with
original bounded regular sources. Every coefficient and leading cost follows
from original syntax. No interpreted-prefix or arithmetic evaluator is read.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularFramedOriginalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Snapshot (P : Parameters) (D : Plan P) (R : BoundedFullWriter.Readers) : Prop where
  ambient : ∀ key,P.ambient (pairFst key)=R.dim key+3
  source : ∀ key,HEq (instruction P D key).source (BoundedRegularLowModularTerm.source R key)

private theorem coefficient_transport {a b : ℕ} (ha : a=b+3)
    (S : SpatialSource a) (T : SpatialSource (b+3)) (h : HEq S T) (W k m : ℕ) :
    residueBits ((S.low.coeff (RationalSubstitution.Indexed.exponentVector (a+1)
      (FixedWidthPolynomial.entry W k)) : ℤ) : ZMod m)=
    residueBits ((T.low.coeff (RationalSubstitution.Indexed.exponentVector (b+4)
      (FixedWidthPolynomial.entry W k)) : ℤ) : ZMod m) := by
  cases ha
  cases eq_of_heq h
  rfl

private theorem leading_transport {a b : ℕ} (ha : a=b+3)
    (S : SpatialSource a) (T : SpatialSource (b+3)) (h : HEq S T) : S.leading=T.leading := by
  cases ha
  exact congrArg SpatialSource.leading (eq_of_heq h)

theorem physical (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedFramedPhysicalBits.family P D H))
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (ha : ∀ key,(ETR.TermView.term (R.source key)).arity≤R.dim key) (s : Snapshot P D R) :
    SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P (IntegralMixedFramedPhysicalBits.family P D H)) := by
  let F := IntegralMixedPhysicalTaskBits.family P (IntegralMixedFramedPhysicalBits.family P D H)
  let I := IntegralMixedPhysicalTaskBits.indices P (IntegralMixedFramedPhysicalBits.family P D H)
  have HM := IntegralMixedPhysicalTaskBits.metadata P a _ h
  let saved := IntegralMixedPhysicalTaskBits.saved P
  have E := BoundedRegularLowCoefficient.scalar_evaluator (hR.comp (IntegralMixedPhysicalTaskBits.saved_FP P a))
    (fun q => (F.spatial q).degree.size) I.modulus
    (IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I HM) HM.modulus I.modulus_ne_zero (fun q => ha (saved q))
  apply E.congr
  funext p
  change _ = IntegralMixedPhysicalOriginalBits.scalar F I p
  rw [IntegralMixedOriginalSpatialTermBits.physical_source_scalar]
  unfold IntegralOriginalTermCoefficientBits.scalar
  exact (coefficient_transport (s.ambient (saved (pairFst p)))
    (F.spatial (pairFst p)) (BoundedRegularLowModularTerm.source R (saved (pairFst p)))
    (s.source (saved (pairFst p))) _ _ _).symm

theorem virtual (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (ha : ∀ key,(ETR.TermView.term (R.source key)).arity≤R.dim key) (s : Snapshot P D R) :
    SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P (IntegralMixedFramedHistoryFamilyBits.family P D H)) := by
  let F := IntegralMixedVirtualTaskBits.family P (IntegralMixedFramedHistoryFamilyBits.family P D H)
  let I := IntegralMixedVirtualTaskBits.indices P (IntegralMixedFramedHistoryFamilyBits.family P D H)
  have HM := IntegralMixedVirtualTaskBits.metadata P a _ h
  let saved := IntegralMixedVirtualTaskBits.saved P
  have E := BoundedRegularLowCoefficient.scalar_evaluator (hR.comp (IntegralMixedVirtualTaskBits.saved_FP P a))
    (fun q => (F.spatial q).degree.size) I.modulus
    (IntegralMixedVirtualNativeBits.sourceWidth_unary F I HM) HM.modulus I.modulus_ne_zero (fun q => ha (saved q))
  apply E.congr
  funext p
  change _ = IntegralMixedVirtualOriginalBits.scalar F I p
  rw [IntegralMixedOriginalSpatialTermBits.virtual_source_scalar]
  unfold IntegralOriginalTermCoefficientBits.scalar
  exact (coefficient_transport (s.ambient (saved (pairFst p)))
    (F.spatial (pairFst p)) (BoundedRegularLowModularTerm.source R (saved (pairFst p)))
    (s.source (saved (pairFst p))) _ _ _).symm

theorem leading_FP (P : Parameters) (a : Access P) (D : Plan P)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime) (s : Snapshot P D R) :
    IntegralMixedFramedScalarCellsBits.leadingValue P D∈FP := by
  let saved := IntegralMixedVirtualTaskBits.saved P
  let modulusWord := fun q => BinaryNatCode.encode (modulus P q-1)
  have HM : modulusWord∈FP := ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP
  have E := BoundedRegularLowCoefficient.leading_FP (hR.comp (IntegralMixedVirtualTaskBits.saved_FP P a)) HM
  apply mem_FP_of_eq E
  intro q
  have Hmod : Nat.fromBitsLE (modulusWord q)+1=modulus P q := by
    simp only [modulusWord,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H := modulus_ne_zero P q
    omega
  unfold BoundedRegularLowCoefficient.leadingValue IntegralMixedFramedScalarCellsBits.leadingValue
  rw [Hmod]
  exact congrArg (fun x : ℤ => residueBits (x : ZMod (modulus P q)))
    (leading_transport (s.ambient (saved q)) (instruction P D (saved q)).source
      (BoundedRegularLowModularTerm.source R (saved q)) (s.source (saved q))).symm

theorem leading (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime) (s : Snapshot P D R) :
    IntegralMixedFramedScalarLeadingBits.Primitive P D H := by
  have E := SpaceFunction.ofFP _ (leading_FP P a D R hR s)
  exact E.congr (funext fun q => rfl)

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (ha : ∀ key,(ETR.TermView.term (R.source key)).arity≤R.dim key) (s : Snapshot P D R) :
    IntegralMixedFramedCriticalBits.Controls P D H where
  tables := T
  native := ht
  represents := hr
  physicalOriginal := physical P a D H (IntegralMixedFramedPhysicalBits.inputMetadata P a D H T ht hr) R hR ha s
  virtualOriginal := virtual P a D H (IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H T ht hr) R hR ha s
noncomputable def original_controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (n radius : List Bool → ℕ) (t : List Bool → ETR.Term)
    (hn : UnaryFn n) (ht : (fun key => (t key).toData.toBits)∈FP) (hR : BinaryFn radius)
    (ha : ∀ key,(t key).arity≤n key)
    (s : Snapshot P D (BoundedRegularLowCoefficient.readers n t radius)) :
    IntegralMixedFramedCriticalBits.Controls P D H :=
  controls P a D H T hT hr (BoundedRegularLowCoefficient.readers n t radius)
    (BoundedRegularLowCoefficient.readers_native hn ht hR)
    (fun key => by simpa only [BoundedRegularLowCoefficient.readers,ETR.TermView.term_toBits] using ha key) s
end LeanCanny.Algebra.BoundedRegularFramedOriginalBits
