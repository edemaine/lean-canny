/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.BoundedRegularPermutedCoefficient
public import LeanCanny.Algebra.IntegralMixedFramedCriticalDispatcher
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves
public import LeanCanny.Algebra.IntegralMixedFramedScalarLeading
/-! # Permuted regular-source leaves at the full framed saved key

A literal source snapshot identifies instructions, including defaults, with
original bounded regular sources. Every coefficient and leading cost follows
from original syntax. No interpreted-prefix or arithmetic evaluator is read.
-/
@[expose] public section
namespace LeanCanny.Algebra.BoundedRegularFramedPermutedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Permutation (R : BoundedFullWriter.Readers) where
  permutation : (key : List Bool) → Equiv.Perm (Fin (R.dim key+4))
  inverse : List Bool → List Bool
  native : inverse∈FP
  packet : ∀ key (i : Fin (R.dim key+4)), inverse (pair key (BinaryNatCode.encode i.val))=
    BinaryNatCode.encode ((permutation key).symm i).val

noncomputable def frozen (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (mask : List Bool → List Bool) (hm : mask∈FP) : Permutation R where
  permutation := BoundedRegularPermutedCoefficient.frozenPermutation R mask
  inverse := FixedWidthPermutationBits.frozenInverse (fun key => R.dim key+4) mask
  native := FixedWidthPermutationBits.frozenInverse_FP _ (hR.dim.add (UnaryFn.const 4)) mask hm
  packet := FixedWidthPermutationBits.frozenInverse_packet _ mask

structure Snapshot (P : Parameters) (D : Plan P) (R : BoundedFullWriter.Readers) (e : Permutation R) : Prop where
  ambient : ∀ key,P.ambient (pairFst key)=R.dim key+3
  source : ∀ key,HEq (instruction P D key).source
    (BoundedRegularPermutedCoefficient.source R e.permutation key)

def pullInverse (saved inverse : List Bool → List Bool) (z : List Bool) :=
  inverse (pair (saved (pairFst z)) (pairSnd z))
theorem pullInverse_FP {saved inverse : List Bool → List Bool} (hs : saved∈FP) (hi : inverse∈FP) : pullInverse saved inverse∈FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hs) pairSnd_mem_FP) hi

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
    (ha : ∀ key,(ETR.TermView.term (R.source key)).arity≤R.dim key) (e : Permutation R) (s : Snapshot P D R e) :
    SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P (IntegralMixedFramedPhysicalBits.family P D H)) := by
  let F := IntegralMixedPhysicalTaskBits.family P (IntegralMixedFramedPhysicalBits.family P D H)
  let I := IntegralMixedPhysicalTaskBits.indices P (IntegralMixedFramedPhysicalBits.family P D H)
  have HM := IntegralMixedPhysicalTaskBits.metadata P a _ h
  let saved := IntegralMixedPhysicalTaskBits.saved P
  have E := BoundedRegularPermutedCoefficient.scalar_evaluator (R.comp saved) (fun q => e.permutation (saved q))
    (hR.comp (IntegralMixedPhysicalTaskBits.saved_FP P a)) (fun q => (F.spatial q).degree.size) I.modulus
    (IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I HM) HM.modulus I.modulus_ne_zero
    (pullInverse saved e.inverse) (pullInverse_FP (IntegralMixedPhysicalTaskBits.saved_FP P a) e.native)
    (fun q i => by
      simp only [pullInverse,pairFst_pair,pairSnd_pair]
      exact e.packet (saved q) i) (fun q => ha (saved q))
  apply E.congr
  funext p
  change _ = IntegralMixedPhysicalOriginalBits.scalar F I p
  rw [IntegralMixedOriginalSpatialTermBits.physical_source_scalar]
  unfold IntegralOriginalTermCoefficientBits.scalar
  exact (coefficient_transport (s.ambient (saved (pairFst p)))
    (F.spatial (pairFst p)) (BoundedRegularPermutedCoefficient.source R e.permutation (saved (pairFst p)))
    (s.source (saved (pairFst p))) _ _ _).symm

theorem virtual (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (ha : ∀ key,(ETR.TermView.term (R.source key)).arity≤R.dim key) (e : Permutation R) (s : Snapshot P D R e) :
    SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P (IntegralMixedFramedHistoryFamilyBits.family P D H)) := by
  let F := IntegralMixedVirtualTaskBits.family P (IntegralMixedFramedHistoryFamilyBits.family P D H)
  let I := IntegralMixedVirtualTaskBits.indices P (IntegralMixedFramedHistoryFamilyBits.family P D H)
  have HM := IntegralMixedVirtualTaskBits.metadata P a _ h
  let saved := IntegralMixedVirtualTaskBits.saved P
  have E := BoundedRegularPermutedCoefficient.scalar_evaluator (R.comp saved) (fun q => e.permutation (saved q))
    (hR.comp (IntegralMixedVirtualTaskBits.saved_FP P a)) (fun q => (F.spatial q).degree.size) I.modulus
    (IntegralMixedVirtualNativeBits.sourceWidth_unary F I HM) HM.modulus I.modulus_ne_zero
    (pullInverse saved e.inverse) (pullInverse_FP (IntegralMixedVirtualTaskBits.saved_FP P a) e.native)
    (fun q i => by
      simp only [pullInverse,pairFst_pair,pairSnd_pair]
      exact e.packet (saved q) i) (fun q => ha (saved q))
  apply E.congr
  funext p
  change _ = IntegralMixedVirtualOriginalBits.scalar F I p
  rw [IntegralMixedOriginalSpatialTermBits.virtual_source_scalar]
  unfold IntegralOriginalTermCoefficientBits.scalar
  exact (coefficient_transport (s.ambient (saved (pairFst p)))
    (F.spatial (pairFst p)) (BoundedRegularPermutedCoefficient.source R e.permutation (saved (pairFst p)))
    (s.source (saved (pairFst p))) _ _ _).symm

theorem leading_FP (P : Parameters) (a : Access P) (D : Plan P)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime) (e : Permutation R) (s : Snapshot P D R e) :
    IntegralMixedFramedScalarCellsBits.leadingValue P D∈FP := by
  let saved := IntegralMixedVirtualTaskBits.saved P
  let modulusWord := fun q => BinaryNatCode.encode (modulus P q-1)
  have HM : modulusWord∈FP := ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP
  have E := BoundedRegularPermutedCoefficient.leading_FP (R.comp saved) (fun q => e.permutation (saved q))
    (hR.comp (IntegralMixedVirtualTaskBits.saved_FP P a)) HM
  apply mem_FP_of_eq E
  intro q
  have Hmod : Nat.fromBitsLE (modulusWord q)+1=modulus P q := by
    simp only [modulusWord,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H := modulus_ne_zero P q
    omega
  unfold IntegralMixedFramedScalarCellsBits.leadingValue
  rw [Hmod]
  exact congrArg (fun x : ℤ => residueBits (x : ZMod (modulus P q)))
    (leading_transport (s.ambient (saved q)) (instruction P D (saved q)).source
      (BoundedRegularPermutedCoefficient.source R e.permutation (saved q)) (s.source (saved q))).symm

theorem leading (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime) (e : Permutation R) (s : Snapshot P D R e) :
    IntegralMixedFramedScalarLeadingBits.Primitive P D H := by
  have E := SpaceFunction.ofFP _ (leading_FP P a D R hR e s)
  exact E.congr (funext fun q => rfl)

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (ha : ∀ key,(ETR.TermView.term (R.source key)).arity≤R.dim key) (e : Permutation R) (s : Snapshot P D R e) :
    IntegralMixedFramedCriticalBits.Controls P D H where
  tables := T
  native := ht
  represents := hr
  physicalOriginal := physical P a D H (IntegralMixedFramedPhysicalBits.inputMetadata P a D H T ht hr) R hR ha e s
  virtualOriginal := virtual P a D H (IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H T ht hr) R hR ha e s
end LeanCanny.Algebra.BoundedRegularFramedPermutedBits
