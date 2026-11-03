/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowReadback
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderReadback
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowPullback
public import LeanCanny.Encoding.IntegralFramedPhysicalSquare
/-! # The total original-control reader reads every literal full physical row -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength)
open IntegralMixedFramedPhysicalRowTransport
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedPhysicalIndex (arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family
  IntegralMixedFramedPhysicalBlockBits.poweredRowPolynomial value

theorem lifted_count (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    arity (commands (lifted P) (liftedPlan P D) (liftedKey key q))=count P D key q :=by
  have H:=IntegralMixedFramedPhysicalRowPullback.count_pullback P D pairFst
    IntegralMixedFramedModulusPacket.extra (liftedKey key q)
  have HE : arity (commands P D (IntegralMixedFramedRootPullback.key pairFst (liftedKey key q)))=
      arity (commands P D (saved key q)) :=by
    apply Nat.le_antisymm
    · exact key_count_le P D _ _ (projected_root key q) (projected_prefix P key q).le
    · exact key_count_le P D _ _ (projected_root key q).symm (projected_prefix P key q).symm.le
  exact H.trans HE

theorem lifted_coefficient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (key : List Bool→List Bool) (q : List Bool) (r : ℕ) (hr : r<count P D key q) (V t : ℕ) :
    (indexedRow (lifted P) (liftedPlan P D) Jnew (liftedKey key q)
      ⟨r,hr.trans_eq (lifted_count P D key q).symm⟩).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t)=
    (indexedRow P D J (saved key q) ⟨r,hr⟩).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t) :=by
  apply IntegralMixedFramedPhysicalFreshRowSemantics.native_coefficient_of_natural
    (lifted_count P D key q) _ _ ?_ V t
  have HI : r<arity (commands P D (IntegralMixedFramedRootPullback.key pairFst (liftedKey key q))) :=
    (hr.trans_eq (lifted_count P D key q).symm).trans_eq
      (IntegralMixedFramedPhysicalRowPullback.count_pullback P D pairFst IntegralMixedFramedModulusPacket.extra _)
  have HE:=(IntegralMixedFramedPhysicalRowPullback.row_pullback P D pairFst
    IntegralMixedFramedModulusPacket.extra (liftedKey key q) r).trans
    (key_rows P D (IntegralMixedFramedRootPullback.key pairFst (liftedKey key q)) (saved key q)
      (projected_root key q) (projected_prefix P key q).le r HI).symm
  exact (keyRow_family (lifted P) (liftedPlan P D) Jnew (liftedKey key q) r
    (hr.trans_eq (lifted_count P D key q).symm)).symm.trans
    (HE.trans (keyRow_family P D J (saved key q) r hr))

theorem full_count_pos (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P (saved key) q) :
    ∀q,0<count P D key q :=by
  intro q
  have HP : 0<(IntegralMixedFramedHistoryFamilyBits.family P D J).birth (saved key q) :=
    (hpos q).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth P D J (saved key q)).symm
  exact HP.trans_le (IntegralFramedPhysicalSquare.birth_le_count P D J (saved key q))

noncomputable def literal (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hpos : ∀q,0<count P D key q) (q : List Bool) :=
  residueBits (((indexedRow P D J (saved key q) ⟨row P D key q,row_lt P D key hpos q⟩).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (width q) (Nat.fromBitsLE (SquareSampleInput.rankWord q)))) :
      ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q)+1))


theorem fresh_literal (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (key : List Bool→List Bool) (hpos : ∀q,0<count P D key q) (q : List Bool)
    (hs : ¬IntegralMixedFramedPhysicalRowSelector.IsScalar P T
      (pair (saved key q) (BinaryNatCode.encode (row P D key q)))) :
    IntegralMixedFramedPhysicalFreshRowBits.value (lifted P) (liftedPlan P D) Jnew
      c.critical.tables c.critical.represents (width∘origin) (SquareSampleInput.rankWord∘origin) (datum P D key q)=
      literal P D J key hpos q :=by
  have HR:=row_lt P D key hpos q
  have HN : row P D key q<IntegralMixedFramedPhysicalRowSelector.fullArity (lifted P) c.critical.tables
      (pair (liftedKey key q) (BinaryNatCode.encode (row P D key q))) :=
    (HR.trans_eq (lifted_count P D key q).symm).trans_eq
      (native_full_count (lifted P) (liftedPlan P D) Jnew c.critical.tables c.critical.represents
        (liftedKey key q) (row P D key q)).symm
  have HS : ¬IntegralMixedFramedPhysicalRowSelector.IsScalar (lifted P) c.critical.tables
      (pair (liftedKey key q) (BinaryNatCode.encode (row P D key q))) :=
    fun h=>hs ((scalar_predicate P D J T hT Jnew c.critical.tables c.critical.represents key q).mp h)
  have HM : Nat.fromBitsLE (SquareSampleInput.modulusWord q)+1≤numericCap (lifted P) (pairFst (liftedKey key q)) :=by
    simpa only [datum_key,datum_modulus] using caller_budget P D key q
  have HV:=IntegralMixedFramedPhysicalFreshRowSemantics.value_packet (lifted P) (liftedPlan P D) Jnew
    c.critical.tables c.critical.represents (liftedKey key q) (row P D key q) HN HS
    (SquareSampleInput.modulusWord q) (width∘origin) (SquareSampleInput.rankWord∘origin) HM
  have HD : pair (pair (liftedKey key q) (BinaryNatCode.encode (row P D key q)))
      (SquareSampleInput.modulusWord q)=datum P D key q :=rfl
  rw [HD,width_read,target_read] at HV
  exact HV.trans (congrArg (fun z : ℤ=>residueBits (z : ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q)+1)))
    (lifted_coefficient P D J Jnew key q (row P D key q) HR (width q) (Nat.fromBitsLE (SquareSampleInput.rankWord q))))

theorem scalar_literal (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key : List Bool→List Bool) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P (saved key) q) (q : List Bool)
    (hs : IntegralMixedFramedPhysicalRowSelector.IsScalar P T
      (pair (saved key q) (BinaryNatCode.encode (row P D key q)))) :
    FixedWidthRowBits.value (count P D key) width
      (IntegralMixedFramedPhysicalScalarRowBits.polynomial P D J T hT (saved key) (row P D key) hpos)
      SquareSampleInput.rankWord SquareSampleInput.modulusWord q=
      literal P D J key (full_count_pos P D J key hpos) q :=by
  have HR:=row_lt P D key (full_count_pos P D J key hpos) q
  have HN : row P D key q<IntegralMixedFramedPhysicalRowSelector.fullArity P T
      (pair (saved key q) (BinaryNatCode.encode (row P D key q))) :=
    HR.trans_eq (native_full_count P D J T hT (saved key q) (row P D key q)).symm
  have HP:=IntegralMixedFramedPhysicalScalarRowBits.polynomial_actual P D J T hT (saved key) (row P D key) hpos q HN hs
  unfold FixedWidthRowBits.value literal
  rw [HP]
  rfl

theorem value_literal (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (key : List Bool→List Bool) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P (saved key) q) (q : List Bool) :
    value P D J T hT Jnew c key hpos q=literal P D J key (full_count_pos P D J key hpos) q :=by
  unfold value
  split_ifs with hs
  · exact scalar_literal P D J T hT key hpos q hs
  · exact fresh_literal P D J T hT Jnew c key (full_count_pos P D J key hpos) q hs

theorem literal_rowCoefficient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hb : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D J).birth (key c))
    (q : List Bool) :
    literal P D J key (fun q=>(hpos (SquareSampleInput.source q)).trans_le
      (IntegralFramedPhysicalSquare.birth_le_count P D J (saved key q))) q=
      SquareSampleInput.rowCoefficient (IntegralFramedPhysicalSquare.input P D J L F C hb key hpos) q :=by
  rfl


theorem scalar_positive (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D J).birth (key c)) :
    ∀q,0<IntegralMixedFramedRowBits.count P (saved key) q :=by
  intro q
  exact (hpos (SquareSampleInput.source q)).trans_eq
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D J (saved key q))

theorem value_rowCoefficient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Jnew)
    (L F C : List Bool→ℕ) (hb : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D J).birth (key c))
    (q : List Bool) :
    value P D J T hT Jnew c key (scalar_positive P D J key hpos) q=
      SquareSampleInput.rowCoefficient (IntegralFramedPhysicalSquare.input P D J L F C hb key hpos) q :=
  (value_literal P D J T hT Jnew c key (scalar_positive P D J key hpos) q).trans
    (literal_rowCoefficient P D J L F C hb key hpos q)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderBits
