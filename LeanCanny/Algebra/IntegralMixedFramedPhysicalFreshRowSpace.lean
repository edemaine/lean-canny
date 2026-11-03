/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBirthQuery
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockRowExact
public import LeanCanny.Algebra.FixedWidthLocalEmbeddingSpace
/-! # Total native fresh-row coefficients at terminal full-column queries

The original headers select the creator. Exponent blocks stay in the external
datum. A local embedding guard rejects later-column monomials. Its finite
injection is needed only in the current semantic readback, never as input cost.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value IntegralCriticalHistoryTask.modulus
  IntegralCriticalFlatCoordinateQuery.writer IntegralMixedFramedPhysicalBits.family
  IntegralMixedFramedPhysicalBlockBits.poweredRowPolynomial MvPolynomial.rename MvPolynomial.pderiv
  IntegralMixedFramedPhysicalBirthQueryBits.base IntegralMixedFramedPhysicalBirthQueryBits.packet
  IntegralMixedFramedCompanionQueryBits.query

noncomputable abbrev base (P : Parameters) (D : Plan P)
    (T : IntegralMixedHeaderTablesBits.Tables) :=IntegralMixedFramedPhysicalBirthQueryBits.base P D T
abbrev localIndex (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables) :=
  IntegralMixedFramedPhysicalRowSelector.localRow P T∘pairFst
noncomputable abbrev prepared (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) :=
  IntegralMixedFramedPhysicalBlockBits.prepared P D J (base P D T) (localIndex P T)
noncomputable abbrev smallCount (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) :=IntegralMixedFramedPhysicalBlockBits.fullCount P D J (prepared P D J T)
noncomputable abbrev largeCount (P : Parameters) (D : Plan P) :=
  IntegralMixedFramedFullScalarRowBits.fullCount P D (pairFst∘pairFst)
noncomputable abbrev polynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T) :=
  IntegralMixedFramedPhysicalBlockBits.poweredRowPolynomial P D J T hr (prepared P D J T)
    (IntegralMixedFramedPhysicalBlockBits.rowSelected P D J (base P D T) (localIndex P T)) (localIndex P T)
    (IntegralMixedFramedPhysicalBlockBits.prepared_selected_lt P D J (base P D T) (localIndex P T))

noncomputable def value (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (V : List Bool→ℕ) (target : List Bool→List Bool) :=
  FixedWidthLocalEmbeddingBits.value (smallCount P D J T) (largeCount P D) V target pairSnd
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘prepared P D J T) (polynomial P D J T hr)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (value P D J c.critical.tables c.critical.represents V target) := by
  have HB:=IntegralMixedFramedPhysicalBirthQueryBits.base_FP P a D J c.critical.tables c.critical.native c.critical.represents
  have HI : UnaryFn (localIndex P c.critical.tables):=
    (IntegralMixedFramedPhysicalRowSelector.localRow_unary P a c.critical.tables c.critical.native).comp pairFst_mem_FP
  have HP:=IntegralMixedFramedPhysicalBlockBits.prepared_FP P a D J c (base P D c.critical.tables) HB
    (localIndex P c.critical.tables) (BinaryFn.ofUnary HI)
  have HA:=IntegralMixedFramedPhysicalBlockBits.fullCount_unary P a D J c (prepared P D J c.critical.tables) HP
  have HN : UnaryFn (largeCount P D):=IntegralMixedFramedFullScalarRowBits.fullCount_unary P a D J c.critical.tables
    c.critical.native c.critical.represents (pairFst∘pairFst) (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HW:=FixedWidthEmbeddingBits.word_FP (smallCount P D J c.critical.tables) (largeCount P D) V target pairSnd HA HN hV ht pairSnd_mem_FP
  have E:=IntegralMixedFramedPhysicalBlockBits.prepared_evaluator P a D J c hc (base P D c.critical.tables) HB
    (localIndex P c.critical.tables) (BinaryFn.ofUnary HI) V hV _ HW
  unfold value
  exact FixedWidthLocalEmbeddingBits.evaluator _ _ V target pairSnd _ _ HA HN hV ht pairSnd_mem_FP E

theorem value_prefix (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (V : List Bool→ℕ) (target : List Bool→List Bool) (q : List Bool)
    (hN : smallCount P D J T q≤largeCount P D q) :
    value P D J T hr V target q=residueBits
      (((MvPolynomial.rename (Fin.castLE hN) (polynomial P D J T hr q)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (V q) (Nat.fromBitsLE (target q)))) :
          ZMod (modulus P (prepared P D J T q))) := by
  unfold value
  have HE:=FixedWidthLocalEmbeddingBits.value_at (smallCount P D J T) (largeCount P D) V target pairSnd
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘prepared P D J T) (polynomial P D J T hr) q
    (Fin.castLE hN) (Fin.castLE_injective hN) (fun _=>pairSnd_pair _ _)
  exact HE.trans (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl
    (IntegralMixedFramedPhysicalHeightBits.modulusWord_value P (prepared P D J T q)))

theorem modulus_at_caller (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (q : List Bool)
    (hm : Nat.fromBitsLE (pairSnd q)+1≤numericCap P (pairFst (pairFst (pairFst q)))) :
    modulus P (prepared P D J T q)=Nat.fromBitsLE (pairSnd q)+1 := by
  have HP : modulus P (prepared P D J T q)=modulus P (base P D T q) :=
    IntegralMixedFramedPhysicalBlockBits.sourceTask_modulus P (base P D T) _ q
  exact HP.trans (IntegralMixedFramedPhysicalBirthQueryBits.base_modulus P D T q hm)

theorem value_prefix_caller (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (V : List Bool→ℕ) (target : List Bool→List Bool) (q : List Bool)
    (hN : smallCount P D J T q≤largeCount P D q)
    (hm : Nat.fromBitsLE (pairSnd q)+1≤numericCap P (pairFst (pairFst (pairFst q)))) :
    value P D J T hr V target q=residueBits
      (((MvPolynomial.rename (Fin.castLE hN) (polynomial P D J T hr q)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (V q) (Nat.fromBitsLE (target q)))) :
          ZMod (Nat.fromBitsLE (pairSnd q)+1)) :=
  (value_prefix P D J T hr V target q hN).trans
    (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl (modulus_at_caller P D J T q hm))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowBits
