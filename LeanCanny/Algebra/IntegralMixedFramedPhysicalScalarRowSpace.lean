/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarSelection
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarRowSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowTransport
/-! # Original headers bind the charged scalar reader to each full scalar row -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarRowBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan commands)
open IntegralMixedFramedPhysicalRowSelector IntegralMixedFramedPhysicalIndex
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value

def indexWord (P : Parameters) (T : Tables) (key : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) :=
  BinaryNatCode.encode (IntegralMixedFramedPhysicalScalarSelection.index P T (pair (key q) (BinaryNatCode.encode (row q))))

attribute [local irreducible] indexWord IntegralMixedFramedPhysicalScalarSelection.index

theorem indexWord_FP (P : Parameters) (a : Access P) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (key : List Bool→List Bool) (hk : key∈FP) (row : List Bool→ℕ) (hr : BinaryFn row) : indexWord P T key row∈FP := by
  have HQ : (fun q=>pair (key q) (BinaryNatCode.encode (row q)))∈FP:=mem_FP_pair hk hr.bits_mem_FP
  have HI : UnaryFn (fun q=>IntegralMixedFramedPhysicalScalarSelection.index P T
      (pair (key q) (BinaryNatCode.encode (row q)))):=
    (IntegralMixedFramedPhysicalScalarSelection.index_unary P a T ht).comp HQ
  exact mem_FP_of_eq (BinaryFn.ofUnary HI).bits_mem_FP (fun _=>by unfold indexWord;rfl)

theorem scalarCount_pos (P : Parameters) (D : Plan P) (key : List Bool→List Bool)
    (hpos : ∀q,0<IntegralMixedFramedFullScalarRowBits.fullCount P D key q) :
    ∀q,0<IntegralMixedFramedRowBits.count P key q := by
  intro q
  by_contra h
  have HE : (commands P D (key q)).length=0 :=by
    rw [commands,IntegralMixedFramedHistoryScript.paddedPast_length]
    exact Nat.eq_zero_of_not_pos h
  have HN:=List.eq_nil_of_length_eq_zero HE
  have HP:=hpos q
  change 0<arity (commands P D (key q)) at HP
  rw [HN] at HP
  exact Nat.not_lt_zero _ HP

noncomputable abbrev polynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool→List Bool)
    (row : List Bool→ℕ) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q) :=
  IntegralMixedFramedFullScalarRowBits.polynomial P D J T hT key (indexWord P T key row) hpos

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key : List Bool→List Bool) (hk : key∈FP) (row : List Bool→ℕ) (hr : BinaryFn row)
    (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target modulus : List Bool→List Bool) (hTarget : target∈FP) (hModulus : modulus∈FP)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Jnew)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Jnew c) :
    SpaceFunction (FixedWidthRowBits.value (IntegralMixedFramedFullScalarRowBits.fullCount P D key) V
      (polynomial P D J T hT key row hpos) target modulus) :=
  IntegralMixedFramedFullScalarRowBits.currentQ_evaluator P a D J T ht hT key (indexWord P T key row)
    target modulus hpos V hk (indexWord_FP P a T ht key hk row hr) hV hTarget hModulus Jnew c hc

theorem polynomial_actual (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool→List Bool)
    (row : List Bool→ℕ) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q) (q : List Bool)
    (hr : row q<fullArity P T (pair (key q) (BinaryNatCode.encode (row q))))
    (hs : IsScalar P T (pair (key q) (BinaryNatCode.encode (row q)))) :
    polynomial P D J T hT key row hpos q=
      IntegralMixedFramedPhysicalRowTransport.indexedRow P D J (key q)
        ⟨row q,hr.trans_eq (IntegralMixedFramedPhysicalRowTransport.native_full_count P D J T hT (key q) (row q))⟩ := by
  rw [polynomial,IntegralMixedFramedFullScalarRowBits.polynomial_actual]
  apply congrArg (PolynomialSystemReindex.system (enumerate (commands P D (key q)))
    ((IntegralMixedFramedHistoryFamilyBits.family P D J).state (key q)).sampler.rows)
  apply Fin.ext
  have HI:=IntegralMixedFramedPhysicalScalarSelection.index_lt P T (key q) (row q) hr
  have HE : (IntegralMixedFramedRowBits.selectedIndex P D J key (indexWord P T key row) hpos q).val=
      IntegralMixedFramedPhysicalScalarSelection.index P T (pair (key q) (BinaryNatCode.encode (row q))) := by
    have HV : (IntegralMixedFramedRowBits.selectedIndex P D J key (indexWord P T key row) hpos q).val=
        IntegralMixedFramedRowBits.selected P key (indexWord P T key row) q :=rfl
    rw [HV,IntegralMixedFramedRowBits.selected,indexWord]
    rw [show Nat.fromBitsLE (BinaryNatCode.encode (IntegralMixedFramedPhysicalScalarSelection.index P T
      (pair (key q) (BinaryNatCode.encode (row q)))))=IntegralMixedFramedPhysicalScalarSelection.index P T
      (pair (key q) (BinaryNatCode.encode (row q))) from Nat.fromBitsLE_bits _]
    exact min_eq_left (by change _≤IntegralMixedFramedHistoryFamilyBits.prefixLength P (key q)-1;omega)
  have HC : (nativeScalarColumn P D J T hT (key q)
      (IntegralMixedFramedRowBits.selectedIndex P D J key (indexWord P T key row) hpos q)).val=
    scalarColumn P T (pair (key q) (BinaryNatCode.encode
      (IntegralMixedFramedRowBits.selectedIndex P D J key (indexWord P T key row) hpos q).val)) :=rfl
  rw [HC,HE]
  exact IntegralMixedFramedPhysicalScalarSelection.scalar_column P T (key q) (row q) hr hs

end LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarRowBits
