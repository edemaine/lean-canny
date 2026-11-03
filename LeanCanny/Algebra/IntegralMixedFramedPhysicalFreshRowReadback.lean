/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSemantics
/-! # Caller-modulus fresh coefficients read the actual full indexed row -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSemantics
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan commands)
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedFramedPhysicalRowTransport
open IntegralMixedFramedPhysicalFreshRowBits (smallCount largeCount polynomial value)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family
  IntegralMixedFramedPhysicalBlockBits.poweredRowPolynomial MvPolynomial.rename

theorem native_coefficient_of_natural {a b : ℕ} (h : a=b)
    (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hp : rename Fin.val p=rename Fin.val q) (V t : ℕ) :
    p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t)=
      q.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t) :=by
  cases h
  exact congrArg (fun p : MvPolynomial (Fin a) ℤ=>
    p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t))
    (MvPolynomial.rename_injective Fin.val Fin.val_injective hp)

variable (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
  (key : List Bool) (r : ℕ)
  (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
  (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) (M : List Bool)

include hT hr hs in
theorem native_coefficient (V t : ℕ) :
    (rename (Fin.castLE (count_le P D J T hT key r hr hs M))
      (polynomial P D J T hT (pair (pair key (BinaryNatCode.encode r)) M))).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t)=
    (indexedRow P D J key ⟨r,hr.trans_eq (native_full_count P D J T hT key r)⟩).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) V t) :=by
  apply native_coefficient_of_natural (largeCount_packet P D key r M) _ _ ?_ V t
  rw [rename_rename]
  change rename Fin.val (polynomial P D J T hT (pair (pair key (BinaryNatCode.encode r)) M))=_
  exact (polynomial_terminal P D J T hT key r hr hs M).trans
    (keyRow_family P D J key r (hr.trans_eq (native_full_count P D J T hT key r)))

include hT hr hs in
theorem value_packet (V : List Bool→ℕ) (target : List Bool→List Bool)
    (hm : Nat.fromBitsLE M+1≤numericCap P (pairFst key)) :
    value P D J T hT V target (pair (pair key (BinaryNatCode.encode r)) M)=residueBits
      (((indexedRow P D J key ⟨r,hr.trans_eq (native_full_count P D J T hT key r)⟩).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _)
          (V (pair (pair key (BinaryNatCode.encode r)) M))
          (Nat.fromBitsLE (target (pair (pair key (BinaryNatCode.encode r)) M)))) : ℤ) :
            ZMod (Nat.fromBitsLE M+1)) :=by
  have HM : Nat.fromBitsLE (pairSnd (pair (pair key (BinaryNatCode.encode r)) M))+1≤
      numericCap P (pairFst (pairFst (pairFst (pair (pair key (BinaryNatCode.encode r)) M)))) :=by
    simpa only [pairFst_pair,pairSnd_pair] using hm
  have HV:=IntegralMixedFramedPhysicalFreshRowBits.value_prefix_caller P D J T hT V target
    (pair (pair key (BinaryNatCode.encode r)) M) (count_le P D J T hT key r hr hs M) HM
  have HC:=native_coefficient P D J T hT key r hr hs M
    (V (pair (pair key (BinaryNatCode.encode r)) M))
    (Nat.fromBitsLE (target (pair (pair key (BinaryNatCode.encode r)) M)))
  exact HV.trans (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) HC
    (congrArg (fun w=>Nat.fromBitsLE w+1) (pairSnd_pair _ _)))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalFreshRowSemantics
