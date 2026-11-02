/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateIndexPolynomial
/-! # Native coefficients of the actual symbolic coordinate equation

Independent binary Y/E selectors retain one weighted old joint tuple.
Out-of-degree requests vanish. The only charged child is current-Q.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCoefficientSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

def Core (P : Parameters) (parent : List Bool→List Bool) (q : List Bool) : Prop :=
  IntegralMixedFramedFullCutProbeBits.Active P (parent q) ∧
    get P .slot13 (parent q)≤P.ambient (RankedHistoryTask.root (parent q))+1
noncomputable def Box (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) : Prop :=
  y q<IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) (parent q) ∧
    k q<2^P.width (RankedHistoryTask.root (parent q))

theorem core_FP (P : Parameters) (a : Access P) (parent : List Bool→List Bool) (hp : parent∈FP) : FPPred (Core P parent) := by
  have HJ : BinaryFn (fun q=>get P .slot13 (parent q)) := (get_binary P a .slot13).comp hp
  exact ((IntegralMixedFramedFullCutProbeBits.active_FP P a).comp hp).and
    (HJ.le ((BinaryFn.ofUnary (a.ambient.comp (mem_FP_comp hp RankedHistoryTask.root_FP))).add (BinaryFn.const 1)))

theorem box_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H)) (parent : List Bool→List Bool) (hp : parent∈FP)
    (y k : List Bool→ℕ) (hy : BinaryFn y) (hk : BinaryFn k) : FPPred (Box P D H parent y k) :=
  (hy.lt ((IntegralMixedCoordinateCoefficientTasks.choiceBound_binary P a (family P D H) I).comp hp)).and
    (hk.lt ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp hp RankedHistoryTask.root_FP))))

noncomputable def arity (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (q : List Bool) := (family P D H).birth (IntegralMixedVirtualTaskBits.saved P (parent q))
noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) :=
  IntegralMixedFramedCoordinateRepresentativeBits.atContext P D H (IntegralMixedFramedAllCoordinateSourceBits.horizon P (parent q))
    (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P .slot13 (parent q)) (y q) (k q)
noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k W : List Bool→ℕ) (target modulus : List Bool→List Bool) (q : List Bool) :=
  if Core P parent q then FixedWidthRowBits.value (arity P D H parent) W (polynomial P D H parent y k) target modulus q else []

noncomputable def queriedValue (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k W : List Bool→ℕ) (target modulus : List Bool→List Bool) :=
  FixedWidthRowBits.value
    (fun q=>(IntegralMixedFramedAllCoordinateSourceBits.source P D H).arity (IntegralMixedFramedCoordinateIndexBits.query P parent y k q)) W
    (fun q=>IntegralMixedFramedAllCoordinateSourceBits.polynomial P D H (IntegralMixedFramedCoordinateIndexBits.query P parent y k q)) target modulus

private theorem coefficient_value_congr {m n : ℕ} (p : MvPolynomial (Fin m) ℤ) (q : MvPolynomial (Fin n) ℤ)
    (hm : m=n) (hP : HEq p q) (W : ℕ) (r mw : List Bool) :
    residueBits ((p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W (Nat.fromBitsLE r)) : ℤ) : ZMod (Nat.fromBitsLE mw+1))=
      residueBits ((q.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W (Nat.fromBitsLE r)) : ℤ) : ZMod (Nat.fromBitsLE mw+1)) := by
  cases hm
  cases hP
  rfl

theorem queried_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k W : List Bool→ℕ) (target modulus : List Bool→List Bool) (q : List Bool)
    (hc : Core P parent q) (hb : Box P D H parent y k q) :
    queriedValue P D H parent y k W target modulus q=value P D H parent y k W target modulus q := by
  unfold value
  rw [ite_eq_left hc]
  unfold queriedValue FixedWidthRowBits.value
  apply coefficient_value_congr _ _ ?_ (IntegralMixedFramedCoordinateIndexBits.polynomial P D H parent y k q hc.1 hc.2 hb.1 hb.2)
  rw [IntegralMixedFramedAllCoordinateSourceBits.arity,IntegralMixedFramedCoordinateIndexBits.birth]
  exact (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth (parent q) |>.symm

theorem polynomial_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (y k : List Bool→ℕ) (q : List Bool) (hb : ¬Box P D H parent y k q) :
    polynomial P D H parent y k q=0 := by
  apply IntegralMixedFramedCoordinateIndexBits.atContext_outside
  by_cases hy : y q<IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) (parent q)
  · right
    have HK : ¬k q<2^P.width (RankedHistoryTask.root (parent q)):=fun hk=>hb ⟨hy,hk⟩
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width (parent q)]
    exact Nat.le_of_not_gt HK
  · exact Or.inl (Nat.le_of_not_gt hy)

private theorem pull_value (G : IntegralCoordinateCoefficientBits.Family) (J : List Bool→List Bool)
    (S W : List Bool→ℕ) (target modulus : List Bool→List Bool) :
    FixedWidthRowBits.value (G.pull J).arity W ((G.pull J).poweredPolynomial (S∘J)) target modulus=
      FixedWidthRowBits.value (G.arity∘J) W (fun q=>G.poweredPolynomial S (J q)) target modulus := rfl

attribute [local irreducible] arity polynomial value queriedValue
  IntegralMixedFramedAllCoordinateSourceBits.source IntegralMixedFramedCoordinateIndexBits.query
  IntegralMixedFramedCoordinateIndexBits.first

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (y k W : List Bool→ℕ) (hy : BinaryFn y) (hk : BinaryFn k)
    (hW : UnaryFn W) (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (value P D H parent y k W target modulus) := by
  have HQ:=IntegralMixedFramedCoordinateIndexBits.query_FP P a parent hp y k hy hk
  have E0:=IntegralMixedFramedAllCoordinateSourceBits.pulled_powered_evaluator P a D H L F C hL hF hC I h hb
    (IntegralMixedFramedCoordinateIndexBits.query P parent y k) HQ
    (IntegralMixedFramedAllCoordinateSourceBits.horizon P ∘ IntegralMixedFramedCoordinateIndexBits.query P parent y k) W
    ((IntegralMixedFramedAllCoordinateSourceBits.horizon_unary P a).comp HQ) hW target modulus ht hm
  have EQ : SpaceFunction (queriedValue P D H parent y k W target modulus) := by
    apply E0.congr
    rw [pull_value]
    unfold queriedValue IntegralMixedFramedAllCoordinateSourceBits.polynomial
    rfl

  have E:=SpaceFunction.branch (fun q=>decide (Core P parent q ∧ Box P D H parent y k q))
    ((core_FP P a parent hp).and (box_FP P a D H I parent hp y k hy hk)).flag_mem_FP
    EQ (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply E.congr
  funext q
  simp only [decide_eq_true_eq]
  by_cases hc : Core P parent q
  · by_cases hbox : Box P D H parent y k q
    · rw [ite_eq_left ⟨hc,hbox⟩]
      exact queried_value P D H parent y k W target modulus q hc hbox
    · rw [ite_eq_right (fun h'=>hbox h'.2)]
      unfold value
      rw [ite_eq_left hc]
      unfold FixedWidthRowBits.value
      rw [polynomial_outside P D H parent y k q hbox]
      change []=residueBits (0 : ZMod (Nat.fromBitsLE (modulus q)+1))
      simp only [residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]
  · rw [ite_eq_right (fun h'=>hc h'.1)]
    unfold value
    exact (ite_eq_right hc).symm

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCoefficientSpaceBits
