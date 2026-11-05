/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceGramGridReplayDatum
public import LeanCanny.Encoding.IntegralFramedPhysicalUnivariateSpace
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareNative
public import LeanCanny.Encoding.IntegralFramedBankQuery
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateThom
public import LeanCanny.Algebra.IntegralMixedDenominatorNative
/-! # External grid derivatives at the same full physical retained value

An external grid slot 4*i+side addresses chronological old coordinate i.
All derivative orders retain both sampler contexts and both own words.
Native current-Q controls construct the full-row reader internally.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalGridReplay
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralFramedBankPolynomialModel (Source)
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ImplicitSourceGramGrid.polynomial

noncomputable abbrev input (B : Bank) := IntegralFramedPhysicalSquare.input B.parameters B.plan B.data
  B.nodes B.factor B.seed B.bounds B.key B.positive

noncomputable def count (B : Bank) (c : List Bool) :=
  (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count

noncomputable def coordinate (B : Bank) (c d : List Bool) :
    Fin ((family B.parameters B.plan B.data).birth (B.key c)) :=
  ⟨count B c - 1 - ImplicitSourceGramGridReplayDatum.index d / 4, by
    have h := B.positive c
    change 0 < count B c at h
    change _ < count B c
    omega⟩

theorem count_unary (B : Bank) (A : IntegralFramedBankQuery.Access B) : UnaryFn (count B) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters A.parameters B.plan B.data).comp A.key

theorem coordinate_unary (B : Bank) (A : IntegralFramedBankQuery.Access B) :
    UnaryFn (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data B.key (coordinate B)) := by
  have HC := (count_unary B A).comp pairFst_mem_FP
  have HI : BinaryFn (fun z => ImplicitSourceGramGridReplayDatum.index (pairSnd z)) :=
    BinaryFn.fromBits (by polytime)
  have HB : BinaryFn (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data B.key (coordinate B)) :=
    ((BinaryFn.ofUnary HC).sub (BinaryFn.const 1)).sub (HI.div (BinaryFn.const 4))
  exact IntegralMixedDenominatorScriptBits.binary_bounded_unary HB HC (fun _ => by
    change _ - 1 - _ ≤ _
    omega)

theorem input_access (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) : (input B).Access :=
  IntegralFramedPhysicalSquare.native_access B.parameters A.parameters B.plan B.data T hT hr
    B.nodes B.factor B.seed B.bounds A.nodes A.factor A.seed B.key A.key B.positive A.liftedData A.controls A.bounds

noncomputable def value (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank) :=
  IntegralFramedPhysicalUnivariateTest.value B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    B.key B.positive (coordinate B) (ImplicitSourceGramGridReplayDatum.source S hp)

theorem evaluator (S : Source) (AS : IntegralFramedBankPolynomialModel.Access S)
    (hp : ∀ u, 0 < S.arity u) (B : Bank) (A : IntegralFramedBankQuery.Access B)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) :
    SpaceFunction (value S hp B) :=
  IntegralFramedPhysicalUnivariateTest.evaluator B.parameters A.parameters B.plan B.data T hT hr B.key A.key
    (coordinate B) (coordinate_unary B A) A.liftedData A.controls A.bounds A.nodes A.factor A.seed B.bounds
    (ImplicitSourceGramGridReplayDatum.source S hp) (ImplicitSourceGramGridReplayDatum.access S AS hp) B.positive
    (IntegralFramedPhysicalSquare.native_row_evaluator B.parameters A.parameters B.plan B.data T hT hr
      B.nodes B.factor B.seed B.bounds B.key A.key B.positive A.liftedData A.controls A.bounds)

theorem coordinate_packet (B : Bank) (target c : List Bool) (i k : ℕ) :
    (coordinate B target (ImplicitSourceGramGridReplayDatum.packet c i k)).val = count B target - 1 - i / 4 := by
  simp only [coordinate, ImplicitSourceGramGridReplayDatum.index, ImplicitSourceGramGridReplayDatum.packet,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def point (B : Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input B) c w) (i : ℕ) : ℝ :=
  IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive
    c w hw (coordinate B c (ImplicitSourceGramGridReplayDatum.packet [] i 0))

theorem packet (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank)
    (target w c : List Bool) (hw : SquareSampleCompleteVertices.Valid (input B) target w)
    (i : Fin (ImplicitSourceGramGrid.count S c)) (k : ℕ) :
    value S hp B (pair (pair target w) (ImplicitSourceGramGridReplayDatum.packet c i.val k)) =
      InfinitesimalSign.encode (ThomEncoding.sign
        ((ImplicitSourceGramGrid.polynomial S c i).map (Int.castRingHom ℝ)) (point B target w hw i.val) k) := by
  have H := IntegralFramedPhysicalUnivariateTest.packet B.parameters B.plan B.data B.nodes B.factor B.seed
    B.bounds B.key B.positive (coordinate B) (ImplicitSourceGramGridReplayDatum.source S hp)
    target w (ImplicitSourceGramGridReplayDatum.packet c i.val k) hw
  have HC : coordinate B target (ImplicitSourceGramGridReplayDatum.packet c i.val k) =
      coordinate B target (ImplicitSourceGramGridReplayDatum.packet [] i.val 0) := by
    apply Fin.ext
    rw [coordinate_packet, coordinate_packet]
  rw [ImplicitSourceGramGridReplayDatum.polynomial_packet, HC] at H
  simpa only [value, point, ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map] using H

theorem signs_iff (S : Source) (hp : ∀ u, 0 < S.arity u) (B : Bank)
    (target w c own : List Bool) (hw : SquareSampleCompleteVertices.Valid (input B) target w)
    (ho : SquareSampleCompleteVertices.Valid (ImplicitSourceGramGrid.input S hp) c own)
    (i : Fin (ImplicitSourceGramGrid.count S c)) :
    (∀ k ≤ ImplicitSourceGramGrid.degree S c,
      SquareSampleCompleteCoordinateThom.value (ImplicitSourceGramGrid.input S hp)
        (pair (pair c own) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      value S hp B (pair (pair target w) (ImplicitSourceGramGridReplayDatum.packet c i.val k))) ↔
      (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c own ho).val i =
        point B target w hw i.val := by
  let p := (ImplicitSourceGramGrid.polynomial S c i).map (Int.castRingHom ℝ)
  let a := (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c own ho).val i
  let b := point B target w hw i.val
  have HL (k : ℕ) := SquareSampleCompleteCoordinateThom.packet (ImplicitSourceGramGrid.input S hp) c own ho i k
  have HR (k : ℕ) := packet S hp B target w c hw i k
  have HA : p.eval a = 0 := by
    rw [Polynomial.eval_map]
    exact ImplicitSourceGramGrid.complete S hp c _
      (SquareSampleCompleteVertices.candidate (ImplicitSourceGramGrid.input S hp) c own ho).property i
  constructor
  · intro hs
    have HS (k : ℕ) (hk : k ≤ ImplicitSourceGramGrid.degree S c) :
        ThomEncoding.sign p a k = ThomEncoding.sign p b k :=
      (SquareSampleTestSign.encode_eq_iff _ _).mp ((HL k).symm.trans ((hs k hk).trans (HR k)))
    have H0 : p.eval b = 0 := by
      apply sign_eq_zero_iff.mp
      have H := HS 0 (Nat.zero_le _)
      simpa only [ThomEncoding.sign, Function.iterate_zero_apply, HA, sign_zero] using H.symm
    exact ThomEncoding.root_eq p
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (ImplicitSourceGramGrid.nonzero S c i))
      (ImplicitSourceGramGrid.degree S c)
      (Polynomial.natDegree_map_le.trans (ImplicitSourceGramGrid.polynomial_degree S c i)) a b HA H0 HS
  · intro he k _
    apply (HL k).trans
    change InfinitesimalSign.encode (ThomEncoding.sign p a k) = _
    rw [show a = b from he]
    exact (HR k).symm

end LeanCanny.Encoding.IntegralFramedPhysicalGridReplay
