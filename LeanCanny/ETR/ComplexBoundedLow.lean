/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexZeroEnergy
public import LeanCanny.ETR.ComplexScaleShift

/-! # The bounded zero source's shifted lower polynomial as a circuit

Radius, inner scale and shift are computed from binary exponent words. The
source and radial sum are existing wires; neither is duplicated.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedLow
open MvPolynomial

def energyStart (start : ℕ) (radius : List Bool) : ℕ := start + 2 * radius.length + 2
def scaleStart (start : ℕ) (radius : List Bool) : ℕ := energyStart start radius + 6
def shiftStart (start : ℕ) (radius scale : List Bool) : ℕ := scaleStart start radius + 2 * scale.length + 2
def joinStart (start : ℕ) (radius scale shift : List Bool) : ℕ := shiftStart start radius scale + 2 * shift.length + 2

def program (source radial start : ℕ) (radius scale shift : List Bool) : List Operation :=
  BinaryScale.program start radius ++
    (ZeroEnergy.program source radial (BinaryScale.output start radius) (energyStart start radius) ++
      (BinaryScale.program (scaleStart start radius) scale ++
        (BinaryScale.program (shiftStart start radius scale) shift ++
          ScaleShift.program (ZeroEnergy.output (energyStart start radius))
            (BinaryScale.output (scaleStart start radius) scale)
            (BinaryScale.output (shiftStart start radius scale) shift) (joinStart start radius scale shift))))

def output (start : ℕ) (radius scale shift : List Bool) : ℕ := ScaleShift.output (joinStart start radius scale shift)

noncomputable def polynomial (q radial : MvPolynomial ℕ ℤ) (radius scale shift : List Bool) : MvPolynomial ℕ ℤ :=
  C ((2 : ℤ) ^ Nat.fromBitsLE scale) *
    (q ^ 2 + (radial - C ((2 : ℤ) ^ Nat.fromBitsLE radius)) ^ 2) - C ((2 : ℤ) ^ Nat.fromBitsLE shift)

theorem radius_next (start : ℕ) (radius : List Bool) :
    start + (BinaryScale.program start radius).length = energyStart start radius := by
  rw [BinaryScale.program_length]; unfold energyStart; omega
theorem energy_next (source radial start : ℕ) (radius : List Bool) :
    energyStart start radius + (ZeroEnergy.program source radial (BinaryScale.output start radius)
      (energyStart start radius)).length = scaleStart start radius := rfl
theorem scale_next (start : ℕ) (radius scale : List Bool) :
    scaleStart start radius + (BinaryScale.program (scaleStart start radius) scale).length = shiftStart start radius scale := by
  rw [BinaryScale.program_length]; unfold shiftStart; omega
theorem shift_next (start : ℕ) (radius scale shift : List Bool) :
    shiftStart start radius scale + (BinaryScale.program (shiftStart start radius scale) shift).length =
      joinStart start radius scale shift := by
  rw [BinaryScale.program_length]; unfold joinStart; omega

theorem program_length (source radial start : ℕ) (radius scale shift : List Bool) :
    (program source radial start radius scale shift).length =
      2 * radius.length + 2 * scale.length + 2 * shift.length + 16 := by
  simp only [program, List.length_append, BinaryScale.program_length, ZeroEnergy.program_length, ScaleShift.program_length]
  omega

theorem next_eq (source radial start : ℕ) (radius scale shift : List Bool) :
    start + (program source radial start radius scale shift).length = output start radius scale shift + 1 := by
  rw [program_length]
  unfold output ScaleShift.output joinStart shiftStart scaleStart energyStart
  omega

theorem wellFormed (source radial start : ℕ) (radius scale shift : List Bool)
    (hq : source < start) (hr : radial < start) :
    StraightLine.WellFormed start (program source radial start radius scale shift) := by
  rw [program, StraightLine.wellFormed_append, radius_next, StraightLine.wellFormed_append,
    energy_next, StraightLine.wellFormed_append, scale_next, StraightLine.wellFormed_append, shift_next]
  have hR := BinaryScale.output_lt start radius
  rw [radius_next] at hR
  have hF := BinaryScale.output_lt (scaleStart start radius) scale
  rw [scale_next] at hF
  have hb := BinaryScale.output_lt (shiftStart start radius scale) shift
  rw [shift_next] at hb
  have hs : start ≤ energyStart start radius := by unfold energyStart; omega
  have he : ZeroEnergy.output (energyStart start radius) < scaleStart start radius := by
    unfold ZeroEnergy.output scaleStart; omega
  have hf : scaleStart start radius ≤ shiftStart start radius scale := by unfold shiftStart; omega
  have hg : shiftStart start radius scale ≤ joinStart start radius scale shift := by unfold joinStart; omega
  exact ⟨BinaryScale.wellFormed start radius,
    ZeroEnergy.wellFormed source radial _ _ (by omega) (by omega) hR,
    BinaryScale.wellFormed _ scale, BinaryScale.wellFormed _ shift,
    ScaleShift.wellFormed _ _ _ _ (by omega) (by omega) hb⟩

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (source radial start : ℕ) (radius scale shift : List Bool)
    (hr : Differential.Realizes wire start (program source radial start radius scale shift)) :
    wire (output start radius scale shift) = polynomial (wire source) (wire radial) radius scale shift := by
  rw [program, Differential.realizes_append, radius_next, Differential.realizes_append,
    energy_next, Differential.realizes_append, scale_next, Differential.realizes_append, shift_next] at hr
  have hR := BinaryScale.realized_output wire start radius hr.1
  have he := ZeroEnergy.realized_output wire source radial _ _ hr.2.1
  have hF := BinaryScale.realized_output wire (scaleStart start radius) scale hr.2.2.1
  have hb := BinaryScale.realized_output wire (shiftStart start radius scale) shift hr.2.2.2.1
  have hj := ScaleShift.realized_output wire _ _ _ _ hr.2.2.2.2
  rw [he, hR, hF, hb] at hj
  exact hj

theorem energyStart_unary {start : List Bool → ℕ} {radius : List Bool → List Bool}
    (hs : UnaryFn start) (hR : radius ∈ FP) : UnaryFn (fun c => energyStart (start c) (radius c)) :=
  ((hs.add ((UnaryFn.const 2).mul (UnaryFn.length hR))).add (UnaryFn.const 2)).of_eq (fun _ => rfl)
theorem scaleStart_unary {start : List Bool → ℕ} {radius : List Bool → List Bool}
    (hs : UnaryFn start) (hR : radius ∈ FP) : UnaryFn (fun c => scaleStart (start c) (radius c)) :=
  ((energyStart_unary hs hR).add (UnaryFn.const 6)).of_eq (fun _ => rfl)
theorem shiftStart_unary {start : List Bool → ℕ} {radius scale : List Bool → List Bool}
    (hs : UnaryFn start) (hR : radius ∈ FP) (hF : scale ∈ FP) : UnaryFn (fun c => shiftStart (start c) (radius c) (scale c)) :=
  (((scaleStart_unary hs hR).add ((UnaryFn.const 2).mul (UnaryFn.length hF))).add (UnaryFn.const 2)).of_eq (fun _ => rfl)
theorem joinStart_unary {start : List Bool → ℕ} {radius scale shift : List Bool → List Bool}
    (hs : UnaryFn start) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) :
    UnaryFn (fun c => joinStart (start c) (radius c) (scale c) (shift c)) :=
  (((shiftStart_unary hs hR hF).add ((UnaryFn.const 2).mul (UnaryFn.length hb))).add (UnaryFn.const 2)).of_eq (fun _ => rfl)
theorem output_unary {start : List Bool → ℕ} {radius scale shift : List Bool → List Bool}
    (hs : UnaryFn start) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) :
    UnaryFn (fun c => output (start c) (radius c) (scale c) (shift c)) :=
  ((joinStart_unary hs hR hF hb).add (UnaryFn.const 3)).of_eq (fun _ => rfl)
theorem length_unary {source radial start : List Bool → ℕ} {radius scale shift : List Bool → List Bool}
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) :
    UnaryFn (fun c => (program (source c) (radial c) (start c) (radius c) (scale c) (shift c)).length) :=
  (((((UnaryFn.const 2).mul (UnaryFn.length hR)).add ((UnaryFn.const 2).mul (UnaryFn.length hF))).add
    ((UnaryFn.const 2).mul (UnaryFn.length hb))).add (UnaryFn.const 16)).of_eq
      (fun _ => (program_length _ _ _ _ _ _).symm)

theorem encode_mem_FP {source radial start : List Bool → ℕ} {radius scale shift : List Bool → List Bool}
    (hq : UnaryFn source) (hr : UnaryFn radial) (hs : UnaryFn start)
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (source c) (radial c) (start c) (radius c) (scale c) (shift c)))) ∈ FP := by
  have he := energyStart_unary hs hR
  have hf := scaleStart_unary hs hR
  have hbstart := shiftStart_unary hs hR hF
  have hj := joinStart_unary hs hR hF hb
  have hrad := BinaryScale.output_unary hs hR
  have hscale := BinaryScale.output_unary hf hF
  have hshift := BinaryScale.output_unary hbstart hb
  unfold program
  apply StraightLine.encode_append_mem_FP (BinaryScale.encode_mem_FP hs hR)
  simp only [radius_next]
  apply StraightLine.encode_append_mem_FP (ZeroEnergy.encode_mem_FP hq hr hrad he)
  simp only [energy_next]
  apply StraightLine.encode_append_mem_FP (BinaryScale.encode_mem_FP hf hF)
  simp only [scale_next]
  apply StraightLine.encode_append_mem_FP (BinaryScale.encode_mem_FP hbstart hb)
  simp only [shift_next]
  exact ScaleShift.encode_mem_FP ((he.add (UnaryFn.const 5)).of_eq (fun _ => rfl)) hscale hshift hj

end LeanCanny.ETR.ComplexCircuit.BoundedLow
