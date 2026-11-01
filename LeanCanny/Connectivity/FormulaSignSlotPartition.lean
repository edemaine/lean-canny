/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotTruth
public import LeanCanny.Connectivity.FormulaSignSlotBounded
/-! # The native finite sign-slot decomposition of arbitrary canonical Boolean inputs -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotTruth
open ETR LeanCanny.Computation LeanCanny.Encoding BooleanCircuitSpace
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  FormulaView.normalize FormulaSignSlotCircuit.atom FormulaSignSlotCircuit.read frozenAtom

theorem value_truth (c label : List Bool) (env : ℕ → ℝ)
    (H : (FormulaSignSlotSource.stratum (pair c label)).Holds env) (p : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode)
    (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    value FormulaSignSlotCircuit.family FormulaSignSlotCircuit.atom (pair c label)=decide (p.Holds env) := by
  have HV := value_comp FormulaBooleanCircuitSource.circuit FormulaSignSlotCircuit.read
    FormulaSignSlotCircuit.atom (frozenAtom c label) (pair c label)
    (fun k _ => by simp only [frozenAtom,pairSnd_pair])
  change value (FormulaBooleanCircuitSource.circuit.comp FormulaSignSlotCircuit.read)
    FormulaSignSlotCircuit.atom (pair c label)=_
  rw [HV]
  have HR : FormulaSignSlotCircuit.read (pair c label)=Input.field 2 c := by
    simp only [FormulaSignSlotCircuit.read,pairFst_pair]
  rw [HR]
  have HN : 0 < FormulaBooleanCircuitSource.circuit.count (Input.field 2 c) := by
    change 0 < (FormulaView.normalize (Input.field 2 c)).length
    rw [hc]
    simp [Formula.encode]
  rw [value_eq_wireValue _ _ _ HN]
  change wireValue FormulaBooleanCircuitSource.circuit (frozenAtom c label) (Input.field 2 c)
    ((FormulaView.normalize (Input.field 2 c)).length-1)=_
  have HW := wire_truth c label env H p [] [] (by simpa only [List.nil_append,List.append_nil] using hc) hs
  simpa only [FormulaBooleanCircuitSource.wire,List.length_nil,Nat.sub_zero] using HW

theorem selected_iff (c : List Bool) (env : ℕ → ℝ) (p : Formula)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode)
    (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    p.Holds env ↔ ∃ label : List Bool, label.length=2*ClosedFormulaGateMetadata.count c ∧
      (pair c label)∈FormulaSignSlotCircuit.language ∧
      (FormulaSignSlotSource.stratum (pair c label)).Holds env := by
  constructor
  · intro HP
    let label := FormulaSignSlotSource.pointLabel c env
    have HH := FormulaSignSlotSource.pointLabel_stratum c env
    refine ⟨label,FormulaSignSlotSource.pointLabel_length c env,?_,HH⟩
    change value FormulaSignSlotCircuit.family FormulaSignSlotCircuit.atom (pair c label)=true
    rw [value_truth c label env HH p hc hs,decide_eq_true_eq]
    exact HP
  · rintro ⟨label,_,HA,HH⟩
    change value FormulaSignSlotCircuit.family FormulaSignSlotCircuit.atom (pair c label)=true at HA
    rw [value_truth c label env HH p hc hs,decide_eq_true_eq] at HA
    exact HA

theorem canonical_selected_iff (d : Description) (hd : d.WellFormed) (x : Fin d.dimension → ℝ) :
    x∈d.realization ↔ ∃ label : List Bool,
      label.length=2*ClosedFormulaGateMetadata.count (Input.whole d).encode ∧
      (pair (Input.whole d).encode label)∈FormulaSignSlotCircuit.language ∧
      (FormulaSignSlotSource.stratum (pair (Input.whole d).encode label)).Holds (Formula.extend x) := by
  apply selected_iff _ _ d.formula
  · rw [Input.field_whole_space,FormulaView.normalize_encode]
  · simpa only [ClosedFormulaGateMetadata.dimension,Input.field_whole_dimension,Codec.unaryValue_toBits,Description.WellFormed] using hd

end LeanCanny.Connectivity.FormulaSignSlotTruth
