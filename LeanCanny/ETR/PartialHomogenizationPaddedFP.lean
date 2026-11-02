/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationFP
/-! # Uniform polynomial-time writing with an original degree allowance -/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationNative
open LeanCanny.Encoding Brackets PartialHomogenizationData

def degreeExtract (state : List Bool) : ℕ :=
  Codec.unaryValue (firstChild (degrees (pairFst (state.drop 1))))

theorem degreeExtract_unary : UnaryFn degreeExtract := by
  have HF : (fun s : List Bool => pairFst (s.drop 1)) ∈ FP :=
    mem_FP_comp (f:=fun s => s.drop 1) (g:=pairFst) (drop_mem_FP id_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
  have HD : (fun s : List Bool => degrees (pairFst (s.drop 1))) ∈ FP :=
    mem_FP_comp (f:=fun s => pairFst (s.drop 1)) (g:=degrees) HF degrees_FP
  have H : (fun s => firstChild (degrees (pairFst (s.drop 1)))) ∈ FP :=
    mem_FP_comp (f:=fun s => degrees (pairFst (s.drop 1))) (g:=firstChild) HD firstChild_mem_FP
  exact UnaryFn.comp (f:=Codec.unaryValue) (g:=fun s => firstChild (degrees (pairFst (s.drop 1))))
    Codec.unaryValue_unary H

theorem degreeExtract_data (P : Parameters) (source : List Bool → List Bool) (z : List Bool) (d : Data)
    (hd : source z=d.toBits) :
    degreeExtract (run P source z) = degree (P.parameterCount z) (P.degree z) d := by
  simp [run,hd,TreeFold.run_toBits,NNF.foldData_identity,NNF.combine,DynamicTreeFold.encode,
    DynamicTreeFold.stackBits,degreeExtract,degrees,code,frameCode,firstChild_toBits]

def paddedWrite (P : Parameters) (source : List Bool → List Bool) (z : List Bool) : List Bool :=
  Codec.taggedTwo 3
    (TermPower.write (fun _ => (Term.var 0).toData.toBits)
      (fun c => P.degree c-degreeExtract (run P source c)) z)
    (write P source z)

theorem paddedWrite_FP (P : Parameters) (hP : Access P) (source : List Bool → List Bool) (hs : source ∈ FP) :
    paddedWrite P source ∈ FP := by
  have HD := degreeExtract_unary.comp (run_FP P hP source hs)
  exact Codec.taggedTwo_mem_FP 3
    (TermPower.write_mem_FP (constFn_mem_FP (Term.var 0).toData.toBits) (hP.degree.sub HD)) (write_FP P hP source hs)

theorem paddedWrite_term (P : Parameters) (source : List Bool → List Bool) (z : List Bool) (t : Term)
    (hs : source z=t.toData.toBits) (ht : t.degreeBound ≤ P.degree z) (hL : t.toData.size ≤ P.limit z) :
    paddedWrite P source z = (PartialHomogenization.padded (P.parameterCount z) (P.degree z) t).toData.toBits := by
  rw [paddedWrite,TermPower.write_correct,TermView.term_toBits,degreeExtract_data P source z t.toData hs,
    degree_term _ _ t ht,write_term P source z t hs ht hL]
  exact (Term.mul_toBits _ _).symm

end LeanCanny.ETR.PartialHomogenizationNative

namespace LeanCanny.ETR.PartialHomogenization
open LeanCanny.Encoding PartialHomogenizationNative

theorem homogenize_FP {t : List Bool → Term} {k D : List Bool → ℕ}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hk : UnaryFn k) (hD : UnaryFn D)
    (hb : ∀ c, (t c).degreeBound ≤ D c) :
    (fun c => (homogenize (k c) (t c)).toData.toBits) ∈ FP := by
  let P : Parameters := ⟨k,D,fun c => (t c).toData.size⟩
  have HL : UnaryFn (fun c => (t c).toData.size) := (UnaryFn.length ht).of_eq (fun c => Data.length_toBits _)
  have HA : Access P := ⟨hk,hD,HL⟩
  apply mem_FP_of_eq (write_FP P HA (fun c => (t c).toData.toBits) ht)
  intro c
  exact write_term P _ c (t c) rfl (hb c) (Nat.le_refl _)

theorem padded_FP {t : List Bool → Term} {k D : List Bool → ℕ}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hk : UnaryFn k) (hD : UnaryFn D)
    (hb : ∀ c, (t c).degreeBound ≤ D c) :
    (fun c => (padded (k c) (D c) (t c)).toData.toBits) ∈ FP := by
  let P : Parameters := ⟨k,D,fun c => (t c).toData.size⟩
  have HL : UnaryFn (fun c => (t c).toData.size) := (UnaryFn.length ht).of_eq (fun c => Data.length_toBits _)
  have HA : Access P := ⟨hk,hD,HL⟩
  apply mem_FP_of_eq (paddedWrite_FP P HA (fun c => (t c).toData.toBits) ht)
  intro c
  exact paddedWrite_term P _ c (t c) rfl (hb c) (Nat.le_refl _)

end LeanCanny.ETR.PartialHomogenization
