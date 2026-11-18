/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.AbstractEncodingBridge
public import LeanCanny.Encoding.DerivedSyntax
public import CslibFrontier.Computability.Complexity.Classes.Space.Closure

/-! # Uniform PSPACE transfers for derived syntax encodings -/

@[expose] public section
namespace LeanCanny.DerivedEncodingBridge
open Turing.MultiTapeTM Encoding Encoding.DerivedSyntax

/-- The original flat formula word is an injective encoding. -/
def oldFormulaEncoding : ETR.Formula ↪ List Bool where
  toFun p := FlatSyntax.encoding (FlatSyntax.formulaTokens p)
  inj' := by
    intro p q h
    apply ETR.Formula.encode_injective
    simpa only [FlatSyntaxInverse.parse_formula] using congrArg FlatSyntaxInverse.parse h

def oldSpaceEncoding := encPair encUnary oldFormulaEncoding
def oldPointEncoding := encPair encUnary (encList oldFormulaEncoding)

/-- Strict image recognition and one uniform inverse translation transfer PSPACE. -/
theorem reencode_mem_PSPACE {α : Type} (old new : α ↪ List Bool) (D : PartialDecoder new)
    (convert : List Bool → List Bool) (hc : convert ∈ FP)
    (he : ∀ a, convert (new a) = old a) (S : Set α)
    (hS : old '' S ∈ Cslib.Complexity.PSPACE encBits) :
    new '' S ∈ Cslib.Complexity.PSPACE encBits := by
  have hEq : new '' S = {w | valid D w = true} ∩ convert ⁻¹' (old '' S) := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(valid_iff D _).mpr ⟨a, rfl⟩, a, ha, (he a).symm⟩
    · rintro ⟨hv, b, hb, hbw⟩
      obtain ⟨a, ha⟩ := (valid_iff D _).mp hv
      have hba : b = a := old.injective
        (hbw.trans ((congrArg convert ha).symm.trans (he a)))
      exact ⟨a, hba ▸ hb, ha⟩
  rw [hEq]
  apply Cslib.Complexity.inter_mem_PSPACE
  · exact Cslib.Complexity.P_subset_PSPACE
      ⟨valid D, valid_polyTime D, fun _ => Iff.rfl⟩
  · exact Computation.mem_PSPACE_preimage hc hS

def etrLanguage : Set (List Bool) :=
  {w | ∃ p : ETR.Formula, w = formulaEncoding p ∧ p.Satisfiable}

def spaceCode (n : ℕ) (p : ETR.Formula) := spaceEncoding (n, p)
def pointCode (n : ℕ) (p a b : ETR.Formula) := pointEncoding (n, [p, a, b])

def connectedLanguage : Set (List Bool) :=
  {w | ∃ d : Connectivity.Description, w = spaceCode d.dimension d.formula ∧ d.Connected}

def pointLanguage : Set (List Bool) :=
  {w | ∃ q : Connectivity.PointQuery,
    w = pointCode q.space.dimension q.space.formula q.source q.target ∧ q.Reachable}

theorem etr_mem_PSPACE : etrLanguage ∈ Cslib.Complexity.PSPACE encBits := by
  have hold : oldFormulaEncoding '' {p : ETR.Formula | p.Satisfiable} =
      AbstractEncodingBridge.etrLanguage := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, AbstractEncodingBridge.etrLanguage,
      oldFormulaEncoding, Function.Embedding.coeFn_mk]
    aesop
  have h := reencode_mem_PSPACE oldFormulaEncoding formulaEncoding formulaDecoder
    toFlat toFlat_FP toFlat_encoded {p : ETR.Formula | p.Satisfiable}
    (hold.symm ▸ AbstractEncodingBridge.etr_mem_PSPACE)
  convert h using 1
  ext w
  simp only [etrLanguage, Set.mem_ofPred_eq, Set.mem_image]
  aesop

theorem connected_mem_PSPACE : connectedLanguage ∈ Cslib.Complexity.PSPACE encBits := by
  let S : Set (ℕ × ETR.Formula) := {d | (Connectivity.Description.mk d.1 d.2).Connected}
  have hold : oldSpaceEncoding '' S = AbstractEncodingBridge.connectedLanguage := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, AbstractEncodingBridge.connectedLanguage]
    constructor
    · rintro ⟨⟨n, p⟩, hp, hw⟩
      exact ⟨⟨n, p⟩, hw.symm, hp⟩
    · rintro ⟨⟨n, p⟩, hw, hp⟩
      exact ⟨(n, p), hp, hw.symm⟩
  have h := reencode_mem_PSPACE oldSpaceEncoding spaceEncoding spaceDecoder spaceToFlat
    spaceToFlat_FP (fun ⟨n, p⟩ => spaceToFlat_encoded n p) S
    (hold.symm ▸ AbstractEncodingBridge.connected_mem_PSPACE)
  convert h using 1
  ext w
  simp only [connectedLanguage, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨n, p⟩, hw, hp⟩
    exact ⟨(n, p), hp, hw.symm⟩
  · rintro ⟨⟨n, p⟩, hp, hw⟩
    exact ⟨⟨n, p⟩, hw.symm, hp⟩

private theorem pointToFlat_list (n : ℕ) (ps : List ETR.Formula) :
    pointToFlat (pointEncoding (n, ps)) = oldPointEncoding (n, ps) := by
  have hl : mapFrames (fun token => frame (toFlat token)) (encList formulaEncoding ps) =
      encList oldFormulaEncoding ps := by
    rw [mapFrames, frames_encList]
    simp only [List.flatMap_map]
    change ps.flatMap (fun p => frame (toFlat (formulaEncoding p))) =
      ps.flatMap (fun p => frame (oldFormulaEncoding p))
    congr 1
    funext p
    rw [toFlat_encoded]
    rfl
  change frame (unframe (frame (encUnary n) ++ encList formulaEncoding ps)) ++
      mapFrames (fun token => frame (toFlat token))
        (dropFrame (frame (encUnary n) ++ encList formulaEncoding ps)) =
    frame (encUnary n) ++ encList oldFormulaEncoding ps
  rw [unframe_frame_append, dropFrame_frame_append, hl]

theorem point_mem_PSPACE : pointLanguage ∈ Cslib.Complexity.PSPACE encBits := by
  let S : Set (ℕ × List ETR.Formula) :=
    {d | ∃ p a b, d.2 = [p, a, b] ∧
      (Connectivity.PointQuery.mk (Connectivity.Description.mk d.1 p) a b).Reachable}
  have hold : oldPointEncoding '' S = AbstractEncodingBridge.pointLanguage := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, AbstractEncodingBridge.pointLanguage]
    constructor
    · rintro ⟨⟨n, ps⟩, ⟨p, a, b, rfl, hp⟩, hw⟩
      exact ⟨⟨⟨n, p⟩, a, b⟩, hw.symm, hp⟩
    · rintro ⟨⟨⟨n, p⟩, a, b⟩, hw, hp⟩
      exact ⟨(n, [p, a, b]), ⟨p, a, b, rfl, hp⟩, hw.symm⟩
  have h := reencode_mem_PSPACE oldPointEncoding pointEncoding pointDecoder pointToFlat
    pointToFlat_FP (fun ⟨n, ps⟩ => pointToFlat_list n ps) S
    (hold.symm ▸ AbstractEncodingBridge.point_mem_PSPACE)
  convert h using 1
  ext w
  simp only [pointLanguage, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨⟨n, p⟩, a, b⟩, hw, hp⟩
    exact ⟨(n, [p, a, b]), ⟨p, a, b, rfl, hp⟩, hw.symm⟩
  · rintro ⟨⟨n, ps⟩, ⟨p, a, b, rfl, hp⟩, hw⟩
    exact ⟨⟨⟨n, p⟩, a, b⟩, hw.symm, hp⟩

end LeanCanny.DerivedEncodingBridge
