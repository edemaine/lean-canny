/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryPrefix
public import LeanCanny.Algebra.IntegralMixedFullHistoryFamily
/-! # Actual changing-source prefixes as a generic cut family

A saved birth key uses the source of its next creating instruction. Its bank
is the actual run of all earlier instructions, reframed without a new birth.
Chronological source lookup is independent of the auxiliary context field.
Native header/body readers remain separate obligations; this module does not
assume any evaluator for the interpreted history.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

structure Plan (P : Parameters) where
  initialSource : ∀ root, SpatialSource (P.ambient root)
  initial_degree : ∀ root, (initialSource root).degree=P.degree root
  scalar_cap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root
  rules : ∀ root, List (Instruction (P.ambient root) (P.width root))
  room : ∀ root, (rules root).length+2≤P.cap root+1

noncomputable def initial (P : Parameters) (D : Plan P) (root : List Bool) :
    State (D.initialSource root) (P.cap root+1) (P.width root) 0 (Fin 0) :=
  IntegralMixedHistory.base (D.initialSource root) (IntegralHistorySampler.base (P.cap root+1) (2^P.width root))
    (by
      rw [D.initial_degree]
      exact (by unfold IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K; omega :
        PurePowerReductionBounds.dimension (P.ambient root+1) (P.degree root)≤
          IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)).trans (D.scalar_cap root))

noncomputable def defaultInstruction (P : Parameters) (D : Plan P) (root : List Bool) :
    Instruction (P.ambient root) (P.width root) where
  source := D.initialSource root
  source_cap := (initial P D root).critical_cap
  command := IntegralMixedFullHistoryScript.defaultCommand

abbrev prefixLength := IntegralMixedFullHistoryFamilyBits.prefixLength

noncomputable def commands (P : Parameters) (D : Plan P) (key : List Bool) :=
  paddedPast (defaultInstruction P D (pairFst key)) (D.rules (pairFst key)) (prefixLength P key)

noncomputable def instruction (P : Parameters) (D : Plan P) (key : List Bool) :=
  (chronological (D.rules (pairFst key)) (prefixLength P key)).getD (defaultInstruction P D (pairFst key))

structure Data (P : Parameters) (D : Plan P) where
  degree_eq : ∀ key, (instruction P D key).source.degree=P.degree (pairFst key)
  sourceWidth : ∀ key, (instruction P D key).source.degree.size≤P.sourceWidth (pairFst key)
  fallback : ∀ key, IntegralMixedFullHistoryFamilyBits.Selection (instruction P D key).source

noncomputable def selection (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool) :
    IntegralMixedFullHistoryFamilyBits.Selection (instruction P D key).source :=
  match (instruction P D key).command with
  | .cut r k d ha _ => ⟨r,k,d,ha⟩
  | _ => H.fallback key

noncomputable def family (P : Parameters) (D : Plan P) (H : Data P D) : IntegralMixedCutSource.Family where
  ambient key := P.ambient (pairFst key)
  cap key := P.cap (pairFst key)+1
  width key := P.width (pairFst key)
  birth key := (commands P D key).length
  physical key := Index (Fin 0) (commands P D key)
  spatial key := (instruction P D key).source
  state key := reframe (run (initial P D (pairFst key)) (commands P D key) (by
      rw [commands, paddedPast_length]
      exact (min_le_right _ _).trans (Nat.le_succ _)))
    (instruction P D key).source (instruction P D key).source_cap
  birth_bound key := by rw [commands,paddedPast_length]; exact min_le_right _ _
  rule key := (selection P D H key).rule
  kind key := (selection P D H key).kind
  degree key := (selection P D H key).degree
  degree_bound key := (selection P D H key).degree_bound
  scalar_cap key := by rw [H.degree_eq]; exact D.scalar_cap (pairFst key)

theorem family_birth (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool) :
    (family P D H).birth key=prefixLength P key := paddedPast_length _ _ _

theorem family_spatial (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool) :
    (family P D H).spatial key=(instruction P D key).source := rfl

theorem family_bank (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool) :
    ((family P D H).state key).bank=
      (run (initial P D (pairFst key)) (commands P D key)
        (((family P D H).birth_bound key).trans (Nat.le_succ _))).bank := rfl

theorem family_canonical (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool) :
    Canonical ((family P D H).state key) := by
  apply reframe_canonical
  apply run_canonical
  intro i
  exact Fin.elim0 i

theorem geometry (P : Parameters) (D : Plan P) (H : Data P D) :
    IntegralMixedVirtualCaps.RootGeometry P (family P D H) where
  ambient q := by change P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q))≤_; rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  degree q := by
    change (instruction P D (IntegralMixedVirtualTaskBits.saved P q)).source.degree≤_
    rw [H.degree_eq,IntegralMixedFullHistoryFamilyBits.saved_root]
  sourceWidth q := by
    have HW := H.sourceWidth (IntegralMixedVirtualTaskBits.saved P q)
    exact HW.trans_eq (congrArg P.sourceWidth (IntegralMixedFullHistoryFamilyBits.saved_root P q))
  width q := by change P.width (pairFst (IntegralMixedVirtualTaskBits.saved P q))=_; rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  birth q := (family_birth P D H _).trans (IntegralMixedFullHistoryFamilyBits.saved_prefix P q)

noncomputable def origin (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) :=
  IntegralMixedFramedHistoryScript.origin (initial P D (pairFst key)) (commands P D key)
    (((family P D H).birth_bound key).trans (Nat.le_succ _)) i

theorem origin_birth (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) :
    (older (commands P D key) i).length=prefixLength P key-1-i.val := by
  exact (older_length (commands P D key) ⟨i.val,i.isLt⟩).trans
    (congrArg (fun length : ℕ => length-1-i.val) (family_birth P D H key))

theorem origin_instruction (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) :
    chosen (commands P D key) i=
      (chronological (D.rules (pairFst key)) (prefixLength P key-1-i.val)).getD
        (defaultInstruction P D (pairFst key)) := by
  have HI : i.val<prefixLength P key := lt_of_lt_of_eq i.isLt (family_birth P D H key)
  have HB : prefixLength P key-1-i.val<prefixLength P key := by omega
  have HA := chronological_older (commands P D key) i
  rw [origin_birth P D H key i] at HA
  have HC := paddedPast_chronological (defaultInstruction P D (pairFst key))
    (D.rules (pairFst key)) (prefixLength P key) _ HB
  exact Option.some.inj (HA.symm.trans HC)

theorem origin_denominator (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) :
    ((family P D H).state key).bank.denominator i=
      IntegralMixedFullHistoryScript.leading
        (birthState (initial P D (pairFst key)) (commands P D key)
          (((family P D H).birth_bound key).trans (Nat.le_succ _)) i)
        (older_bound (commands P D key) (((family P D H).birth_bound key).trans (Nat.le_succ _)) i)
        (chosen (commands P D key) i).command := (origin P D H key i).denominator_eq

abbrev keyAt (root : List Bool) (birth : ℕ) (context : List Bool) :=
  pair root (pair (BinaryNatCode.encode birth) context)

theorem keyAt_root (root : List Bool) (birth : ℕ) (context : List Bool) :
    pairFst (keyAt root birth context)=root := pairFst_pair _ _

theorem keyAt_prefix (P : Parameters) (root : List Bool) (birth : ℕ) (context : List Bool)
    (hb : birth≤P.cap root+1) : prefixLength P (keyAt root birth context)=birth := by
  simp only [prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,keyAt,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,min_eq_left hb]

private theorem lookup_congr (P : Parameters) (D : Plan P) (root root' : List Bool) (birth birth' : ℕ)
    (hr : root=root') (hb : birth=birth') :
    HEq ((chronological (D.rules root) birth).getD (defaultInstruction P D root))
      ((chronological (D.rules root') birth').getD (defaultInstruction P D root')) := by
  cases hr
  cases hb
  rfl

theorem origin_instruction_key (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Fin ((family P D H).birth key)) (context : List Bool) :
    HEq (chosen (commands P D key) i)
      (instruction P D (keyAt (pairFst key) (prefixLength P key-1-i.val) context)) := by
  have HB : prefixLength P key-1-i.val≤P.cap (pairFst key)+1 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))
  have HO := heq_of_eq (origin_instruction P D H key i)
  exact HO.trans (lookup_congr P D _ _ _ _
    (keyAt_root (pairFst key) (prefixLength P key-1-i.val) context).symm
    (keyAt_prefix P (pairFst key) (prefixLength P key-1-i.val) context HB).symm)

end LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits
