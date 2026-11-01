/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalFactorModel
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeHeight
public import LeanCanny.Algebra.IntegralCriticalActualMonomialHeight
/-! # Exact actual physical height children of monomial factors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalMonomialHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalMonomialBits IntegralMixedPhysicalFactorBits IntegralCriticalActualLowMatrixModel
open IntegralCriticalActualMonomialHeight (heightMatrix)
set_option backward.isDefEq.respectTransparency false

noncomputable def heightAt (F : Family) (key : List Bool) (i r t m : ℕ) (hm : m ≠ 0) :=
  IntegralMixedPhysicalNativeLowerBits.heightAt (IntegralMixedPhysicalSnapshotBits.sourceAt F key 0 0 0 r t m hm) i
noncomputable def heightEntryAt (F : Family) (key : List Bool) (i r t m : ℕ) (hm : m ≠ 0) :=
  entryBits (heightMatrix (monomialAt F key 0 0 0 0 0 m hm) [] i) r t
noncomputable def heightEntry (P : Parameters) (F : Family) (q : List Bool) (i r t : ℕ) :=
  entryBits (heightMatrix (source P F) q i) r t

theorem height_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPhysicalNativeLowerBits.height P F q = heightAt F (IntegralMixedPhysicalTaskBits.saved P q)
      (get P .slot8 q) (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q) := rfl

theorem heightEntry_snapshot (P : Parameters) (F : Family) (q : List Bool) (i r t : ℕ) :
    heightEntry P F q i r t = heightEntryAt F (IntegralMixedPhysicalTaskBits.saved P q) i r t (modulus P q) (modulus_ne_zero P q) := by
  change entryBits (heightMatrix ((source P F).snapshot q) [] i) r t = _
  rw [source_snapshot]
  rfl

theorem heightEntryAt_value (F : Family) (key : List Bool) (i r t m : ℕ) (hm : m ≠ 0)
    (hr : r < rankAt F key) (ht : t < rankAt F key) : heightEntryAt F key i r t m hm = heightAt F key i r t m hm := by
  let E := (IntegralMixedPhysicalSnapshotBits.sourceAt F key 0 0 0 0 0 m hm).toEuler
  let := E.ring []
  have HR0 : r < (monomialAt F key 0 0 0 0 0 m hm).rank [] := hr
  have HT0 : t < (monomialAt F key 0 0 0 0 0 m hm).rank [] := ht
  refine (entryBits_fin (heightMatrix (monomialAt F key 0 0 0 0 0 m hm) [] i) ⟨r, HR0⟩ ⟨t, HT0⟩).trans ?_
  have HR : (⟨r % E.rank [], Nat.mod_lt _ (by change 0 < rankAt F key; unfold rankAt; exact pow_pos (Nat.two_pow_pos _) _)⟩ : Fin (E.rank [])) = ⟨r, hr⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hr)
  have HT : (⟨t % E.rank [], Nat.mod_lt _ (by change 0 < rankAt F key; unfold rankAt; exact pow_pos (Nat.two_pow_pos _) _)⟩ : Fin (E.rank [])) = ⟨t, ht⟩ :=
    Fin.ext (Nat.mod_eq_of_lt ht)
  change _ = residueBits ((Algebra.leftMulMatrix (E.basis []) (E.height [] i)
    ⟨r % E.rank [], _⟩ ⟨t % E.rank [], _⟩ : ℤ) : ZMod m)
  rw [HR, HT]
  rfl

theorem heightAt_congr (F : Family) (key key' : List Bool) (i r t m i' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hi : i = i') (hr : r = r') (ht : t = t') (hmod : m = m') :
    heightAt F key i r t m hm = heightAt F key' i' r' t' m' hm' := by
  subst key'; subst i'; subst r'; subst t'; subst m'
  rfl

theorem height_leaf (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (q : List Bool) (i : ℕ) (r t : Fin ((source P F).rank q)) :
    (access P a F h).height (IntegralMonomialTermBits.packet q i r.val t.val) =
      heightAt F (IntegralMixedPhysicalTaskBits.saved P q) i r.val t.val (modulus P q) (modulus_ne_zero P q) := by
  change (access P a F h).height (pair q (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) = _
  rw [(access P a F h).height_eq q i r t]
  refine (entryBits_fin (heightMatrix (source P F) q i) r t).symm.trans ?_
  change heightEntry P F q i r.val t.val = _
  rw [heightEntry_snapshot]
  apply heightEntryAt_value
  · rw [← rank_snapshot P F q]; exact r.isLt
  · rw [← rank_snapshot P F q]; exact t.isLt

theorem height_child (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) (i : ℕ)
    (r t : Fin ((source P F).rank q)) (hi : i ≤ numericCap P (RankedHistoryTask.root q)) :
    IntegralMixedPhysicalNativeLowerBits.height P F
      (IntegralCriticalFlatFactorQuery.writer P .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)) =
      (access P a F h).height (IntegralMonomialTermBits.packet q i r.val t.val) := by
  let child := IntegralCriticalFlatFactorQuery.writer P .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HR : RankedHistoryTask.root child = RankedHistoryTask.root q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_root P .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HB : birth P child = birth P q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_birth P .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HX : get P .slot15 child = get P .slot15 q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_other P .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val) .slot15 (by decide) (by decide) (by decide)
  have HM : modulus P child = modulus P q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_modulus P .clearedHeight (IntegralMonomialTermBits.packet q i r.val t.val)
  have HF := IntegralCriticalFlatFactorQuery.writer_packet_fields P .clearedHeight q i r.val t.val hi
    (r.isLt.le.trans (rank_cap P F g q)) (t.isLt.le.trans (rank_cap P F g q))
  change IntegralMixedPhysicalNativeLowerBits.height P F child = _
  rw [height_snapshot, HF.1, HF.2.1, HF.2.2, height_leaf P a F h q i r t]
  apply heightAt_congr
  · exact IntegralMixedPhysicalTaskBits.saved_invariance P q child HR HB HX
  · rfl
  · rfl
  · rfl
  · exact HM
end LeanCanny.Algebra.IntegralMixedPhysicalMonomialHeightBits
