/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelCircuit

/-! # Exact root semantics of the shared affine kernel query -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open MvPolynomial
open scoped Classical BigOperators

noncomputable def selectedPolynomial (p : MvPolynomial ℕ ℤ) (j : ℕ) : MvPolynomial ℕ ℤ :=
  if j = 0 then p else pderiv j p
noncomputable def entryPolynomial (p : MvPolynomial ℕ ℤ) (j k : ℕ) : MvPolynomial ℕ ℤ :=
  if j = 0 then pderiv k p else pderiv k (pderiv j p)
noncomputable def criticalValue (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (x : ℕ → ℂ) (j : ℕ) : ℂ :=
  (selectedPolynomial p j).eval₂ (Int.castRingHom ℂ) x +
    (coefficient v j : ℂ) * (pderiv 0 p).eval₂ (Int.castRingHom ℂ) x
noncomputable def kernelValue (p : MvPolynomial ℕ ℤ) (m : ℕ) (v : ℕ → ℤ) (x u : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range m, ((entryPolynomial p j k).eval₂ (Int.castRingHom ℂ) x +
    (coefficient v j : ℂ) * (pderiv k (pderiv 0 p)).eval₂ (Int.castRingHom ℂ) x) * u k

def Bad (p : MvPolynomial ℕ ℤ) (m : ℕ) (v : ℕ → ℤ) (chart : ℕ) : Prop :=
  ∃ x u : ℕ → ℂ, u chart = 1 ∧ ∀ j < m, criticalValue p v x j = 0 ∧ kernelValue p m v x u j = 0

theorem jet_sound (wire : ℕ → MvPolynomial ℕ ℤ) (start m : ℕ) (ops : List Operation) (out : ℕ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length)
    (x env : ℕ → ℂ) (hx : ∀ i < start, env i = x i) (hz : env (zeroWire start m) = 0)
    (hg : ∀ g ∈ HessianFamily.gates (zeroWire start m) (copyBase start m) start m ops (m * m), g.Holds env)
    (j k : ℕ) (hj : j < m) (hk : k < m) :
    env (jetWire start m ops out j k 0) = (wire out).eval₂ (Int.castRingHom ℂ) x ∧
      env (jetWire start m ops out j k 3) = (pderiv k (wire out)).eval₂ (Int.castRingHom ℂ) x ∧
      env (jetWire start m ops out j k 15) = (pderiv k (pderiv j (wire out))).eval₂ (Int.castRingHom ℂ) x := by
  have hm : 0 < m := by omega
  have hq : j * m + k < m * m := by nlinarith
  have hdiv : (j * m + k) / m = j := by
    rw [Nat.mul_comm j m, Nat.mul_add_div hm, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmod : (j * m + k) % m = k := by rw [Nat.mul_comm j m, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  have h := HessianFamily.sound wire (zeroWire start m) (copyBase start m) start m ops hw hr hin
    x env hz hx (m * m) hg (j * m + k) hq out ho
  rw [hdiv, hmod] at h
  have h0 : jetWire start m ops out j k 0 = HessianFamily.blockStart (copyBase start m) start ops (j * m + k) +
      Differential.valueWire (Differential.valueWire out) := by unfold jetWire Differential.valueWire; omega
  have h3 : jetWire start m ops out j k 3 = HessianFamily.blockStart (copyBase start m) start ops (j * m + k) +
      Differential.derivativeWire (Differential.valueWire out) := by
    unfold jetWire Differential.valueWire Differential.derivativeWire; omega
  have h15 : jetWire start m ops out j k 15 = HessianFamily.blockStart (copyBase start m) start ops (j * m + k) +
      Differential.derivativeWire (Differential.derivativeWire out) := by
    unfold jetWire Differential.derivativeWire; omega
  exact ⟨h0 ▸ h.1, h3 ▸ h.2.1, h15 ▸ h.2.2.2⟩

theorem rows_sound (wire : ℕ → MvPolynomial ℕ ℤ) (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length)
    (x u env : ℕ → ℂ) (hx : ∀ i < start, env i = x i) (hu : ∀ k < m, env (start + k) = u k)
    (hg : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m ops out v), g.Holds env) :
    ∀ j < m,
      env (KernelRow.criticalWire (rowStart start m ops j) m) = criticalValue (wire out) v x j ∧
      env (KernelRow.sumWire (zeroWire start m) (rowStart start m ops j) m) = kernelValue (wire out) m v x u j := by
  have hz : env (zeroWire start m) = 0 := by
    have h := hg (.constant (zeroWire start m) 0) (by rw [gates_eq]; simp)
    simpa only [Gate.Holds, Int.cast_zero] using h
  have hfamily : ∀ g ∈ HessianFamily.gates (zeroWire start m) (copyBase start m) start m ops (m * m), g.Holds env := by
    intro g h
    exact hg g (by rw [gates_eq]; exact List.mem_append_left _ (List.mem_append_right _ h))
  have hjets := jet_sound wire start m ops out hw hr hin ho x env hx hz hfamily
  intro j hj
  have hm : 0 < m := by omega
  have hrow : ∀ g ∈ StraightLine.gates (rowStart start m ops j) (row start m ops out v j), g.Holds env := by
    intro g h
    rw [gates_eq] at hg
    exact hg g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, h⟩))
  have h := KernelRow.sound (zeroWire start m) (rowStart start m ops j) start m
    (selectedValue start m ops out j) (gradientWire start m ops out 0) (coefficient v j)
    (hessianWire start m ops out 0) (entry start m ops out j) env hz hrow
  have hb : env (gradientWire start m ops out 0) = (pderiv 0 (wire out)).eval₂ (Int.castRingHom ℂ) x :=
    (hjets 0 0 hm hm).2.1
  have hv : env (selectedValue start m ops out j) = (selectedPolynomial (wire out) j).eval₂ (Int.castRingHom ℂ) x := by
    unfold selectedValue selectedPolynomial
    split_ifs
    · exact (hjets 0 0 hm hm).1
    · exact (hjets 0 j hm hj).2.1
  have he (k : ℕ) (hk : k < m) : env (entry start m ops out j k) =
      (entryPolynomial (wire out) j k).eval₂ (Int.castRingHom ℂ) x := by
    unfold entry entryPolynomial
    split_ifs
    · exact (hjets 0 k hm hk).2.1
    · exact (hjets j k hj hk).2.2
  refine ⟨h.2.trans ?_, h.1.trans ?_⟩
  · rw [hv, hb]
    rfl
  · apply Finset.sum_congr rfl
    intro k hk
    have hkm := Finset.mem_range.mp hk
    rw [he k hkm, hessianWire, (hjets 0 k hm hkm).2.2, hu k hkm]

theorem constraints_holds_iff (start m : ℕ) (ops : List Operation) (chart : ℕ) (env : ℕ → ℂ) :
    (∀ g ∈ constraints start m ops chart, g.Holds env) ↔ env (start + chart) = 1 ∧
      ∀ j < m, env (KernelRow.sumWire (zeroWire start m) (rowStart start m ops j) m) = 0 ∧
        env (KernelRow.criticalWire (rowStart start m ops j) m) = 0 := by
  constructor
  · intro hg
    have hn := hg (.constant (start + chart) 1) (List.mem_append_left _ (by simp))
    refine ⟨by simpa only [Gate.Holds, Int.cast_one] using hn, fun j hj => ?_⟩
    have hm (g : Gate) (h : g ∈ [.zero (KernelRow.sumWire (zeroWire start m) (rowStart start m ops j) m),
        .zero (KernelRow.criticalWire (rowStart start m ops j) m)]) : g ∈ constraints start m ops chart :=
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, h⟩)
    exact ⟨hg (.zero (KernelRow.sumWire (zeroWire start m) (rowStart start m ops j) m)) (hm _ (by simp)),
      hg (.zero (KernelRow.criticalWire (rowStart start m ops j) m)) (hm _ (by simp))⟩
  · rintro ⟨hn, hrows⟩ g hg
    rcases List.mem_append.mp hg with h | h
    · have he : g = .constant (start + chart) 1 := by simpa only [List.mem_singleton] using h
      subst g
      simpa only [Gate.Holds, Int.cast_one] using hn
    · obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp h
      have hr := hrows j (List.mem_range.mp hj)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact hr.1
      · exact hr.2

theorem query_satisfiable (wire : ℕ → MvPolynomial ℕ ℤ) (start m : ℕ) (ops : List Operation) (out : ℕ)
    (v : ℕ → ℤ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length) :
    Satisfiable (query start m ops out v chart) ↔ Bad (wire out) m v chart := by
  constructor
  · rintro ⟨env, hg⟩
    have hp : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m ops out v), g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hc : ∀ g ∈ constraints start m ops chart, g.Holds env :=
      fun g h => hg g (List.mem_append_right _ h)
    obtain ⟨hn, hc⟩ := (constraints_holds_iff start m ops chart env).mp hc
    have hs := rows_sound wire start m ops out v hw hr hin ho env (fun k => env (start + k)) env
      (fun _ _ => rfl) (fun _ _ => rfl) hp
    refine ⟨env, (fun k => env (start + k)), hn, fun j hj => ?_⟩
    exact ⟨(hs j hj).1.symm.trans (hc j hj).2, (hs j hj).2.symm.trans (hc j hj).1⟩
  · rintro ⟨x, u, hn, hroot⟩
    let initial : ℕ → ℂ := fun r => if r < start then x r else u (r - start)
    obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion initial (zeroWire start m)
      (program start m ops out v) (wellFormed start m ops out v hw ho)
    have hx : ∀ i < start, env i = x i := by
      intro i hi
      rw [hp i (by unfold zeroWire; omega)]
      exact ite_eq_left hi
    have hu : ∀ k < m, env (start + k) = u k := by
      intro k hk
      rw [hp _ (by unfold zeroWire; omega)]
      simp only [initial, ite_eq_right (show ¬ start + k < start by omega), Nat.add_sub_cancel_left]
    have hs := rows_sound wire start m ops out v hw hr hin ho x u env hx hu hg
    refine ⟨env, ?_⟩
    intro g h
    rcases List.mem_append.mp h with h | h
    · exact hg g h
    · have hc : ∀ g ∈ constraints start m ops chart, g.Holds env := by
        apply (constraints_holds_iff start m ops chart env).mpr
        refine ⟨(hu chart hchart).trans hn, fun j hj => ?_⟩
        exact ⟨(hs j hj).2.trans (hroot j hj).2, (hs j hj).1.trans (hroot j hj).1⟩
      exact hc g h

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
