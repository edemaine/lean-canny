/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FormulaPathCover
public import LeanCanny.Connectivity.InputFP
public import LeanCanny.ETR.InterleaveFP
public import LeanCanny.ETR.FormulaArityFP

/-! # Validating singleton endpoint descriptions with ETR

Two disjoint copies of a formula admit different values in coordinate `i`
exactly when the endpoint is nonunique in that coordinate. Scanning the
declared coordinates uses polynomial space. No approximation or separation
bound for algebraic coordinates is needed.
-/

@[expose] public section

namespace LeanCanny.Connectivity.EndpointValidation
open ETR Computation Turing.MultiTapeTM
open scoped Classical

def merge (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then a (k / 2) else b (k / 2)

@[simp] theorem merge_even (a b : ℕ → ℝ) (i : ℕ) : merge a b (2 * i) = a i := by
  simp [merge]

@[simp] theorem merge_odd (a b : ℕ → ℝ) (i : ℕ) : merge a b (2 * i + 1) = b i := by
  simp [merge, Nat.add_mod, Nat.add_div]

def difference (i : ℕ) : Formula :=
  .not (.eqZero (.add (.var (2 * i)) (.mul (.const (-1)) (.var (2 * i + 1)))))

def distinctQuery (p : Formula) (i : ℕ) : Formula :=
  .and (p.rename (Interleave.index false))
    (.and (p.rename (Interleave.index true)) (difference i))

theorem distinctQuery_holds (p : Formula) (i : ℕ) (env : ℕ → ℝ) :
    (distinctQuery p i).Holds env ↔
      p.Holds (fun k => env (2 * k)) ∧ p.Holds (fun k => env (2 * k + 1)) ∧
        env (2 * i) ≠ env (2 * i + 1) := by
  simp [distinctQuery, difference, Formula.Holds, Formula.holds_rename,
    Interleave.index, Function.comp_def, Term.eval, ← sub_eq_add_neg, sub_eq_zero]

theorem distinctQuery_satisfiable (p : Formula) (i : ℕ) :
    (distinctQuery p i).Satisfiable ↔
      ∃ a b : ℕ → ℝ, p.Holds a ∧ p.Holds b ∧ a i ≠ b i := by
  constructor
  · rintro ⟨env, h⟩
    exact ⟨fun k => env (2 * k), fun k => env (2 * k + 1),
      (distinctQuery_holds p i env).mp h⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨merge a b, (distinctQuery_holds p i (merge a b)).mpr (by simp [ha, hb, hab])⟩

/-- A well-formed endpoint denotes one point iff it has a solution and no
coordinate admits two different values. This also covers dimension zero. -/
theorem exists_denotes_iff {p : Formula} {n : ℕ} (hp : p.arity ≤ n) :
    (∃ x : Fin n → ℝ, Denotes n p x) ↔
      p.Satisfiable ∧ ∀ i < n, ¬ (distinctQuery p i).Satisfiable := by
  have restrict (env : ℕ → ℝ) :
      p.Holds env ↔ p.Holds (Formula.extend (fun i : Fin n => env i.val)) := by
    apply p.holds_congr
    intro i hi
    simp [Formula.extend, hi.trans_le hp]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨Formula.extend x, (hx.2 x).mpr rfl⟩, ?_⟩
    intro i hi h
    obtain ⟨a, b, ha, hb, hab⟩ := (distinctQuery_satisfiable p i).mp h
    have heA := (hx.2 _).mp ((restrict a).mp ha)
    have heB := (hx.2 _).mp ((restrict b).mp hb)
    exact hab ((congrFun heA ⟨i, hi⟩).trans (congrFun heB ⟨i, hi⟩).symm)
  · rintro ⟨⟨env, henv⟩, huniq⟩
    refine ⟨fun i => env i.val, hp, ?_⟩
    intro y
    constructor
    · intro hy
      funext i
      by_contra he
      exact huniq i.val i.isLt ((distinctQuery_satisfiable p i.val).mpr
        ⟨Formula.extend y, env, hy, henv, by simpa [Formula.extend] using he⟩)
    · rintro rfl
      exact (restrict env).mp henv

def distinctBits (packet : List Bool) : List Bool :=
  Codec.taggedTwo 4 (Interleave.renameBits false (LeanCanny.pairFst packet))
    (Codec.taggedTwo 4 (Interleave.renameBits true (LeanCanny.pairFst packet))
      (Codec.taggedOne 3 (Codec.taggedOne 1
        (Codec.taggedTwo 2
          (Term.variableBits (2 * (LeanCanny.pairSnd packet).length))
          (Codec.taggedTwo 3 (Term.const (-1)).toData.toBits
            (Term.variableBits (2 * (LeanCanny.pairSnd packet).length + 1)))))))

theorem distinctBits_mem_FP : distinctBits ∈ LeanCanny.FP := by
  have hk := LeanCanny.UnaryFn.length LeanCanny.pairSnd_mem_FP
  have he := (LeanCanny.UnaryFn.const 2).mul hk
  have ho := he.add (LeanCanny.UnaryFn.const 1)
  have hv0 := Term.variableBits_mem_FP he
  have hv1 := Term.variableBits_mem_FP ho
  have hd := Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 1
    (Codec.taggedTwo_mem_FP 2 hv0
      (Codec.taggedTwo_mem_FP 3 (LeanCanny.constFn_mem_FP (Term.const (-1)).toData.toBits) hv1)))
  have hp0 := LeanCanny.mem_FP_comp LeanCanny.pairFst_mem_FP (Interleave.renameBits_mem_FP false)
  have hp1 := LeanCanny.mem_FP_comp LeanCanny.pairFst_mem_FP (Interleave.renameBits_mem_FP true)
  exact Codec.taggedTwo_mem_FP 4 hp0 (Codec.taggedTwo_mem_FP 4 hp1 hd)

theorem distinctBits_pair (p : Formula) (i : ℕ) :
    distinctBits (LeanCanny.pair p.encode (List.replicate i true)) = (distinctQuery p i).encode := by
  simp only [distinctBits, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair,
    List.length_replicate, Interleave.renameBits_encode]
  simp only [distinctQuery, difference, Formula.encode, Formula.toData, Term.toData,
    Codec.taggedOne_toBits, Codec.taggedTwo_toBits, Term.variableBits_eq]


/-- Uniformly write the nonuniqueness query at a unary-computable coordinate. -/
theorem distinctQuery_computable {α : Type} {enc : α ↪ List Bool}
    {p : α → Formula} {i : α → ℕ}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hi : ComputableTidilyInPolyTime i enc encUnary) :
    ComputableTidilyInPolyTime (fun a => (distinctQuery (p a) (i a)).encode) enc encBits := by
  have hargs := LeanCanny.pair_computable hp hi.encoded
  exact (distinctBits_mem_FP.comp hargs).of_enc_eq fun a => (distinctBits_pair (p a) (i a)).symm

/-- Native polynomial-space singleton validation. Inconsistent, nonunique,
and dimensionally ill-formed descriptions are rejected. The original query
writer and unary dimension are charged. -/
theorem exists_denotes_computable {α : Type} [Inhabited α] {enc : α ↪ List Bool}
    {p : α → Formula} {n : α → ℕ}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolySpace
      (fun a => decide (∃ x : Fin (n a) → ℝ, Denotes (n a) (p a) x)) enc encBool := by
  have hpar := ComputableTidilyInPolyTime.fst enc encNat
  have hcounter := ComputableTidilyInPolyTime.snd enc encNat
  -- The total query writer caps a binary counter before expanding its index.
  have hcap := hn.comp hpar
  have hdecode := ComputableTidilyInPolyTime.bitsBoundedBinaryValueWithInput hcap
    (ComputableTidilyInPolyTime.bitsReverse.comp hcounter.encoded)
  have hindex : ComputableTidilyInPolyTime
      (fun q : α × ℕ => min q.2 (n q.1)) (encPair enc encNat) encUnary := by
    apply hdecode.of_enc_eq
    intro q
    apply congrArg encUnary
    simp [Cslib.BitString.boundedBinaryValue_eq, Cslib.BitString.binaryValue_reverse_bits,
      encNat_apply, Nat.min_comm]
  have hqueries := satisfiable_computable (distinctQuery_computable (hp.comp hpar) hindex)
  have hfalse : ComputableTidilyInPolySpace (fun _ : α × ℕ => false)
      (encPair enc encNat) encBool := .of_polyTime (.const false)
  have htrue : ComputableTidilyInPolySpace (fun _ : α × ℕ => true)
      (encPair enc encNat) encBool := .of_polyTime (.const true)
  have hnot := hqueries.ite hfalse htrue
  have hall := ImplicitGraph.forall_below_computable hnot
    (ComputableTidilyInPolyTime.unary_to_binary.comp hn)
  have hsat := satisfiable_computable hp
  have hf : ComputableTidilyInPolySpace (fun _ : α => false) enc encBool := .of_polyTime (.const false)
  have harity : ComputableTidilyInPolyTime (fun a => (p a).arity) enc encUnary := by
    apply (ComputableTidilyInPolyTime.comp FormulaArity.value_unary hp).of_enc_eq
    intro a
    exact congrArg encUnary (FormulaArity.value_encode (p a)).symm
  have hwell := ComputableTidilyInPolyTime.unary_le' harity hn
  apply ((ComputableTidilyInPolySpace.of_polyTime hwell).ite (hsat.ite hall hf) hf).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Function.comp_apply]
  by_cases hb : (p a).arity ≤ n a
  · simp only [hb, ite_true]
    rw [exists_denotes_iff hb]
    by_cases hs : (p a).Satisfiable
    · simp only [hs, ite_true, true_and, decide_eq_true_eq]
      apply forall_congr'
      intro k
      apply forall_congr'
      intro hk
      simp [min_eq_left (Nat.le_of_lt hk)]
    · simp [hs]
  · have hbad : ¬ ∃ x : Fin (n a) → ℝ, Denotes (n a) (p a) x := by
      rintro ⟨x, hx⟩
      exact hb hx.1
    simp [hb, hbad]

/-- Endpoint validation only: both formulas describe single points of the
declared dimension. Membership in the space and path reachability are separate. -/
def validEndpointLanguage : Language :=
  {bits | ∃ q : PointQuery, bits = (Input.point q).encode ∧
    (∃ x : Fin q.space.dimension → ℝ, Denotes q.space.dimension q.source x) ∧
    (∃ y : Fin q.space.dimension → ℝ, Denotes q.space.dimension q.target y)}

@[simp] theorem validEndpoint_encode (q : PointQuery) :
    (Input.point q).encode ∈ validEndpointLanguage ↔
      (∃ x : Fin q.space.dimension → ℝ, Denotes q.space.dimension q.source x) ∧
      (∃ y : Fin q.space.dimension → ℝ, Denotes q.space.dimension q.target y) := by
  simp only [validEndpointLanguage, Set.mem_ofPred_eq, Input.encode_injective.eq_iff,
    Input.point.injEq, exists_eq_left']

/-- The complete canonical point-input endpoint check is in native PSPACE.
Malformed inputs, out-of-dimension variables, and nonunique or inconsistent
endpoint descriptions are rejected on every bitstring. -/
theorem validEndpoints_mem_PSPACE : validEndpointLanguage ∈ PSPACE := by
  have hn := Codec.unaryValue_unary.comp (Input.field_mem_FP 1)
  have hs := exists_denotes_computable
    (FormulaView.encoded_computable.comp (Input.field_mem_FP 3)) hn
  have ht := exists_denotes_computable
    (FormulaView.encoded_computable.comp (Input.field_mem_FP 4)) hn
  have hf : ComputableTidilyInPolySpace (fun _ : List Bool => false) encBits encBool :=
    .of_polyTime (.const false)
  have hp := ComputableTidilyInPolySpace.of_polyTime Input.isPoint_fppred.computable
  apply NativeSpace.of_computable (hp.ite (hs.ite ht hf) hf)
  intro bits
  by_cases hpoint : Input.IsPoint bits
  · obtain ⟨q, rfl⟩ := (Input.isPoint_iff bits).mp hpoint
    have hdim := congrArg Codec.unaryValue (Input.field_point_dimension q)
    simp only [Codec.unaryValue_toBits] at hdim
    simp only [hpoint, decide_true, ite_true, validEndpoint_encode, decide_eq_true_eq,
      Function.comp_apply, Input.field_point_source, Input.field_point_target, FormulaView.formula_encode]
    rw [hdim]
    simp
  · have hbad : bits ∉ validEndpointLanguage := by
      rintro ⟨q, rfl, _, _⟩
      exact hpoint ((Input.isPoint_iff _).mpr ⟨q, rfl⟩)
    simp [hpoint, hbad]

end LeanCanny.Connectivity.EndpointValidation
