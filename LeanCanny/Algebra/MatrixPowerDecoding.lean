/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerEncoding

/-!
# Exact decoding of matrix-power states

Decoders check binary natural fields, index bounds, tags, and complete framing.
The stack parser uses fuel bounded by the input's bit length. Re-encoding checks
make successful decoding equivalent to equality with the canonical code, even
when a supplied scalar decoder accepts additional representations.

The resulting checked transition agrees with the abstract machine on every
encoded state. `MatrixPowerController` supplies an FP transition using direct
string projections and an invariant of encoded states; the checked decoder
transition here remains a separate reference implementation.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower


variable {R : Type} {n : ℕ}

def checkedDecode {α : Type*} (enc : α → List Bool) (raw : List Bool → Option α)
    (bits : List Bool) : Option α := do
  let x ← raw bits
  if enc x = bits then some x else none

theorem checkedDecode_encode {α : Type*} (enc : α → List Bool) (raw : List Bool → Option α)
    (hraw : ∀ x, raw (enc x) = some x) (x : α) :
    checkedDecode enc raw (enc x) = some x := by simp [checkedDecode, hraw]

theorem checkedDecode_eq_some_iff {α : Type*} (enc : α → List Bool) (raw : List Bool → Option α)
    (hraw : ∀ x, raw (enc x) = some x) (bits : List Bool) (x : α) :
    checkedDecode enc raw bits = some x ↔ bits = enc x := by
  constructor
  · intro h
    cases hr : raw bits with
    | none => simp [checkedDecode, hr] at h
    | some y =>
        by_cases hy : enc y = bits
        · simp [checkedDecode, hr, hy] at h
          subst y
          exact hy.symm
        · simp [checkedDecode, hr, hy] at h
  · rintro rfl
    exact checkedDecode_encode enc raw hraw x

def decodeFin? (n : ℕ) (bits : List Bool) : Option (Fin n) := do
  let k ← BinaryNatCode.decode? bits
  if hk : k < n then some ⟨k, hk⟩ else none

@[simp] theorem decodeFin?_encode (k : Fin n) :
    decodeFin? n (BinaryNatCode.encode k.val) = some k := by
  simp [decodeFin?, k.isLt]

def rawQuery? (n : ℕ) (bits : List Bool) : Option (Query n) := do
  let (h, rest) ← unpair? bits
  let (e, indices) ← unpair? rest
  let (i, j) ← unpair? indices
  let h ← BinaryNatCode.decode? h
  let e ← BinaryNatCode.decode? e
  let i ← decodeFin? n i
  let j ← decodeFin? n j
  pure ⟨h, e, i, j⟩

@[simp] theorem rawQuery?_queryBits (q : Query n) : rawQuery? n (queryBits q) = some q := by
  simp [rawQuery?, queryBits]

def decodeQuery? (n : ℕ) : List Bool → Option (Query n) := checkedDecode queryBits (rawQuery? n)

@[simp] theorem decodeQuery?_queryBits (q : Query n) : decodeQuery? n (queryBits q) = some q :=
  checkedDecode_encode _ _ rawQuery?_queryBits q

theorem decodeQuery?_eq_some_iff (bits : List Bool) (q : Query n) :
    decodeQuery? n bits = some q ↔ bits = queryBits q :=
  checkedDecode_eq_some_iff _ _ rawQuery?_queryBits bits q

def rawFrame? (n : ℕ) (dec : List Bool → Option R) : List Bool → Option (Frame R n)
  | false :: bits => do
      let (q, rest) ← unpair? bits
      let (k, acc) ← unpair? rest
      let q ← decodeQuery? n q
      let k ← decodeFin? n k
      let acc ← dec acc
      pure (.left q k acc)
  | true :: bits => do
      let (q, rest) ← unpair? bits
      let (k, scalars) ← unpair? rest
      let (acc, lhs) ← unpair? scalars
      let q ← decodeQuery? n q
      let k ← decodeFin? n k
      let acc ← dec acc
      let lhs ← dec lhs
      pure (.right q k acc lhs)
  | [] => none

theorem rawFrame?_frameBits (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (f : Frame R n) :
    rawFrame? n dec (frameBits enc f) = some f := by
  cases f <;> simp [rawFrame?, frameBits, hdec]

def decodeFrame? (n : ℕ) (enc : R → List Bool) (dec : List Bool → Option R) :
    List Bool → Option (Frame R n) := checkedDecode (frameBits enc) (rawFrame? n dec)

@[simp] theorem decodeFrame?_frameBits (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (f : Frame R n) :
    decodeFrame? n enc dec (frameBits enc f) = some f :=
  checkedDecode_encode _ _ (rawFrame?_frameBits enc dec hdec) f

def rawStackFuel? (n : ℕ) (enc : R → List Bool) (dec : List Bool → Option R) :
    ℕ → List Bool → Option (List (Frame R n))
  | 0, bits => if bits = [] then some [] else none
  | _ + 1, [] => some []
  | fuel + 1, true :: bits => do
      let (f, rest) ← unpair? bits
      let f ← decodeFrame? n enc dec f
      let rest ← rawStackFuel? n enc dec fuel rest
      pure (f :: rest)
  | _ + 1, false :: _ => none

theorem rawStackFuel?_stackBits (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (stack : List (Frame R n))
    (fuel : ℕ) (hf : stack.length ≤ fuel) :
    rawStackFuel? n enc dec fuel (stackBits enc stack) = some stack := by
  induction stack generalizing fuel with
  | nil => cases fuel <;> simp [stackBits, rawStackFuel?]
  | cons f stack ih =>
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
          have ht : stack.length ≤ fuel := by simpa using hf
          simp [stackBits, rawStackFuel?, decodeFrame?_frameBits enc dec hdec, ih fuel ht]

theorem stackBits_length_ge (enc : R → List Bool) (stack : List (Frame R n)) :
    stack.length ≤ (stackBits enc stack).length := by
  induction stack <;> simp_all [stackBits]; omega

def rawStack? (n : ℕ) (enc : R → List Bool) (dec : List Bool → Option R)
    (bits : List Bool) : Option (List (Frame R n)) := rawStackFuel? n enc dec bits.length bits

def decodeStack? (n : ℕ) (enc : R → List Bool) (dec : List Bool → Option R) :
    List Bool → Option (List (Frame R n)) := checkedDecode (stackBits enc) (rawStack? n enc dec)

@[simp] theorem decodeStack?_stackBits (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (stack : List (Frame R n)) :
    decodeStack? n enc dec (stackBits enc stack) = some stack := by
  apply checkedDecode_encode
  intro s
  exact rawStackFuel?_stackBits enc dec hdec s _ (stackBits_length_ge enc s)

def rawState? (n : ℕ) (enc : R → List Bool) (dec : List Bool → Option R) :
    List Bool → Option (State R n)
  | false :: false :: bits => do
      let (q, stack) ← unpair? bits
      let q ← decodeQuery? n q
      let stack ← decodeStack? n enc dec stack
      pure (.eval q stack)
  | false :: true :: bits => do
      let (x, stack) ← unpair? bits
      let x ← dec x
      let stack ← decodeStack? n enc dec stack
      pure (.ret x stack)
  | true :: bits => State.done <$> dec bits
  | _ => none

theorem rawState?_stateBits (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (s : State R n) :
    rawState? n enc dec (stateBits enc s) = some s := by
  cases s <;> simp [rawState?, stateBits, hdec, decodeStack?_stackBits enc dec hdec]

def decodeState? (n : ℕ) (enc : R → List Bool) (dec : List Bool → Option R) :
    List Bool → Option (State R n) := checkedDecode (stateBits enc) (rawState? n enc dec)

@[simp] theorem decodeState?_stateBits (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (s : State R n) :
    decodeState? n enc dec (stateBits enc s) = some s :=
  checkedDecode_encode _ _ (rawState?_stateBits enc dec hdec) s

theorem decodeState?_eq_some_iff (enc : R → List Bool) (dec : List Bool → Option R)
    (hdec : ∀ x, dec (enc x) = some x) (bits : List Bool) (s : State R n) :
    decodeState? n enc dec bits = some s ↔ bits = stateBits enc s :=
  checkedDecode_eq_some_iff _ _ (rawState?_stateBits enc dec hdec) bits s

def decodeResidue? (m : ℕ) (bits : List Bool) : Option (ZMod m) := do
  let x ← BinaryNatCode.decode? bits
  if x < m then some (x : ZMod m) else none

@[simp] theorem decodeResidue?_residueBits (m : ℕ) [NeZero m] (x : ZMod m) :
    decodeResidue? m (residueBits x) = some x := by
  simp [decodeResidue?, residueBits, ZMod.val_lt]

def encodedStep [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (enc : R → List Bool) (dec : List Bool → Option R) (bits : List Bool) : List Bool :=
  match decodeState? n enc dec bits with
  | some s => stateBits enc (step A s)
  | none => stateBits (n := n) enc (.done 0)

theorem encodedStep_stateBits [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (enc : R → List Bool) (dec : List Bool → Option R) (hdec : ∀ x, dec (enc x) = some x)
    (s : State R n) : encodedStep A enc dec (stateBits enc s) = stateBits enc (step A s) := by
  simp only [encodedStep, decodeState?_stateBits enc dec hdec]

theorem encodedStep_iterate [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (enc : R → List Bool) (dec : List Bool → Option R) (hdec : ∀ x, dec (enc x) = some x)
    (t : ℕ) (s : State R n) :
    (encodedStep A enc dec)^[t] (stateBits enc s) = stateBits enc ((step A)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, encodedStep_stateBits A enc dec hdec,
      Function.iterate_succ_apply']

theorem encodedStep_run_pow [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (enc : R → List Bool) (dec : List Bool → Option R) (hdec : ∀ x, dec (enc x) = some x)
    (e : ℕ) (i j : Fin n) :
    (encodedStep A enc dec)^[work n e.size e + 1]
        (stateBits enc (.eval ⟨e.size, e, i, j⟩ [])) =
          stateBits (n := n) enc (.done ((A ^ e) i j)) := by
  rw [encodedStep_iterate A enc dec hdec, run_pow]

/-- The total bitstring implementation inherits the complete modular-state
bound for every iterate, including iterates after termination. -/
theorem encodedStep_residue_length_le (m : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (e t : ℕ) (i j : Fin n) :
    ((encodedStep A residueBits (decodeResidue? m))^[t]
      (stateBits (residueBits (m := m)) (.eval ⟨e.size, e, i, j⟩ []))).length ≤
        64 * (n.size + e.size + m.size + 1) ^ 2 := by
  rw [encodedStep_iterate A residueBits (decodeResidue? m) (decodeResidue?_residueBits m)]
  exact run_residueBits_quadratic m A e t i j

end LeanCanny.Algebra.MatrixPower
