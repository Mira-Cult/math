import Shared.Codes.SATRefinement

/-! Computable exhaustive UNSAT-verifier comparisons over the shared finite
program universe. This module proves no class equality, TM2 cost bridge, or
finite beeping-machine implementation. The cutoff wrapper theorem is semantic;
a compiled wrapper preserving the cutoff is a separate obligation. -/
namespace Shared.Codes.VerifierPrograms
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF

/-- All binary witnesses of length at most the supplied bound. -/
def witnesses : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => assignments (n + 1) ++ witnesses n

theorem mem_witnesses_iff (w : List Bool) (n : Nat) :
    w ∈ witnesses n ↔ w.length ≤ n := by
  induction n with
  | zero => cases w <;> simp [witnesses]
  | succ n ih =>
    simp only [witnesses, List.mem_append, mem_assignments_iff, ih]
    omega

theorem witnesses_primrec : Primrec witnesses := by
  have hs : Primrec₂ (fun n : Nat => fun ws : List (List Bool) =>
      assignments (n + 1) ++ ws) :=
    (Primrec.list_append.comp (assignments_primrec.comp (Primrec.succ.comp Primrec.fst)) Primrec.snd).to₂
  have h := Primrec.nat_rec₁ ([[]] : List (List Bool)) hs
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [witnesses, ih]

/-- Shared primitive-recursive encoding proofs, retained under their existing names. -/
theorem delimit_primrec : Primrec BitstringEncoding.delimit :=
  Shared.Codes.FinitePrograms.InputEncoding.delimit_primrec

theorem boolEncoding_primrec : Primrec (@BitstringEncoding.bitEncode Bool _) :=
  Shared.Codes.FinitePrograms.InputEncoding.boolEncoding_primrec

theorem bitListEncoding_primrec : Primrec (@BitstringEncoding.bitEncode (List Bool) _) :=
  Shared.Codes.FinitePrograms.InputEncoding.bitListEncoding_primrec

theorem pairEncoding_primrec : Primrec (fun p : List Bool × List Bool => BitstringEncoding.bitEncode p) := by
  have h := Primrec.list_append.comp (delimit_primrec.comp (bitListEncoding_primrec.comp Primrec.fst))
    (bitListEncoding_primrec.comp Primrec.snd)
  apply h.of_eq
  intro p
  rfl


/-- Witness exponent and a checker with its own program and clock exponent. -/
abbrev Verifier := Nat × Candidate

def witnessBound (v : Verifier) (input : List Bool) : Nat := clock input v.1

def verify (v : Verifier) (input witness : List Bool) : Option Bool :=
  evaluate v.2 (BitstringEncoding.bitEncode (input, witness))

def terminates (v : Verifier) (input : List Bool) : Bool :=
  (witnesses (witnessBound v input)).all fun w => (verify v input w).isSome

def accepts (v : Verifier) (input : List Bool) : Bool :=
  (witnesses (witnessBound v input)).any fun w => verify v input w == some true

def test (v : Verifier) (input : List Bool) : Bool :=
  terminates v input && (accepts v input == complementSat input)

def decode (n : Nat) : Option Verifier :=
  match (Encodable.decode n : Option Verifier) with
  | none => none
  | some (b, c) => if valid c.2 then some (b, c) else none

def compare (e n : Nat) : Bool :=
  match decode e with
  | none => false
  | some v => test v (Shared.Codes.Inputs.inputAt n)

theorem decode_encode (v : Verifier) (h : valid v.2.2 = true) :
    decode (Encodable.encode v) = some v := by
  rcases v with ⟨b, c⟩
  simp [decode, h]

theorem coverage (v : Verifier) (h : valid v.2.2 = true) :
    ∃ e, decode e = some v := ⟨Encodable.encode v, decode_encode v h⟩

theorem decode_some_valid {e : Nat} {v : Verifier} (h : decode e = some v) : valid v.2.2 = true := by
  unfold decode at h
  cases hd : (Encodable.decode e : Option Verifier) with
  | none => simp [hd] at h
  | some d =>
    rcases d with ⟨b, c⟩
    cases hv : valid c.2 <;> simp [hd, hv] at h
    subst v
    exact hv

theorem terminates_iff (v : Verifier) (input : List Bool) : terminates v input = true ↔
    ∀ w, w.length ≤ witnessBound v input → (verify v input w).isSome = true := by
  simp [terminates, List.all_eq_true, mem_witnesses_iff]

theorem accepts_iff (v : Verifier) (input : List Bool) : accepts v input = true ↔
    ∃ w, w.length ≤ witnessBound v input ∧ verify v input w = some true := by
  simp [accepts, List.any_eq_true, mem_witnesses_iff]

theorem test_iff (v : Verifier) (input : List Bool) : test v input = true ↔
    (∀ w, w.length ≤ witnessBound v input → (verify v input w).isSome = true) ∧
    ((∃ w, w.length ≤ witnessBound v input ∧ verify v input w = some true) ↔
      complementSat input = true) := by
  have hbool : (accepts v input == complementSat input) = true ↔
      (accepts v input = true ↔ complementSat input = true) := by
    cases accepts v input <;> cases complementSat input <;> simp
  rw [← terminates_iff, ← accepts_iff, ← hbool]
  simp [test]

theorem compare_iff (e n : Nat) : compare e n = true ↔ ∃ v,
    decode e = some v ∧ test v (Shared.Codes.Inputs.inputAt n) = true := by
  cases hd : decode e with
  | none => simp [compare, hd]
  | some v => simp [compare, hd]

theorem good_iff (e : Nat) : (∀ n, compare e n = true) ↔ ∃ v,
    decode e = some v ∧ ∀ input, test v input = true := by
  constructor
  · intro h
    obtain ⟨v, hv, _⟩ := (compare_iff e 0).1 (h 0)
    refine ⟨v, hv, ?_⟩
    intro input
    obtain ⟨n, hn⟩ := Shared.Codes.Inputs.covers input
    obtain ⟨v', hv', he⟩ := (compare_iff e n).1 (h n)
    have hcc : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst v'
    simpa [hn] using he
  · rintro ⟨v, hv, h⟩ n
    exact (compare_iff e n).2 ⟨v, hv, h _⟩

theorem controller_silent_iff :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent ↔
      ∃ v : Verifier, valid v.2.2 = true ∧ ∀ input, test v input = true := by
  rw [Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨v, hv, hcorrect⟩ := (good_iff e).1 he
    exact ⟨v, decode_some_valid hv, hcorrect⟩
  · rintro ⟨v, hv, hcorrect⟩
    obtain ⟨e, he⟩ := coverage v hv
    exact ⟨e, (good_iff e).2 ⟨v, he, hcorrect⟩⟩

theorem certified_machine_silent_iff {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate compare 0 M) :
    M.system.EventuallySilent ↔ ∃ v : Verifier, valid v.2.2 = true ∧
      ∀ input, test v input = true := by
  calc
    M.system.EventuallySilent ↔ ∃ e, Shared.Beeping.Controller.Good compare e := by
      simpa using cert.eventuallySilent_iff_good
    _ ↔ (Shared.Beeping.Controller.system compare 0).EventuallySilent :=
      (Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good compare).symm
    _ ↔ _ := controller_silent_iff


theorem witnessBound_primrec : Primrec₂ witnessBound := by
  exact (clock_primrec.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂

theorem verify_primrec : Primrec (fun p : (Verifier × List Bool) × List Bool =>
    verify p.1.1 p.1.2 p.2) := by
  have hpair : Primrec (fun p : (Verifier × List Bool) × List Bool =>
      BitstringEncoding.bitEncode (p.1.2, p.2)) :=
    pairEncoding_primrec.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact evaluate_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) hpair

theorem witnessList_primrec : Primrec (fun p : Verifier × List Bool =>
    witnesses (witnessBound p.1 p.2)) :=
  witnesses_primrec.comp witnessBound_primrec

theorem terminates_primrec : Primrec₂ terminates := by
  have hg : Primrec₂ (fun p : Verifier × List Bool => fun w : List Bool =>
      (verify p.1 p.2 w).isSome) := (Primrec.option_isSome.comp verify_primrec).to₂
  exact (Shared.ComplexityBridge.CNF.list_all_primrec witnessList_primrec hg).to₂

set_option maxHeartbeats 2000000 in
theorem accepts_primrec : Primrec₂ accepts := by
  have hg : Primrec₂ (fun p : Verifier × List Bool => fun w : List Bool =>
      verify p.1 p.2 w == some true) := by
    have h := (Primrec.beq.comp verify_primrec (Primrec.const (some true : Option Bool))).to₂
    apply h.of_eq
    intro p w
    cases verify p.1 p.2 w with
    | none => rfl
    | some b => cases b <;> rfl
  exact (Shared.ComplexityBridge.CNF.list_any_primrec witnessList_primrec hg).to₂

theorem test_computable : Computable₂ test := by
  have href : Computable (fun p : Verifier × List Bool => complementSat p.2) :=
    Shared.ComplexityBridge.ParserComputability.complementSat_computable.comp Computable.snd
  have heq := Primrec.beq.to_comp.comp accepts_primrec.to_comp href
  exact (Primrec.and.to_comp.comp terminates_primrec.to_comp heq).to₂

def checked (v : Verifier) : Option Verifier :=
  if valid v.2.2 then some v else none

theorem checked_primrec : Primrec checked := by
  have hv := valid_primrec.comp (Primrec.snd.comp Primrec.snd : Primrec (fun v : Verifier => v.2.2))
  have h := Primrec.cond hv Primrec.option_some (Primrec.const none)
  apply h.of_eq
  intro v
  unfold checked
  cases valid v.2.2 <;> rfl

theorem decode_computable : Computable decode := by
  have h := Computable.option_bind (Computable.decode : Computable (Encodable.decode : Nat → Option Verifier))
    (checked_primrec.to_comp.comp Computable.snd).to₂
  apply h.of_eq
  intro n
  unfold decode checked
  cases (Encodable.decode n : Option Verifier) with
  | none => rfl
  | some v => rcases v with ⟨b, c⟩; cases valid c.2 <;> rfl

theorem compare_computable : Computable₂ compare := by
  have htest : Computable (fun p : Verifier × Nat => test p.1 (Shared.Codes.Inputs.inputAt p.2)) :=
    test_computable.comp Computable.fst (Shared.Codes.Inputs.computable.comp Computable.snd)
  have h := Computable.option_casesOn (decode_computable.comp Computable.fst) (Computable.const false)
    (htest.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨e, n⟩
  unfold compare
  cases decode e <;> rfl


theorem witnessBound_eq (v : Verifier) (input : List Bool) :
    witnessBound v input = (input.length + 2) ^ v.1 := rfl

theorem pair_clock_eq (v : Verifier) (input witness : List Bool) :
    clock (BitstringEncoding.bitEncode (input, witness)) v.2.1 =
      (6 * input.length + 1 + 3 * witness.length + 2) ^ v.2.1 := by
  simp [clock, Shared.ComplexityBridge.bitstring_pair_encoded_length]

theorem timeout_fails (v : Verifier) (input w : List Bool)
    (hw : w.length ≤ witnessBound v input) (ht : verify v input w = none) :
    test v input = false := by
  have hterm : terminates v input = false := by
    cases h : terminates v input with
    | false => rfl
    | true =>
      have hall := (terminates_iff v input).1 h w hw
      simp [ht] at hall
  simp [test, hterm]

theorem invalid_fails (e n : Nat) (h : decode e = none) : compare e n = false := by
  simp [compare, h]


/-- Mathematical cutoff wrapper: additional witnesses are rejected. Compiling
this wrapper into a finite program is a separate obligation. -/
def cutoffAccept (limit : Nat) (checker : List Bool → Bool) (w : List Bool) : Bool :=
  if w.length ≤ limit then checker w else false

theorem cutoff_search_iff (oldLimit newLimit : Nat) (h : oldLimit ≤ newLimit)
    (checker : List Bool → Bool) :
    (∃ w, w.length ≤ newLimit ∧ cutoffAccept oldLimit checker w = true) ↔
      ∃ w, w.length ≤ oldLimit ∧ checker w = true := by
  constructor
  · rintro ⟨w, _, hw⟩
    by_cases hl : w.length ≤ oldLimit
    · exact ⟨w, hl, by simpa [cutoffAccept, hl] using hw⟩
    · simp [cutoffAccept, hl] at hw
  · rintro ⟨w, hl, hc⟩
    exact ⟨w, le_trans hl h, by simpa [cutoffAccept, hl] using hc⟩

end Shared.Codes.VerifierPrograms
