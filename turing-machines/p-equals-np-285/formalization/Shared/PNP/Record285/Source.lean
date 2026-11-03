import Shared.Beeping.Events

/-! Finite comparison operations transcribed from the selected producer's
`halt_toggle/source.py`. This is source-side work: equivalence to the Python
AST and to the literal tape machine has not yet been proved. -/
namespace Shared.PNP.Record285.Source

/-- Read a unary one-run and its terminating zero from a low-bit-first natural
stream, extending the finite representation with zeroes. -/
def popUnary (stream : Nat) : Nat × Nat :=
  if h : stream % 2 = 1 then
    let p := popUnary (stream / 2)
    (p.1 + 1, p.2)
  else (0, stream / 2)
termination_by stream
decreasing_by omega


@[simp] theorem popUnary_even (n : Nat) : popUnary (2*n) = (0,n) := by
  simp [popUnary]

@[simp] theorem popUnary_odd (n : Nat) :
    popUnary (2*n+1) = ((popUnary n).1+1, (popUnary n).2) := by
  have hdiv : (2*n+1)/2 = n := by omega
  rw [popUnary]
  have hmod : (2*n+1)%2 = 1 := by omega
  simp only [hmod, ↓reduceDIte, hdiv]

/-- Unary decoding accounts for every bit of the finite numeric stream,
including virtual zero padding. -/
theorem popUnary_sound (stream : Nat) :
    stream + 1 = 2 ^ (popUnary stream).1 * (2 * (popUnary stream).2 + 1) := by
  induction stream using Nat.strongRecOn with
  | ind stream ih =>
    by_cases hodd : stream % 2 = 1
    · have hpos : 0 < stream := by omega
      have hv := ih (stream/2) (by omega)
      rw [popUnary]
      simp only [hodd, ↓reduceDIte, Nat.pow_succ]
      calc
        stream + 1 = 2 * (stream/2 + 1) := by omega
        _ = 2 * (2 ^ (popUnary (stream/2)).1 *
          (2 * (popUnary (stream/2)).2 + 1)) := by rw [hv]
        _ = (2 ^ (popUnary (stream/2)).1 * 2) *
          (2 * (popUnary (stream/2)).2 + 1) := by ac_rfl
    · rw [popUnary]
      simp only [hodd, ↓reduceDIte, Nat.pow_zero, Nat.one_mul]
      omega


/-- Reading one unary record consumes at least one stream bit. -/
theorem popUnary_tail_le_half (stream : Nat) : (popUnary stream).2 ≤ stream/2 := by
  induction stream using Nat.strongRecOn with
  | ind stream ih =>
    by_cases hodd : stream % 2 = 1
    · have hpos : 0 < stream := by omega
      have hrec := ih (stream/2) (by omega)
      rw [popUnary]
      simp only [hodd, ↓reduceDIte]
      have hdiv : stream/2/2 ≤ stream/2 := Nat.div_le_self _ _
      omega
    · rw [popUnary]
      simp only [hodd, ↓reduceDIte, Nat.le_refl]

/-- A unary action count is bounded by the original stream's bit length. -/
theorem popUnary_count_le_bits (stream bits : Nat) (hbound : stream < 2^bits) :
    (popUnary stream).1 ≤ bits := by
  have hs := popUnary_sound stream
  have hfactor : 0 < 2*(popUnary stream).2+1 := by omega
  have hpow : 2^(popUnary stream).1 ≤ stream+1 := by
    rw [hs]
    exact Nat.le_mul_of_pos_right _ hfactor
  by_cases h : (popUnary stream).1 ≤ bits
  · exact h
  · have hlt : bits < (popUnary stream).1 := by omega
    have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    omega

/-- Skip a fixed number of unary records, including implicit zero records. -/
def skipUnary : Nat → Nat → Nat
  | 0, stream => stream
  | n+1, stream => skipUnary n (popUnary stream).2


/-- Skipping `n` records consumes at least `n` low-order stream bits. -/
theorem skipUnary_le_div_pow (count stream : Nat) :
    skipUnary count stream ≤ stream / 2^count := by
  induction count generalizing stream with
  | zero => simp [skipUnary]
  | succ count ih =>
    simp only [skipUnary, Nat.pow_succ]
    have hh := ih (popUnary stream).2
    have hdiv := Nat.div_le_div_right (c := 2^count) (popUnary_tail_le_half stream)
    rw [Nat.div_div_eq_div_mul] at hdiv
    have heq : stream / (2 * 2^count) = stream / (2^count * 2) := by rw [Nat.mul_comm]
    omega

theorem skipUnary_le (count stream : Nat) : skipUnary count stream ≤ stream := by
  exact Nat.le_trans (skipUnary_le_div_pow count stream) (Nat.div_le_self _ _)

/-- Beyond the bit length, every implicitly padded action is zero. -/
theorem skipUnary_zero_of_lt (count stream : Nat) (h : stream < 2^count) :
    skipUnary count stream = 0 := by
  have hh := skipUnary_le_div_pow count stream
  rw [Nat.div_eq_of_lt h] at hh
  omega

structure SimState where
  left : Nat
  right : Nat
  /-- The next state's zero-based row selector already includes the read bit. -/
  selector : Nat
  choices : Nat
  deriving DecidableEq, Repr

/-- Decode and perform one bounded source simulation step. `none` means the
decoded target state is zero (HALT). -/
def simStep (program : Nat) (s : SimState) : Option SimState :=
  let choice := s.choices % 2
  let ordinal := s.selector + choice
  let packed := (popUnary (skipUnary ordinal program)).1
  let write := packed % 2
  let direction := (packed / 2) % 2
  let next := packed / 4
  let l := if direction = 0 then s.left else s.right
  let r := if direction = 0 then s.right else s.left
  let newLeft := 2*l + write
  if next = 0 then none
  else some ⟨newLeft, r / 2, next - 1 + 2*(r % 2), s.choices / 2⟩

/-- Test whether the source simulation enters HALT within the supplied clock.
HALT on the final transition is counted; a zero clock or timeout is false. -/
def haltedWithin (program : Nat) : Nat → SimState → Bool
  | 0, _ => false
  | clock+1, s =>
    match simStep program s with
    | none => true
    | some next => haltedWithin program clock next


/-- The finite run retains `none` once a HALT has happened. -/
def runSteps (program : Nat) : Nat → SimState → Option SimState
  | 0, s => some s
  | clock+1, s =>
    match simStep program s with
    | none => none
    | some next => runSteps program clock next

theorem haltedWithin_iff_runSteps (program clock : Nat) (s : SimState) :
    haltedWithin program clock s = true ↔ runSteps program clock s = none := by
  induction clock generalizing s with
  | zero => simp [haltedWithin, runSteps]
  | succ clock ih =>
    cases h : simStep program s with
    | none => simp [haltedWithin, runSteps, h]
    | some next => simpa [haltedWithin, runSteps, h] using ih next

/-- Exhaust branches in descending order, as in the producer. -/
def referenceSearch (program clock : Nat) : Nat → Bool
  | 0 => false
  | branches+1 =>
    if haltedWithin program clock ⟨0,0,0,branches⟩ then true
    else referenceSearch program clock branches

/-- The exact candidate input frame used by the producer. -/
def frame (radix remaining : Nat) : Nat := 2 * (remaining * radix) + radix - 1

def candidate (program exponent n radix remaining : Nat) : Bool :=
  let initial := frame radix remaining
  haltedWithin program ((n+2)^exponent) ⟨0, initial / 2, 2*(initial % 2), 0⟩

def reference (n radix remaining : Nat) : Bool :=
  referenceSearch (radix + remaining) n radix

/-- `true` is the comparison failure that causes the next candidate/event. -/
def mismatch (program exponent n radix remaining : Nat) : Bool :=
  reference n radix remaining != candidate program exponent n radix remaining

@[simp] theorem haltedWithin_zero (program : Nat) (s : SimState) :
    haltedWithin program 0 s = false := rfl

@[simp] theorem haltedWithin_halt (program clock : Nat) (s : SimState)
    (h : simStep program s = none) : haltedWithin program (clock+1) s = true := by
  simp [haltedWithin, h]

@[simp] theorem haltedWithin_continue (program clock : Nat) (s s' : SimState)
    (h : simStep program s = some s') :
    haltedWithin program (clock+1) s = haltedWithin program clock s' := by
  simp [haltedWithin, h]

@[simp] theorem referenceSearch_zero (program clock : Nat) :
    referenceSearch program clock 0 = false := rfl


/-- Search covers every branch below the bound, including branch zero. -/
theorem referenceSearch_spec (program clock branches : Nat) :
    referenceSearch program clock branches = true ↔
      ∃ branch, branch < branches ∧
        haltedWithin program clock ⟨0,0,0,branch⟩ = true := by
  induction branches with
  | zero => simp [referenceSearch]
  | succ branches ih =>
    by_cases hlast : haltedWithin program clock ⟨0,0,0,branches⟩ = true
    · simp only [referenceSearch, hlast, ↓reduceIte, true_iff]
      exact ⟨branches, by omega, hlast⟩
    · simp only [referenceSearch, hlast, Bool.false_eq_true, if_false]
      rw [ih]
      constructor
      · rintro ⟨branch, hb, hbranch⟩
        exact ⟨branch, by omega, hbranch⟩
      · rintro ⟨branch, hb, hbranch⟩
        have hn : branch ≠ branches := by
          intro he
          subst branch
          exact hlast hbranch
        exact ⟨branch, by omega, hbranch⟩


@[simp] theorem referenceSearch_zero_clock (program branches : Nat) :
    referenceSearch program 0 branches = false := by
  induction branches with
  | zero => rfl
  | succ branches ih => simp [referenceSearch, haltedWithin, ih]

/-- The failure bit is exactly disagreement, not complementation. -/
theorem mismatch_iff (program exponent n radix remaining : Nat) :
    mismatch program exponent n radix remaining = true ↔
      reference n radix remaining ≠ candidate program exponent n radix remaining := by
  simp [mismatch]

/-- Increasing the finite clock preserves an already observed HALT. -/
theorem haltedWithin_succ (program clock : Nat) (s : SimState)
    (h : haltedWithin program clock s = true) :
    haltedWithin program (clock+1) s = true := by
  induction clock generalizing s with
  | zero => simp at h
  | succ clock ih =>
    cases ht : simStep program s with
    | none => simp [haltedWithin, ht]
    | some next =>
      simp only [haltedWithin_continue _ _ _ _ ht] at h ⊢
      exact ih next h



/-- Diagonal schedule for candidate programs and positive clock exponents. -/
def advanceCandidate (program exponent : Nat) : Nat × Nat :=
  if program = 0 then (exponent,1) else (program-1,exponent+1)

def triangle : Nat → Nat
  | 0 => 0
  | n+1 => triangle n + n+1

def candidateRank (program exponent : Nat) : Nat :=
  triangle (program + exponent - 1) + exponent - 1

theorem advanceCandidate_positive (program exponent : Nat) :
    0 < (advanceCandidate program exponent).2 := by
  unfold advanceCandidate
  split <;> simp

theorem advanceCandidate_rank (program exponent : Nat) (h : 0 < exponent) :
    candidateRank (advanceCandidate program exponent).1
      (advanceCandidate program exponent).2 = candidateRank program exponent + 1 := by
  by_cases hp : program = 0
  · subst program
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
    simp [advanceCandidate, candidateRank, triangle]
  · have hp' : 0 < program := by omega
    simp only [advanceCandidate, if_neg hp, candidateRank]
    have heq : program - 1 + (exponent + 1) - 1 = program + exponent - 1 := by omega
    rw [heq]
    omega


/-- Iterate the source's candidate advance. -/
def candidateAfter : Nat → (Nat × Nat) → (Nat × Nat)
  | 0, pair => pair
  | n+1, pair =>
    let current := candidateAfter n pair
    advanceCandidate current.1 current.2

theorem candidateAfter_add (a b : Nat) (pair : Nat × Nat) :
    candidateAfter (a+b) pair = candidateAfter b (candidateAfter a pair) := by
  induction b with
  | zero => simp [candidateAfter]
  | succ b ih => simp [candidateAfter, ih]

theorem candidateAfter_within (steps program exponent : Nat) (h : steps ≤ program) :
    candidateAfter steps (program,exponent) = (program-steps,exponent+steps) := by
  induction steps with
  | zero => simp [candidateAfter]
  | succ steps ih =>
    have hsteps : steps ≤ program := by omega
    have hpositive : program - steps ≠ 0 := by omega
    simp only [candidateAfter, ih hsteps, advanceCandidate, hpositive, ↓reduceIte]
    congr 1 <;> omega

theorem candidateAfter_diagonal (diagonal : Nat) :
    candidateAfter (triangle diagonal) (0,1) = (diagonal,1) := by
  induction diagonal with
  | zero => rfl
  | succ diagonal ih =>
    simp only [triangle, candidateAfter]
    rw [candidateAfter_add, ih, candidateAfter_within diagonal diagonal 1 (Nat.le_refl _)]
    simp [advanceCandidate, Nat.add_comm]

/-- Every program and positive exponent is reached after a specific finite
number of advances. This is enumeration coverage, not polynomial-time model
coverage for deciders. -/
theorem candidateAfter_covers (program exponent : Nat) (h : 0 < exponent) :
    candidateAfter (triangle (program + exponent - 1) + (exponent - 1)) (0,1) =
      (program,exponent) := by
  rw [candidateAfter_add, candidateAfter_diagonal]
  have hb : exponent - 1 ≤ program + exponent - 1 := by omega
  rw [candidateAfter_within _ _ _ hb]
  congr 1 <;> omega


/-- Zero-based index of the current `(n, remaining)` in the input sweep. -/
def inputOrdinal (n remaining : Nat) : Nat := 2^(n+1) - 2 - remaining

theorem inputOrdinal_decrement (n remaining : Nat)
    (hbound : remaining < 2^n) (hpositive : 0 < remaining) :
    inputOrdinal n (remaining-1) = inputOrdinal n remaining + 1 := by
  have hp : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
  simp only [inputOrdinal, Nat.pow_succ]
  omega

theorem inputOrdinal_nextBlock (n : Nat) :
    inputOrdinal (n+1) (2 * 2^n - 1) = inputOrdinal n 0 + 1 := by
  have hp : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
  simp only [inputOrdinal, Nat.pow_succ]
  omega


/-- Each length block occupies its own consecutive interval of indices. -/
theorem inputOrdinal_bounds (n remaining : Nat) (h : remaining < 2^n) :
    2^n - 1 ≤ inputOrdinal n remaining ∧ inputOrdinal n remaining < 2^(n+1) - 1 := by
  have hp : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
  simp only [inputOrdinal, Nat.pow_succ]
  omega

theorem inputOrdinal_injective (n₁ w₁ n₂ w₂ : Nat)
    (h₁ : w₁ < 2^n₁) (h₂ : w₂ < 2^n₂)
    (h : inputOrdinal n₁ w₁ = inputOrdinal n₂ w₂) : n₁ = n₂ ∧ w₁ = w₂ := by
  have b₁ := inputOrdinal_bounds n₁ w₁ h₁
  have b₂ := inputOrdinal_bounds n₂ w₂ h₂
  have hn : n₁ = n₂ := by
    have hnot₁ : ¬ n₁ < n₂ := by
      intro hlt
      have hp : 2^(n₁+1) ≤ 2^n₂ :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      omega
    have hnot₂ : ¬ n₂ < n₁ := by
      intro hlt
      have hp : 2^(n₂+1) ≤ 2^n₁ :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      omega
    omega
  subst n₂
  constructor
  · rfl
  · have hp : 0 < 2^n₁ := Nat.pow_pos (by decide : 0 < 2)
    simp only [inputOrdinal, Nat.pow_succ] at h
    omega

inductive Phase where
  | begin | compare
  deriving DecidableEq, Repr

structure SearchState where
  program : Nat
  exponent : Nat
  n : Nat
  radix : Nat
  remaining : Nat
  phase : Phase
  deriving DecidableEq, Repr

/-- One controller step denotes an entire finite comparison, not one physical
transition. A failing comparison reaches `begin`; the next step emits. -/
def controllerStep (s : SearchState) : SearchState × Bool :=
  match s.phase with
  | .begin =>
      (⟨s.program, s.exponent, 0, 1, 0, .compare⟩, true)
  | .compare =>
      if mismatch s.program s.exponent s.n s.radix s.remaining then
        let next := advanceCandidate s.program s.exponent
        (⟨next.1, next.2, s.n, s.radix, s.remaining, .begin⟩, false)
      else if s.remaining = 0 then
        (⟨s.program, s.exponent, s.n + 1, 2*s.radix, 2*s.radix - 1, .compare⟩, false)
      else (⟨s.program, s.exponent, s.n, s.radix, s.remaining - 1, .compare⟩, false)

def controller : Shared.Beeping.EventSystem SearchState :=
  ⟨⟨0,1,0,1,0,.begin⟩, controllerStep⟩

@[simp] theorem controllerStep_beep (s : SearchState) :
    (controllerStep s).2 = true ↔ s.phase = .begin := by
  cases h : s.phase with
  | begin => simp [controllerStep, h]
  | compare =>
    simp only [controllerStep, h]
    split <;> simp <;> split <;> simp

/-- All reachable input frames have positive radix and an in-range remainder.
This excludes the producer's unreachable subtraction-at-zero situation. -/
def InputInvariant (s : SearchState) : Prop :=
  s.radix = 2^s.n ∧ s.remaining < s.radix

theorem controllerStep_inputInvariant (s : SearchState)
    (h : InputInvariant s) : InputInvariant (controllerStep s).1 := by
  rcases h with ⟨hradix, hrem⟩
  cases hp : s.phase with
  | begin => simp [controllerStep, hp, InputInvariant]
  | compare =>
    simp only [controllerStep, hp]
    split
    · exact ⟨hradix, hrem⟩
    · split
      · simp only [InputInvariant, Nat.pow_succ]
        constructor
        · omega
        · omega
      · simp only [InputInvariant]
        exact ⟨hradix, by omega⟩



/-- A successful comparison advances the flat input index by exactly one. -/
theorem controllerStep_input_progress (s : SearchState) (h : InputInvariant s)
    (hphase : s.phase = .compare)
    (hsuccess : mismatch s.program s.exponent s.n s.radix s.remaining = false) :
    inputOrdinal (controllerStep s).1.n (controllerStep s).1.remaining =
      inputOrdinal s.n s.remaining + 1 := by
  rcases h with ⟨hradix, hbound⟩
  simp only [controllerStep, hphase, hsuccess, Bool.false_eq_true, if_false]
  by_cases hzero : s.remaining = 0
  · simp only [hzero, ↓reduceIte]
    rw [hradix]
    exact inputOrdinal_nextBlock s.n
  · simp only [hzero, ↓reduceIte]
    apply inputOrdinal_decrement
    · simpa [← hradix] using hbound
    · omega

theorem controllerStep_positiveExponent (s : SearchState) (h : 0 < s.exponent) :
    0 < (controllerStep s).1.exponent := by
  cases hp : s.phase with
  | begin => simpa [controllerStep, hp] using h
  | compare =>
    simp only [controllerStep, hp]
    split
    · exact advanceCandidate_positive _ _
    · split <;> exact h

theorem controller_positiveExponent (t : Nat) : 0 < (controller.run t).exponent := by
  induction t with
  | zero => decide
  | succ t ih => exact controllerStep_positiveExponent _ ih

theorem controller_inputInvariant (t : Nat) : InputInvariant (controller.run t) := by
  induction t with
  | zero => simp [Shared.Beeping.EventSystem.run, controller, InputInvariant]
  | succ t ih => exact controllerStep_inputInvariant _ ih


/-- Start a candidate at its first comparison. Each scan step is one complete
finite comparison in the abstract source model. -/
def scanSystem (program exponent : Nat) : Shared.Beeping.EventSystem SearchState :=
  ⟨⟨program,exponent,0,1,0,.compare⟩, controllerStep⟩

/-- The candidate agrees on every admissible framed input. -/
def GoodCandidate (program exponent : Nat) : Prop :=
  ∀ n remaining, remaining < 2^n →
    mismatch program exponent n (2^n) remaining = false


/-- If no earlier comparison has failed, the current candidate has advanced
to exactly this input index. This does not assume the candidate is good. -/
theorem scan_prefix_progress (program exponent t : Nat)
    (hprefix : ∀ j, j < t →
      let s := (scanSystem program exponent).run j
      s.phase = .compare → mismatch s.program s.exponent s.n s.radix s.remaining = false) :
    let s := (scanSystem program exponent).run t
    s.program = program ∧ s.exponent = exponent ∧ s.phase = .compare ∧
      InputInvariant s ∧ inputOrdinal s.n s.remaining = t := by
  induction t with
  | zero => simp [Shared.Beeping.EventSystem.run, scanSystem, InputInvariant, inputOrdinal]
  | succ t ih =>
    have hprev : ∀ j, j < t →
        let s := (scanSystem program exponent).run j
        s.phase = .compare → mismatch s.program s.exponent s.n s.radix s.remaining = false := by
      intro j hj
      exact hprefix j (by omega)
    have hs := ih hprev
    dsimp only at hs ⊢
    rcases hs with ⟨hp, he, hphase, hinv, hord⟩
    have hmismatch := hprefix t (by omega) hphase
    have hnext := controllerStep_inputInvariant _ hinv
    have hprogress := controllerStep_input_progress _ hinv hphase hmismatch
    change (controllerStep ((scanSystem program exponent).run t)).1.program = program ∧
      (controllerStep ((scanSystem program exponent).run t)).1.exponent = exponent ∧
      (controllerStep ((scanSystem program exponent).run t)).1.phase = .compare ∧
      InputInvariant (controllerStep ((scanSystem program exponent).run t)).1 ∧
      inputOrdinal (controllerStep ((scanSystem program exponent).run t)).1.n
        (controllerStep ((scanSystem program exponent).run t)).1.remaining = t+1
    refine ⟨?_, ?_, ?_, hnext, ?_⟩
    · simp only [controllerStep, hphase, hmismatch, Bool.false_eq_true, if_false]
      split <;> simp [hp]
    · simp only [controllerStep, hphase, hmismatch, Bool.false_eq_true, if_false]
      split <;> simp [he]
    · simp only [controllerStep, hphase, hmismatch, Bool.false_eq_true, if_false]
      split <;> rfl
    · simpa [hord] using hprogress


def Failure (s : SearchState) : Prop :=
  s.phase = .compare ∧ mismatch s.program s.exponent s.n s.radix s.remaining = true

theorem noFailure_mismatch (s : SearchState) (hphase : s.phase = .compare)
    (h : ¬ Failure s) : mismatch s.program s.exponent s.n s.radix s.remaining = false := by
  cases hm : mismatch s.program s.exponent s.n s.radix s.remaining with
  | false => rfl
  | true => exact False.elim (h ⟨hphase, hm⟩)

/-- A concrete disagreement causes a failure no later than its input index. -/
theorem scan_bad_fails (program exponent n remaining : Nat)
    (hbound : remaining < 2^n)
    (hbad : mismatch program exponent n (2^n) remaining = true) :
    ∃ t, t ≤ inputOrdinal n remaining ∧ Failure ((scanSystem program exponent).run t) := by
  classical
  by_cases hearly : ∃ j, j < inputOrdinal n remaining ∧
      Failure ((scanSystem program exponent).run j)
  · obtain ⟨j,hj,hfail⟩ := hearly
    exact ⟨j, by omega, hfail⟩
  · have hprefix : ∀ j, j < inputOrdinal n remaining →
        let s := (scanSystem program exponent).run j
        s.phase = .compare → mismatch s.program s.exponent s.n s.radix s.remaining = false := by
      intro j hj
      dsimp only
      intro hphase
      apply noFailure_mismatch _ hphase
      intro hf
      exact hearly ⟨j,hj,hf⟩
    have hs := scan_prefix_progress program exponent (inputOrdinal n remaining) hprefix
    rcases hs with ⟨hp, he, hphase, hinv, hord⟩
    have hpair := inputOrdinal_injective _ _ n remaining
      (by simpa [← hinv.1] using hinv.2) hbound hord
    refine ⟨inputOrdinal n remaining, Nat.le_refl _, hphase, ?_⟩
    rw [hp, he, hinv.1, hpair.1, hpair.2]
    exact hbad


/-- A failed comparison leads to the next candidate's event in one further
source-controller step. -/
theorem scan_failure_next_beep (program exponent t : Nat)
    (hfail : Failure ((scanSystem program exponent).run t)) :
    (scanSystem program exponent).BeepAt (t+1) := by
  rcases hfail with ⟨hphase, hbad⟩
  change (controllerStep (controllerStep ((scanSystem program exponent).run t)).1).2 = true
  apply (controllerStep_beep _).2
  simp [controllerStep, hphase, hbad]

theorem scan_bad_beeps (program exponent n remaining : Nat)
    (hbound : remaining < 2^n)
    (hbad : mismatch program exponent n (2^n) remaining = true) :
    ∃ t, t ≤ inputOrdinal n remaining ∧ (scanSystem program exponent).BeepAt (t+1) := by
  obtain ⟨t, ht, hf⟩ := scan_bad_fails program exponent n remaining hbound hbad
  exact ⟨t, ht, scan_failure_next_beep program exponent t hf⟩

/-- A good candidate visits the `t`th input at source step `t`, with its
program and clock unchanged and no administrative detour in this model. -/
theorem scan_progress (program exponent : Nat) (hgood : GoodCandidate program exponent)
    (t : Nat) :
    let s := (scanSystem program exponent).run t
    s.program = program ∧ s.exponent = exponent ∧ s.phase = .compare ∧
      InputInvariant s ∧ inputOrdinal s.n s.remaining = t := by
  induction t with
  | zero => simp [Shared.Beeping.EventSystem.run, scanSystem, InputInvariant, inputOrdinal]
  | succ t ih =>
    dsimp only at ih ⊢
    rcases ih with ⟨hp, he, hphase, hinv, hord⟩
    have hmismatch : mismatch ((scanSystem program exponent).run t).program
        ((scanSystem program exponent).run t).exponent ((scanSystem program exponent).run t).n
        ((scanSystem program exponent).run t).radix ((scanSystem program exponent).run t).remaining = false := by
      rw [hp, he, hinv.1]
      exact hgood _ _ (by simpa [← hinv.1] using hinv.2)
    have hnext := controllerStep_inputInvariant _ hinv
    have hprogress := controllerStep_input_progress _ hinv hphase hmismatch
    change (controllerStep ((scanSystem program exponent).run t)).1.program = program ∧
      (controllerStep ((scanSystem program exponent).run t)).1.exponent = exponent ∧
      (controllerStep ((scanSystem program exponent).run t)).1.phase = .compare ∧
      InputInvariant (controllerStep ((scanSystem program exponent).run t)).1 ∧
      inputOrdinal (controllerStep ((scanSystem program exponent).run t)).1.n
        (controllerStep ((scanSystem program exponent).run t)).1.remaining = t+1
    refine ⟨?_, ?_, ?_, hnext, ?_⟩
    · simp only [controllerStep, hphase, hmismatch, Bool.false_eq_true, if_false]
      split <;> simp [hp]
    · simp only [controllerStep, hphase, hmismatch, Bool.false_eq_true, if_false]
      split <;> simp [he]
    · simp only [controllerStep, hphase, hmismatch, Bool.false_eq_true, if_false]
      split <;> rfl
    · simpa [hord] using hprogress


/-- On a good candidate every source comparison step is silent. -/
theorem scan_good_silent (program exponent : Nat) (hgood : GoodCandidate program exponent)
    (t : Nat) : ¬ (scanSystem program exponent).BeepAt t := by
  intro hbeep
  have hphase := (scan_progress program exponent hgood t).2.2.1
  change (controllerStep ((scanSystem program exponent).run t)).2 = true at hbeep
  have := (controllerStep_beep _).1 hbeep
  simp [hphase] at this

/-- Every admissible input is reached after its displayed finite index. -/
theorem scan_covers (program exponent n remaining : Nat)
    (hgood : GoodCandidate program exponent) (hbound : remaining < 2^n) :
    let t := inputOrdinal n remaining
    let s := (scanSystem program exponent).run t
    s.n = n ∧ s.radix = 2^n ∧ s.remaining = remaining := by
  dsimp only
  have hs := scan_progress program exponent hgood (inputOrdinal n remaining)
  rcases hs with ⟨_, _, _, hinv, hord⟩
  have hidx : inputOrdinal ((scanSystem program exponent).run (inputOrdinal n remaining)).n
      ((scanSystem program exponent).run (inputOrdinal n remaining)).remaining =
        inputOrdinal n remaining := hord
  have hpair := inputOrdinal_injective _ _ n remaining
    (by simpa [← hinv.1] using hinv.2) hbound hidx
  exact ⟨hpair.1, by simpa [hpair.1] using hinv.1, hpair.2⟩

end Shared.PNP.Record285.Source
