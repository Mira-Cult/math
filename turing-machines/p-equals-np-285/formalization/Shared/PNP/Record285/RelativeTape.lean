import Shared.PNP.Record285.Source

/-! Full, two-sided tape semantics for the selected source simulator. This
relates its natural-number streams to a tape at every integer position. It is
not a refinement of the physical 285-state table. -/
namespace Shared.PNP.Record285.RelativeTape

/-- `facingLeft = false` means that ahead is toward increasing coordinates. -/
structure TapeConfig where
  tape : Int → Bool
  head : Int
  facingLeft : Bool

def behindPos (c : TapeConfig) (i : Nat) : Int :=
  if c.facingLeft then c.head + (i : Int) + 1 else c.head - (i : Int) - 1

def aheadPos (c : TapeConfig) (i : Nat) : Int :=
  if c.facingLeft then c.head - (i : Int) - 1 else c.head + (i : Int) + 1

/-- Entire tape, including all cells beyond any finite window. -/
def TapeRel (c : TapeConfig) (left right : Nat) (read : Bool) : Prop :=
  c.tape c.head = read ∧
    (∀ i, c.tape (behindPos c i) = left.testBit i) ∧
    (∀ i, c.tape (aheadPos c i) = right.testBit i)


/-- The head and the two oriented half-tapes cover every integer cell. -/
theorem positions_cover (c : TapeConfig) (p : Int) :
    p = c.head ∨ (∃ i, p = behindPos c i) ∨ (∃ i, p = aheadPos c i) := by
  by_cases heq : p = c.head
  · exact Or.inl heq
  · by_cases hlt : p < c.head
    · have hn : 0 ≤ c.head - p - 1 := by omega
      let i := (c.head-p-1).toNat
      have hi : (i : Int) = c.head-p-1 := Int.toNat_of_nonneg hn
      cases hf : c.facingLeft with
      | false =>
        right; left; refine ⟨i,?_⟩
        simp only [behindPos, hf, Bool.false_eq_true, if_false, hi]
        omega
      | true =>
        right; right; refine ⟨i,?_⟩
        simp only [aheadPos, hf, if_true, hi]
        omega
    · have hn : 0 ≤ p - c.head - 1 := by omega
      let i := (p-c.head-1).toNat
      have hi : (i : Int) = p-c.head-1 := Int.toNat_of_nonneg hn
      cases hf : c.facingLeft with
      | false =>
        right; right; refine ⟨i,?_⟩
        simp only [aheadPos, hf, Bool.false_eq_true, if_false, hi]
        omega
      | true =>
        right; left; refine ⟨i,?_⟩
        simp only [behindPos, hf, if_true, hi]
        omega

/-- There is no untracked tape suffix: equal represented streams and a shared
head/orientation determine equality of the complete integer tapes. -/
theorem tapeRel_ext (a b : TapeConfig) (left right : Nat) (read : Bool)
    (hhead : a.head = b.head) (hfacing : a.facingLeft = b.facingLeft)
    (ha : TapeRel a left right read) (hb : TapeRel b left right read) :
    a.tape = b.tape := by
  funext p
  rcases positions_cover a p with heq | ⟨i,heq⟩ | ⟨i,heq⟩
  · rw [heq, ha.1, hhead, hb.1]
  · have hp : behindPos a i = behindPos b i := by simp [behindPos,hhead,hfacing]
    rw [heq, ha.2.1 i, hp, hb.2.1 i]
  · have hp : aheadPos a i = aheadPos b i := by simp [aheadPos,hhead,hfacing]
    rw [heq, ha.2.2 i, hp, hb.2.2 i]

def writeTape (c : TapeConfig) (write : Bool) : Int → Bool :=
  fun p => if p = c.head then write else c.tape p

/-- Write, turn iff requested, then move one cell in the new facing. -/
def physicalStep (c : TapeConfig) (write turn : Bool) : TapeConfig :=
  let facing := c.facingLeft != turn
  ⟨writeTape c write, c.head + (if facing then -1 else 1), facing⟩

def bitVal (b : Bool) : Nat := if b then 1 else 0

theorem bit_push_zero (n : Nat) (b : Bool) :
    (2*n + bitVal b).testBit 0 = b := by
  cases b <;> simp [bitVal, Nat.testBit_zero]

theorem bit_push_succ (n : Nat) (b : Bool) (i : Nat) :
    (2*n + bitVal b).testBit (i+1) = n.testBit i := by
  rw [Nat.testBit_add_one]
  have hdiv : (2*n + bitVal b)/2 = n := by cases b <;> simp [bitVal] <;> omega
  rw [hdiv]

/-- Numeric simulator's pushed and popped tape streams after a physical step. -/
def behindNumber (left right : Nat) (write turn : Bool) : Nat :=
  2*(if turn then right else left) + bitVal write

def aheadNumber (left right : Nat) (turn : Bool) : Nat :=
  (if turn then left else right) / 2

def nextRead (left right : Nat) (turn : Bool) : Bool :=
  (if turn then left else right).testBit 0


/-- Updating the numeric streams is exactly write/turn/move on the complete
integer tape. No tape suffix is discarded. -/
theorem physicalStep_tapeRel (c : TapeConfig) (left right : Nat) (read write turn : Bool)
    (h : TapeRel c left right read) :
    TapeRel (physicalStep c write turn) (behindNumber left right write turn)
      (aheadNumber left right turn) (nextRead left right turn) := by
  rcases c with ⟨tape,head,facing⟩
  cases facing <;> cases turn <;>
    simp [TapeRel, physicalStep, behindPos, aheadPos, behindNumber,
      aheadNumber, nextRead] at h ⊢
  case false.false =>
    rcases h with ⟨_,hl,hr⟩
    constructor
    · simp only [writeTape]
      have hne : head + 1 ≠ head := by omega
      rw [if_neg hne]
      simpa using hr 0
    constructor
    · intro i
      cases i with
      | zero => cases write <;> simp [writeTape, bitVal]
      | succ i =>
        rw [bit_push_succ]
        simp only [writeTape]
        have hne : head + 1 - (↑(i+1) : Int) - 1 ≠ head := by omega
        rw [if_neg hne]
        have hpos : head + 1 - (↑(i+1) : Int) - 1 = head - ↑i - 1 := by omega
        rw [hpos]
        exact hl i
    · intro i
      rw [Nat.testBit_div_two]
      simp only [writeTape]
      have hne : head + 1 + (↑i : Int) + 1 ≠ head := by omega
      rw [if_neg hne]
      have hpos : head + 1 + (↑i : Int) + 1 = head + ↑(i+1) + 1 := by omega
      rw [hpos]
      exact hr (i+1)

  case false.true =>
    rcases h with ⟨_,hl,hr⟩
    constructor
    · simp only [writeTape]
      have hne : head + -1 ≠ head := by omega
      rw [if_neg hne]
      have hp : head + -1 = head - 1 := by omega
      rw [hp]
      simpa using hl 0
    constructor
    · intro i
      cases i with
      | zero =>
        have hp : head + -1 + 1 = head := by omega
        cases write <;> simp [writeTape, bitVal, hp]
      | succ i =>
        rw [bit_push_succ]
        simp only [writeTape]
        have hne : head + -1 + (↑(i+1) : Int) + 1 ≠ head := by omega
        rw [if_neg hne]
        have hpos : head + -1 + (↑(i+1) : Int) + 1 = head + ↑i + 1 := by omega
        rw [hpos]
        exact hr i
    · intro i
      rw [Nat.testBit_div_two]
      simp only [writeTape]
      have hne : head + -1 - (↑i : Int) - 1 ≠ head := by omega
      rw [if_neg hne]
      have hpos : head + -1 - (↑i : Int) - 1 = head - ↑(i+1) - 1 := by omega
      rw [hpos]
      exact hl (i+1)
  case true.false =>
    rcases h with ⟨_,hl,hr⟩
    constructor
    · simp only [writeTape]
      have hne : head + -1 ≠ head := by omega
      rw [if_neg hne]
      have hp : head + -1 = head - 1 := by omega
      rw [hp]
      simpa using hr 0
    constructor
    · intro i
      cases i with
      | zero =>
        have hp : head + -1 + 1 = head := by omega
        cases write <;> simp [writeTape, bitVal, hp]
      | succ i =>
        rw [bit_push_succ]
        simp only [writeTape]
        have hne : head + -1 + (↑(i+1) : Int) + 1 ≠ head := by omega
        rw [if_neg hne]
        have hpos : head + -1 + (↑(i+1) : Int) + 1 = head + ↑i + 1 := by omega
        rw [hpos]
        exact hl i
    · intro i
      rw [Nat.testBit_div_two]
      simp only [writeTape]
      have hne : head + -1 - (↑i : Int) - 1 ≠ head := by omega
      rw [if_neg hne]
      have hpos : head + -1 - (↑i : Int) - 1 = head - ↑(i+1) - 1 := by omega
      rw [hpos]
      exact hr (i+1)
  case true.true =>
    rcases h with ⟨_,hl,hr⟩
    constructor
    · simp only [writeTape]
      have hne : head + 1 ≠ head := by omega
      rw [if_neg hne]
      simpa using hl 0
    constructor
    · intro i
      cases i with
      | zero => cases write <;> simp [writeTape, bitVal]
      | succ i =>
        rw [bit_push_succ]
        simp only [writeTape]
        have hne : head + 1 - (↑(i+1) : Int) - 1 ≠ head := by omega
        rw [if_neg hne]
        have hpos : head + 1 - (↑(i+1) : Int) - 1 = head - ↑i - 1 := by omega
        rw [hpos]
        exact hr i
    · intro i
      rw [Nat.testBit_div_two]
      simp only [writeTape]
      have hne : head + 1 + (↑i : Int) + 1 ≠ head := by omega
      rw [if_neg hne]
      have hpos : head + 1 + (↑i : Int) + 1 = head + ↑(i+1) + 1 := by omega
      rw [hpos]
      exact hl (i+1)


structure Action where
  write : Bool
  turn : Bool
  next : Nat
  deriving DecidableEq, Repr

/-- The action decoded by the source evaluator, including the current choice. -/
def action (program : Nat) (s : Source.SimState) : Action :=
  let ordinal := s.selector + s.choices % 2
  let packed := (Source.popUnary (Source.skipUnary ordinal program)).1
  ⟨decide (packed % 2 = 1), decide ((packed / 2) % 2 = 1), packed / 4⟩

theorem bitVal_decide_one (n : Nat) (h : n < 2) : bitVal (decide (n = 1)) = n := by
  cases n with
  | zero => rfl
  | succ n =>
    have hn : n = 0 := by omega
    subst n
    rfl

theorem bitVal_lowBit (n : Nat) : bitVal (n.testBit 0) = n % 2 := by
  rw [Nat.testBit_zero]
  exact bitVal_decide_one _ (Nat.mod_lt _ (by decide))

/-- The source's arithmetic update after a decoded action uses precisely the
new full-tape streams and next read bit. -/
theorem action_arithmetic (program : Nat) (s : Source.SimState) :
    let a := action program s
    let packed := (Source.popUnary (Source.skipUnary (s.selector+s.choices%2) program)).1
    let direction := (packed / 2) % 2
    let l := if direction = 0 then s.left else s.right
    let r := if direction = 0 then s.right else s.left
    behindNumber s.left s.right a.write a.turn = 2*l + packed % 2 ∧
      aheadNumber s.left s.right a.turn = r / 2 ∧
      bitVal (nextRead s.left s.right a.turn) = r % 2 := by
  dsimp only [action, behindNumber, aheadNumber, nextRead]
  let packed := (Source.popUnary (Source.skipUnary (s.selector+s.choices%2) program)).1
  change 2*(if decide ((packed/2)%2 = 1) then s.right else s.left) +
      bitVal (decide (packed%2 = 1)) =
        2*(if (packed/2)%2 = 0 then s.left else s.right) + packed%2 ∧
    (if decide ((packed/2)%2 = 1) then s.left else s.right)/2 =
        (if (packed/2)%2 = 0 then s.right else s.left)/2 ∧
    bitVal ((if decide ((packed/2)%2 = 1) then s.left else s.right).testBit 0) =
        (if (packed/2)%2 = 0 then s.right else s.left)%2
  have hwrite : bitVal (decide (packed % 2 = 1)) = packed % 2 :=
    bitVal_decide_one _ (Nat.mod_lt _ (by decide))
  have hdir : (packed/2)%2 < 2 := Nat.mod_lt _ (by decide)
  by_cases hd : (packed/2)%2 = 0
  · simp [hd, hwrite]
    exact bitVal_decide_one _ (Nat.mod_lt _ (by decide))
  · have hd1 : (packed/2)%2 = 1 := by omega
    simp [hd1, hwrite]
    exact bitVal_decide_one _ (Nat.mod_lt _ (by decide))

/-- A nonhalting source step preserves the exact infinite tape representation,
and its selector contains the decoded next state and next physical head bit. -/
theorem simStep_preserves_tape (program : Nat) (s s' : Source.SimState)
    (c : TapeConfig) (read : Bool) (hrel : TapeRel c s.left s.right read)
    (hstep : Source.simStep program s = some s') :
    let a := action program s
    TapeRel (physicalStep c a.write a.turn) s'.left s'.right
        (nextRead s.left s.right a.turn) ∧
      s'.selector = a.next - 1 + 2 * bitVal (nextRead s.left s.right a.turn) ∧
      s'.choices = s.choices / 2 ∧ 0 < a.next := by
  have harith := action_arithmetic program s
  have htape := physicalStep_tapeRel c s.left s.right read
    (action program s).write (action program s).turn hrel
  unfold Source.simStep at hstep
  dsimp only at hstep
  split at hstep
  · contradiction
  · rename_i hnext
    cases hstep
    dsimp only [action] at *
    rcases harith with ⟨hl, hr, hb⟩
    rw [hl, hr] at htape
    refine ⟨htape, ?_, rfl, by omega⟩
    rw [hb]

/-- On HALT, the source still performs the write and head move before exiting;
the complete final tape has the same representation. -/
theorem simStep_halt_tape (program : Nat) (s : Source.SimState)
    (c : TapeConfig) (read : Bool) (hrel : TapeRel c s.left s.right read)
    (hstep : Source.simStep program s = none) :
    (action program s).next = 0 ∧
      TapeRel (physicalStep c (action program s).write (action program s).turn)
        (behindNumber s.left s.right (action program s).write (action program s).turn)
        (aheadNumber s.left s.right (action program s).turn)
        (nextRead s.left s.right (action program s).turn) := by
  constructor
  · unfold Source.simStep at hstep
    dsimp only at hstep
    split at hstep
    · assumption
    · contradiction
  · exact physicalStep_tapeRel c s.left s.right read _ _ hrel


/-- One-based record `state + 2*read + choice`; the skipped ordinal is one
less. Unspecified records decode as zero using the padded unary stream. -/
def rowAction (program state : Nat) (read choice : Bool) : Action :=
  let ordinal := state - 1 + 2*bitVal read + bitVal choice
  let packed := (Source.popUnary (Source.skipUnary ordinal program)).1
  ⟨decide (packed % 2 = 1), decide ((packed / 2) % 2 = 1), packed / 4⟩


/-- Once the requested row is beyond the binary program's bit length, virtual
zero padding gives the default write-zero, straight, HALT action. -/
theorem rowAction_default_after_bits (program state bits : Nat) (read choice : Bool)
    (hprogram : program < 2^bits)
    (hordinal : bits ≤ state - 1 + 2*bitVal read + bitVal choice) :
    rowAction program state read choice = ⟨false,false,0⟩ := by
  let ordinal := state - 1 + 2*bitVal read + bitVal choice
  have hp : program < 2^ordinal :=
    Nat.lt_of_lt_of_le hprogram (Nat.pow_le_pow_right (by decide : 0 < 2) hordinal)
  have hz : Source.skipUnary ordinal program = 0 := Source.skipUnary_zero_of_lt ordinal program hp
  have hpop : Source.popUnary 0 = (0,0) := by rw [Source.popUnary]; rfl
  unfold rowAction
  dsimp only
  rw [hz, hpop]
  rfl

/-- Every decoded destination is bounded by one quarter of the program's bit
length, even for arbitrary malformed finite numeric streams. -/
theorem rowAction_next_le_bits (program state bits : Nat) (read choice : Bool)
    (hprogram : program < 2^bits) : (rowAction program state read choice).next ≤ bits/4 := by
  let ordinal := state - 1 + 2*bitVal read + bitVal choice
  have hskip : Source.skipUnary ordinal program < 2^bits :=
    Nat.lt_of_le_of_lt (Source.skipUnary_le ordinal program) hprogram
  have hcount := Source.popUnary_count_le_bits (Source.skipUnary ordinal program) bits hskip
  exact Nat.div_le_div_right hcount

theorem action_matches_row (program state : Nat) (s : Source.SimState) (read : Bool)
    (hselector : s.selector = state - 1 + 2*bitVal read) :
    action program s = rowAction program state read (s.choices.testBit 0) := by
  unfold action rowAction
  rw [hselector, bitVal_lowBit]

structure RelativeConfig where
  state : Nat
  physical : TapeConfig
  choices : Nat

/-- A concrete relative machine step. The tape update also occurs on HALT,
although the return `none` records only the halting observation. -/
def relativeStep (program : Nat) (c : RelativeConfig) : Option RelativeConfig :=
  let a := rowAction program c.state (c.physical.tape c.physical.head) (c.choices.testBit 0)
  if a.next = 0 then none
  else some ⟨a.next, physicalStep c.physical a.write a.turn, c.choices/2⟩

def SimRel (c : RelativeConfig) (s : Source.SimState) : Prop :=
  0 < c.state ∧ c.choices = s.choices ∧ ∃ read,
    TapeRel c.physical s.left s.right read ∧
      s.selector = c.state - 1 + 2*bitVal read

/-- The numeric and relative machines agree on HALT or have related complete
successor configurations, preserving the entire tape and remaining choices. -/
theorem relativeStep_refines (program : Nat) (c : RelativeConfig) (s : Source.SimState)
    (hrel : SimRel c s) :
    match Source.simStep program s with
    | none => relativeStep program c = none
    | some s' => ∃ c', relativeStep program c = some c' ∧ SimRel c' s' := by
  rcases hrel with ⟨hstate,hchoices,read,htape,hselector⟩
  have hread : c.physical.tape c.physical.head = read := htape.1
  have ha := action_matches_row program c.state s read hselector
  have hact : rowAction program c.state (c.physical.tape c.physical.head)
      (c.choices.testBit 0) = action program s := by
    rw [hread, hchoices, ← ha]
  cases hs : Source.simStep program s with
  | none =>
    have hh := (simStep_halt_tape program s c.physical read htape hs).1
    unfold relativeStep
    rw [hact]
    dsimp only
    rw [hh]
    rfl
  | some s' =>
    have hp := simStep_preserves_tape program s s' c.physical read htape hs
    refine ⟨⟨(action program s).next,
      physicalStep c.physical (action program s).write (action program s).turn, c.choices/2⟩,
      ?_, ?_⟩
    · unfold relativeStep
      rw [hact]
      simp only [Nat.ne_of_gt hp.2.2.2, if_false]
    · refine ⟨hp.2.2.2, ?_, nextRead s.left s.right (action program s).turn, hp.1, hp.2.1⟩
      rw [hchoices, hp.2.2.1]


/-- Every live target after one step lies in the finite state bound determined
by the program's bit length. -/
theorem relativeStep_state_bound (program bits : Nat) (c c' : RelativeConfig)
    (hprogram : program < 2^bits) (hstep : relativeStep program c = some c') :
    c'.state ≤ bits/4 := by
  unfold relativeStep at hstep
  dsimp only at hstep
  split at hstep
  · contradiction
  · cases hstep
    exact rowAction_next_le_bits program c.state bits _ _ hprogram



/-- Live configurations stay related and halting observations agree for every
finite clock, including a HALT on the last allowed step. The final halting
tape itself is covered separately by `simStep_halt_tape`. -/
def relativeRun (program : Nat) : Nat → RelativeConfig → Option RelativeConfig
  | 0, c => some c
  | clock+1, c =>
    match relativeStep program c with
    | none => none
    | some next => relativeRun program clock next

theorem relativeRun_state_bound (program bits clock : Nat) (c c' : RelativeConfig)
    (hprogram : program < 2^bits) (hinit : c.state ≤ max 1 (bits/4))
    (hrun : relativeRun program clock c = some c') : c'.state ≤ max 1 (bits/4) := by
  induction clock generalizing c with
  | zero => cases hrun; exact hinit
  | succ clock ih =>
    simp only [relativeRun] at hrun
    cases hs : relativeStep program c with
    | none => simp [hs] at hrun
    | some next =>
      simp only [hs] at hrun
      have hnext := relativeStep_state_bound program bits c next hprogram hs
      exact ih next (Nat.le_trans hnext (Nat.le_max_right _ _)) hrun


theorem relativeRun_refines (program clock : Nat) (c : RelativeConfig) (s : Source.SimState)
    (hrel : SimRel c s) :
    match Source.runSteps program clock s with
    | none => relativeRun program clock c = none
    | some s' => ∃ c', relativeRun program clock c = some c' ∧ SimRel c' s' := by
  induction clock generalizing c s with
  | zero => exact ⟨c, rfl, hrel⟩
  | succ clock ih =>
    have hstep := relativeStep_refines program c s hrel
    cases hs : Source.simStep program s with
    | none =>
      simp only [hs] at hstep
      simp [Source.runSteps, hs, relativeRun, hstep]
    | some s' =>
      simp only [hs] at hstep
      obtain ⟨c',hc',hrel'⟩ := hstep
      simpa [Source.runSteps, hs, relativeRun, hc'] using ih c' s' hrel'


/-- Ordinary input lies at nonnegative positions, low bit at the origin;
negative positions and the infinite high suffix are blank. -/
def inputTape (input : Nat) (position : Int) : Bool :=
  if 0 ≤ position then input.testBit position.toNat else false

def initialRelative (input choices : Nat) : RelativeConfig :=
  ⟨1, ⟨inputTape input, 0, false⟩, choices⟩

def initialSim (input choices : Nat) : Source.SimState :=
  ⟨0, input/2, 2*(input%2), choices⟩

/-- Every finite code denotes a finite-control relative machine from its
standard initial state; this does not bound the time taken to interpret it. -/
theorem initialRelative_state_bound (program bits clock input choices : Nat)
    (hprogram : program < 2^bits) (c' : RelativeConfig)
    (hrun : relativeRun program clock (initialRelative input choices) = some c') :
    c'.state ≤ max 1 (bits/4) := by
  apply relativeRun_state_bound program bits clock _ _ hprogram ?_ hrun
  change 1 ≤ max 1 (bits/4)
  exact Nat.le_max_left _ _

theorem initial_related (input choices : Nat) :
    SimRel (initialRelative input choices) (initialSim input choices) := by
  refine ⟨?_, rfl, input.testBit 0, ?_, ?_⟩
  · change 0 < 1
    decide
  · change TapeRel ⟨inputTape input,0,false⟩ 0 (input/2) (input.testBit 0)
    constructor
    · simp [inputTape]
    constructor
    · intro i
      change inputTape input (0-(i : Int)-1) = (0:Nat).testBit i
      unfold inputTape
      have hn : ¬ 0 ≤ 0 - (i : Int) - 1 := by omega
      rw [if_neg hn]
      simp
    · intro i
      change inputTape input (0+(i : Int)+1) = (input/2).testBit i
      unfold inputTape
      have hp : 0 ≤ 0 + (i : Int) + 1 := by omega
      rw [if_pos hp]
      have hnat : (0+(i : Int)+1).toNat = i+1 := by simp
      rw [hnat, Nat.testBit_div_two]
  · change 2*(input%2) = 1-1 + 2*bitVal (input.testBit 0)
    rw [bitVal_lowBit]
    simp

/-- Initial numeric evaluation and ordinary relative execution have the same
bounded halting result for every finite program, input, choices and clock. -/
theorem initial_halted_iff (program input choices clock : Nat) :
    Source.haltedWithin program clock (initialSim input choices) = true ↔
      relativeRun program clock (initialRelative input choices) = none := by
  rw [Source.haltedWithin_iff_runSteps]
  have hrun := relativeRun_refines program clock (initialRelative input choices)
    (initialSim input choices) (initial_related input choices)
  cases hr : Source.runSteps program clock (initialSim input choices) with
  | none => simp only [hr] at hrun ⊢; simp [hrun]
  | some next =>
    simp only [hr] at hrun ⊢
    obtain ⟨c,hc,_⟩ := hrun
    simp [hc]

/-- Candidate acceptance is exactly bounded deterministic relative-machine
HALT on its canonical numeric input frame. -/
theorem candidate_halts_iff (program exponent n radix remaining : Nat) :
    Source.candidate program exponent n radix remaining = true ↔
      relativeRun program ((n+2)^exponent)
        (initialRelative (Source.frame radix remaining) 0) = none := by
  exact initial_halted_iff program (Source.frame radix remaining) 0 ((n+2)^exponent)

/-- Reference acceptance is exactly existence of a bounded relative-machine
branch on blank tape. A zero clock never accepts. -/
theorem reference_halts_iff (n radix remaining : Nat) :
    Source.reference n radix remaining = true ↔
      ∃ branch, branch < radix ∧
        relativeRun (radix+remaining) n (initialRelative 0 branch) = none := by
  rw [Source.reference, Source.referenceSearch_spec]
  constructor <;> rintro ⟨branch,hbound,hhalt⟩ <;> refine ⟨branch,hbound,?_⟩
  · exact (initial_halted_iff (radix+remaining) 0 branch n).1 hhalt
  · exact (initial_halted_iff (radix+remaining) 0 branch n).2 hhalt


/-- Exact low-bit-first canonical frame: `n` ones, a zero delimiter, then
`n` data bits when `remaining < 2^n`. -/
theorem frame_normal (n remaining : Nat) :
    Source.frame (2^n) remaining = 2^(n+1)*remaining + (2^n-1) := by
  have hp : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
  unfold Source.frame
  rw [Nat.pow_succ]
  have hmul : 2*(remaining*2^n) = 2^n*2*remaining := by ac_rfl
  rw [hmul]
  omega

theorem frame_bit (n remaining i : Nat) :
    (Source.frame (2^n) remaining).testBit i =
      if i < n then true else if i = n then false else remaining.testBit (i-(n+1)) := by
  rw [frame_normal]
  have hlo : 2^n - 1 < 2^(n+1) := by
    have hp : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
    rw [Nat.pow_succ]
    omega
  rw [Nat.testBit_two_pow_mul_add remaining hlo]
  by_cases hi : i < n+1
  · rw [if_pos hi, Nat.testBit_two_pow_sub_one]
    by_cases hn : i < n <;> simp [hn] <;> omega
  · rw [if_neg hi]
    have hn : ¬ i < n := by omega
    have hne : i ≠ n := by omega
    simp [hn, hne]

theorem frame_high_zero (n remaining i : Nat) (hbound : remaining < 2^n)
    (hi : 2*n+1 ≤ i) : (Source.frame (2^n) remaining).testBit i = false := by
  rw [frame_bit]
  have hn : ¬ i < n := by omega
  have hne : i ≠ n := by omega
  simp only [hn, hne, ↓reduceIte]
  apply Nat.testBit_lt_two_pow
  have hp : 2^n ≤ 2^(i-(n+1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact Nat.lt_of_lt_of_le hbound hp


/-- The actual initialized candidate tape has the canonical frame at every
nonnegative coordinate, with zeroes beyond its specified input length. -/
theorem candidate_input_tape (n remaining i : Nat) :
    (initialRelative (Source.frame (2^n) remaining) 0).physical.tape (i : Int) =
      if i < n then true else if i = n then false else remaining.testBit (i-(n+1)) := by
  simp [initialRelative, inputTape, frame_bit]

theorem candidate_input_blank_suffix (n remaining i : Nat) (hbound : remaining < 2^n)
    (hi : 2*n+1 ≤ i) :
    (initialRelative (Source.frame (2^n) remaining) 0).physical.tape (i : Int) = false := by
  simpa [initialRelative, inputTape] using frame_high_zero n remaining i hbound hi

/-- The reference program code retains the data bits and a single sentinel at
index `n`; bits above the sentinel are zero. -/
theorem reference_code_bit (n remaining i : Nat) (hbound : remaining < 2^n) :
    (2^n+remaining).testBit i = if i<n then remaining.testBit i else decide (i=n) := by
  have heq : 2^n + remaining = 2^n * 1 + remaining := by simp
  rw [heq, Nat.testBit_two_pow_mul_add 1 hbound]
  by_cases hi : i<n
  · simp [hi]
  · simp only [hi, if_false]
    by_cases he : i=n
    · subst i; simp
    · have hgt : n < i := by omega
      have hne : i-n ≠ 0 := by omega
      simp only [he, decide_false]
      apply Bool.eq_false_iff.mpr
      intro hh
      exact hne (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hh)

end Shared.PNP.Record285.RelativeTape
