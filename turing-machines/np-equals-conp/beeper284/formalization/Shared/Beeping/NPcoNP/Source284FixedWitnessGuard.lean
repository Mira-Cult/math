import Shared.Beeping.NPcoNP.Source284TaggedScannerCutoff
import Shared.Beeping.NPcoNP.Source284TableCountdown

/-! A finite, fixed-limit tagged-witness guard. Its clock is unrolled into
logical states; it does not compute a limit from an input or implement the
canonical verifier. Logical states are not physical beeper states. -/
namespace Shared.Beeping.NPcoNP.Source284FixedWitnessGuard

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

abbrev scanner := Source284TaggedScanner.table

/-- Accept on entering the scanner's completed-frame state. -/
def acceptFrame (q : Nat) (b : Bool) : Row :=
  let r := scanner q b
  if r.next = some 3 then { r with next := none } else r

theorem acceptFrame_closed : Closed 7 acceptFrame := by
  intro q hq b q' h
  interval_cases q <;> cases b <;> simp_all [acceptFrame, scanner, Source284TaggedScanner.table] <;> omega

/-- Before completion the configurations coincide; afterwards the guard is
accepted and the scanner remains at its completed-frame control state. -/
def Related (a b : Config) : Prop :=
  (a.state = some 3 ∧ b.state = none) ∨ (a = b ∧ a.state ≠ some 3)

theorem related_step (a b : Config) (ha : Valid 7 a) (h : Related a b) :
    Related (step scanner a) (step acceptFrame b) := by
  rcases a with ⟨l,r,s⟩
  rcases b with ⟨l',r',s'⟩
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · simp only at h1 h2
    subst s
    subst s'
    simp [Related, step, scanner, Source284TaggedScanner.table]
  · cases h1
    cases s with
    | none => simp [Related, step]
    | some q =>
      have hq : q < 7 := ha q rfl
      interval_cases q <;> cases hb : r.testBit 0 <;>
        simp_all [Related, step, acceptFrame, scanner, Source284TaggedScanner.table]

theorem run_related (c : Config) (hvalid : Valid 7 c) (hstate : c.state ≠ some 3)
    (k : Nat) : Related (run scanner c k) (run acceptFrame c k) := by
  induction k with
  | zero => exact Or.inr ⟨rfl, hstate⟩
  | succ k ih =>
    exact related_step _ _ (valid_run 7 scanner c Source284TaggedScanner.table_closed hvalid k) ih

def cutoff (m : Nat) : Nat := 2*m+4

def table (m : Nat) : Nat → Bool → Row :=
  Source284TableCountdown.table 7 (cutoff m) acceptFrame

def states (m : Nat) : Nat := Source284TableCountdown.allocated 7 (cutoff m)

theorem table_closed (m : Nat) : Closed (states m) (table m) :=
  Source284TableCountdown.closed _ _ _

/-- At the paid fixed cutoff the actual finite table has either accepted or
entered the permanent reject sink. -/
theorem finished (m c i : Nat) :
    let s := (run (table m) ⟨c,i,some 0⟩ (cutoff m)).state
    s = none ∨ s = some (Source284TableCountdown.sink 7 (cutoff m)) := by
  dsimp only
  have hv : Valid 7 ⟨c,i,some 0⟩ := by
    intro q hq; simp only [Option.some.injEq] at hq; omega
  have h := Source284TableCountdown.run_mapped 7 (cutoff m) acceptFrame
    ⟨c,i,some 0⟩ hv acceptFrame_closed (cutoff m) (by omega)
  rw [Source284TableCountdown.mapped_start] at h
  unfold table
  rw [h]
  cases hs : (run acceptFrame ⟨c,i,some 0⟩ (cutoff m)).state <;>
    simp [Source284TableCountdown.mapped, hs]

/-- A valid tag starts the scanner in marker mode. At every even number of
subsequent steps its mode is marker or completed; at the next step it is
payload or completed. -/
theorem scanner_even (m : Nat) (c : Config)
    (hc : c.state = some 1 ∨ c.state = some 3) :
    (run scanner c (2*m)).state = some 1 ∨ (run scanner c (2*m)).state = some 3 := by
  induction m generalizing c with
  | zero => simpa [run] using hc
  | succ m ih =>
    have htime : 2*(m+1) = 2*m+2 := by omega
    rw [htime, Source284TaggedScanner.run_add]
    have hs := ih c hc
    cases hx : run scanner c (2*m) with
    | mk l r s =>
      simp only [hx] at hs
      rcases hs with hs | hs <;> subst s <;> cases hb : r.testBit 0 <;>
        simp [run, step, scanner, Source284TaggedScanner.table, hb]

theorem scanner_odd (m left right : Nat) :
    (run scanner ⟨left,right,some 1⟩ (2*m+1)).state = some 2 ∨
      (run scanner ⟨left,right,some 1⟩ (2*m+1)).state = some 3 := by
  rw [Source284TaggedScanner.run_add]
  have hs := scanner_even m ⟨left,right,some 1⟩ (Or.inl rfl)
  cases hx : run scanner ⟨left,right,some 1⟩ (2*m) with
  | mk l r s =>
    simp only [hx] at hs
    rcases hs with hs | hs <;> subst s <;> cases hb : r.testBit 0 <;>
      simp [run, step, scanner, Source284TaggedScanner.table, hb]

/-- At the observation boundary the only possible modes are rejection
(payload or invalid-tag sink) and completed frame. -/
theorem scanner_final_states (m c i : Nat) :
    let s := (run scanner ⟨c,i,some 0⟩ (cutoff m)).state
    s = some 2 ∨ s = some 3 ∨ s = some 6 := by
  dsimp only
  have ht : cutoff m = 3+(2*m+1) := by simp [cutoff]; omega
  rw [ht, Source284TaggedScanner.run_add, Source284TaggedScanner.run_three]
  by_cases h : c%4 = 0
  · have h0 : c%2 = 0 := by omega
    have h1 : (c/2)%2 = 0 := by omega
    simp only [h, h0, h1, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    rcases scanner_odd m (4*i) (c/4) with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · simp only [h, ↓reduceIte]
    exact Or.inr (Or.inr (Source284TaggedScanner.sink_run _ _ _))

/-- The scanner's rejecting states characterize the executable fixed-window
decoder, including invalid tags and arbitrary high certificate bits. -/
theorem scanner_reject (m c i : Nat) :
    ((run scanner ⟨c,i,some 0⟩ (cutoff m)).state = some 2 ∨
     (run scanner ⟨c,i,some 0⟩ (cutoff m)).state = some 6) ↔
      Source284TaggedWitnessCodec.decode m c = none := by
  have h := Source284TaggedScannerCutoff.source_reject_iff m c i 0
  have hv : Valid 7 ⟨c,i,some 0⟩ := by
    intro q hq; simp only [Option.some.injEq] at hq; omega
  have hr := Source284TaggedScanner.source_run 0 ⟨c,i,some 0⟩ hv (cutoff m)
  change Source284Relative.run (Source284TaggedScanner.description 0)
    (Source284Relative.initial i c) (cutoff m) = _ at hr
  change ((Source284Relative.run (Source284TaggedScanner.description 0)
    (Source284Relative.initial i c) (cutoff m)).state = 5 ∨
    (Source284Relative.run (Source284TaggedScanner.description 0)
    (Source284Relative.initial i c) (cutoff m)).state = 13) ↔ _ at h
  rw [hr] at h
  cases hs : (run scanner ⟨c,i,some 0⟩ (cutoff m)).state with
  | none => simpa [toSource, nextState, hs] using h
  | some q =>
    have hq : q < 7 := (valid_run 7 scanner ⟨c,i,some 0⟩
      Source284TaggedScanner.table_closed hv (cutoff m)) q hs
    interval_cases q <;> simpa [toSource, nextState, active, hs] using h

theorem acceptFrame_correct (m c i : Nat) :
    (run acceptFrame ⟨c,i,some 0⟩ (cutoff m)).state = none ↔
      Source284TaggedWitnessCodec.decode m c ≠ none := by
  have hv : Valid 7 ⟨c,i,some 0⟩ := by
    intro q hq; simp only [Option.some.injEq] at hq; omega
  have hr := run_related ⟨c,i,some 0⟩ hv (by simp) (cutoff m)
  have hs := scanner_final_states m c i
  have hd := scanner_reject m c i
  dsimp only at hs
  rcases hs with hs | hs | hs
  · have hnone := hd.mp (Or.inl hs)
    rcases hr with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [hs] at ha; contradiction
    · rw [← ha,hs]
      simp [hnone]
  · have hsome : Source284TaggedWitnessCodec.decode m c ≠ none := by
      intro hn
      rcases hd.mpr hn with h | h <;> rw [hs] at h <;> contradiction
    rcases hr with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp [hb, hsome]
    · exact False.elim (hb hs)
  · have hnone := hd.mp (Or.inr hs)
    rcases hr with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [hs] at ha; contradiction
    · rw [← ha,hs]
      simp [hnone]

/-- The encoded source table decides exactly whether the tagged fixed-window
decoder succeeds. It has completed by the fixed cutoff and remains stable at
all later finite clocks. -/
theorem source_accepts_iff (m c i tail extra : Nat) :
    Source284Relative.accepts (encode (states m) (table m) tail) i c
      (cutoff m + extra) = true ↔ Source284TaggedWitnessCodec.decode m c ≠ none := by
  rw [bounded_acceptance (states m) (table m) tail (by simp [states, Source284TableCountdown.allocated])
    (table_closed m)]
  rw [show table m = Source284TableCountdown.table 7 (cutoff m) acceptFrame by rfl]
  rw [Source284TableCountdown.initial_acceptance_stable 7 (cutoff m) acceptFrame
    (by omega) acceptFrame_closed c i extra]
  simp only [Option.isNone_iff_eq_none]
  exact acceptFrame_correct m c i

/-- The source control is either accepting or at the explicitly allocated
reject sink by the cutoff, and remains so for every later finite clock. -/
theorem source_finished (m c i tail extra : Nat) :
    let s := (Source284Relative.run (encode (states m) (table m) tail)
      (Source284Relative.initial i c) (cutoff m + extra)).state
    s = 0 ∨ s = active (Source284TableCountdown.sink 7 (cutoff m)) := by
  dsimp only
  have hv : Valid (states m) ⟨c,i,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [states, Source284TableCountdown.allocated]
  have hr := run_toSource (states m) (table m) tail ⟨c,i,some 0⟩
    (table_closed m) hv (cutoff m+extra)
  change Source284Relative.run (encode (states m) (table m) tail)
    (Source284Relative.initial i c) _ = _ at hr
  rw [hr, Source284TableCountdown.run_add]
  rcases finished m c i with h | h
  · have hn := Source284TableCountdown.run_none (table m) _ h extra
    rw [hn]
    simp [toSource, nextState, h]
  · have hs := Source284TableCountdown.sink_run 7 (cutoff m) acceptFrame
      (run (table m) ⟨c,i,some 0⟩ (cutoff m)) h extra
    change (run (table m) _ extra).state = _ at hs
    simp [toSource, nextState, hs]

/-- The rejection route is exact, including after any additional steps. -/
theorem source_sink_iff (m c i tail extra : Nat) :
    (Source284Relative.run (encode (states m) (table m) tail)
      (Source284Relative.initial i c) (cutoff m + extra)).state =
        active (Source284TableCountdown.sink 7 (cutoff m)) ↔
      Source284TaggedWitnessCodec.decode m c = none := by
  have hf := source_finished m c i tail extra
  have ha := source_accepts_iff m c i tail extra
  change (((Source284Relative.run (encode (states m) (table m) tail)
    (Source284Relative.initial i c) (cutoff m + extra)).state == 0) = true ↔ _) at ha
  have hp : active (Source284TableCountdown.sink 7 (cutoff m)) ≠ 0 := by
    simp [active]
  dsimp only at hf
  constructor
  · intro hs
    by_contra hn
    have hz := ha.mpr hn
    rw [hs] at hz
    simp [hp] at hz
  · intro hn
    rcases hf with hz | hs
    · have hnot : Source284TaggedWitnessCodec.decode m c ≠ none := by
        apply ha.mp
        simp [hz]
      exact False.elim (hnot hn)
    · exact hs

/-- The countdown costs a quadratic bound in the fixed cutoff. This counts
logical states, not serialized bits, physical states, or evaluation time. -/
theorem states_bound (m : Nat) :
    states m ≤ (max 7 (cutoff m)+1)^2+1 :=
  Source284TableCountdown.allocated_le 7 (cutoff m)

theorem record_count (m : Nat) :
    (records (states m) (table m)).length = 2 * states m := by
  simp [records]

-- Empty witness, malformed tag, and an overlong one-bit witness. These
-- concrete checks supplement the universal source theorem.
example : (run (table 0) ⟨0,0,some 0⟩ (cutoff 0)).state = none := by decide +kernel
example : (run (table 0) ⟨1,0,some 0⟩ (cutoff 0)).state =
    some (Source284TableCountdown.sink 7 (cutoff 0)) := by decide +kernel
example : (run (table 0) ⟨4,0,some 0⟩ (cutoff 0)).state =
    some (Source284TableCountdown.sink 7 (cutoff 0)) := by decide +kernel
example : (run (table 1) ⟨4,0,some 0⟩ (cutoff 1)).state = none := by decide +kernel

end Shared.Beeping.NPcoNP.Source284FixedWitnessGuard
