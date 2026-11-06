import Shared.ComplexityBridge.PairMarkedScanner
import Shared.Codes.FiniteProgramTapeEquiv

/-! A concrete finite table compares a fixed-width tape word without changing
its contents. It reads the whole word even after a mismatch, so both branches
have the same charged length and head position. -/
namespace Shared.Codes.FiniteProgramWordCompare
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed consumed_cons)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def state (i : Nat) (matched : Bool) : Nat := 2*i + if matched then 0 else 1

def liveRow (word : List Bool) (i : Nat) (matched read : Bool) : Row :=
  (read,true,state (i+1) (matched && (read == word[i]!)),0)

def terminalRow (matched read : Bool) : Row :=
  (read,true,0,if matched then 2 else 1)

def rowPair (word : List Bool) (q : Fin (2*(word.length+1))) : Row × Row :=
  let i := q.val / 2
  let matched := q.val % 2 == 0
  if i < word.length then (liveRow word i matched false,liveRow word i matched true)
  else (terminalRow matched false,terminalRow matched true)

def program (word : List Bool) : Program := List.ofFn (rowPair word)

@[simp] theorem program_length (word : List Bool) :
    (program word).length = 2*(word.length+1) := by simp [program]; omega

theorem state_bound (word : List Bool) (i : Nat) (matched : Bool) (hi : i ≤ word.length) :
    state i matched < (program word).length := by
  cases matched <;> simp [state] <;> omega

theorem row_at (word : List Bool) (i : Nat) (matched : Bool) (hi : i ≤ word.length) :
    (program word)[state i matched]? =
      some (if i < word.length then
        (liveRow word i matched false,liveRow word i matched true)
      else (terminalRow matched false,terminalRow matched true)) := by
  have hb := state_bound word i matched hi
  rw [List.getElem?_eq_getElem hb]
  simp only [program,List.getElem_ofFn,rowPair]
  cases matched with
  | false =>
    have hd : (2*i+1)/2 = i := by omega
    simp [state,hd]
  | true => simp [state]

theorem step_live (word : List Bool) (i : Nat) (matched bit : Bool)
    (hi : i < word.length) (L R : List Bool) :
    step (program word) (state i matched,tapeAt L (bit::R)) =
      some (.inr (state (i+1) (matched && (bit == word[i]!)),tapeAt (bit::L) R)) := by
  have hr := row_at word i matched (by omega)
  simp only [hi,if_true] at hr
  cases bit <;> simp [step,hr,liveRow,tapeAt,moveTape]

theorem step_terminal (word : List Bool) (matched : Bool) (t : Tape) :
    step (program word) (state word.length matched,t) = some (.inl matched) := by
  have hr := row_at word word.length matched (by omega)
  simp only [lt_self_iff_false,if_false] at hr
  cases matched <;> cases ht : t.2.1 <;> simp [step,hr,terminalRow,ht]

/-- All generated rows are valid, with two control states per read position
and two final states. -/
theorem program_valid (word : List Bool) : valid (program word) = true := by
  have hn : (program word).isEmpty = false := by
    cases h : program word with
    | nil =>
      have hl := program_length word
      rw [h] at hl
      simp at hl
    | cons r rs => rfl
  have hall : (program word).all
      (fun r => validRow (program word).length r.1 && validRow (program word).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    change r ∈ List.ofFn (rowPair word) at hr
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
    have hq := q.isLt
    simp only [program_length,rowPair]
    split
    · have hi : q.val / 2 < word.length := by assumption
      have hb : ∀ b : Bool, state (q.val / 2+1) b < 2*(word.length+1) := by
        intro b; cases b <;> simp [state] <;> omega
      simp [liveRow,validRow,hb]
    · cases h : (q.val % 2 == 0) <;> simp [terminalRow,validRow,h]
  change (!(program word).isEmpty && (program word).all
    (fun r => validRow (program word).length r.1 && validRow (program word).length r.2)) = true
  rw [hn,hall]
  rfl

/-- A complete scan makes exactly one transition per input bit, retains the
entire word, and records equality with the fixed word in the final state. -/
theorem run_scan (word pre remaining observed suffix L : List Bool) (matched : Bool)
    (hw : word = pre ++ remaining) (hl : observed.length = remaining.length) :
    run (program word) (state pre.length matched,tapeAt L (observed++suffix)) observed.length =
      some (.inr (state word.length (matched && (observed == remaining)),
        tapeAt (consumed L observed) suffix)) := by
  induction remaining generalizing pre observed L matched with
  | nil =>
    cases observed with
    | nil => simp [hw,consumed]
    | cons b obs => simp at hl
  | cons a rest ih =>
    cases observed with
    | nil => simp at hl
    | cons b obs =>
      have hlen : obs.length = rest.length := by simpa using hl
      have hi : pre.length < word.length := by rw [hw]; simp
      have hread : word[pre.length]! = a := by simp [hw]
      have hstep := step_live word pre.length matched b hi L (obs++suffix)
      have hrun : run (program word) (state pre.length matched,tapeAt L ((b::obs)++suffix)) 1 =
          some (.inr (state (pre.length+1) (matched && (b == a)),tapeAt (b::L) (obs++suffix))) := by
        simpa [run,advance,hread] using hstep
      have hnext : word = (pre++[a]) ++ rest := by simpa [List.append_assoc] using hw
      have htail := ih (pre++[a]) obs (b::L) (matched && (b == a)) hnext hlen
      rw [show (b::obs).length = 1+obs.length by simp [Nat.add_comm],run_continue _ _ _ 1 _ hrun]
      cases matched <;> cases a <;> cases b <;>
        simpa [consumed_cons,List.append_assoc] using htail

/-- Starting at state zero, equal-length words enter the matching or
mismatching continuation after exactly the fixed word width. -/
theorem compare_word (word observed suffix L : List Bool) (hlen : observed.length = word.length) :
    run (program word) (0,tapeAt L (observed++suffix)) word.length =
      some (.inr (state word.length (observed == word),tapeAt (consumed L observed) suffix)) := by
  have h := run_scan word [] word observed suffix L true (by simp) (by simpa using hlen)
  simpa [state,hlen] using h

/-- The next charged transition reports the comparison result. -/
theorem compare_result (word observed suffix L : List Bool) (hlen : observed.length = word.length) :
    run (program word) (0,tapeAt L (observed++suffix)) (word.length+1) =
      some (.inl (observed == word)) := by
  rw [run_continue _ _ _ _ _ (compare_word word observed suffix L hlen)]
  simpa [run,advance] using step_terminal word (observed == word) (tapeAt (consumed L observed) suffix)

/-- The scan is unchanged by any blank padding in a physical list-tape
representation, including blanks inside the final code word. -/
theorem compare_word_related (word observed suffix L : List Bool) (hlen : observed.length = word.length)
    (t : Tape) (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t (tapeAt L (observed++suffix))) :
    ∃ t', run (program word) (0,t) word.length = some (.inr (state word.length (observed == word),t')) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel t' (tapeAt (consumed L observed) suffix) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program word) (0,t)
    (0,tapeAt L (observed++suffix)) rfl ht word.length
  rw [compare_word word observed suffix L hlen] at h
  cases hr : run (program word) (0,t) word.length with
  | none => simp [Shared.Codes.FiniteProgramTapeEquiv.StatusRel,hr] at h
  | some value =>
    cases value with
    | inl b => simp [Shared.Codes.FiniteProgramTapeEquiv.StatusRel,hr] at h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = state word.length (observed == word) ∧
        Shared.Codes.FiniteProgramTapeEquiv.TapeRel t' (tapeAt (consumed L observed) suffix) at h
      refine ⟨t',?_,h.2⟩
      rw [h.1]

end Shared.Codes.FiniteProgramWordCompare
