import Shared.Codes.FiniteProgramTaggedSkipFixed
import Shared.Codes.FiniteProgramAppendSkip

/-! Append one data bit, then execute a statically selected number of skip
stages before entering a distinct terminal placeholder. -/
namespace Shared.Codes.FiniteProgramAppendSkipFixed
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical tapeAt_append_blank)
open Shared.Codes.FiniteProgramAppendSkip (source exit offset source_valid exit_bound source_exit)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (n : Nat) : Program := Shared.Codes.FiniteProgramOneExit.program source
  (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) exit

@[simp] theorem program_length (n : Nat) : (program n).length = offset+(17*n+1) := by
  simp [program,offset]

theorem offset_value : offset = 41 := by decide

/-- Each compiled skip stage costs 17 states in addition to the 42-state
append, handoff, and final-placeholder base. -/
theorem program_length_explicit (n : Nat) : (program n).length = 17*n+42 := by
  rw [program_length,offset_value]
  omega

theorem program_valid (n : Nat) : valid (program n) = true :=
  Shared.Codes.FiniteProgramOneExit.program_valid _ _ _ source_valid
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program_valid n) exit_bound

/-- The saved bit is appended before the fixed-count skip begins. The final
state is an explicit continuation placeholder, not an infinite machine. -/
theorem append_then_skip (remaining : List Bool) (b p : Bool) (xs L : List Bool) :
    ∃ t, run (program remaining.length) (canonical (p::(remaining++L)) b xs)
        ((16*xs.length+29)+2+remaining.length*(10*(xs.length+1)+7)) =
        some (.inr (offset+17*remaining.length,t)) ∧
      TapeRel t (canonical L (Shared.Codes.FiniteProgramTaggedSkip.finalHead remaining p) (xs++[b])).2 := by
  let n := remaining.length
  let word := xs++[b]
  let t := tapeAt (remaining++L) (p::false::tagged word ++ [false,false])
  have h := Shared.Codes.FiniteProgramExtendAdvance.extend_advance [] [] [] b false p xs (remaining++L)
  have hs : run source (canonical (p::(remaining++L)) b xs) (16*xs.length+29) =
      some (.inr (exit,t)) := by
    simpa [source,exit,t,word,canonical,Shared.Codes.FiniteProgramTaggedLoop.base,
      Shared.Codes.FiniteProgramTaggedLoop.stop] using h
  have hp := Shared.Codes.FiniteProgramOneExit.first_entry source
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) exit _ _ _ source_valid
    (by simp [canonical,source,Shared.Codes.FiniteProgramTaggedLoop.base_length]) source_exit hs
  have hh := Shared.Codes.FiniteProgramOneExit.handoff source
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) exit exit_bound t
  have ht : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce t)
      (canonical (remaining++L) p word).2 := by
    apply Eq.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related t)
    have hb := tapeAt_append_blank (remaining++L) (false::tagged word ++ [false,false]) p
    simpa [t,canonical,List.append_assoc,TapeRel] using hb
  obtain ⟨u,hu,hrel⟩ := Shared.Codes.FiniteProgramTaggedSkipFixed.skips remaining p word L
    (0,Shared.Codes.FiniteProgramThreeExit.bounce t) rfl ht
  have hc := Shared.Codes.FiniteProgramOneExit.continuation source
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) exit
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program_valid n)
    (0,Shared.Codes.FiniteProgramThreeExit.bounce t) (by simp)
    (remaining.length*(10*word.length+7))
  change run (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) _ _ = _ at hu
  rw [hu] at hc
  refine ⟨u,?_,hrel⟩
  have heq : remaining.length*(10*word.length+7) =
      remaining.length*(10*(xs.length+1)+7) := by simp [word]
  rw [← heq,show (16*xs.length+29)+2+remaining.length*(10*word.length+7) =
      (16*xs.length+29)+(2+remaining.length*(10*word.length+7)) by omega]
  change run (Shared.Codes.FiniteProgramOneExit.program source
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) exit) _ _ = _
  rw [run_continue _ _ _ _ _ hp,run_continue _ _ _ _ _ hh]
  simpa [offset,shiftConfig,shiftStatus] using hc

/-- The fixed-count pass also works from any tape with the same infinite tape
contents, allowing finite blank padding in either representation. -/
theorem append_then_skip_related (remaining : List Bool) (b p : Bool) (xs L : List Bool)
    (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (p::(remaining++L)) b xs).2) :
    ∃ t, run (program remaining.length) c
        ((16*xs.length+29)+2+remaining.length*(10*(xs.length+1)+7)) =
        some (.inr (offset+17*remaining.length,t)) ∧
      TapeRel t (canonical L (Shared.Codes.FiniteProgramTaggedSkip.finalHead remaining p) (xs++[b])).2 := by
  obtain ⟨u,hu,hurel⟩ := append_then_skip remaining b p xs L
  have hr := run_related (program remaining.length) c (canonical (p::(remaining++L)) b xs)
    (by simpa [canonical] using hq) ht
    ((16*xs.length+29)+2+remaining.length*(10*(xs.length+1)+7))
  rw [hu] at hr
  cases h : run (program remaining.length) c
      ((16*xs.length+29)+2+remaining.length*(10*(xs.length+1)+7)) with
  | none => rw [h] at hr; exact False.elim hr
  | some v => cases v with
    | inl out => rw [h] at hr; exact False.elim hr
    | inr d =>
      rcases d with ⟨q,t⟩
      rw [h] at hr
      change q = offset+17*remaining.length ∧ TapeRel t u at hr
      refine ⟨t,?_,hr.2.trans hurel⟩
      simpa [hr.1] using h

/-- Executing the final placeholder returns false; it must be rebound before
using this finite table as part of a total nonhalting machine. -/
theorem terminal_placeholder (n : Nat) (t : Tape) :
    step (program n) (offset+17*n,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramOneExit.continuation source
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) exit
    (Shared.Codes.FiniteProgramTaggedSkipFixed.program_valid n)
    (17*n,t) (by simp) 1
  have hr : run (Shared.Codes.FiniteProgramTaggedSkipFixed.program n) (17*n,t) 1 = some (.inl false) := by
    simpa [run,advance] using Shared.Codes.FiniteProgramTaggedSkipFixed.terminal_placeholder n t
  rw [hr] at h
  simpa [program,offset,run,advance,shiftConfig,shiftStatus] using h

end Shared.Codes.FiniteProgramAppendSkipFixed
