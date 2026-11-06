import Shared.Codes.FiniteProgramTaggedSkip
import Shared.Codes.FiniteProgramOneExit

/-! A single finite table appends the current bit to a tagged buffer and
then skips a caller-specified finite number of already-consumed cells. The
number of skips is a run length in the theorem, not a runtime stop detector. -/
namespace Shared.Codes.FiniteProgramAppendSkip
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical tapeAt_append_blank)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def source : Program := Shared.Codes.FiniteProgramTaggedLoop.base [] []
def exit : Nat := Shared.Codes.FiniteProgramTaggedLoop.stop [] []
def program : Program := Shared.Codes.FiniteProgramOneExit.program source
  Shared.Codes.FiniteProgramTaggedSkip.program exit
def offset : Nat := Shared.Codes.FiniteProgramOneExit.offset source

theorem source_valid : valid source = true := Shared.Codes.FiniteProgramTaggedLoop.base_valid [] []
theorem exit_bound : exit < source.length := Shared.Codes.FiniteProgramTaggedLoop.stop_bound [] []
theorem source_exit (t : Tape) : step source (exit,t) = some (.inl false) :=
  Shared.Codes.FiniteProgramTaggedLoop.base_stop [] [] t

theorem program_valid : valid program = true :=
  Shared.Codes.FiniteProgramOneExit.program_valid _ _ _ source_valid
    Shared.Codes.FiniteProgramTaggedSkip.program_valid exit_bound

@[simp] theorem program_length : program.length = offset+17 := by
  simp [program,offset]

/-- Starting on a data bit, append it to the tagged buffer and advance to
the next cell. The run stops just before the explicit handoff. -/
theorem append (b p : Bool) (xs L : List Bool) :
    run program (canonical (p::L) b xs) (16*xs.length+29) =
      some (.inr (exit,tapeAt L (p::false::tagged (xs++[b]) ++ [false,false]))) := by
  have h := Shared.Codes.FiniteProgramExtendAdvance.extend_advance [] [] [] b false p xs L
  have hsource : run source (canonical (p::L) b xs) (16*xs.length+29) =
      some (.inr (exit,tapeAt L (p::false::tagged (xs++[b]) ++ [false,false]))) := by
    simpa [source,exit,canonical,Shared.Codes.FiniteProgramTaggedLoop.base,
      Shared.Codes.FiniteProgramTaggedLoop.stop] using h
  exact Shared.Codes.FiniteProgramOneExit.first_entry source
    Shared.Codes.FiniteProgramTaggedSkip.program exit _ _ _ source_valid
    (by simp [canonical,source,Shared.Codes.FiniteProgramTaggedLoop.base_length]) source_exit hsource

/-- One append followed by a finite number of skips, all in the same linked
table. The original data bit is appended before any skipped cell is erased.
The last predecessor, or the first predecessor when `remaining` is empty,
remains under the head. -/
theorem append_then_skip (remaining : List Bool) (b p : Bool) (xs L : List Bool) :
    ∃ d, run program (canonical (p::(remaining++L)) b xs)
        ((16*xs.length+29)+2+remaining.length*(10*(xs.length+1)+7)) =
        some (.inr (shiftConfig offset d)) ∧
      d.1 = 0 ∧ TapeRel d.2
        (canonical L (Shared.Codes.FiniteProgramTaggedSkip.finalHead remaining p) (xs++[b])).2 := by
  let word := xs++[b]
  let t := tapeAt (remaining++L) (p::false::tagged word ++ [false,false])
  have ha := append b p xs (remaining++L)
  have hh := Shared.Codes.FiniteProgramOneExit.handoff source
    Shared.Codes.FiniteProgramTaggedSkip.program exit exit_bound t
  have ht : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce t)
      (canonical (remaining++L) p word).2 := by
    apply Eq.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related t)
    have hb := tapeAt_append_blank (remaining++L) (false::tagged word ++ [false,false]) p
    simpa [t,canonical,List.append_assoc,TapeRel] using hb
  obtain ⟨d,hd,hq,hrel⟩ := Shared.Codes.FiniteProgramTaggedSkip.skips remaining p word L
    (0,Shared.Codes.FiniteProgramThreeExit.bounce t) rfl ht
  have hshift := Shared.Codes.FiniteProgramOneExit.continuation source
    Shared.Codes.FiniteProgramTaggedSkip.program exit
    Shared.Codes.FiniteProgramTaggedSkip.program_valid
    (0,Shared.Codes.FiniteProgramThreeExit.bounce t) (by simp)
    (remaining.length*(10*word.length+7))
  rw [hd] at hshift
  refine ⟨d,?_,hq,hrel⟩
  have heq : remaining.length*(10*word.length+7) =
      remaining.length*(10*(xs.length+1)+7) := by simp [word]
  rw [← heq,show (16*xs.length+29)+2+remaining.length*(10*word.length+7) =
      (16*xs.length+29)+(2+remaining.length*(10*word.length+7)) by omega,
    run_continue _ _ _ _ _ ha]
  change run (Shared.Codes.FiniteProgramOneExit.program source
    Shared.Codes.FiniteProgramTaggedSkip.program exit) (exit,t) _ = _
  rw [run_continue _ _ _ _ _ hh]
  simpa [program,offset,shiftConfig,shiftStatus] using hshift

end Shared.Codes.FiniteProgramAppendSkip
