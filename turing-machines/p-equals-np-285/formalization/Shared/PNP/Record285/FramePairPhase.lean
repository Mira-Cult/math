import Shared.Codes.FiniteProgramPhasesWith
import Shared.PNP.Record285.FramePairProbe

/-! Consume a full `(data, tag)` pair through two physical tagged-buffer
phases, then run the real bit/sentinel probe and an arbitrary continuation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.FramePairPhase
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost result totalCost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramPhaseProbe (stride shiftStatus_add)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (zero one : List Bool) (next : Program) : Program :=
  Shared.Codes.FiniteProgramPhasesWith.phases zero one (FramePairProbe.program next) 2

theorem program_valid (zero one : List Bool) (next : Program)
    (hn : valid next = true) (hlen : 3 ≤ next.length) : valid (program zero one next) = true :=
  Shared.Codes.FiniteProgramPhasesWith.phases_valid zero one (FramePairProbe.program next)
    (FramePairProbe.program_valid next hn hlen) 2

def pairCost (zero one : List Bool) (head bit : Bool) (xs : List Bool) : Nat :=
  cost zero one head xs + cost zero one bit (output zero one head xs)

def pairOutput (zero one : List Bool) (head bit : Bool) (xs : List Bool) : List Bool :=
  output zero one bit (output zero one head xs)

/-- Both physical phases finish at the actual linked probe entry. The
buffer's complete tape is related to the canonical post-pair layout. -/
theorem pair_run (zero one : List Bool) (next : Program) (hn : valid next = true)
    (hlen : 3 ≤ next.length) (head bit : Bool) (xs left : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (bit::true::left) head xs).2) :
    ∃ d, run (program zero one next) c (pairCost zero one head bit xs) = some (.inr d) ∧
      d.1 = 2*stride zero one ∧ TapeRel d.2 (canonical left true (pairOutput zero one head bit xs)).2 := by
  have hp := FramePairProbe.program_valid next hn hlen
  have h := Shared.Codes.FiniteProgramPhasesWith.run_phases zero one (FramePairProbe.program next) hp
    2 [bit,true] (by simp) head xs left c hq (by simpa using ht)
  simpa [program,pairCost,pairOutput,totalCost,result] using h

/-- A further tagged pair selects the zero or one entry of the supplied
continuation, preserving the full physical tape and charging the probe. -/
theorem pair_then_bit (zero one : List Bool) (next : Program) (hn : valid next = true)
    (hlen : 3 ≤ next.length) (head bit nextBit : Bool) (xs tail : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (bit::true::nextBit::true::tail) head xs).2) (fuel : Nat) :
    let out := pairOutput zero one head bit xs
    let tape := (canonical (nextBit::true::tail) true out).2
    StatusRel (run (program zero one next) c (pairCost zero one head bit xs+4+fuel))
      (shiftStatus (2*stride zero one+8) (run next ((if nextBit then 1 else 0),tape) fuel)) := by
  dsimp only
  obtain ⟨d,hd,hstate,htape⟩ := pair_run zero one next hn hlen head bit xs (nextBit::true::tail) c hq ht
  have hp := FramePairProbe.program_valid next hn hlen
  have hcont := Shared.Codes.FiniteProgramPhasesWith.continuation_run zero one (FramePairProbe.program next) hp
    2 (0,d.2) (by have := Shared.Codes.FiniteProgramLink.valid_nonempty _ hp; omega) (4+fuel)
  change run (program zero one next) (shiftConfig (2*stride zero one) (0,d.2)) (4+fuel) = _ at hcont
  have hcfg : d = shiftConfig (2*stride zero one) (0,d.2) := by
    cases d with | mk q t => simp only at hstate; subst q; rfl
  rw [show pairCost zero one head bit xs+4+fuel = pairCost zero one head bit xs+(4+fuel) by omega,
    run_continue _ _ _ _ _ hd,hcfg,hcont]
  have hrel := run_related (FramePairProbe.program next) (0,d.2)
    (0,(canonical (nextBit::true::tail) true (pairOutput zero one head bit xs)).2)
    rfl htape (4+fuel)
  have hprobe := FramePairProbe.probe_bit_then_continue next hn hlen true nextBit tail
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged (pairOutput zero one head bit xs) ++ [false,false,false]) fuel
  change run (FramePairProbe.program next)
      (0,(canonical (nextBit::true::tail) true (pairOutput zero one head bit xs)).2) (4+fuel) = _ at hprobe
  rw [hprobe] at hrel
  have hshift := FrameBufferHandoff.shift_status_related (2*stride zero one) _ _ hrel
  rw [shiftStatus_add] at hshift
  exact hshift

/-- With a blank sentinel the same physical block selects the end entry. -/
theorem pair_then_end (zero one : List Bool) (next : Program) (hn : valid next = true)
    (hlen : 3 ≤ next.length) (head bit : Bool) (xs tail : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (bit::true::false::false::tail) head xs).2) (fuel : Nat) :
    let out := pairOutput zero one head bit xs
    let tape := (canonical (false::false::tail) true out).2
    StatusRel (run (program zero one next) c (pairCost zero one head bit xs+4+fuel))
      (shiftStatus (2*stride zero one+8) (run next (2,tape) fuel)) := by
  dsimp only
  obtain ⟨d,hd,hstate,htape⟩ := pair_run zero one next hn hlen head bit xs (false::false::tail) c hq ht
  have hp := FramePairProbe.program_valid next hn hlen
  have hcont := Shared.Codes.FiniteProgramPhasesWith.continuation_run zero one (FramePairProbe.program next) hp
    2 (0,d.2) (by have := Shared.Codes.FiniteProgramLink.valid_nonempty _ hp; omega) (4+fuel)
  change run (program zero one next) (shiftConfig (2*stride zero one) (0,d.2)) (4+fuel) = _ at hcont
  have hcfg : d = shiftConfig (2*stride zero one) (0,d.2) := by
    cases d with | mk q t => simp only at hstate; subst q; rfl
  rw [show pairCost zero one head bit xs+4+fuel = pairCost zero one head bit xs+(4+fuel) by omega,
    run_continue _ _ _ _ _ hd,hcfg,hcont]
  have hrel := run_related (FramePairProbe.program next) (0,d.2)
    (0,(canonical (false::false::tail) true (pairOutput zero one head bit xs)).2)
    rfl htape (4+fuel)
  have hprobe := FramePairProbe.probe_end_then_continue next hn hlen true tail
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged (pairOutput zero one head bit xs) ++ [false,false,false]) fuel
  change run (FramePairProbe.program next)
      (0,(canonical (false::false::tail) true (pairOutput zero one head bit xs)).2) (4+fuel) = _ at hprobe
  rw [hprobe] at hrel
  have hshift := FrameBufferHandoff.shift_status_related (2*stride zero one) _ _ hrel
  rw [shiftStatus_add] at hshift
  exact hshift

end Shared.PNP.Record285.FramePairPhase
