import Shared.PNP.Record285.FramePairPhase

/-! One real pair block with different output words for its two phases.
The first emits its source head, the second emits the data bit and `true`.
This is intended to produce reverse canonical payload triples. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.EncodedPairPhase
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramPhaseProbe (stride shiftStatus_add)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.Codes.FiniteProgramPhasesWith (phases)

def program (next : Program) : Program :=
  phases [] [] (phases [true] [true] (FramePairProbe.program next) 1) 1

theorem program_valid (next : Program) (hn : valid next = true) (hlen : 3 ≤ next.length) :
    valid (program next) = true := by
  apply Shared.Codes.FiniteProgramPhasesWith.phases_valid
  apply Shared.Codes.FiniteProgramPhasesWith.phases_valid
  exact FramePairProbe.program_valid next hn hlen

def pairCost (head bit : Bool) (xs : List Bool) : Nat :=
  cost [] [] head xs + cost [true] [true] bit (output [] [] head xs)

def pairOutput (head bit : Bool) (xs : List Bool) : List Bool :=
  output [true] [true] bit (output [] [] head xs)

theorem pairOutput_eq (head bit : Bool) (xs : List Bool) :
    pairOutput head bit xs = xs ++ [head,bit,true] := by
  cases head <;> cases bit <;> simp [pairOutput,output,List.append_assoc]

/-- The two differently configured literal phases run in order and preserve
the complete tape at the relocated probe. -/
theorem pair_run (next : Program) (hn : valid next = true) (hlen : 3 ≤ next.length)
    (head bit : Bool) (xs left : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (bit::true::left) head xs).2) :
    ∃ d, run (program next) c (pairCost head bit xs) = some (.inr d) ∧
      d.1 = 86 ∧ TapeRel d.2 (canonical left true (pairOutput head bit xs)).2 := by
  let tail := phases [true] [true] (FramePairProbe.program next) 1
  have ht' : TapeRel c.2 (canonical (bit::(true::left)) head xs).2 := ht
  obtain ⟨mid,hm,hqmid,htmid⟩ :=
    Shared.Codes.FiniteProgramPhasesWith.first_phase_related [] [] tail 0 head bit xs (true::left) c hq ht'
  have htail : valid tail = true := by
    exact Shared.Codes.FiniteProgramPhasesWith.phases_valid _ _ _ (FramePairProbe.program_valid next hn hlen) _
  have hnxt : valid (FramePairProbe.program next) = true := FramePairProbe.program_valid next hn hlen
  obtain ⟨last,hl,hql,htl⟩ := Shared.Codes.FiniteProgramPhasesWith.run_phases [true] [true]
    (FramePairProbe.program next) hnxt 1 [true] rfl bit (output [] [] head xs) left (0,mid.2) rfl (by simpa using htmid)
  have hc : ((0,mid.2) : Config).1 < tail.length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty tail htail
  have hs := Shared.Codes.FiniteProgramSplice.second_run
    (Shared.Codes.FiniteProgramPhase.program [] []) tail htail (0,mid.2) hc
    (cost [true] [true] bit (output [] [] head xs))
  have hl' : run tail (0,mid.2) (cost [true] [true] bit (output [] [] head xs)) = some (.inr last) := by
    simpa [tail,Shared.Codes.FiniteProgramTaggedLoop.totalCost] using hl
  rw [hl'] at hs
  have h40 : stride [] [] = 40 := by rw [Shared.Codes.FiniteProgramPhaseProbe.stride_length]; decide
  have h46 : stride [true] [true] = 46 := by rw [Shared.Codes.FiniteProgramPhaseProbe.stride_length]; decide
  change run (program next) c (cost [] [] head xs) = some (.inr mid) at hm
  change run (program next) (shiftConfig (stride [] []) (0,mid.2))
    (cost [true] [true] bit (output [] [] head xs)) =
      shiftStatus (stride [] []) (some (.inr last)) at hs
  rw [h40] at hs
  refine ⟨shiftConfig 40 last,?_,?_,?_⟩
  · change run (program next) c (cost [] [] head xs + cost [true] [true] bit (output [] [] head xs)) = _
    rw [run_continue _ _ _ _ _ hm]
    have hcfg : mid = shiftConfig 40 (0,mid.2) := by
      cases mid with | mk q t => simp only at hqmid; rw [h40] at hqmid; subst q; rfl
    rw [hcfg]
    simpa [shiftStatus] using hs
  · simp only [shiftConfig]
    rw [h46] at hql
    omega
  · simpa [pairOutput,shiftConfig,Shared.Codes.FiniteProgramTaggedLoop.result] using htl

/-- Every finite probe run starts after the two distinct physical phases. -/
theorem continuation_run (next : Program) (hn : valid next = true) (hlen : 3 ≤ next.length)
    (c : Config) (hc : c.1 < (FramePairProbe.program next).length) (fuel : Nat) :
    run (program next) (shiftConfig 86 c) fuel =
      shiftStatus 86 (run (FramePairProbe.program next) c fuel) := by
  let probe := FramePairProbe.program next
  let tail := phases [true] [true] probe 1
  have hp := FramePairProbe.program_valid next hn hlen
  have ht := Shared.Codes.FiniteProgramPhasesWith.phases_valid [true] [true] probe hp 1
  have h46 : stride [true] [true] = 46 := by rw [Shared.Codes.FiniteProgramPhaseProbe.stride_length]; decide
  have h40 : stride [] [] = 40 := by rw [Shared.Codes.FiniteProgramPhaseProbe.stride_length]; decide
  have hsecond := Shared.Codes.FiniteProgramPhasesWith.continuation_run [true] [true] probe hp 1 c hc fuel
  simp only [Nat.one_mul,h46] at hsecond
  have hin : (shiftConfig 46 c).1 < tail.length := by
    change c.1 < probe.length at hc
    simp only [tail,Shared.Codes.FiniteProgramPhasesWith.phases_length,Nat.one_mul,h46,shiftConfig]
    omega
  have hfirst := Shared.Codes.FiniteProgramSplice.second_run
    (Shared.Codes.FiniteProgramPhase.program [] []) tail ht (shiftConfig 46 c) hin fuel
  change run (program next) (shiftConfig (stride [] []) (shiftConfig 46 c)) fuel =
    shiftStatus (stride [] []) (run tail (shiftConfig 46 c) fuel) at hfirst
  rw [h40] at hfirst
  rw [hsecond,shiftStatus_add] at hfirst
  simpa [probe,shiftConfig,← Nat.add_assoc] using hfirst

/-- After the encoded pair, the bit probe dispatches to the arbitrary next
program with exact relocation and full-tape status relation. -/
theorem pair_then_bit (next : Program) (hn : valid next = true) (hlen : 3 ≤ next.length)
    (head bit nextBit : Bool) (xs tail : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (bit::true::nextBit::true::tail) head xs).2) (fuel : Nat) :
    StatusRel (run (program next) c (pairCost head bit xs+4+fuel))
      (shiftStatus 94 (run next ((if nextBit then 1 else 0),
        (canonical (nextBit::true::tail) true (pairOutput head bit xs)).2) fuel)) := by
  obtain ⟨d,hd,hstate,htape⟩ := pair_run next hn hlen head bit xs (nextBit::true::tail) c hq ht
  have hc : ((0,d.2) : Config).1 < (FramePairProbe.program next).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (FramePairProbe.program_valid next hn hlen)
  have hcont := continuation_run next hn hlen (0,d.2) hc (4+fuel)
  have hcfg : d = shiftConfig 86 (0,d.2) := by
    cases d with | mk q t => simp only at hstate; subst q; rfl
  rw [show pairCost head bit xs+4+fuel = pairCost head bit xs+(4+fuel) by omega,
    run_continue _ _ _ _ _ hd,hcfg,hcont]
  have hrel := run_related (FramePairProbe.program next) (0,d.2)
    (0,(canonical (nextBit::true::tail) true (pairOutput head bit xs)).2) rfl htape (4+fuel)
  have hprobe := FramePairProbe.probe_bit_then_continue next hn hlen true nextBit tail
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged (pairOutput head bit xs) ++ [false,false,false]) fuel
  change run (FramePairProbe.program next)
    (0,(canonical (nextBit::true::tail) true (pairOutput head bit xs)).2) (4+fuel) = _ at hprobe
  rw [hprobe] at hrel
  have hshift := FrameBufferHandoff.shift_status_related 86 _ _ hrel
  rw [shiftStatus_add] at hshift
  exact hshift

theorem pair_then_end (next : Program) (hn : valid next = true) (hlen : 3 ≤ next.length)
    (head bit : Bool) (xs tail : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (bit::true::false::false::tail) head xs).2) (fuel : Nat) :
    StatusRel (run (program next) c (pairCost head bit xs+4+fuel))
      (shiftStatus 94 (run next (2,(canonical (false::false::tail) true (pairOutput head bit xs)).2) fuel)) := by
  obtain ⟨d,hd,hstate,htape⟩ := pair_run next hn hlen head bit xs (false::false::tail) c hq ht
  have hc : ((0,d.2) : Config).1 < (FramePairProbe.program next).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (FramePairProbe.program_valid next hn hlen)
  have hcont := continuation_run next hn hlen (0,d.2) hc (4+fuel)
  have hcfg : d = shiftConfig 86 (0,d.2) := by
    cases d with | mk q t => simp only at hstate; subst q; rfl
  rw [show pairCost head bit xs+4+fuel = pairCost head bit xs+(4+fuel) by omega,
    run_continue _ _ _ _ _ hd,hcfg,hcont]
  have hrel := run_related (FramePairProbe.program next) (0,d.2)
    (0,(canonical (false::false::tail) true (pairOutput head bit xs)).2) rfl htape (4+fuel)
  have hprobe := FramePairProbe.probe_end_then_continue next hn hlen true tail
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged (pairOutput head bit xs) ++ [false,false,false]) fuel
  change run (FramePairProbe.program next)
    (0,(canonical (false::false::tail) true (pairOutput head bit xs)).2) (4+fuel) = _ at hprobe
  rw [hprobe] at hrel
  have hshift := FrameBufferHandoff.shift_status_related 86 _ _ hrel
  rw [shiftStatus_add] at hshift
  exact hshift

end Shared.PNP.Record285.EncodedPairPhase
