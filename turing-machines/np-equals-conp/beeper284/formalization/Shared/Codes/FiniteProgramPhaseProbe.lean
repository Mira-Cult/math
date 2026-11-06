import Shared.Codes.FiniteProgramPhase
import Shared.Codes.FiniteProgramFirstBlockProbe

/-! Fixed-count finite phase blocks spliced directly to a two-row boundary
probe. The fixed counter is represented by separate table states. -/
namespace Shared.Codes.FiniteProgramPhaseProbe
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramSplice (stem)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost result totalCost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def dummy : Row × Row := ((false,true,0,1),(true,true,0,1))
def probe : Program := Shared.Codes.FiniteProgramFirstBlockProbe.program [dummy,dummy]
theorem probe_valid : valid probe = true := by decide

def phases (zero one : List Bool) : Nat → Program
  | 0 => probe
  | n+1 => Shared.Codes.FiniteProgramSplice.program (Shared.Codes.FiniteProgramPhase.program zero one) (phases zero one n)

def stride (zero one : List Bool) : Nat := (Shared.Codes.FiniteProgramPhase.program zero one).length-1

theorem phases_valid (zero one : List Bool) (n : Nat) : valid (phases zero one n) = true := by
  induction n with
  | zero => exact probe_valid
  | succ n ih =>
    exact Shared.Codes.FiniteProgramSplice.program_valid _ _
      (Shared.Codes.FiniteProgramPhase.program_valid zero one) ih

theorem phases_length (zero one : List Bool) (n : Nat) :
    (phases zero one n).length = n*stride zero one+probe.length := by
  induction n with
  | zero => simp [phases]
  | succ n ih =>
    simp [phases,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramLink.link,
      Shared.Codes.FiniteProgramSplice.stem_length,ih,stride,Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

/-- State accounting for one phase, including its two charged handoff rows. -/
theorem stride_length (zero one : List Bool) :
    stride zero one = 40+3*zero.length+3*one.length := by
  simp [stride,Shared.Codes.FiniteProgramPhase.length,
    Shared.Codes.FiniteProgramTaggedLoop.base_length,
    Shared.Codes.FiniteProgramExtendAdvance.prefix_length,
    Shared.Codes.FiniteProgramExtendAdvance.old_length,
    Shared.Codes.FiniteProgramTaggedExtend.stagePre_length,
    Shared.Codes.FiniteProgramTaggedExtend.codeZero,
    Shared.Codes.FiniteProgramBitShuttle.tagged_length,
    Shared.Codes.FiniteProgramSelectWord.finish]
  omega

theorem six_phase_length (zero one : List Bool) :
    (phases zero one 6).length = 244+18*zero.length+18*one.length := by
  rw [phases_length,stride_length]
  simp [probe,Shared.Codes.FiniteProgramFirstBlockProbe.program]
  omega

/-- One phase in the assembled table reaches the next phase entry and
preserves the required tape relation. -/
theorem first_phase_related (zero one : List Bool) (n : Nat) (b p : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2) :
    ∃ d, run (phases zero one (n+1)) c (cost zero one b xs) = some (.inr d) ∧
      d.1 = stride zero one ∧ TapeRel d.2 (canonical L p (output zero one b xs)).2 := by
  let phase := Shared.Codes.FiniteProgramPhase.program zero one
  let rest := phases zero one n
  have hp := Shared.Codes.FiniteProgramPhase.cycle zero one b false p xs L
  change run phase (canonical (p::L) b xs) (cost zero one b xs) =
    some (.inr (stride zero one,tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false]))) at hp
  have hp' := Shared.Codes.FiniteProgramSplice.first_run phase rest
    (Shared.Codes.FiniteProgramPhase.program_valid zero one) (canonical (p::L) b xs) _ _ false
    (by simp [canonical,phase,Shared.Codes.FiniteProgramPhase.length])
    (Shared.Codes.FiniteProgramPhase.terminal_step zero one) hp
  change run (phases zero one (n+1)) (canonical (p::L) b xs) _ = _ at hp'
  have h := run_related (phases zero one (n+1)) c (canonical (p::L) b xs)
    (by simpa [canonical] using hq) ht (cost zero one b xs)
  rw [hp'] at h
  cases hs : run (phases zero one (n+1)) c (cost zero one b xs) with
  | none => rw [hs] at h; exact False.elim h
  | some v => cases v with
    | inl out => rw [hs] at h; exact False.elim h
    | inr d =>
      rw [hs] at h
      have hd : d.1 = stride zero one ∧
          TapeRel d.2 (tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false])) := h
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      have hpad := Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank L
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false]) p
      change TapeRel (tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one b xs) ++ [false,false]))
        (canonical L p (output zero one b xs)).2
      simpa [canonical,List.append_assoc] using hpad

set_option maxHeartbeats 1000000 in
/-- The fixed-count assembly runs one phase for each supplied predecessor.
At the end, control is at the first row of the spliced probe. -/
theorem run_phases (zero one : List Bool) (n : Nat) (remaining : List Bool)
    (hlen : remaining.length = n) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ d, run (phases zero one n) c (totalCost zero one remaining b xs) = some (.inr d) ∧
      d.1 = n*stride zero one ∧ TapeRel d.2 (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 := by
  induction n generalizing remaining b xs c with
  | zero =>
    have he : remaining = [] := List.length_eq_zero_iff.mp hlen
    subst remaining
    refine ⟨c,rfl,by simpa using hq,?_⟩
    simpa [result] using ht
  | succ n ih =>
    cases remaining with
    | nil => simp at hlen
    | cons p ps =>
      have hl : ps.length = n := by simp at hlen; omega
      have ht' : TapeRel c.2 (canonical (p::(ps++L)) b xs).2 := by simpa using ht
      obtain ⟨mid,hmid,hmidq,hmidt⟩ := first_phase_related zero one n b p xs (ps++L) c hq ht'
      obtain ⟨last,hlast,hlastq,hlastt⟩ := ih ps hl p (output zero one b xs) (0,mid.2) rfl hmidt
      let phase := Shared.Codes.FiniteProgramPhase.program zero one
      let rest := phases zero one n
      have hc : ((0,mid.2) : Config).1 < rest.length := by
        have hv := phases_valid zero one n
        exact Shared.Codes.FiniteProgramLink.valid_nonempty rest hv
      have hs := Shared.Codes.FiniteProgramSplice.second_run phase rest (phases_valid zero one n)
        (0,mid.2) hc (totalCost zero one ps p (output zero one b xs))
      rw [hlast] at hs
      refine ⟨shiftConfig (stride zero one) last,?_,?_,?_⟩
      · change run (phases zero one (n+1)) c
          (cost zero one b xs + totalCost zero one ps p (output zero one b xs)) = _
        rw [run_continue _ _ _ _ _ hmid]
        have hcfg : mid = shiftConfig (stride zero one) (0,mid.2) := by
          cases mid with | mk q t => simp only at hmidq; subst q; rfl
        rw [hcfg]
        simpa [phase,rest,stride,shiftStatus,phases] using hs
      · simp only [shiftConfig,hlastq]
        simp [Nat.add_mul,Nat.add_comm]
      · exact hlastt

theorem shiftStatus_add (a b : Nat) (s : Status) :
    shiftStatus a (shiftStatus b s) = shiftStatus (a+b) s := by
  cases s with
  | none => rfl
  | some v => cases v with
    | inl x => rfl
    | inr c => simp [shiftStatus,shiftConfig,Nat.add_assoc]

/-- After the fixed phases, the probe runs in its actual spliced rows, with
exactly the same transition count as its standalone table. -/
theorem probe_segment (zero one : List Bool) (n : Nat) (c : Config) (hc : c.1 < probe.length) (k : Nat) :
    run (phases zero one n) (shiftConfig (n*stride zero one) c) k =
      shiftStatus (n*stride zero one) (run probe c k) := by
  induction n with
  | zero =>
    cases h : run probe c k with
    | none => simp [phases,shiftConfig,shiftStatus,h]
    | some v => cases v <;> simp [phases,shiftConfig,shiftStatus,h]
  | succ n ih =>
    let phase := Shared.Codes.FiniteProgramPhase.program zero one
    let s := stride zero one
    have hin : (shiftConfig (n*s) c).1 < (phases zero one n).length := by
      simp only [shiftConfig,phases_length,s]
      omega
    have h := Shared.Codes.FiniteProgramSplice.second_run phase (phases zero one n)
      (phases_valid zero one n) (shiftConfig (n*s) c) hin k
    rw [ih] at h
    rw [shiftStatus_add] at h
    simpa [phase,s,stride,phases,shiftConfig,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

set_option maxHeartbeats 1000000 in
/-- A single assembled table executes the supplied fixed number of phases,
then its own two-row probe distinguishes the first-component boundary. The
source tape must already be phase aligned as specified by `ht`. -/
theorem run_to_boundary (zero one : List Bool) (ps : List Bool) (b : Bool)
    (xs remaining L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical
      ((ps++[false]) ++ ((Shared.ComplexityBridge.PairReverseFirst.expanded remaining).reverse ++ false::false::L).tail) b xs).2) :
    let n := (ps++[false]).length
    ∃ d, run (phases zero one n) c (totalCost zero one (ps++[false]) b xs+2) = some (.inr d) ∧
      d.1 = n*stride zero one + (if remaining.isEmpty then 2 else 3) ∧
      TapeRel d.2 (Shared.ComplexityBridge.PairReverseWitness.tapeLeft
        ((Shared.ComplexityBridge.PairReverseFirst.expanded remaining).reverse ++ false::false::L)
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (result zero one (ps++[false]) b xs).2 ++ [false,false,false])) := by
  dsimp only
  let n := (ps++[false]).length
  let source := (Shared.ComplexityBridge.PairReverseFirst.expanded remaining).reverse ++ false::false::L
  let res := result zero one (ps++[false]) b xs
  obtain ⟨mid,hm,hmid,htape⟩ := run_phases zero one n (ps++[false]) rfl b xs source.tail c hq ht
  have hbit : res.1 = false := Shared.Codes.FiniteProgramFirstBlockProbe.last_predecessor zero one ps b xs
  change TapeRel mid.2 (canonical source.tail res.1 res.2).2 at htape
  rw [hbit] at htape
  let right := false::Shared.Codes.FiniteProgramBitShuttle.tagged res.2 ++ [false,false,false]
  have hcfg : (canonical source.tail false res.2).2 =
      Shared.ComplexityBridge.PairReverseWitness.tapeLeft source right := by
    have hh : source.head?.getD false = false :=
      Shared.Codes.FiniteProgramFirstBlockProbe.first_component_head remaining L
    simp [canonical,Shared.ComplexityBridge.PairMarkedScanner.tapeAt,
      Shared.ComplexityBridge.PairReverseWitness.tapeLeft,hh,right,List.cons_append]
  rw [hcfg] at htape
  obtain ⟨out,ho,hout,htout⟩ := Shared.Codes.FiniteProgramFirstBlockProbe.first_component_boundary_related
    [dummy,dummy] remaining L right (0,mid.2) rfl htape
  have hc : ((0,mid.2) : Config).1 < probe.length := by simp [probe,Shared.Codes.FiniteProgramFirstBlockProbe.program]
  have hp := probe_segment zero one n (0,mid.2) hc 2
  change run (phases zero one n) (shiftConfig (n*stride zero one) (0,mid.2)) 2 =
    shiftStatus (n*stride zero one) (run (Shared.Codes.FiniteProgramFirstBlockProbe.program [dummy,dummy]) (0,mid.2) 2) at hp
  rw [ho] at hp
  refine ⟨shiftConfig (n*stride zero one) out,?_,?_,?_⟩
  · rw [run_continue _ _ _ _ _ hm]
    have he : mid = shiftConfig (n*stride zero one) (0,mid.2) := by
      cases mid with | mk q t => simp only at hmid; subst q; rfl
    rw [he]
    simpa [shiftStatus] using hp
  · simp [shiftConfig,hout,n]
  · exact htout

/-- A literal six-phase controller followed by the boundary probe. The five
listed predecessors plus the final false predecessor give six cycles. -/
theorem six_to_boundary (zero one : List Bool) (ps : List Bool) (hps : ps.length = 5) (b : Bool)
    (xs remaining L : List Bool) (c : Config) (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical
      ((ps++[false]) ++ ((Shared.ComplexityBridge.PairReverseFirst.expanded remaining).reverse ++ false::false::L).tail) b xs).2) :
    ∃ d, run (phases zero one 6) c (totalCost zero one (ps++[false]) b xs+2) = some (.inr d) ∧
      d.1 = 6*stride zero one + (if remaining.isEmpty then 2 else 3) ∧
      TapeRel d.2 (Shared.ComplexityBridge.PairReverseWitness.tapeLeft
        ((Shared.ComplexityBridge.PairReverseFirst.expanded remaining).reverse ++ false::false::L)
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (result zero one (ps++[false]) b xs).2 ++ [false,false,false])) := by
  have h := run_to_boundary zero one ps b xs remaining L c hq ht
  simpa [List.length_append,hps] using h

namespace Fixtures
example : run (phases [] [] 0) (0,([false],false,[])) 2 =
    some (.inr (2,([false],false,[]))) := by decide
example : run (phases [] [] 1)
    (0,tapeAt [true] [false,false,false,false,false]) 31 =
      some (.inr (40,tapeAt [] (true::false::Shared.Codes.FiniteProgramBitShuttle.tagged [false] ++ [false,false]))) := by decide
example : valid (phases [false] [true] 6) = true := phases_valid [false] [true] 6
example : (phases [false] [true] 6).length = 280 := by
  simpa using six_phase_length [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramPhaseProbe
