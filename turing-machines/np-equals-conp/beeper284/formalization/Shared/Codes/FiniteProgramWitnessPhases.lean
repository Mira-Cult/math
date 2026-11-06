import Shared.Codes.FiniteProgramPhaseProbe
import Shared.ComplexityBridge.PairReverseWitness

/-! Three-bit witness-block phases with an explicit marker probe. The table
starts from a phase-aligned witness, with its existing tagged output buffer. -/
namespace Shared.Codes.FiniteProgramWitnessPhases
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramSplice (stem)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost result totalCost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def dummy : Row × Row := ((false,true,0,1),(true,true,0,1))
/-- False marks the next witness block; true marks the delimiter. -/
def probe : Program :=
  [ ((false,true,1,0),(true,true,2,0)),
    ((false,false,3,0),(true,false,3,0)),
    ((false,false,4,0),(true,false,4,0)), dummy, dummy ]
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

attribute [local irreducible] Shared.Codes.FinitePrograms.run

theorem shift_from_state (c : Config) (q : Nat) (h : c.1 = q) :
    c = shiftConfig q (0,c.2) := by
  apply Prod.ext
  · change c.1 = q + 0
    rw [Nat.add_zero]
    exact h
  · rfl

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
    refine ⟨c,by simp only [totalCost,run_zero],by simpa using hq,?_⟩
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
      have hcfg := shift_from_state mid (stride zero one) hmidq
      refine ⟨shiftConfig (stride zero one) last,?_,?_,?_⟩
      · change run (phases zero one (n+1)) c
          (cost zero one b xs + totalCost zero one ps p (output zero one b xs)) = _
        rw [run_continue _ _ _ _ _ hmid]
        rw [hcfg]
        simpa only [phase,rest,stride,shiftStatus,phases] using hs
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


/-- The probe restores the head and branches on the current marker in two
charged transitions. -/
theorem probe_run (b : Bool) (xs L : List Bool) :
    run probe (0, (canonical L b xs).2) 2 =
      some (.inr (if b then 4 else 3, (canonical L b xs).2)) := by
  cases b <;> simp [probe, dummy, advance, step, canonical, tapeAt, moveTape]

set_option maxHeartbeats 1000000 in
/-- Every phase finishes and the marker probe also finishes. The outcome is
selected by the final source bit, and the tagged buffer is preserved. -/
theorem run_phases_and_probe (zero one : List Bool) (n : Nat) (remaining : List Bool)
    (hlen : remaining.length = n) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ d, run (phases zero one n) c (totalCost zero one remaining b xs + 2) = some (.inr d) ∧
      d.1 = n*stride zero one + (if (result zero one remaining b xs).1 then 4 else 3) ∧
      TapeRel d.2 (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 := by
  let r := result zero one remaining b xs
  let t := (canonical L r.1 r.2).2
  obtain ⟨mid,hm,hqmid,htmid⟩ := run_phases zero one n remaining hlen b xs L c hq ht
  have hp := probe_segment zero one n (0,t) (by simp [probe]) 2
  have hp0 : run probe (0,t) 2 = some (.inr (if r.1 then 4 else 3,t)) :=
    probe_run r.1 r.2 L
  rw [hp0] at hp
  have hr := run_related (phases zero one n) mid (shiftConfig (n*stride zero one) (0,t))
    (by simpa only [shiftConfig, Nat.add_zero] using hqmid) htmid 2
  rw [hp] at hr
  cases hs : run (phases zero one n) mid 2 with
  | none => rw [hs] at hr; exact False.elim hr
  | some v => cases v with
    | inl out => rw [hs] at hr; exact False.elim hr
    | inr d =>
      rw [hs] at hr
      have hd : d.1 = n*stride zero one + (if r.1 then 4 else 3) ∧ TapeRel d.2 t := hr
      refine ⟨d,?_,hd.1,hd.2⟩
      rw [run_continue _ _ _ _ _ hm]
      exact hs

/-- Nearest source cell at a reverse-witness block boundary. A true cell is
only the marked separator; encoded witness blocks start with false in this
orientation. -/
theorem witness_boundary_head (earlier L : List Bool) :
    (((BitstringEncoding.bitEncode earlier).reverse ++ true::L).head?).getD false = earlier.isEmpty := by
  induction earlier using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [Shared.ComplexityBridge.PairReverseWitness.encode_append,
      Shared.ComplexityBridge.PairReverseWitness.encode_cons]
    have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simp [hnil,List.reverse_append]

def witnessSource (earlier L : List Bool) : List Bool :=
  (BitstringEncoding.bitEncode earlier).reverse ++ true::L

def witnessTape (earlier xs L : List Bool) : Tape :=
  Shared.ComplexityBridge.PairReverseWitness.tapeLeft (witnessSource earlier L)
    (false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,false,false])

theorem witness_source_cons (earlier L : List Bool) :
    earlier.isEmpty::(witnessSource earlier L).tail = witnessSource earlier L := by
  have hn : witnessSource earlier L ≠ [] := by simp [witnessSource]
  have hh : (witnessSource earlier L).head?.getD false = earlier.isEmpty :=
    witness_boundary_head earlier L
  cases he : witnessSource earlier L with
  | nil => exact False.elim (hn he)
  | cons a as =>
    simp [he] at hh
    subst a
    rfl

def witnessPred (earlier : List Bool) (b : Bool) : List Bool := [b,true,earlier.isEmpty]

def witnessOutput (zero one earlier : List Bool) (b : Bool) (xs : List Bool) : List Bool :=
  (result zero one (witnessPred earlier b) false xs).2

def witnessCost (zero one earlier : List Bool) (b : Bool) (xs : List Bool) : Nat :=
  totalCost zero one (witnessPred earlier b) false xs + 2

/-- A complete encoded witness triple is positioned for three phase steps. -/
theorem witness_aligned (earlier : List Bool) (b : Bool) (xs L : List Bool) :
    (canonical (witnessPred earlier b ++ (witnessSource earlier L).tail) false xs).2 =
      witnessTape (earlier++[b]) xs L := by
  have hs := witness_source_cons earlier L
  have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
  simp [canonical,witnessTape,witnessSource,witnessPred,tapeAt,hnil,
    Shared.ComplexityBridge.PairReverseWitness.tapeLeft,
    Shared.ComplexityBridge.PairReverseWitness.encode_append,
    Shared.ComplexityBridge.PairReverseWitness.encode_cons,List.reverse_append,List.cons_append]
  simpa [witnessSource] using hs

/-- One complete witness triple is processed in the assembled table. The
probe stops on the marked separator or on the next triple; the exact cost
includes its two transitions. -/
theorem run_witness_block (zero one earlier : List Bool) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (witnessTape (earlier++[b]) xs L)) :
    ∃ d, run (phases zero one 3) c (witnessCost zero one earlier b xs) = some (.inr d) ∧
      d.1 = 3*stride zero one + (if earlier.isEmpty then 4 else 3) ∧
      TapeRel d.2 (witnessTape earlier (witnessOutput zero one earlier b xs) L) := by
  have ht' : TapeRel c.2 (canonical (witnessPred earlier b ++ (witnessSource earlier L).tail) false xs).2 := by
    rw [witness_aligned]
    exact ht
  obtain ⟨d,hd,hstate,htape⟩ := run_phases_and_probe zero one 3 (witnessPred earlier b)
    (by simp [witnessPred]) false xs (witnessSource earlier L).tail c hq ht'
  have hh : (result zero one (witnessPred earlier b) false xs).1 = earlier.isEmpty := by
    simp [result,witnessPred]
  have hc : (canonical (witnessSource earlier L).tail earlier.isEmpty
      (witnessOutput zero one earlier b xs)).2 =
      witnessTape earlier (witnessOutput zero one earlier b xs) L := by
    have hhead := witness_boundary_head earlier L
    change (witnessSource earlier L).head?.getD false = earlier.isEmpty at hhead
    simp [canonical,tapeAt,witnessTape,Shared.ComplexityBridge.PairReverseWitness.tapeLeft,hhead]
  refine ⟨d,hd,?_,?_⟩
  · simpa [hh] using hstate
  · change TapeRel d.2 (canonical (witnessSource earlier L).tail
        (result zero one (witnessPred earlier b) false xs).1
        (witnessOutput zero one earlier b xs)).2 at htape
    rw [hh,hc] at htape
    exact htape

/-- The phase table has an explicit finite state cost. -/
theorem three_phase_length (zero one : List Bool) :
    (phases zero one 3).length = 125 + 9*zero.length + 9*one.length := by
  rw [phases_length]
  have h := Shared.Codes.FiniteProgramPhaseProbe.stride_length zero one
  change stride zero one = _ at h
  rw [h]
  simp [probe]
  omega

/-- The exact three-phase cost is bounded in terms of the buffer and the
fixed output words, with both probe steps charged. -/
theorem witnessCost_bound (zero one earlier : List Bool) (b : Bool) (xs : List Bool) :
    witnessCost zero one earlier b xs ≤
      3*(16*(xs.length+3*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one)) +
        16*Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one+31)+2 := by
  have h := Shared.Codes.FiniteProgramTaggedLoop.totalCost_bound zero one (witnessPred earlier b) false xs
  simp only [witnessPred,List.length_cons,List.length_nil] at h
  unfold witnessCost witnessPred
  omega

namespace Fixtures
example : run probe (0,([],false,[false,false])) 2 = some (.inr (3,([],false,[false,false]))) := by simp [advance,step,probe,dummy,moveTape]
example : run probe (0,([],true,[false,false])) 2 = some (.inr (4,([],true,[false,false]))) := by simp [advance,step,probe,dummy,moveTape]
example : (((BitstringEncoding.bitEncode ([] : List Bool)).reverse ++ [true]).head?).getD false = true := by decide
example : (((BitstringEncoding.bitEncode [true]).reverse ++ [true]).head?).getD false = false := by decide
end Fixtures

end Shared.Codes.FiniteProgramWitnessPhases
