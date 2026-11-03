import Shared.PNP.Record285.EncodedPairPhase
import Shared.Codes.FiniteProgramFirstEntryMany

/-! A fixed finite controller emits reverse-encoding triples for tagged
payload pairs. Each restart clears the source head for the next triple. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.EncodedPairLoop
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTaggedLoop (canonical output)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)

def base : Program := EncodedPairPhase.program FramePairProbe.dummy
def clearBranch (target : Nat) : Row × Row :=
  ((false,true,target,0),(false,true,target,0))
def program : Program := (base.set 94 (clearBranch 97)).set 95 (clearBranch 98) ++ [bridge 0,bridge 0]

theorem base_valid : valid base = true := EncodedPairPhase.program_valid _ (by decide) (by decide)
theorem base_length : base.length = 97 := by decide
theorem program_valid : valid program = true := by decide

theorem base_stop (q : Nat) (hq : q = 94 ∨ q = 95) (t : Tape) :
    step base (q,t) = some (.inl false) := by
  have h94 : base[94]? = some ((false,true,94,1),(true,true,94,1)) := by decide
  have h95 : base[95]? = some ((false,true,94,1),(true,true,94,1)) := by decide
  rcases hq with rfl | rfl <;> cases ht : t.2.1 <;> simp [step,h94,h95,ht]

theorem base_other (d : Config) (hd : d.1 < base.length) (h94 : d.1 ≠ 94) (h95 : d.1 ≠ 95) :
    step base d = step program d := by
  have hl : program[d.1]? = base[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm h94,Ne.symm h95]
  simp [step,hl]

theorem first_entry (c d : Config) (n : Nat) (hc : c.1 < base.length)
    (h : run base c n = some (.inr d)) : run program c n = some (.inr d) := by
  let stops : Set Nat := {94,95}
  apply Shared.Codes.FiniteProgramFirstEntry.first_entry_many base program c d n stops base_valid hc ?_ ?_ h
  · intro q hq
    have hq' : q = 94 ∨ q = 95 := by simpa [stops] using hq
    exact ⟨false,base_stop q hq'⟩
  · intro d hd hn
    have h94 : d.1 ≠ 94 := by intro hq; apply hn; simp [stops,hq]
    have h95 : d.1 ≠ 95 := by intro hq; apply hn; simp [stops,hq]
    exact base_other d hd h94 h95

theorem restart (bit head : Bool) (left right : List Bool) :
    run program ((if bit then 95 else 94),tapeAt left (head::false::right)) 2 =
      some (.inr (0,tapeAt left (false::false::right))) := by
  have h94 : program[94]? = some (clearBranch 97) := by simp [program,base_length]
  have h95 : program[95]? = some (clearBranch 98) := by simp [program,base_length]
  have h97 : program[97]? = some (bridge 0) := by simp [program,base_length]
  have h98 : program[98]? = some (bridge 0) := by simp [program,base_length]
  cases bit <;> cases head <;> simp [run,advance,step,h94,h95,h97,h98,clearBranch,bridge,tapeAt,moveTape]

/-- If another tagged bit remains, one physical pair/probe block and its
restart return to state zero, with the complete post-pair tape related. -/
theorem pair_continue (head bit nextBit : Bool) (xs tail : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (bit::true::nextBit::true::tail) head xs).2) :
    ∃ d, run program c (EncodedPairPhase.pairCost head bit xs+4+2) = some (.inr d) ∧
      d.1 = 0 ∧ TapeRel d.2 (canonical (nextBit::true::tail) false (EncodedPairPhase.pairOutput head bit xs)).2 := by
  let out := EncodedPairPhase.pairOutput head bit xs
  let ideal := (canonical (nextBit::true::tail) true out).2
  let cleared := (canonical (nextBit::true::tail) false out).2
  have hp := EncodedPairPhase.pair_then_bit FramePairProbe.dummy (by decide) (by decide)
    head bit nextBit xs tail c hq ht 0
  have hnext : 94+(if nextBit then 1 else 0) = (if nextBit then 95 else 94) := by
    cases nextBit <;> decide
  have hrel : StatusRel (run base c (EncodedPairPhase.pairCost head bit xs+4))
      (some (.inr ((if nextBit then 95 else 94),ideal))) := by
    change StatusRel (run base c (EncodedPairPhase.pairCost head bit xs+4+0))
      (shiftStatus 94 (run FramePairProbe.dummy ((if nextBit then 1 else 0),ideal) 0)) at hp
    simp only [Nat.add_zero,run_zero,shiftStatus,shiftConfig] at hp
    rw [hnext] at hp
    exact hp
  cases hr : run base c (EncodedPairPhase.pairCost head bit xs+4) with
  | none => rw [hr] at hrel; exact False.elim hrel
  | some v => cases v with
    | inl result => rw [hr] at hrel; exact False.elim hrel
    | inr mid =>
      rw [hr] at hrel
      have hm : mid.1 = (if nextBit then 95 else 94) ∧ TapeRel mid.2 ideal := hrel
      have hc : c.1 < base.length := by rw [hq,base_length]; decide
      have hp' := first_entry c mid _ hc hr
      have hrestart := restart nextBit true (nextBit::true::tail)
        (Shared.Codes.FiniteProgramBitShuttle.tagged out ++ [false,false,false])
      change run program ((if nextBit then 95 else 94),ideal) 2 = some (.inr (0,cleared)) at hrestart
      have hr' := run_related program mid ((if nextBit then 95 else 94),ideal) hm.1 hm.2 2
      rw [hrestart] at hr'
      cases hx : run program mid 2 with
      | none => rw [hx] at hr'; exact False.elim hr'
      | some x => cases x with
        | inl value => rw [hx] at hr'; exact False.elim hr'
        | inr d =>
          rw [hx] at hr'
          have hd : d.1 = 0 ∧ TapeRel d.2 cleared := hr'
          exact ⟨d,by rw [run_continue _ _ _ _ _ hp']; exact hx,hd.1,hd.2⟩

/-- At the final pair the physical controller reaches its distinct end row. -/
theorem pair_end (head bit : Bool) (xs tail : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (bit::true::false::false::tail) head xs).2) :
    ∃ d, run program c (EncodedPairPhase.pairCost head bit xs+4) = some (.inr d) ∧
      d.1 = 96 ∧ TapeRel d.2 (canonical (false::false::tail) true (EncodedPairPhase.pairOutput head bit xs)).2 := by
  let ideal := (canonical (false::false::tail) true (EncodedPairPhase.pairOutput head bit xs)).2
  have hp := EncodedPairPhase.pair_then_end FramePairProbe.dummy (by decide) (by decide)
    head bit xs tail c hq ht 0
  have hrel : StatusRel (run base c (EncodedPairPhase.pairCost head bit xs+4))
      (some (.inr (96,ideal))) := by
    change StatusRel (run base c (EncodedPairPhase.pairCost head bit xs+4+0))
      (shiftStatus 94 (run FramePairProbe.dummy (2,ideal) 0)) at hp
    simpa only [Nat.add_zero,run_zero,shiftStatus,shiftConfig,Nat.reduceAdd] using hp
  cases hr : run base c (EncodedPairPhase.pairCost head bit xs+4) with
  | none => rw [hr] at hrel; exact False.elim hrel
  | some v => cases v with
    | inl result => rw [hr] at hrel; exact False.elim hrel
    | inr d =>
      rw [hr] at hrel
      have hd : d.1 = 96 ∧ TapeRel d.2 ideal := hrel
      have hc : c.1 < base.length := by rw [hq,base_length]; decide
      exact ⟨d,first_entry c d _ hc hr,hd.1,hd.2⟩

def loopOutput : Bool → List Bool → List Bool → List Bool
  | _, xs, [] => xs
  | head, xs, bit::remaining =>
      loopOutput false (EncodedPairPhase.pairOutput head bit xs) remaining

def loopCost : Bool → List Bool → List Bool → Nat
  | _, _, [] => 0
  | head, xs, bit::remaining =>
      EncodedPairPhase.pairCost head bit xs+4+
        if remaining.isEmpty then 0 else
          2+loopCost false (EncodedPairPhase.pairOutput head bit xs) remaining

/-- One actual patched table processes all nonempty tagged-pair input,
restarting by itself on further bits and stopping on the blank sentinel. -/
theorem run_pairs (head : Bool) (xs todo tail : List Bool) (hne : todo ≠ []) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical (FrameBufferLoader.tagged todo ++ false::false::tail) head xs).2) :
    ∃ d, run program c (loopCost head xs todo) = some (.inr d) ∧ d.1 = 96 ∧
      TapeRel d.2 (canonical (false::false::tail) true (loopOutput head xs todo)).2 := by
  induction todo generalizing head xs c with
  | nil => contradiction
  | cons bit remaining ih =>
    cases remaining with
    | nil =>
      have ht' : TapeRel c.2 (canonical (bit::true::false::false::tail) head xs).2 := by
        simpa using ht
      obtain ⟨d,hd,hq',htape⟩ := pair_end head bit xs tail c hq ht'
      exact ⟨d,by simpa [loopCost] using hd,hq',by simpa [loopOutput] using htape⟩
    | cons nextBit remaining =>
      have ht' : TapeRel c.2 (canonical
          (bit::true::nextBit::true::(FrameBufferLoader.tagged remaining ++ false::false::tail)) head xs).2 := by
        simpa using ht
      obtain ⟨mid,hm,hq',htape⟩ := pair_continue head bit nextBit xs
        (FrameBufferLoader.tagged remaining ++ false::false::tail) c hq ht'
      have hm' : TapeRel mid.2 (canonical
          (FrameBufferLoader.tagged (nextBit::remaining) ++ false::false::tail)
          false (EncodedPairPhase.pairOutput head bit xs)).2 := by simpa using htape
      obtain ⟨last,hlast,hlastq,hlastt⟩ := ih false (EncodedPairPhase.pairOutput head bit xs)
        (by simp) mid hq' hm'
      refine ⟨last,?_,hlastq,?_⟩
      · change run program c (EncodedPairPhase.pairCost head bit xs+4+
          (2+loopCost false (EncodedPairPhase.pairOutput head bit xs) (nextBit::remaining))) = _
        rw [show EncodedPairPhase.pairCost head bit xs+4+
            (2+loopCost false (EncodedPairPhase.pairOutput head bit xs) (nextBit::remaining)) =
            (EncodedPairPhase.pairCost head bit xs+4+2)+
              loopCost false (EncodedPairPhase.pairOutput head bit xs) (nextBit::remaining) by omega,
          run_continue _ _ _ _ _ hm]
        exact hlast
      · simpa [loopOutput] using hlastt

theorem pair_output (head bit : Bool) (xs : List Bool) :
    EncodedPairPhase.pairOutput head bit xs = xs ++ [head,bit,true] :=
  EncodedPairPhase.pairOutput_eq head bit xs

theorem pair_cost (head bit : Bool) (xs : List Bool) :
    EncodedPairPhase.pairCost head bit xs = 32*xs.length+94 := by
  cases head <;> cases bit <;>
    simp [EncodedPairPhase.pairCost,Shared.Codes.FiniteProgramTaggedLoop.cost,output] <;> omega

def emitted : Bool → List Bool → List Bool
  | _, [] => []
  | head, bit::rest => head::bit::true::emitted false rest

/-- The completed loop's buffer contains exactly these physical source and
data bits, in order. The first head bit is explicit. -/
theorem loopOutput_eq (head : Bool) (xs todo : List Bool) :
    loopOutput head xs todo = xs ++ emitted head todo := by
  induction todo generalizing head xs with
  | nil => simp [loopOutput,emitted]
  | cons bit rest ih =>
    simp only [loopOutput,ih,pair_output,emitted]
    simp [List.append_assoc]

/-- A uniform quadratic bound covers all physical pair phases, probes and
restart bridges. The end case costs no restart. -/
theorem loopCost_bound (head : Bool) (xs todo : List Bool) :
    loopCost head xs todo ≤ todo.length*(32*xs.length+96*todo.length+100) := by
  induction todo generalizing head xs with
  | nil => simp [loopCost]
  | cons bit rest ih =>
    cases rest with
    | nil =>
      simp [loopCost,pair_cost]
    | cons nextBit rest =>
      have h := ih false (EncodedPairPhase.pairOutput head bit xs)
      have hout : (EncodedPairPhase.pairOutput head bit xs).length = xs.length+3 := by
        rw [pair_output]; simp
      rw [hout] at h
      change EncodedPairPhase.pairCost head bit xs+4+
          (2+loopCost false (EncodedPairPhase.pairOutput head bit xs) (nextBit::rest)) ≤
        (rest.length+2)*(32*xs.length+96*(rest.length+2)+100)
      rw [pair_cost]
      simp only [List.length_cons] at h
      nlinarith

end Shared.PNP.Record285.EncodedPairLoop
