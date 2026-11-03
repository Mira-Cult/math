import Shared.PNP.Record285.PreparedHalf
import Shared.PNP.Record285.ControlNextDispatch
import Shared.PNP.Record285.BeepZeroMarker

/-! A blank-terminated bank invariant at literal dispatcher roots. The
operation-specific preconditions still have to be established for the
source-reachable control word. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.CleanBank
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- Every bank field is explicit; all cells beyond the last field are blank.
The existential control prefix and gap are still recorded in the full tape. -/
def Root (fields : List Nat) (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ word marker origin leftTail gap,
    Rel (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false gap true (2*IncrementSelector.blocksBits fields 0))) physical

/-- The suffix format with a blank retained tail is exactly a finite bank. -/
theorem suffix_blank (fields : List Nat) :
    suffixBits fields 0 = IncrementSelector.blocksBits fields 0 := by
  simpa using IncrementMeaning.suffix_bits fields 0

/-- The next dispatcher segment exists on the actual complete tape at any
clean bank root. Its destination need not satisfy an operation premise. -/
theorem root_next_dispatch (fields : List Nat) (physical : Shared.Beeping.Machines.Config 285)
    (h : Root fields physical) : HalfComplete.NextDispatch physical := by
  obtain ⟨word,marker,origin,leftTail,gap,hroot⟩ := h
  let suffix := runPattern false gap true (2*IncrementSelector.blocksBits fields 0)
  have hh : origin-word.length+word.length = origin := by omega
  have hd := root_word_dispatch word marker (origin-word.length) [false] leftTail suffix physical (by
    rw [hh]
    exact hroot)
  obtain ⟨e,len,pre,bit,row,hpos,hbound,hleaf,_,hexpected,hend,hquiet⟩ := hd
  exact ⟨len,e,pre,bit,row,_,_,_,_,hpos,hbound,hleaf,hexpected,hend,hquiet⟩

theorem increment_preserves (gap target : Nat) (before fields : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hlayout : rightTail = if marker then
      2*IncrementSelector.blocksBits (gap::(before++[target])) (suffixBits fields 0)
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧ Root (before++[target+1]++fields)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,_,hroot,hquiet⟩ := PreparedIncrement.root_increment_both_markers
    gap target before fields code hwalk marker head leftTail rightTail 0 hlayout physical hrel
  refine ⟨steps,hpos,?_,hquiet⟩
  refine ⟨(peel code.reverse).2.reverse,true,head-(peel code.reverse).1-1,leftTail,
    (peel code.reverse).1+gap+1,?_⟩
  simpa only [IncrementMeaning.blocks_append] using hroot

/-- The even/odd decrement branch records the finite inserted zero field. -/
def decrementFields (before fields : List Nat) : Nat → List Nat
  | 0 => before++[0]++fields
  | k+1 => before++[k]++fields++[0]

theorem decrement_preserves (gap target : Nat) (before fields : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.dec before.length))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hlayout : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧ Root (decrementFields before fields target)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨_,steps,hpos,hroot,hquiet⟩ := PreparedDecrement.decrement_both_markers code gap target
    before fields hwalk marker head leftTail rightTail 0 hlayout physical hrel
  refine ⟨steps,hpos,?_,hquiet⟩
  cases target with
  | zero =>
    refine ⟨(peel (peel code.reverse).2).2.reverse,true,
      head-(peel code.reverse).1-(peel (peel code.reverse).2).1-2,leftTail,
      (peel code.reverse).1+(peel (peel code.reverse).2).1+gap+2,?_⟩
    simpa only [DecrementComplete.resultConfig,decrementFields,suffix_blank,
      IncrementMeaning.blocks_append] using hroot
  | succ k =>
    refine ⟨(peel code.reverse).2.reverse,true,head-(peel code.reverse).1-1,leftTail,
      (peel code.reverse).1+gap+1,?_⟩
    simpa only [DecrementComplete.resultConfig,decrementFields] using hroot

/-- The exact finite bank yielded by each native-half parity case. -/
inductive HalfFields (before fields : List Nat) : Nat → List Nat → Prop
  | zero : HalfFields before fields 0 (before++[0]++fields)
  | one : HalfFields before fields 1 (before++[0]++fields++[0])
  | even (n : Nat) : HalfFields before fields (2*n+2)
      (before++[n+1]++(fields++List.replicate n 0)++[0])
  | odd (n : Nat) : HalfFields before fields (2*n+3)
      (before++[n+1]++(fields++List.replicate n 0)++[0,0])

/-- When all cells after the finite bank are blank, the half-operation
reserve is available for every target without a separate size premise. -/
theorem half_preserves (gap target : Nat) (before fields : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.half before.length))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hlayout : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps newFields, 0 < steps ∧ HalfFields before fields target newFields ∧
      Root newFields ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  have hlayout' : rightTail = if marker then
      2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields (2^(target/2)*0)))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields (2^(target/2)*0))) := by
    simpa only [Nat.mul_zero] using hlayout
  obtain ⟨steps,hpos,hresult,hquiet⟩ := PreparedHalf.half_both_markers code gap target before fields
    hwalk marker head leftTail rightTail 0 hlayout' physical hrel
  rcases hresult with h | h | h | h
  · rcases h with ⟨rfl,_,hr⟩
    refine ⟨steps,_,hpos,HalfFields.zero,?_,hquiet⟩
    refine ⟨(peel (peel code.reverse).2).2.reverse,true,
      head-(peel code.reverse).1-(peel (peel code.reverse).2).1-2,leftTail,
      (peel code.reverse).1+(peel (peel code.reverse).2).1+gap+2,?_⟩
    simpa only [HalfComplete.evenConfig,suffix_blank,IncrementMeaning.blocks_append] using hr
  · rcases h with ⟨rfl,_,hr⟩
    refine ⟨steps,_,hpos,HalfFields.one,?_,hquiet⟩
    exact ⟨(peel code.reverse).2.reverse,true,head-(peel code.reverse).1-1,leftTail,
      (peel code.reverse).1+gap+1,hr⟩
  · rcases h with ⟨n,rfl,_,hr⟩
    refine ⟨steps,_,hpos,HalfFields.even n,?_,hquiet⟩
    refine ⟨(peel (peel code.reverse).2).2.reverse,true,
      head-(peel code.reverse).1-(peel (peel code.reverse).2).1-2,leftTail,
      (peel code.reverse).1+(peel (peel code.reverse).2).1+gap+2,?_⟩
    simpa only [HalfComplete.evenConfig,Nat.mul_zero] using hr
  · rcases h with ⟨n,rfl,_,hr⟩
    refine ⟨steps,_,hpos,HalfFields.odd n,?_,hquiet⟩
    exact ⟨(peel code.reverse).2.reverse,true,head-(peel code.reverse).1-1,leftTail,
      (peel code.reverse).1+gap+1,hr⟩

/-- Beeping leaves a blank-terminated bank untouched and emits exactly once. -/
theorem beep_preserves (gap : Nat) (fields : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some .beep)
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hlayout : rightTail = if marker then
      2*runPattern true (gap+1) false (IncrementSelector.blocksBits fields 0)
      else 2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    let sys := Shared.Beeping.EventSystem.mk physical Record285.machine.step
    let steps := beepDuration marker gap
    0 < steps ∧ Root fields (sys.run steps) ∧
      ∀ t, t < steps → (sys.BeepAt t ↔ t = beepEventTime marker gap) := by
  have h := beep_both_markers_physical code hwalk marker gap head leftTail rightTail
    (IncrementSelector.blocksBits fields 0) hlayout physical hrel
  dsimp only at h ⊢
  exact ⟨h.2.2.2.2,⟨beepPrecode,true,head-1,leftTail,gap+1,by simpa [beepPrecode] using h.2.2.1⟩,
    h.2.2.2.1⟩

/-- Every break preserves a blank-terminated bank when the stated anchor
is present after its control path. -/
theorem break_preserves (gap i : Nat) (fields : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.brk i))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hanchor : RelativeTape.bitVal marker+2*rightTail =
      runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧ Root fields
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,hresult,hquiet⟩ := ControlBreak.root_break_complete code i hwalk marker gap head
    leftTail rightTail (IncrementSelector.blocksBits fields 0) hanchor physical hrel
  obtain ⟨pre,_,hresult⟩ := hresult
  refine ⟨steps,hpos,?_,hquiet⟩
  cases i with
  | zero =>
    exact ⟨(peel pre.reverse).2.reverse,true,head-2-(peel pre.reverse).1,leftTail,
      (peel pre.reverse).1+gap,hresult.2⟩
  | succ i =>
    cases i with
    | zero =>
      exact ⟨(peel (peel pre.reverse).2).2.reverse,true,
        head-2-(peel pre.reverse).1-1-(peel (peel pre.reverse).2).1,leftTail,
        (peel (peel pre.reverse).2).1+((peel pre.reverse).1+gap+1),hresult.2⟩
    | succ i =>
      cases i with
      | zero =>
        exact ⟨(peel (peel (peel pre.reverse).2).2).2.reverse,true,
          head-2-(peel pre.reverse).1-1-(peel (peel pre.reverse).2).1-1-
            (peel (peel (peel pre.reverse).2).2).1,leftTail,
          (peel (peel (peel pre.reverse).2).2).1+
            ((peel (peel pre.reverse).2).1+((peel pre.reverse).1+gap+1)+1),hresult.2⟩
      | succ i => contradiction

theorem push_zeros_gap (n gap tail : Nat) :
    pushBit n false (runPattern false gap true tail) = runPattern false (n+gap) true tail := by
  induction n with
  | zero => simp [pushBit]
  | succ n ih =>
    rw [pushBit, pushBit_affine]
    simp only [RelativeTape.bitVal,Bool.false_eq_true,if_false,Nat.add_zero,ih]
    have he : n+1+gap = (n+gap)+1 := by omega
    rw [he,runPattern]
    simp only [RelativeTape.bitVal,Bool.false_eq_true,if_false,Nat.zero_add]

/-- A continuation preserves the same clean bank when the following tape
contains the stated anchor. This condition is separate from its original
arbitrary-tape execution theorem. -/
theorem continue_preserves (gap i : Nat) (fields : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.cont i))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat)
    (hanchor : RelativeTape.bitVal marker+2*rightTail =
      runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧ Root fields
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,hresult,hquiet⟩ := ControlContinue.root_continue_complete code i hwalk marker head
    leftTail rightTail physical hrel
  obtain ⟨pre,_,hresult⟩ := hresult
  refine ⟨steps,hpos,?_,hquiet⟩
  cases i with
  | zero => contradiction
  | succ i =>
    cases i with
    | zero =>
      dsimp only at hresult
      refine ⟨(ControlContinue.peelZeros pre.reverse).2.reverse,true,
        head-2-(ControlContinue.peelZeros pre.reverse).1,leftTail,
        (ControlContinue.peelZeros pre.reverse).1+gap,?_⟩
      rw [hanchor,push_zeros_gap] at hresult
      exact hresult.2
    | succ i =>
      cases i with
      | zero =>
        dsimp only at hresult
        let p := ControlContinue.peelZeros pre.reverse
        let q := ControlContinue.peelZeros p.2
        refine ⟨q.2.reverse,true,head-2-p.1-1-q.1,leftTail,q.1+(p.1+gap+1),?_⟩
        rw [hanchor,push_zeros_gap] at hresult
        have hh : 2*runPattern false (p.1+gap) true (2*IncrementSelector.blocksBits fields 0) =
            runPattern false (p.1+gap+1) true (2*IncrementSelector.blocksBits fields 0) := by
          simp only [runPattern,RelativeTape.bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
        rw [hh,push_zeros_gap] at hresult
        exact hresult.2
      | succ i => contradiction

end Shared.PNP.Record285.CleanBank
