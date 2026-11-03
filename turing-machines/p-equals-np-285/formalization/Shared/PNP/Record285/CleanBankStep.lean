import Shared.PNP.Record285.CleanBankInitialization

/-! One interface for positive, event-accounted instruction segments on
blank-terminated banks. `Ready` is an explicit operation-layout obligation;
it is not derived from source reachability. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.CleanBank
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- Each constructor exposes the complete starting tape and the exact bank
layout required by the corresponding already-proved physical action. -/
inductive Ready : Edge → List Nat → Shared.Beeping.Machines.Config 285 → Prop
  | inc (gap target : Nat) (before fields : List Nat) (code : List Bool)
      (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
      (hwalk : walk rootIndex code = some (.inc before.length))
      (hlayout : rightTail = if marker then
        2*IncrementSelector.blocksBits (gap::(before++[target])) (suffixBits fields 0)
        else 2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
      (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        head leftTail rightTail) physical) :
      Ready (.inc before.length) (before++[target]++fields) physical
  | dec (gap target : Nat) (before fields : List Nat) (code : List Bool)
      (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
      (hwalk : walk rootIndex code = some (.dec before.length))
      (hlayout : rightTail = if marker then
        2*pushBit (gap+1) true (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0))
        else 2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
      (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        head leftTail rightTail) physical) :
      Ready (.dec before.length) (before++[target]++fields) physical
  | half (gap target : Nat) (before fields : List Nat) (code : List Bool)
      (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
      (hwalk : walk rootIndex code = some (.half before.length))
      (hlayout : rightTail = if marker then
        2*pushBit (gap+1) true (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0))
        else 2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
      (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        head leftTail rightTail) physical) :
      Ready (.half before.length) (before++[target]++fields) physical
  | beep (gap : Nat) (fields : List Nat) (code : List Bool)
      (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
      (hwalk : walk rootIndex code = some .beep)
      (hlayout : rightTail = if marker then
        2*runPattern true (gap+1) false (IncrementSelector.blocksBits fields 0)
        else 2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
      (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        head leftTail rightTail) physical) : Ready .beep fields physical
  | brk (gap i : Nat) (fields : List Nat) (code : List Bool)
      (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
      (hwalk : walk rootIndex code = some (.brk i))
      (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
      (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        head leftTail rightTail) physical) : Ready (.brk i) fields physical
  | cont (gap i : Nat) (fields : List Nat) (code : List Bool)
      (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
      (hwalk : walk rootIndex code = some (.cont i))
      (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
      (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        head leftTail rightTail) physical) : Ready (.cont i) fields physical

/-- Bank effect of one instruction, independent of physical time. -/
inductive Update : Edge → List Nat → List Nat → Prop
  | inc (before fields : List Nat) (target : Nat) :
      Update (.inc before.length) (before++[target]++fields) (before++[target+1]++fields)
  | dec (before fields : List Nat) (target : Nat) :
      Update (.dec before.length) (before++[target]++fields) (decrementFields before fields target)
  | half (before fields newFields : List Nat) (target : Nat)
      (h : HalfFields before fields target newFields) :
      Update (.half before.length) (before++[target]++fields) newFields
  | beep (fields : List Nat) : Update .beep fields fields
  | brk (i : Nat) (fields : List Nat) : Update (.brk i) fields fields
  | cont (i : Nat) (fields : List Nat) : Update (.cont i) fields fields

/-- A successful finite action has exactly one event precisely for beep. -/
def Events (e : Edge) (physical : Shared.Beeping.Machines.Config 285) (steps : Nat) : Prop :=
  let sys := Shared.Beeping.EventSystem.mk physical Record285.machine.step
  if e = .beep then ∃ j, j < steps ∧ ∀ t, t < steps → (sys.BeepAt t ↔ t = j)
  else ∀ t, t < steps → ¬ sys.BeepAt t

/-- Every enabled instruction makes finite positive progress, performs its
specified bank update, returns to a clean root and accounts for all events.
The next dispatch is available from that exact returned full tape. -/
theorem ready_step (e : Edge) (fields : List Nat) (physical : Shared.Beeping.Machines.Config 285)
    (ready : Ready e fields physical) :
    ∃ steps nextFields, 0 < steps ∧ Update e fields nextFields ∧
      Root nextFields ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      HalfComplete.NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      Events e physical steps := by
  cases ready with
  | inc gap target before suffix code marker head leftTail rightTail physical hwalk hlayout hrel =>
    obtain ⟨steps,hpos,hroot,hquiet⟩ :=
      increment_preserves gap target before suffix code hwalk marker head leftTail rightTail hlayout physical hrel
    exact ⟨steps,_,hpos,Update.inc before suffix target,hroot,root_next_dispatch _ _ hroot,by simpa [Events] using hquiet⟩
  | dec gap target before suffix code marker head leftTail rightTail physical hwalk hlayout hrel =>
    obtain ⟨steps,hpos,hroot,hquiet⟩ :=
      decrement_preserves gap target before suffix code hwalk marker head leftTail rightTail hlayout physical hrel
    exact ⟨steps,_,hpos,Update.dec before suffix target,hroot,root_next_dispatch _ _ hroot,by simpa [Events] using hquiet⟩
  | half gap target before suffix code marker head leftTail rightTail physical hwalk hlayout hrel =>
    obtain ⟨steps,next,hpos,hupdate,hroot,hquiet⟩ :=
      half_preserves gap target before suffix code hwalk marker head leftTail rightTail hlayout physical hrel
    exact ⟨steps,next,hpos,Update.half before suffix next target hupdate,hroot,root_next_dispatch _ _ hroot,
      by simpa [Events] using hquiet⟩
  | beep gap suffix code marker head leftTail rightTail physical hwalk hlayout hrel =>
    have h := beep_preserves gap fields code hwalk marker head leftTail rightTail hlayout physical hrel
    dsimp only at h
    have hevent : beepEventTime marker gap < beepDuration marker gap := by
      cases marker <;> simp [beepEventTime,beepDuration] <;> omega
    exact ⟨_,fields,h.1,Update.beep fields,h.2.1,root_next_dispatch _ _ h.2.1,
      by simpa [Events] using ⟨beepEventTime marker gap,hevent,h.2.2⟩⟩
  | brk gap i fields code marker head leftTail rightTail physical hwalk hanchor hrel =>
    obtain ⟨steps,hpos,hroot,hquiet⟩ :=
      break_preserves gap i fields code hwalk marker head leftTail rightTail hanchor physical hrel
    exact ⟨steps,fields,hpos,Update.brk i fields,hroot,root_next_dispatch _ _ hroot,by simpa [Events] using hquiet⟩
  | cont gap i fields code marker head leftTail rightTail physical hwalk hanchor hrel =>
    obtain ⟨steps,hpos,hroot,hquiet⟩ :=
      continue_preserves gap i fields code hwalk marker head leftTail rightTail hanchor physical hrel
    exact ⟨steps,fields,hpos,Update.cont i fields,hroot,root_next_dispatch _ _ hroot,by simpa [Events] using hquiet⟩

end Shared.PNP.Record285.CleanBank
