import Shared.PNP.Record285.GrammarBeepReturn
import Shared.PNP.Record285.GrammarAutoDispatch
import Shared.PNP.Record285.HalfNextDispatch

/-! The literal beep path when its following marker is initially zero. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
attribute [local irreducible] Record285.machine

theorem beep_route : route treeRoot beepCode = some beepState := by decide
theorem beep_safe : detectorRun 0 (scanWord beepCode) = some 0 := by decide

theorem beep_zero_row : Record285.machine.table.row beepState false =
    ⟨true,.right,IncrementPreparation.prep1,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem beep_preparation_rows : IncrementPreparation.Rows Record285.machine beepState := by
  let common := IncrementPreparation.literal_rows 0 (by decide)
  exact ⟨beep_zero_row,common.prepOneZero,common.prepTwoZero,common.prepTwoOne,
    common.breakZero,common.breakOne,common.dispatchZero,common.dispatchOne,
    common.dispatch1Zero,common.dispatch1One⟩

theorem root_to_beep_zero (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine beepCode.length (rootEntry beepCode head leftTail rightTail) =
      some ⟨beepState,head,bits (pathLeft beepCode) leftTail,false,rightTail⟩ := by
  have hs := route_scan beepCode treeRoot beepState beep_route
    (-(beepCode.length:Int)) false rootLeft []
  have hz : -(beepCode.length:Int)+(beepCode.length:Int) = 0 := by omega
  have hh := run_sound beepCode.length
    (rightWord treeRoot (-(beepCode.length:Int)) beepCode false rootLeft [])
    ⟨beepState,0,beepCode.reverse++rootLeft,false,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [rootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

/-- A zero marker is prepared and redispatched, in finite silent time, to the
previously proved true-marker beep root. No computation or event is hidden. -/
theorem zero_marker_to_marked_root (gap : Nat) (head : Int) (leftTail bank : Nat) :
    silent Record285.machine (2*gap+28)
      (rootEntry beepCode head leftTail (2*runPattern false gap true (2*bank))) =
      some (markedRootEntry beepCode head leftTail (2*runPattern true (gap+1) false bank)) := by
  let tail := 2*bank
  let shifted := pushBit (gap+1) true tail
  have hf := root_to_beep_zero head leftTail (2*runPattern false gap true tail)
  have hp := IncrementPreparation.prepare_to_dispatch Record285.machine beepState beep_preparation_rows
    gap head (bits (pathLeft beepCode) leftTail) tail
  have hr := literal_return_root beepCode beep_safe head leftTail shifted
  have heq : denote (rightWord treeRoot (-(beepCode.length:Int)) beepCode true rootLeft [false])
      head leftTail shifted =
      markedRootEntry beepCode head leftTail (2*runPattern true (gap+1) false bank) := by
    rw [root_word_tail beepCode true [false] head leftTail shifted]
    have hb : shifted = runPattern true (gap+1) false bank := by
      dsimp only [shifted,tail]
      exact IncrementReturn.push_run (gap+1) bank
    simp only [markedRootEntry,bits,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,hb]
  rw [heq] at hr
  let a := rootEntry beepCode head leftTail (2*runPattern false gap true tail)
  let b : PhysicalNumeric.Config 285 :=
    ⟨beepState,head,bits (pathLeft beepCode) leftTail,false,2*runPattern false gap true tail⟩
  let c := atLeftWord IncrementPreparation.dispatch0 (head-1) (bits (pathLeft beepCode) leftTail)
    (1+4*shifted)
  let d := markedRootEntry beepCode head leftTail (2*runPattern true (gap+1) false bank)
  have hmid := BootstrapChecker.silent_compose Record285.machine a b c beepCode.length (2*gap+5) hf hp
  have hall := BootstrapChecker.silent_compose Record285.machine a c d
    (beepCode.length+(2*gap+5)) (beepCode.length+17) hmid hr
  have htime : 2*gap+28 = (beepCode.length+(2*gap+5))+(beepCode.length+17) := by
    simp only [beepCode,List.length_cons,List.length_nil]
    omega
  simpa only [htime] using hall

/-- From a zero-marker beep root, the machine prepares the anchor, emits
exactly one marked transition, and returns to the root in finite time. -/
theorem zero_marker_beep_returns_root_physical (gap : Nat) (head : Int) (leftTail bank : Nat)
    (physical : Machines.Config 285)
    (hrel : Rel (rootEntry beepCode head leftTail (2*runPattern false gap true (2*bank))) physical) :
    let sys := EventSystem.mk physical Record285.machine.step
    let steps := 4*gap+60
    Rel (denote (rightWord treeRoot (-2) beepPrecode true rootLeft [false])
      (head-1) leftTail (runPattern false (gap+1) true (2*bank))) (sys.run steps) ∧
    (∀ t, t < steps → (sys.BeepAt t ↔ t = 2*gap+31)) ∧ 0 < steps := by
  dsimp only
  let sys := EventSystem.mk physical Record285.machine.step
  let start := 2*gap+28
  let duration := 2*gap+32
  have hp := silent_physical Record285.machine _ physical hrel start _
    (zero_marker_to_marked_root gap head leftTail bank)
  have hb := beep_returns_root_physical gap head leftTail bank (sys.run start) hp.1
  dsimp only at hb
  have hoff : (EventSystem.mk (sys.run start) sys.step).run duration = sys.run (start+duration) :=
    restarted_run_offset sys start duration
  rw [hoff] at hb
  have ht : start+duration = 4*gap+60 := by dsimp [start,duration]; omega
  rw [ht] at hb
  refine ⟨hb.1,?_,by omega⟩
  intro t hbound
  constructor
  · intro he
    by_cases hbefore : t < start
    · exact False.elim ((hp.2 t hbefore) he)
    · have hlocal := hb.2.1 (t-start) (by dsimp [start,duration] at *; omega)
      have hoff' := restarted_beep_offset sys start (t-start)
      have heq : start+(t-start) = t := by omega
      rw [heq] at hoff'
      have htime := hlocal.1 (hoff'.2 he)
      dsimp [start] at *
      omega
  · intro he
    have hlocal := hb.2.1 (t-start) (by dsimp [start,duration] at *; omega)
    have hoff' := restarted_beep_offset sys start (t-start)
    have heq : start+(t-start) = t := by dsimp [start] at *; omega
    rw [heq] at hoff'
    apply hoff'.1
    apply hlocal.2
    dsimp [start] at *
    omega

theorem bound_any_zero_marker_beep_returns_root_physical (code : List Bool)
    (hwalk : walk rootIndex code = some .beep) (gap : Nat) (head : Int)
    (leftTail bank : Nat) (physical : Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail (2*runPattern false gap true (2*bank))) physical) :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPath code = some (beepPrecode++[true]) ∧
    let sys := EventSystem.mk physical Record285.machine.step
    let steps := 4*gap+60
    Rel (denote (rightWord treeRoot (-2) beepPrecode true rootLeft [false])
      (head-1) leftTail (runPattern false (gap+1) true (2*bank))) (sys.run steps) ∧
    (∀ t, t < steps → (sys.BeepAt t ↔ t = 2*gap+31)) ∧ 0 < steps := by
  have hw := root_beep_word code hwalk
  change code = beepCode at hw
  subst code
  exact ⟨literal_typed_serialization,beep_return_rule,
    zero_marker_beep_returns_root_physical gap head leftTail bank physical hrel⟩

def beepDuration (marker : Bool) (gap : Nat) : Nat :=
  if marker then 2*gap+32 else 4*gap+60

def beepEventTime (marker : Bool) (gap : Nat) : Nat :=
  if marker then 3 else 2*gap+31

/-- Both marker cases complete with exactly one event. Each input layout is
stated explicitly; the true marker has an already prepared bank, while the
zero marker has a finite gap and anchor to prepare. -/
theorem beep_both_markers_physical (code : List Bool) (hwalk : walk rootIndex code = some .beep)
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hlayout : rightTail = if marker then 2*runPattern true (gap+1) false bank
      else 2*runPattern false gap true (2*bank))
    (physical : Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPath code = some (beepPrecode++[true]) ∧
    let sys := EventSystem.mk physical Record285.machine.step
    let steps := beepDuration marker gap
    Rel (denote (rightWord treeRoot (-2) beepPrecode true rootLeft [false])
      (head-1) leftTail (runPattern false (gap+1) true (2*bank))) (sys.run steps) ∧
    (∀ t, t < steps → (sys.BeepAt t ↔ t = beepEventTime marker gap)) ∧ 0 < steps := by
  cases marker with
  | false =>
    simp only [Bool.false_eq_true,if_false] at hlayout
    rw [hlayout] at hrel
    have h := bound_any_zero_marker_beep_returns_root_physical code hwalk gap head leftTail bank physical hrel
    simpa only [beepDuration,beepEventTime,Bool.false_eq_true,if_false] using h
  | true =>
    simp only [if_true] at hlayout
    rw [hlayout] at hrel
    have h := bound_any_beep_returns_root_physical code hwalk gap head leftTail bank physical hrel
    simpa only [beepDuration,beepEventTime,if_true] using h

/-- After its unique marked event, either beep layout is followed by a
positive, silent dispatcher segment on the actual complete returned tape. -/
theorem beep_then_dispatch (code : List Bool) (hwalk : walk rootIndex code = some .beep)
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hlayout : rightTail = if marker then 2*runPattern true (gap+1) false bank
      else 2*runPattern false gap true (2*bank))
    (physical : Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    let sys := EventSystem.mk physical Record285.machine.step
    let steps := beepDuration marker gap
    returnPath code = some (beepPrecode++[true]) ∧
    Rel (denote (rightWord treeRoot (-2) beepPrecode true rootLeft [false])
      (head-1) leftTail (runPattern false (gap+1) true (2*bank))) (sys.run steps) ∧
    Shared.PNP.Record285.HalfComplete.NextDispatch (sys.run steps) ∧
    (∀ t, t < steps → (sys.BeepAt t ↔ t = beepEventTime marker gap)) ∧ 0 < steps := by
  have h := beep_both_markers_physical code hwalk marker gap head leftTail rightTail bank hlayout physical hrel
  dsimp only at h ⊢
  have hn := Shared.PNP.Record285.HalfComplete.returned_root_dispatch beepPrecode (head-1) leftTail
    (runPattern false (gap+1) true (2*bank)) _ (by simpa [beepPrecode] using h.2.2.1)
  exact ⟨h.2.1,h.2.2.1,hn,h.2.2.2.1,h.2.2.2.2⟩

end Shared.PNP.Record285.Grammar
