import Shared.PNP.Record285.GrammarLeafDispatch

/-! After an increment's lexical carry, return silently to the literal
root dispatcher while preserving the full updated tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant
open Shared.PNP.Record285.SymbolicDispatch

theorem detector_next_mono (lo hi hi' : Nat) (b : Bool) (hle : lo ≤ hi)
    (h : detectorNext hi b = some hi') :
    ∃ lo', detectorNext lo b = some lo' ∧ lo' ≤ hi' := by
  cases b with
  | true =>
    simp only [detectorNext,if_true,Option.some.injEq] at h
    subst hi'
    exact ⟨0,by simp [detectorNext],by omega⟩
  | false =>
    simp only [detectorNext,Bool.false_eq_true,if_false] at h
    split at h
    next hb =>
      have hl : lo < 4 := by omega
      simp only [Option.some.injEq] at h
      subst hi'
      exact ⟨lo+1,by simp [detectorNext,hl],by omega⟩
    next hb => contradiction

theorem detector_run_mono (word : List Bool) (lo hi hi' : Nat) (hle : lo ≤ hi)
    (h : detectorRun hi word = some hi') :
    ∃ lo', detectorRun lo word = some lo' ∧ lo' ≤ hi' := by
  induction word generalizing lo hi with
  | nil =>
    simp only [detectorRun,Option.some.injEq] at h
    subst hi'
    exact ⟨lo,rfl,hle⟩
  | cons b bs ih =>
    simp only [detectorRun] at h
    cases hn : detectorNext hi b with
    | none => simp [hn] at h
    | some next =>
      simp only [hn,Option.bind_some] at h
      obtain ⟨lowNext,hlow,horder⟩ := detector_next_mono lo hi next b hle hn
      obtain ⟨result,hresult,hbound⟩ := ih lowNext next horder h
      exact ⟨result,by simp only [detectorRun,hlow,Option.bind_some]; exact hresult,hbound⟩

theorem detector_true_run (n : Nat) : detectorRun 0 (List.replicate n true) = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,detectorRun,detectorNext,if_true,Option.bind_some] using ih

/-- A skip-zero successor prefix from any grammar increment path remains safe
for the literal five-zero detector. -/
theorem successor_prefix_safe (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) :
    detectorRun 0 (scanWord ((peel code.reverse).2.reverse)) = some 0 := by
  obtain ⟨hi,hr⟩ := producer_increment_route code i hwalk
  have hs := route_is_safe code i hi hr
  have hz : false ∈ code.reverse := by
    simpa using DispatcherIncrement.route_has_zero code i hr
  have hd := peel_decomposition code.reverse hz
  have hs' : detectorRun 0
      ((List.replicate (peel code.reverse).1 true ++ false :: (peel code.reverse).2) ++
        [false,true,true]) = some 0 := by
    rw [← hd]
    exact hs
  rw [List.append_assoc,detector_append,detector_true_run] at hs'
  change detectorRun 1 ((peel code.reverse).2 ++ [false,true,true]) = some 0 at hs'
  have hm := detector_run_mono ((peel code.reverse).2++[false,true,true]) 0 1 0 (by omega) hs'
  obtain ⟨d,hd,hbound⟩ := hm
  have : d = 0 := by omega
  subst d
  simpa only [scanWord,List.reverse_reverse] using hd

/-- A safe control prefix returns to the root in a finite, silent symbolic run. -/
theorem symbolic_return_root (code : List Bool)
    (hsafe : detectorRun 0 (scanWord code) = some 0) :
    run (code.length+17) (pathStart code) =
      some (rightWord treeRoot (-(code.length:Int)) code true rootLeft [false]) := by
  let len := code.length
  have hs := detector_scan (scanWord code) 0 0 (by decide) hsafe (-1) false
    (List.replicate 5 false) [true,false]
  rw [scanWord_length,scanWord_reverse] at hs
  have hr := reset_root code (-1-(len+3:Nat))
  rw [show code.length+17 = (code.length+3)+14 by omega,run_add,pathStart_leftWord,hs]
  simp only [Option.bind_some]
  have hp : (-1:Int)-(len+3:Nat)+4 = -(len:Int) := by omega
  simpa only [hp,rootLeft] using hr

/-- Exact whole-tape literal execution of the root return. -/
theorem literal_return_root (code : List Bool)
    (hsafe : detectorRun 0 (scanWord code) = some 0)
    (origin : Int) (leftTail rightTail : Nat) :
    silent Record285.machine (code.length+17)
      (atLeftWord IncrementPreparation.dispatch0 (origin-1)
        (bits (pathLeft code) leftTail) (1+4*rightTail)) =
      some (denote (rightWord treeRoot (-(code.length:Int)) code true rootLeft [false])
        origin leftTail rightTail) := by
  have h := run_sound (code.length+17) (pathStart code)
    (rightWord treeRoot (-(code.length:Int)) code true rootLeft [false])
    (symbolic_return_root code hsafe) origin leftTail rightTail
  simpa only [path_start_denote] using h

/-- A grammar increment followed by its skip-zero carry returns to state 284.
The entire tape is retained and the complete segment is silent. -/
theorem increment_returns_root (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) :
    let n := (peel code.reverse).1
    let precode := (peel code.reverse).2.reverse
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let rightTail := runPattern false (n+gap+1) true (2*updated)
    let steps := code.length + ((2*gap+5) + pathCost code +
      2*(IncrementSelector.cost (gap::before++[target])+IncrementShift.cost suffix)) +
      (3*n+2*gap+9) + (precode.length+17)
    silent Record285.machine steps
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained)))) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-n-1) leftTail rightTail) := by
  dsimp only
  let n := (peel code.reverse).1
  let precode := (peel code.reverse).2.reverse
  let updated := IncrementSelector.blocksBits (before++[target+1])
    (IncrementSelector.blocksBits suffix retained)
  let tail := 2*runPattern false gap true
    (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))
  let middle := (2*gap+5) + pathCost code +
    2*(IncrementSelector.cost (gap::before++[target])+IncrementShift.cost suffix)
  have hstart := root_dispatch_increment code before.length hwalk head leftTail tail
  obtain ⟨hi,hr⟩ := producer_increment_route code before.length hwalk
  have hterminal := IncrementCleanup.terminal_through_cleanup gap target before suffix hi code
    (DispatcherInvariant.all_increment_routes_checked code before.length hi hr) head leftTail retained
  have hp := producer_increment_preserves_root code before.length hwalk
  have hprecode : pathLeft precode = (peel code.reverse).2 ++ [false,true,true] ++ List.replicate 6 false := by
    simp [precode,pathLeft,List.append_assoc]
  have hword : 1+2*runPattern false (n+gap+2) true (2*updated) =
      1+4*runPattern false (n+gap+1) true (2*updated) := by
    rw [show n+gap+2 = (n+gap+1)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false]
    omega
  have hreturn := literal_return_root precode
    (successor_prefix_safe code before.length hwalk) (head-n-1) leftTail
    (runPattern false (n+gap+1) true (2*updated))
  have hpos : (head-n-1)-1 = head-n-2 := by omega
  rw [hprecode,hpos,← hword] at hreturn
  rw [hp] at hterminal
  change silent Record285.machine (middle+(3*n+2*gap+9))
    ⟨IncrementPreparation.terminal before.length,head,bits (pathLeft code) leftTail,false,tail⟩ =
      some (atLeftWord IncrementPreparation.dispatch0 (head-n-2)
        (bits ((peel code.reverse).2 ++ [false,true,true] ++ List.replicate 6 false) leftTail)
        (1+2*runPattern false (n+gap+2) true (2*updated))) at hterminal
  change silent Record285.machine
    (code.length+middle+(3*n+2*gap+9)+(precode.length+17))
    (rootEntry code head leftTail tail) = _
  rw [show code.length+middle+(3*n+2*gap+9)+(precode.length+17) =
      code.length+(middle+(3*n+2*gap+9))+(precode.length+17) by omega,
    silent_add,silent_add,hstart]
  simp only [Option.bind_some]
  rw [hterminal]
  simp only [Option.bind_some]
  exact hreturn

/-- The root-to-root segment runs for a positive finite number of physical
steps, preserves the represented entire tape, and emits no marked event. -/
theorem increment_returns_root_physical (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained)))) physical) :
    let n := (peel code.reverse).1
    let precode := (peel code.reverse).2.reverse
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let rightTail := runPattern false (n+gap+1) true (2*updated)
    let steps := code.length + ((2*gap+5) + pathCost code +
      2*(IncrementSelector.cost (gap::before++[target])+IncrementShift.cost suffix)) +
      (3*n+2*gap+9) + (precode.length+17)
    Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-n-1) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  dsimp only
  have h := increment_returns_root gap target before suffix code hwalk head leftTail retained
  have hp := silent_physical Record285.machine _ physical hrel _ _ h
  refine ⟨hp.1,hp.2,?_⟩
  omega

end Shared.PNP.Record285.Grammar
