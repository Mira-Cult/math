import Shared.PNP.Record285.HalfOne
import Shared.PNP.Record285.GrammarBeep
import Shared.PNP.Record285.HalfNextDispatch

/-! Increment from the true-marker, already-prepared physical layout. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.PreparedIncrement
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

/-- Generic prepared-bank cleanup to the root for a safe control word with
an earlier zero. Both full tape tails are explicit. -/
theorem break_to_root (code : List Bool) (gap : Nat)
    (hzero : false ∈ code) (hsafe : detectorRun 0 (scanWord code) = some 0)
    (head : Int) (leftTail bank : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    silent Record285.machine ((3*p.1+2*gap+9)+(precode.length+17))
      (atLeftWord IncrementReturn.breakState (head-1) (bits (pathLeft code) leftTail)
        (4*runPattern true (gap+1) false bank)) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let rightTail := runPattern false (p.1+gap+1) true (2*bank)
  have hz : false ∈ code.reverse := by simpa using hzero
  have hroot := IncrementCleanup.path_peel_preserves_root code hzero
  have hroot' : peel (pathLeft code) = (p.1,p.2++rootLeft) := by
    simpa only [rootLeft,List.append_assoc] using hroot
  have hprefix := peel_prefix_safe code hsafe hz
  have hleft := IncrementCleanup.path_peel_bits code leftTail
  rw [hroot'] at hleft
  have hcleanup := IncrementCleanup.literal_cleanup p.1 gap head (bits (p.2++rootLeft) leftTail) bank
  rw [← hleft] at hcleanup
  have hpref : pathLeft precode = p.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hword : 1+2*runPattern false (p.1+gap+2) true (2*bank) = 1+4*rightTail := by
    dsimp only [rightTail]
    rw [show p.1+gap+2 = (p.1+gap+1)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    omega
  have hr := literal_return_root precode hprefix (head-p.1-1) leftTail rightTail
  have hpos : (head-p.1-1)-1 = head-p.1-2 := by omega
  rw [hpref,hpos,← hword] at hr
  have hbreak : IncrementReturn.breakState = IncrementCleanup.lexical := rfl
  rw [hbreak,silent_add,hcleanup]
  simp only [Option.bind_some]
  exact hr

theorem root_dispatch_marked (code : List Bool) (i : Nat)
    (hwalk : walk rootIndex code = some (.inc i)) (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (markedRootEntry code head leftTail rightTail) =
      some ⟨IncrementPreparation.terminal i,head,bits (pathLeft code) leftTail,true,rightTail⟩ := by
  have hr := (producer_increment_route code i hwalk).2
  have hs := route_scan code treeRoot (IncrementPreparation.terminal i) hr
    (-(code.length:Int)) true rootLeft []
  have hz : -(code.length:Int)+(code.length:Int) = 0 := by omega
  have hh := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code true rootLeft [])
    ⟨IncrementPreparation.terminal i,0,code.reverse++rootLeft,true,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [markedRootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

/-- The literal marked terminal immediately enters the selected prepared
bank; the complete increment then reaches the ordinary cleanup state. -/
theorem terminal_marked_to_break (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (code : List Bool) (head : Int) (leftTail retained : Nat) :
    let selected := gap::(before++[target])
    let tail := suffixBits suffix retained
    let bank := IncrementSelector.blocksBits selected tail
    let steps := 1+2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    silent Record285.machine steps
      ⟨IncrementPreparation.terminal before.length,head,bits (pathLeft code) leftTail,true,2*bank⟩ =
      some (atLeftWord IncrementReturn.breakState (head-1) (bits (pathLeft code) leftTail)
        (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
          (IncrementSelector.blocksBits suffix retained))) := by
  dsimp only
  let selected := gap::(before++[target])
  let tail := suffixBits suffix retained
  let bank := IncrementSelector.blocksBits selected tail
  let far := bits (pathLeft code) leftTail
  have hlen : selected.length = before.length+2 := by simp [selected]
  have hb : selected.length ≤ 16 := by omega
  have hrow := (IncrementPreparation.terminal_rows before.length hindex).2
  have hfirst : silent Record285.machine 1
      ⟨IncrementPreparation.terminal before.length,head,far,true,2*bank⟩ =
      some ⟨IncrementSelector.literalState selected.length,head+1,2*far,false,bank⟩ := by
    rw [hlen]
    simp only [silent,PhysicalNumeric.step,hrow,Bool.false_eq_true,if_false,bitVal,if_false,
      Nat.add_zero,even_bit,even_tail]
  have hu := IncrementMeaning.literal_increment gap target before suffix hb (head+1) retained far
  rw [silent_add,hfirst]
  simp only [Option.bind_some]
  have hh : head+1-2 = head-1 := by omega
  simpa only [hh] using hu

/-- A true-marker increment starts from its already-prepared bank, completes
the update and lexical cleanup, then reaches the next root silently. -/
theorem root_marked_increment (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let selected := gap::(before++[target])
    let bank := IncrementSelector.blocksBits selected (suffixBits suffix retained)
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let rightTail := runPattern false (p.1+gap+1) true (2*updated)
    let middle := 1+2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    let steps := code.length+middle+(3*p.1+2*gap+9)+(precode.length+17)
    silent Record285.machine steps (markedRootEntry code head leftTail (2*bank)) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let selected := gap::(before++[target])
  let bank := IncrementSelector.blocksBits selected (suffixBits suffix retained)
  let updated := IncrementSelector.blocksBits (before++[target+1])
    (IncrementSelector.blocksBits suffix retained)
  let middle := 1+2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
  have hroute := producer_increment_route code before.length hwalk
  have hzero := DispatcherIncrement.route_has_zero code before.length hroute.2
  have hsafe := DispatcherInvariant.route_is_safe code before.length hroute.1 hroute.2
  have hd := root_dispatch_marked code before.length hwalk head leftTail (2*bank)
  have ht := terminal_marked_to_break gap target before suffix hroute.1 code head leftTail retained
  have hc := break_to_root code gap hzero hsafe head leftTail updated
  have hbank : IncrementSelector.blocksBits (gap::(before++[target+1]))
      (IncrementSelector.blocksBits suffix retained) = runPattern true (gap+1) false updated := by
    simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true,updated]
  rw [hbank] at ht
  rw [show code.length+middle+(3*p.1+2*gap+9)+(precode.length+17) =
      code.length+(middle+((3*p.1+2*gap+9)+(precode.length+17))) by omega,
    silent_add,hd]
  simp only [Option.bind_some]
  rw [silent_add,ht]
  simp only [Option.bind_some]
  exact hc

theorem root_marked_increment_physical (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (markedRootEntry code head leftTail
      (2*IncrementSelector.blocksBits (gap::(before++[target])) (suffixBits suffix retained))) physical) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let selected := gap::(before++[target])
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let rightTail := runPattern false (p.1+gap+1) true (2*updated)
    let middle := 1+2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    let steps := code.length+middle+(3*p.1+2*gap+9)+(precode.length+17)
    returnPath code = some (precode++[true]) ∧
    Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-1) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_marked_increment gap target before suffix code hwalk head leftTail retained)
  have hc := (increment_return_path code before.length hwalk).1
  exact ⟨hc,hp.1,hp.2,by omega⟩

/-- Both physical marker layouts perform the same increment and return to
the same complete root configuration; each layout is explicitly required. -/
theorem root_increment_both_markers (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (marker : Bool) (head : Int) (leftTail rightTail retained : Nat)
    (hlayout : rightTail = if marker then
      2*IncrementSelector.blocksBits (gap::(before++[target])) (suffixBits suffix retained)
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits suffix retained)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧
      let p := peel code.reverse
      let precode := p.2.reverse
      let updated := IncrementSelector.blocksBits (before++[target+1])
        (IncrementSelector.blocksBits suffix retained)
      returnPath code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail (runPattern false (p.1+gap+1) true (2*updated)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) := by
  cases marker with
  | false =>
    simp only [Bool.false_eq_true,if_false] at hlayout
    rw [hlayout] at hrel
    have hp := increment_returns_root_physical gap target before suffix code hwalk head leftTail retained physical hrel
    have hc := (increment_return_path code before.length hwalk).1
    exact ⟨_,hp.2.2,hc,hp.1,hp.2.1⟩
  | true =>
    simp only [if_true] at hlayout
    rw [hlayout] at hrel
    have hp := root_marked_increment_physical gap target before suffix code hwalk head leftTail retained physical hrel
    exact ⟨_,hp.2.2.2,hp.1,hp.2.1,hp.2.2.1⟩

/-- Either increment layout is followed by a second positive silent dispatch
from the actual resulting tape. -/
theorem increment_then_dispatch (gap target : Nat) (before suffix : List Nat)
    (code : List Bool) (hwalk : walk rootIndex code = some (.inc before.length))
    (marker : Bool) (head : Int) (leftTail rightTail retained : Nat)
    (hlayout : rightTail = if marker then
      2*IncrementSelector.blocksBits (gap::(before++[target])) (suffixBits suffix retained)
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits suffix retained)))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
      head leftTail rightTail) physical) :
    ∃ steps, 0 < steps ∧
      let p := peel code.reverse
      let precode := p.2.reverse
      let updated := IncrementSelector.blocksBits (before++[target+1])
        (IncrementSelector.blocksBits suffix retained)
      returnPath code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail (runPattern false (p.1+gap+1) true (2*updated)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      Shared.PNP.Record285.HalfComplete.NextDispatch
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) := by
  obtain ⟨steps,hpos,hpath,hresult,hquiet⟩ :=
    root_increment_both_markers gap target before suffix code hwalk marker head leftTail rightTail retained
      hlayout physical hrel
  have hn := Shared.PNP.Record285.HalfComplete.returned_root_dispatch _ _ _ _ _ hresult
  exact ⟨steps,hpos,hpath,hresult,hn,hquiet⟩

end Shared.PNP.Record285.PreparedIncrement
