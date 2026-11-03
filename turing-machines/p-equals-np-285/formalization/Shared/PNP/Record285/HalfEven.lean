import Shared.PNP.Record285.HalfOne
import Shared.PNP.Record285.DecrementZeroRoot

/-! Native-half even exits and their one-level control return. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfEven
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.DecrementNonzeroScan (scannedLeft scanCost)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.SymbolicDispatch (bits pathLeft pathCost)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

theorem true_tail_no_half (n i : Nat) :
    walk 159 (List.replicate n true) ≠ some (.half i) := by
  have hchain (rest : List Bool) :
      walk 159 ([true,true,true,true,true,true,true]++rest) =
        if rest.isEmpty then some (.inc 6) else none := by
    cases rest <;> simp [walk,nodeEdge,nodes_fast,fastNodes]
  by_cases hsmall : n < 7
  · have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [walk,nodeEdge,nodes_fast,fastNodes,List.replicate]
  · have hn : n = 7+(n-7) := by omega
    rw [hn,replicate_add]
    change walk 159 ([true,true,true,true,true,true,true]++List.replicate (n-7) true) ≠ _
    rw [hchain]
    split <;> simp

theorem half_two_zeros (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) :
    ∃ pre mid post, code = pre++[false]++mid++[false]++post := by
  cases code with
  | nil => simp [walk] at hwalk
  | cons a as =>
    cases a with
    | false => cases as <;> simp [walk,root_false_edge] at hwalk
    | true =>
      cases as with
      | nil => simp [walk,root_true_edge] at hwalk
      | cons b bs =>
        cases b with
        | true => cases bs <;> simp [walk,root_true_edge,next_true_edge] at hwalk
        | false =>
          cases bs with
          | nil => simp [walk,root_true_edge,next_false_edge] at hwalk
          | cons c cs =>
            cases c with
            | false => exact ⟨[true],[],cs,by simp⟩
            | true =>
              have htail : walk 159 cs = some (.half i) := by
                simpa only [walk,root_true_edge,next_false_edge,beep_true_edge] using hwalk
              have hz : false ∈ cs := by
                by_cases hn : false ∈ cs
                · exact hn
                · have ht := all_true_replicate cs hn
                  rw [ht] at htail
                  exact False.elim ((true_tail_no_half cs.length i) htail)
              obtain ⟨pre,post,h⟩ := false_split cs hz
              refine ⟨[true],true::pre,post,?_⟩
              simp [h,List.append_assoc]

theorem half_reverse_zeros (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) :
    false ∈ code.reverse ∧ false ∈ (peel code.reverse).2 := by
  obtain ⟨pre,mid,post,hcode⟩ := half_two_zeros code i hwalk
  have hrev : code.reverse = post.reverse++[false]++mid.reverse++[false]++pre.reverse := by
    simp [hcode,List.reverse_append,List.append_assoc]
  rw [hrev]
  exact ⟨by simp,peel_tail_zero_of_two post.reverse mid.reverse pre.reverse⟩

theorem half_control_preserves_root (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) :
    let p := peel code.reverse
    let q := peel p.2
    peel (pathLeft code) = (p.1,p.2++rootLeft) ∧
    peel (peel (pathLeft code)).2 = (q.1,q.2++rootLeft) ∧
    returnPathSkipOne code = some (q.2.reverse++[true]) ∧
    detectorRun 0 (scanWord q.2.reverse) = some 0 := by
  obtain ⟨hz,ht⟩ := half_reverse_zeros code i hwalk
  have hzcode : false ∈ code := by simpa using hz
  have hp := IncrementCleanup.path_peel_preserves_root code hzcode
  have hp' : peel (pathLeft code) =
      ((peel code.reverse).1,(peel code.reverse).2++rootLeft) := by
    simpa only [rootLeft,List.append_assoc] using hp
  have hq := IncrementCleanup.peel_append (peel code.reverse).2 rootLeft ht
  have hq' : peel (peel (pathLeft code)).2 =
      ((peel (peel code.reverse).2).1,(peel (peel code.reverse).2).2++rootLeft) := by
    rw [hp']
    exact hq
  have hr := return_after_one_skip code.reverse hz ht
  obtain ⟨_,_,hsafe⟩ := producer_half_safe code i hwalk
  have hs1 := peel_prefix_safe code hsafe hz
  have hz1 : false ∈ ((peel code.reverse).2.reverse).reverse := by simpa using ht
  have hs2 := peel_prefix_safe (peel code.reverse).2.reverse hs1 hz1
  simp only [List.reverse_reverse] at hs2
  exact ⟨hp',hq',hr,hs2⟩

theorem initial_zero : Record285.machine.table.row (⟨68,by decide⟩ : Fin 285) false =
    ⟨false,.left,DecrementZero.scan,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem enter_zero (M : Machine 285) (begin initial qscan : Fin 285)
    (h1 : M.table.row begin true = ⟨true,.right,initial,false⟩)
    (h2 : M.table.row initial false = ⟨false,.left,qscan,false⟩)
    (head : Int) (left tail : Nat) :
    silent M 2 ⟨begin,head,left,true,runPattern true 0 false tail⟩ =
      some (atLeftWord qscan head (1+2*left) (2*tail)) := by
  simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,
    silent,PhysicalNumeric.step,h1,h2,even_bit,even_tail,atLeftWord,odd_bit,odd_tail,if_true]
  rw [show 2*left+1 = 1+2*left by omega,odd_bit,odd_tail]
  have hh : head+1-1 = head := by omega
  simp only [hh,Nat.add_zero]

/-- The zero operand reaches the one-level break with its bank unchanged. -/
theorem target_zero_to_break (gap : Nat) (before fields : List Nat)
    (head : Int) (far retained : Nat) :
    let left := DecrementSelector.leftAfter (gap::before) (2*far)
    let steps := 2+(1+completeCost (0::foldRuns before []) gap)
    silent Record285.machine steps
      ⟨HalfSelector.state 0,head+1+IncrementSelector.cost (gap::before),left,true,
        runPattern true 0 false (suffixBits fields retained)⟩ =
      some (atLeftWord DecrementZero.breakOne (head-1) far
        (4*IncrementSelector.blocksBits (gap::(before++[0])) (suffixBits fields retained))) := by
  dsimp only
  let left := DecrementSelector.leftAfter (gap::before) (2*far)
  let targetHead := head+1+IncrementSelector.cost (gap::before)
  let suffix := suffixBits fields retained
  have he := enter_zero Record285.machine (HalfSelector.state 0) ⟨68,by decide⟩ DecrementZero.scan
    HalfCycle.half_begin_one initial_zero targetHead left suffix
  have hl := DecrementZeroExact.return_layout_exact gap before far
  have hs := IncrementMeaning.scan_leading Record285.machine DecrementZero.scan DecrementZero.check
    DecrementZero.breakOne DecrementZero.literal_scan_rows (0::foldRuns before []) gap targetHead far (2*suffix)
  rw [← hl,show 2*(2*suffix)+1 = 4*suffix+1 by omega,
    DecrementZeroExact.return_output_exact gap before suffix] at hs
  have hc := DecrementZeroExact.return_cost_exact gap before
  have hh : targetHead-(1+(completeCost (0::foldRuns before []) gap:Int)) = head-1 := by
    dsimp only [targetHead]
    omega
  rw [hh] at hs
  rw [silent_add,he]
  simp only [Option.bind_some]
  exact hs

/-- A half path's one-level break completes cleanup and returns to the root,
with both peeled control boundaries and the full bank preserved. -/
theorem break_one_to_root (code : List Bool) (gap i : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail bank : Nat) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let steps := (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    silent Record285.machine steps
      (atLeftWord DecrementZero.breakOne (head-1) (bits (pathLeft code) leftTail)
        (4*runPattern true (gap+1) false bank)) =
      some (SymbolicDispatch.denote
        (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-q.1-2) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
  have hc := half_control_preserves_root code i hwalk
  have hw1 := IncrementCleanup.peel_bits (pathLeft code) (IncrementCleanup.path_has_zero code) leftTail
  have hw2 := IncrementCleanup.peel_bits (peel (pathLeft code)).2
    (DecrementZeroCleanup.path_peel_tail_has_zero code) leftTail
  rw [hc.1] at hw1
  rw [hc.2.1] at hw2
  rw [hc.1] at hw2
  dsimp only at hw1 hw2
  rw [hw2] at hw1
  have hcleanup := DecrementBreakCleanup.skip_and_cleanup p.1 q.1 gap head
    (bits (q.2++rootLeft) leftTail) bank
  rw [← hw1] at hcleanup
  have hpref : pathLeft precode = q.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hword : 1+2*runPattern false (p.1+q.1+gap+3) true (2*bank) = 1+4*rightTail := by
    dsimp only [rightTail]
    rw [show p.1+q.1+gap+3 = (p.1+q.1+gap+2)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    omega
  have hr := literal_return_root precode hc.2.2.2 (head-p.1-q.1-2) leftTail rightTail
  have hpos : (head-p.1-q.1-2)-1 = head-p.1-q.1-3 := by omega
  rw [hpref,hpos,← hword] at hr
  rw [silent_add,hcleanup]
  simp only [Option.bind_some]
  exact hr

theorem root_zero_to_break (code : List Bool) (gap : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let blocks := gap::before
    let far := bits (pathLeft code) leftTail
    let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
    let back := 2+(1+completeCost (0::foldRuns before []) gap)
    silent Record285.machine (start+back)
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)))) =
      some (atLeftWord DecrementZero.breakOne (head-1) far
        (4*IncrementSelector.blocksBits (gap::(before++[0])) (suffixBits fields retained))) := by
  dsimp only
  let blocks := gap::before
  let far := bits (pathLeft code) leftTail
  let tail := suffixBits fields retained
  let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
  let back := 2+(1+completeCost (0::foldRuns before []) gap)
  have hd := HalfDispatch.root_dispatch_half code before.length hwalk head leftTail
    (2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) tail))
  have ht := HalfDispatch.terminal_to_target code gap 0 before hwalk head leftTail tail
  have hr := target_zero_to_break gap before fields head far retained
  rw [show start+back = code.length+(((2*gap+5)+pathCost code+IncrementSelector.cost blocks)+back)
    by dsimp [start]; omega,silent_add,hd]
  simp only [Option.bind_some]
  rw [silent_add,ht]
  simp only [Option.bind_some]
  exact hr

theorem root_zero_returns_root (code : List Bool) (gap : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
    let back := 2+(1+completeCost (0::foldRuns before []) gap)
    let steps := start+back+(3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    silent Record285.machine steps
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)))) =
      some (SymbolicDispatch.denote
        (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-q.1-2) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let bank := IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)
  let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
  let back := 2+(1+completeCost (0::foldRuns before []) gap)
  have hf := root_zero_to_break code gap before fields hwalk head leftTail retained
  dsimp only at hf
  have hbank : IncrementSelector.blocksBits (gap::(before++[0])) (suffixBits fields retained) =
      runPattern true (gap+1) false bank := by
    simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true,bank]
  rw [hbank] at hf
  have hr := break_one_to_root code gap before.length hwalk head leftTail bank
  rw [show start+back+(3*(p.1+q.1)+2*gap+12)+(precode.length+17) =
      (start+back)+((3*(p.1+q.1)+2*gap+12)+(precode.length+17)) by omega,
    silent_add,hf]
  simp only [Option.bind_some]
  exact hr

theorem bound_root_zero_returns_root_physical (code : List Bool) (gap : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)))) physical) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
    let back := 2+(1+completeCost (0::foldRuns before []) gap)
    let steps := start+back+(3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    returnPathSkipOne code = some (precode++[true]) ∧
    Rel (SymbolicDispatch.denote
      (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-q.1-2) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_zero_returns_root code gap before fields hwalk head leftTail retained)
  have hc := (half_control_preserves_root code before.length hwalk).2.2.1
  exact ⟨hc,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.HalfEven
