import Shared.PNP.Record285.ControlBreakZero

/-! Complete literal one-level break, including its skipped zero boundary. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlBreak
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.ControlInvariant
open Shared.PNP.Record285.ControlContinue (literal_control_leaf_any)

def skipState : Fin 285 := ⟨117,by decide⟩

theorem true_tail_no_break (n i : Nat) :
    walk 159 (List.replicate n true) ≠ some (.brk i) := by
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

theorem break_two_zeros (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.brk i)) :
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
              have htail : walk 159 cs = some (.brk i) := by
                simpa only [walk,root_true_edge,next_false_edge,beep_true_edge] using hwalk
              have hz : false ∈ cs := by
                by_cases hn : false ∈ cs
                · exact hn
                · have ht := all_true_replicate cs hn
                  rw [ht] at htail
                  exact False.elim ((true_tail_no_break cs.length i) htail)
              obtain ⟨pre,post,h⟩ := false_split cs hz
              refine ⟨[true],true::pre,post,?_⟩
              simp [h,List.append_assoc]

theorem break_prior_two (pre : List Bool) (i : Nat)
    (hwalk : walk 162 (pre++[true]) = some (.brk i)) :
    false ∈ pre.reverse ∧ false ∈ (peel pre.reverse).2 := by
  obtain ⟨a,b,c,h⟩ := break_two_zeros (pre++[true]) i hwalk
  have hcount : 2 ≤ pre.reverse.count false := by
    have hc := congrArg (fun ys : List Bool => ys.count false) h
    simp [List.count_append] at hc
    have hh : 2 ≤ pre.count false := by omega
    simpa only [List.count_reverse] using hh
  have hfirst : false ∈ pre.reverse := by
    by_cases hm : false ∈ pre.reverse
    · exact hm
    · have hz : pre.reverse.count false = 0 := List.count_eq_zero.mpr hm
      omega
  have hd := peel_decomposition pre.reverse hfirst
  have hc := congrArg (fun ys : List Bool => ys.count false) hd
  have hz : (List.replicate (peel pre.reverse).1 true).count false = 0 := by
    simp [List.count_replicate]
  simp only [List.count_append,hz,Nat.zero_add,List.count_cons_self] at hc
  have hpos : 0 < ((peel pre.reverse).2).count false := by omega
  have hsecond : false ∈ (peel pre.reverse).2 := by
    by_cases hm : false ∈ (peel pre.reverse).2
    · exact hm
    · have hz' : ((peel pre.reverse).2).count false = 0 := List.count_eq_zero.mpr hm
      omega
  exact ⟨hfirst,hsecond⟩

theorem skip_zero : Record285.machine.table.row skipState false = ⟨false,.left,lexical,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem skip_one : Record285.machine.table.row skipState true = ⟨false,.left,skipState,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

/-- Skip one control zero, preserving the entire finite anchor-and-bank tape. -/
theorem skip_control (M : Machine 285) (qskip qnext : Fin 285)
    (h0 : M.table.row qskip false = ⟨false,.left,qnext,false⟩)
    (h1 : M.table.row qskip true = ⟨false,.left,qskip,false⟩)
    (n gap : Nat) (head : Int) (far bank : Nat) :
    silent M (n+1) (atLeftWord qskip head (runPattern true n false far)
      (2*runPattern false gap true (2*bank))) =
      some (atLeftWord qnext (head-n-1) far
        (2*runPattern false (n+gap+1) true (2*bank))) := by
  have hs := sweep_left M qskip true false h1 n false head far
    (2*runPattern false gap true (2*bank))
  have hlast : silent M 1
      (atLeftWord qskip (head-n) (2*far)
        (pushBit n false (2*runPattern false gap true (2*bank)))) =
      some (atLeftWord qnext (head-n-1) far
        (2*runPattern false (n+gap+1) true (2*bank))) := by
    have hp : pushBit n false (2*runPattern false gap true (2*bank)) =
        2*runPattern false (n+gap) true (2*bank) := by
      have ha := pushBit_affine n false (runPattern false gap true (2*bank))
      simp only [bitVal,Bool.false_eq_true,if_false,Nat.add_zero] at ha
      rw [ha,pattern_zero_add]
    simp only [atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,h0,
      Bool.false_eq_true,if_false,bitVal,Nat.add_zero,hp]
    have hr : 2*(2*runPattern false (n+gap) true (2*bank)) =
        2*runPattern false (n+gap+1) true (2*bank) := by
      rw [runPattern]
      simp only [bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    rw [hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  exact hlast

theorem break_one_return (pre : List Bool) (hfirst : false ∈ pre.reverse)
    (hsecond : false ∈ (peel pre.reverse).2)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (gap : Nat) (head : Int)
    (leftTail bank : Nat) :
    let p := peel pre.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let steps := (p.1+1)+(3*q.1+2*(p.1+gap+2)+5)+(precode.length+17)
    silent Record285.machine steps
      (atLeftWord skipState head (bits (pre.reverse++rootLeft) leftTail)
        (2*runPattern false gap true (2*bank))) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1-q.1) leftTail (runPattern false (q.1+(p.1+gap+1)) true (2*bank))) := by
  dsimp only
  let p := peel pre.reverse
  let q := peel p.2
  let precode := q.2.reverse
  have hz : false ∈ pre.reverse++rootLeft := by simp [hfirst]
  have hp := peel_append pre.reverse rootLeft hfirst
  have hw := peel_bits (pre.reverse++rootLeft) hz leftTail
  rw [hp] at hw
  dsimp only at hw
  have hs := skip_control Record285.machine skipState lexical skip_zero skip_one p.1 gap head
    (bits (p.2++rootLeft) leftTail) bank
  have hsafe' := peel_prefix_safe pre hsafe hfirst
  have hr := break_zero_return p.2.reverse (by simpa using hsecond) hsafe'
    (p.1+gap+1) (head-p.1-1) leftTail bank
  simp only [List.reverse_reverse] at hr
  rw [show p.1+1+(3*q.1+2*(p.1+gap+2)+5)+(precode.length+17) =
      (p.1+1)+((3*q.1+2*((p.1+gap+1)+1)+5)+(precode.length+17)) by omega,
    hw,silent_add,hs]
  simp only [Option.bind_some]
  exact hr

theorem root_break_one (code : List Bool) (hwalk : walk 162 code = some (.brk 1))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank)) :
    ∃ pre, code = pre++[true] ∧
      let p := peel pre.reverse
      let q := peel p.2
      let precode := q.2.reverse
      let inner := (p.1+1)+(3*q.1+2*(p.1+gap+2)+5)+(precode.length+17)
      let steps := code.length+inner
      returnPathSkipOne code = some (precode++[true]) ∧
      silent Record285.machine steps
        (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1-1-q.1) leftTail (runPattern false (q.1+(p.1+gap+1)) true (2*bank))) ∧
      0 < steps := by
  obtain ⟨pre,parent,row,hcode,_,_,_,_,hsafe⟩ := break_prefix_safe code 1 hwalk
  have hprior := break_prior_two pre 1 (by simpa [hcode] using hwalk)
  have hf := literal_control_leaf_any code pre (.brk 1) skipState
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) marker head leftTail rightTail
  rw [hanchor] at hf
  have hr := break_one_return pre hprior.1 hprior.2 hsafe gap (head-2) leftTail bank
  have hp := return_after_one_skip pre.reverse hprior.1 hprior.2
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · simpa [returnPathSkipOne,returnAfterOneSkip,hcode,List.reverse_append] using hp
  · rw [silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_break_one_physical (code : List Bool) (hwalk : walk 162 code = some (.brk 1))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peel pre.reverse
      let q := peel p.2
      let precode := q.2.reverse
      let inner := (p.1+1)+(3*q.1+2*(p.1+gap+2)+5)+(precode.length+17)
      let steps := code.length+inner
      returnPathSkipOne code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1) leftTail (runPattern false (q.1+(p.1+gap+1)) true (2*bank)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_break_one code hwalk marker gap head leftTail rightTail bank hanchor
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

end Shared.PNP.Record285.ControlBreak
