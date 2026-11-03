import Shared.PNP.Record285.GrammarExactArithmetic

/-! Decode complete control-transfer results into the shared anchored invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.ControlContinue (peelZeros)

theorem break_result_anchored (fields : List Nat) (i : Nat) (rootHead anchor head : Int)
    (leftTail gap : Nat) (code : List Bool) (out : Shared.Beeping.Machines.Config 285)
    (hwalk : walk rootIndex code = some (.brk i)) (hhead : head-code.length = rootHead)
    (hanchor : head+2+gap = anchor)
    (hresult : ControlBreak.Result code i (gap+2) head leftTail (IncrementSelector.blocksBits fields 0) out) :
    AnchoredRoot fields rootHead anchor out := by
  obtain ⟨pre,hcode,hresult⟩ := hresult
  have hw : walk 162 (pre++[true]) = some (.brk i) := by simpa only [hcode,rootIndex] using hwalk
  have hlen : code.length = pre.length+1 := by simp [hcode]
  let p := peel pre.reverse
  let q := peel p.2
  let r := peel q.2
  cases i with
  | zero =>
    have hz := ControlBreak.break_prior_zero pre 0 hw
    have hl := peel_length pre.reverse hz
    simp only [List.length_reverse] at hl
    change pre.length = p.1+1+p.2.length at hl
    dsimp only at hresult
    have hv : valid (p.2.reverse++[true]) := return_path_valid code _ _ hwalk hresult.1
    have hehead : head-2-p.1-p.2.reverse.length = rootHead := by simp only [List.length_reverse]; omega
    have heanchor : head-2-p.1+2+(p.1+(gap+2) : Nat) = anchor := by omega
    exact ⟨p.2.reverse,true,head-2-p.1,leftTail,p.1+(gap+2),hv,hehead,heanchor,hresult.2⟩
  | succ i =>
    cases i with
    | zero =>
      have hz := ControlBreak.break_prior_two pre 1 hw
      have hl1 := peel_length pre.reverse hz.1
      have hl2 := peel_length p.2 hz.2
      simp only [List.length_reverse] at hl1
      change pre.length = p.1+1+p.2.length at hl1
      change p.2.length = q.1+1+q.2.length at hl2
      dsimp only at hresult
      have hv : valid (q.2.reverse++[true]) := return_skip_one_valid code _ _ hwalk hresult.1
      have hehead : head-2-p.1-1-q.1-q.2.reverse.length = rootHead := by simp only [List.length_reverse]; omega
      have heanchor : head-2-p.1-1-q.1+2+(q.1+(p.1+(gap+2)+1) : Nat) = anchor := by omega
      exact ⟨q.2.reverse,true,head-2-p.1-1-q.1,leftTail,q.1+(p.1+(gap+2)+1),
        hv,hehead,heanchor,hresult.2⟩
    | succ i =>
      cases i with
      | zero =>
        obtain ⟨pre',heq,hcount,_⟩ := ControlBreakRank.break_prefix_zeros code 2 hwalk
        have hpre : pre = pre' := List.append_cancel_right (hcode.symm.trans heq)
        subst pre'
        have hcount' : 3 ≤ pre.reverse.count false := by simpa only [List.count_reverse] using hcount
        have hz := ControlBreak.three_peels pre.reverse hcount'
        have hl1 := peel_length pre.reverse hz.1
        have hl2 := peel_length p.2 hz.2.1
        have hl3 := peel_length q.2 hz.2.2
        simp only [List.length_reverse] at hl1
        change pre.length = p.1+1+p.2.length at hl1
        change p.2.length = q.1+1+q.2.length at hl2
        change q.2.length = r.1+1+r.2.length at hl3
        dsimp only at hresult
        have hv : valid (r.2.reverse++[true]) := return_skip_two_valid code _ _ hwalk hresult.1
        have hehead : head-2-p.1-1-q.1-1-r.1-r.2.reverse.length = rootHead := by
          simp only [List.length_reverse]; omega
        have heanchor : head-2-p.1-1-q.1-1-r.1+2+
            (r.1+(q.1+(p.1+(gap+2)+1)+1) : Nat) = anchor := by omega
        exact ⟨r.2.reverse,true,head-2-p.1-1-q.1-1-r.1,leftTail,r.1+(q.1+(p.1+(gap+2)+1)+1),
          hv,hehead,heanchor,hresult.2⟩
      | succ i => contradiction


theorem continue_result_anchored (fields : List Nat) (i : Nat) (rootHead anchor head : Int)
    (leftTail gap : Nat) (code : List Bool) (out : Shared.Beeping.Machines.Config 285)
    (hwalk : walk rootIndex code = some (.cont i)) (hhead : head-code.length = rootHead)
    (hanchor : head+2+gap = anchor)
    (hresult : ControlContinue.Result code i false head leftTail
      (2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0)) out) :
    AnchoredRoot fields rootHead anchor out := by
  let bank := IncrementSelector.blocksBits fields 0
  have hbank : bitVal false+2*(2*runPattern false gap true (2*bank)) =
      runPattern false (gap+2) true (2*bank) := by
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  obtain ⟨pre,hcode,hresult⟩ := hresult
  have hw : walk 162 (pre++[true]) = some (.cont i) := by simpa only [hcode,rootIndex] using hwalk
  have hlen : code.length = pre.length+1 := by simp [hcode]
  let p := peelZeros pre.reverse
  let q := peelZeros p.2
  cases i with
  | zero => contradiction
  | succ i =>
    cases i with
    | zero =>
      have ht := ControlContinue.continue_one_prior_true pre hw
      have hl := peel_zeros_length pre.reverse ht
      simp only [List.length_reverse] at hl
      change pre.length = p.1+1+p.2.length at hl
      dsimp only at hresult
      rw [hbank,push_zeros_gap] at hresult
      have hv : valid (p.2.reverse++[true]) := continue_one_valid code _ _ hwalk hresult.1
      have hehead : head-2-p.1-p.2.reverse.length = rootHead := by simp only [List.length_reverse]; omega
      have heanchor : head-2-p.1+2+(p.1+(gap+2) : Nat) = anchor := by omega
      exact ⟨p.2.reverse,true,head-2-p.1,leftTail,p.1+(gap+2),hv,hehead,heanchor,hresult.2⟩
    | succ i =>
      cases i with
      | zero =>
        have ht := ControlContinue.continue_two_prior pre hw
        have hl1 := peel_zeros_length pre.reverse ht.1
        have hl2 := peel_zeros_length p.2 ht.2
        simp only [List.length_reverse] at hl1
        change pre.length = p.1+1+p.2.length at hl1
        change p.2.length = q.1+1+q.2.length at hl2
        dsimp only at hresult
        rw [hbank,push_zeros_gap] at hresult
        have hmid : 2*runPattern false (p.1+(gap+2)) true (2*bank) =
            runPattern false (p.1+(gap+2)+1) true (2*bank) := by
          simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
        rw [hmid,push_zeros_gap] at hresult
        have hv : valid (q.2.reverse++[true]) := continue_two_valid code _ _ hwalk hresult.1
        have hehead : head-2-p.1-1-q.1-q.2.reverse.length = rootHead := by simp only [List.length_reverse]; omega
        have heanchor : head-2-p.1-1-q.1+2+(q.1+(p.1+(gap+2)+1) : Nat) = anchor := by omega
        exact ⟨q.2.reverse,true,head-2-p.1-1-q.1,leftTail,q.1+(p.1+(gap+2)+1),
          hv,hehead,heanchor,hresult.2⟩
      | succ i => contradiction


theorem break_exact (fields : List Nat) (i : Nat) (rootHead anchor head : Int)
    (leftTail gap : Nat) (code : List Bool) (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf fields rootHead anchor (.brk i) code head leftTail gap physical) :
    ∃ steps, Duration (.brk i) fields code gap steps ∧ 0 < steps ∧
      AnchoredRoot fields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  let bank := IncrementSelector.blocksBits fields 0
  let right := 2*runPattern false gap true (2*bank)
  have hbank : bitVal false+2*right = runPattern false (gap+2) true (2*bank) := by
    simp only [right,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  cases i with
  | zero =>
    obtain ⟨pre,hcode,hpath,hresult,hquiet,hpos⟩ := ControlBreak.root_break_zero_physical
      code hwalk false (gap+2) head leftTail right bank hbank physical hroot
    have hr : ControlBreak.Result code 0 (gap+2) head leftTail bank
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (breakZeroTime code pre gap)) :=
      ⟨pre,hcode,hpath,hresult⟩
    exact ⟨_,Duration.brkZero fields code pre gap hcode,hpos,
      break_result_anchored fields 0 rootHead anchor head leftTail gap code _ hwalk hhead hanchor hr,hquiet⟩
  | succ i =>
    cases i with
    | zero =>
      obtain ⟨pre,hcode,hpath,hresult,hquiet,hpos⟩ := ControlBreak.root_break_one_physical
        code hwalk false (gap+2) head leftTail right bank hbank physical hroot
      have hr : ControlBreak.Result code 1 (gap+2) head leftTail bank
          ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (breakOneTime code pre gap)) :=
        ⟨pre,hcode,hpath,hresult⟩
      exact ⟨_,Duration.brkOne fields code pre gap hcode,hpos,
        break_result_anchored fields 1 rootHead anchor head leftTail gap code _ hwalk hhead hanchor hr,hquiet⟩
    | succ i =>
      cases i with
      | zero =>
        obtain ⟨pre,hcode,hpath,hresult,hquiet,hpos⟩ := ControlBreak.root_break_two_physical
          code hwalk false (gap+2) head leftTail right bank hbank physical hroot
        have hr : ControlBreak.Result code 2 (gap+2) head leftTail bank
            ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (breakTwoTime code pre gap)) :=
          ⟨pre,hcode,hpath,hresult⟩
        exact ⟨_,Duration.brkTwo fields code pre gap hcode,hpos,
          break_result_anchored fields 2 rootHead anchor head leftTail gap code _ hwalk hhead hanchor hr,hquiet⟩
      | succ i =>
        obtain ⟨_,_,row,_,_,_,hexpected,_,_⟩ :=
          ControlInvariant.break_prefix_safe code (i+3) (by simpa [rootIndex,Nat.add_assoc] using hwalk)
        simp [expected,breakTerminal] at hexpected

theorem continue_exact (fields : List Nat) (i : Nat) (rootHead anchor head : Int)
    (leftTail gap : Nat) (code : List Bool) (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf fields rootHead anchor (.cont i) code head leftTail gap physical) :
    ∃ steps, Duration (.cont i) fields code gap steps ∧ 0 < steps ∧
      AnchoredRoot fields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  let right := 2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0)
  cases i with
  | zero =>
    obtain ⟨_,_,row,_,_,_,hexpected,_,_⟩ := ControlInvariant.continue_prefix_safe code 0 hwalk
    simp [expected,continueTerminal] at hexpected
  | succ i =>
    cases i with
    | zero =>
      obtain ⟨pre,hcode,hpath,hresult,hquiet,hpos⟩ := ControlContinue.root_continue_one_any_physical
        code hwalk false head leftTail right physical hroot
      have hr : ControlContinue.Result code 1 false head leftTail right
          ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (continueOneTime code pre)) :=
        ⟨pre,hcode,hpath,hresult⟩
      exact ⟨_,Duration.contOne fields code pre gap hcode,hpos,
        continue_result_anchored fields 1 rootHead anchor head leftTail gap code _ hwalk hhead hanchor hr,hquiet⟩
    | succ i =>
      cases i with
      | zero =>
        obtain ⟨pre,hcode,hpath,hresult,hquiet,hpos⟩ := ControlContinue.root_continue_two_any_physical
          code hwalk false head leftTail right physical hroot
        have hr : ControlContinue.Result code 2 false head leftTail right
            ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (continueTwoTime code pre)) :=
          ⟨pre,hcode,hpath,hresult⟩
        exact ⟨_,Duration.contTwo fields code pre gap hcode,hpos,
          continue_result_anchored fields 2 rootHead anchor head leftTail gap code _ hwalk hhead hanchor hr,hquiet⟩
      | succ i =>
        obtain ⟨_,_,row,_,_,_,hexpected,_,_⟩ :=
          ControlInvariant.continue_prefix_safe code (i+3) (by simpa [rootIndex,Nat.add_assoc] using hwalk)
        simp [expected,continueTerminal] at hexpected

end Shared.PNP.Record285.GrammarExact
