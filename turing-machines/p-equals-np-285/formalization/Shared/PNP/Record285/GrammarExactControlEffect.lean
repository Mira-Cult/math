import Shared.PNP.Record285.GrammarDeterministicLeaf

/-! Executable lexical-control successor for a single physical grammar
instruction, paired with its complete returned tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.GrammarOperationalRun
open Shared.PNP.Record285.CleanBank

def controlStep (e : Edge) (fields : List Nat) (code : List Bool) : Option (List Bool) :=
  match e with
  | .inc _ => returnPath code
  | .dec i => if (fields.drop i).headD 0 = 0 then returnPathSkipOne code else returnPath code
  | .half i => if (fields.drop i).headD 0 % 2 = 0 then returnPathSkipOne code else returnPath code
  | .beep => returnPath code
  | .brk 0 => returnPath code
  | .brk 1 => returnPathSkipOne code
  | .brk 2 => ControlBreak.returnPathSkipTwo code
  | .cont 1 => ControlContinue.continuePathOne code
  | .cont 2 => ControlContinue.continuePathTwo code
  | _ => none

/-- Full returned physical tape and its explicitly recorded control word. -/
def AtControl (control : List Bool) (fields : List Nat)
    (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ word origin leftTail gap, control = word++[true] ∧ 164 ≤ gap ∧
    Rel (denote (rightWord treeRoot (-(word.length:Int)) word true rootLeft [false])
      origin leftTail (runPattern false gap true (2*IncrementSelector.blocksBits fields 0))) physical

theorem break_result_effect (fields : List Nat) (i gap : Nat) (code : List Bool)
    (head : Int) (leftTail : Nat) (out : Shared.Beeping.Machines.Config 285)
    (hgap : 164 ≤ gap)
    (h : ControlBreak.Result code i gap head leftTail (IncrementSelector.blocksBits fields 0) out) :
    ∃ control, controlStep (.brk i) fields code = some control ∧ AtControl control fields out := by
  obtain ⟨pre,_,h⟩ := h
  let p := peel pre.reverse
  let q := peel p.2
  let r := peel q.2
  cases i with
  | zero =>
    exact ⟨p.2.reverse++[true],h.1,p.2.reverse,head-2-p.1,leftTail,p.1+gap,rfl,by omega,h.2⟩
  | succ i =>
    cases i with
    | zero =>
      exact ⟨q.2.reverse++[true],h.1,q.2.reverse,head-2-p.1-1-q.1,leftTail,
        q.1+(p.1+gap+1),rfl,by omega,h.2⟩
    | succ i =>
      cases i with
      | zero =>
        exact ⟨r.2.reverse++[true],h.1,r.2.reverse,head-2-p.1-1-q.1-1-r.1,leftTail,
          r.1+(q.1+(p.1+gap+1)+1),rfl,by omega,h.2⟩
      | succ i => contradiction

theorem continue_result_effect (fields : List Nat) (i gap : Nat) (code : List Bool)
    (head : Int) (leftTail : Nat) (out : Shared.Beeping.Machines.Config 285)
    (hgap : 163 ≤ gap)
    (h : ControlContinue.Result code i false head leftTail
      (2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0)) out) :
    ∃ control, controlStep (.cont i) fields code = some control ∧ AtControl control fields out := by
  obtain ⟨pre,_,h⟩ := h
  let p := ControlContinue.peelZeros pre.reverse
  let q := ControlContinue.peelZeros p.2
  have hbank : bitVal false+2*(2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0)) =
      runPattern false (gap+2) true (2*IncrementSelector.blocksBits fields 0) := by
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  cases i with
  | zero => contradiction
  | succ i =>
    cases i with
    | zero =>
      dsimp only at h
      rw [hbank,push_zeros_gap] at h
      exact ⟨p.2.reverse++[true],h.1,p.2.reverse,head-2-p.1,leftTail,p.1+(gap+2),rfl,by omega,h.2⟩
    | succ i =>
      cases i with
      | zero =>
        dsimp only at h
        rw [hbank,push_zeros_gap] at h
        have hmid : 2*runPattern false (p.1+(gap+2)) true (2*IncrementSelector.blocksBits fields 0) =
            runPattern false (p.1+(gap+2)+1) true (2*IncrementSelector.blocksBits fields 0) := by
          simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
        rw [hmid,push_zeros_gap] at h
        exact ⟨q.2.reverse++[true],h.1,q.2.reverse,head-2-p.1-1-q.1,leftTail,
          q.1+(p.1+(gap+2)+1),rfl,by omega,h.2⟩
      | succ i => contradiction

/-- Exact duration and full input layout determine the lexical successor and
complete output bank. This is grammar semantics, not source equivalence. -/
theorem exact_control_effect (e : Edge) (fields : List Nat) (code : List Bool) (gap steps : Nat)
    (rootHead anchor head : Int) (leftTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf fields rootHead anchor e code head leftTail gap physical)
    (hspace : rootHead+328 ≤ anchor)
    (hduration : Duration e fields code gap steps) :
    ∃ control, controlStep e fields code = some control ∧
      AtControl control (applyUpdate e fields)
        ((EventSystem.mk physical Record285.machine.step).run steps) := by
  have hvalid : GrammarPrefix.valid code := ⟨e,GrammarPrefix.walk_follow code rootIndex e hleaf.1⟩
  have hlen := GrammarPrefix.valid_length_bound code hvalid
  have hhead := hleaf.2.1
  have hanchor := hleaf.2.2.1
  have hgap : 163 ≤ gap := by omega
  cases hduration with
  | inc before fields target code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hp := increment_returns_root_physical gap target before fields code hwalk head leftTail 0 physical hroot
    let p := peel code.reverse
    let word := p.2.reverse
    have hpath : returnPath code = some (word++[true]) := (increment_return_path code before.length hwalk).1
    have hu := update_sound _ _ _ (Update.inc before fields target)
    refine ⟨word++[true],by simpa only [controlStep] using hpath,
      word,head-p.1-1,leftTail,p.1+gap+1,rfl,by omega,?_⟩
    rw [hu]
    simpa only [incTime,IncrementMeaning.blocks_append] using hp.1
  | decZero before fields code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hp := DecrementZeroRoot.bound_root_zero_returns_root_physical code gap before hwalk
      head leftTail (suffixBits fields 0) physical hroot
    let p := peel code.reverse
    let q := peel p.2
    let word := q.2.reverse
    have hparts := split_parts before fields 0
    have hu := update_sound _ _ _ (Update.dec before fields 0)
    refine ⟨word++[true],?_,word,head-p.1-q.1-2,leftTail,p.1+q.1+gap+2,rfl,by omega,?_⟩
    · simpa only [controlStep,hparts.2.1,if_true] using hp.2.1
    · rw [hu]
      simpa only [decZeroTime,decrementFields,suffix_blank,IncrementMeaning.blocks_append] using hp.2.2.1
  | decPositive before fields k code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hp := DecrementNonzeroRoot.bound_root_nonzero_returns_root_physical code gap k before fields hwalk
      head leftTail 0 physical hroot
    let p := peel code.reverse
    let word := p.2.reverse
    have hparts := split_parts before fields (k+1)
    have hu := update_sound _ _ _ (Update.dec before fields (k+1))
    refine ⟨word++[true],?_,word,head-p.1-1,leftTail,p.1+gap+1,rfl,by omega,?_⟩
    · simpa only [controlStep,hparts.2.1,Nat.succ_ne_zero,if_false] using hp.2.1
    · rw [hu]
      simpa only [decPositiveTime,decrementFields] using hp.2.2.1
  | halfZero before fields code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hp := HalfEven.bound_root_zero_returns_root_physical code gap before fields hwalk
      head leftTail 0 physical hroot
    let p := peel code.reverse
    let q := peel p.2
    let word := q.2.reverse
    have hparts := split_parts before fields 0
    have hu := update_sound _ _ _ (Update.half before fields _ 0 HalfFields.zero)
    refine ⟨word++[true],?_,word,head-p.1-q.1-2,leftTail,p.1+q.1+gap+2,rfl,by omega,?_⟩
    · simpa only [controlStep,hparts.2.1,Nat.zero_mod,if_true] using hp.1
    · rw [hu]
      simpa only [halfZeroTime,suffix_blank,IncrementMeaning.blocks_append] using hp.2.1
  | halfOne before fields code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hp := HalfOne.bound_root_one_returns_root_physical code gap before fields hwalk
      head leftTail 0 physical hroot
    let p := peel code.reverse
    let word := p.2.reverse
    have hparts := split_parts before fields 1
    have hu := update_sound _ _ _ (Update.half before fields _ 1 HalfFields.one)
    refine ⟨word++[true],?_,word,head-p.1-1,leftTail,p.1+gap+1,rfl,by omega,?_⟩
    · simpa only [controlStep,hparts.2.1,show 1%2 ≠ 0 by decide,if_false] using hp.1
    · rw [hu]
      simpa only [halfOneTime] using hp.2.1
  | halfEven before fields n code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hinput : Rel (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+2]) (suffixBits fields (2^n*0))))) physical := by
      simpa only [Nat.mul_zero,rootEntry] using hroot
    have hp := HalfEvenPositive.bound_root_returns_root_physical code gap n before fields hwalk
      head leftTail 0 physical hinput
    let p := peel code.reverse
    let q := peel p.2
    let word := q.2.reverse
    have hparts := split_parts before fields (2*n+2)
    have heven : (2*n+2)%2 = 0 := by omega
    have hu := update_sound _ _ _ (Update.half before fields _ (2*n+2) (HalfFields.even n))
    refine ⟨word++[true],?_,word,head-p.1-q.1-2,leftTail,p.1+q.1+gap+2,rfl,by omega,?_⟩
    · simpa only [controlStep,hparts.2.1,heven,if_true] using hp.1
    · rw [hu]
      simpa only [halfEvenTime] using hp.2.1
  | halfOdd before fields n code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    rw [split_bank] at hroot
    have hinput : Rel (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[2*n+3]) (suffixBits fields (2^n*(2*0)))))) physical := by
      simpa only [Nat.mul_zero,rootEntry] using hroot
    have hp := HalfOdd.bound_root_odd_returns_root_physical code gap n before fields hwalk
      head leftTail 0 physical hinput
    let p := peel code.reverse
    let word := p.2.reverse
    have hparts := split_parts before fields (2*n+3)
    have hodd : (2*n+3)%2 ≠ 0 := by omega
    have hu := update_sound _ _ _ (Update.half before fields _ (2*n+3) (HalfFields.odd n))
    refine ⟨word++[true],?_,word,head-p.1-1,leftTail,p.1+gap+1,rfl,by omega,?_⟩
    · simpa only [controlStep,hparts.2.1,hodd,if_false] using hp.2.1
    · rw [hu]
      simpa only [halfOddTime] using hp.2.2.1
  | beep fields code gap =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    have hp := beep_both_markers_physical code hwalk false gap head leftTail
      (2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
      (IncrementSelector.blocksBits fields 0) rfl physical hroot
    refine ⟨beepPrecode++[true],by simpa only [controlStep] using hp.2.1,
      beepPrecode,head-1,leftTail,gap+1,rfl,by omega,?_⟩
    simpa [applyUpdate,beepPrecode] using hp.2.2.1
  | brkZero fields code pre gap hcode =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    let bank := IncrementSelector.blocksBits fields 0
    let right := 2*runPattern false gap true (2*bank)
    have hbank : bitVal false+2*right = runPattern false (gap+2) true (2*bank) := by
      simp only [right,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    obtain ⟨pre',hcode',hpath,hresult,_,_⟩ := ControlBreak.root_break_zero_physical
      code hwalk false (gap+2) head leftTail right bank hbank physical hroot
    have he : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hr : ControlBreak.Result code 0 (gap+2) head leftTail bank
        ((EventSystem.mk physical Record285.machine.step).run (breakZeroTime code pre gap)) :=
      ⟨pre,hcode,hpath,hresult⟩
    simpa only [applyUpdate] using break_result_effect fields 0 (gap+2) code head leftTail _ (by omega) hr
  | brkOne fields code pre gap hcode =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    let bank := IncrementSelector.blocksBits fields 0
    let right := 2*runPattern false gap true (2*bank)
    have hbank : bitVal false+2*right = runPattern false (gap+2) true (2*bank) := by
      simp only [right,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    obtain ⟨pre',hcode',hpath,hresult,_,_⟩ := ControlBreak.root_break_one_physical
      code hwalk false (gap+2) head leftTail right bank hbank physical hroot
    have he : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hr : ControlBreak.Result code 1 (gap+2) head leftTail bank
        ((EventSystem.mk physical Record285.machine.step).run (breakOneTime code pre gap)) :=
      ⟨pre,hcode,hpath,hresult⟩
    simpa only [applyUpdate] using break_result_effect fields 1 (gap+2) code head leftTail _ (by omega) hr
  | brkTwo fields code pre gap hcode =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    let bank := IncrementSelector.blocksBits fields 0
    let right := 2*runPattern false gap true (2*bank)
    have hbank : bitVal false+2*right = runPattern false (gap+2) true (2*bank) := by
      simp only [right,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    obtain ⟨pre',hcode',hpath,hresult,_,_⟩ := ControlBreak.root_break_two_physical
      code hwalk false (gap+2) head leftTail right bank hbank physical hroot
    have he : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hr : ControlBreak.Result code 2 (gap+2) head leftTail bank
        ((EventSystem.mk physical Record285.machine.step).run (breakTwoTime code pre gap)) :=
      ⟨pre,hcode,hpath,hresult⟩
    simpa only [applyUpdate] using break_result_effect fields 2 (gap+2) code head leftTail _ (by omega) hr
  | contOne fields code pre gap hcode =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    let right := 2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0)
    obtain ⟨pre',hcode',hpath,hresult,_,_⟩ := ControlContinue.root_continue_one_any_physical
      code hwalk false head leftTail right physical hroot
    have he : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hr : ControlContinue.Result code 1 false head leftTail right
        ((EventSystem.mk physical Record285.machine.step).run (continueOneTime code pre)) :=
      ⟨pre,hcode,hpath,hresult⟩
    simpa only [applyUpdate] using continue_result_effect fields 1 gap code head leftTail _ hgap hr
  | contTwo fields code pre gap hcode =>
    obtain ⟨hwalk,_,_,hroot⟩ := hleaf
    let right := 2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0)
    obtain ⟨pre',hcode',hpath,hresult,_,_⟩ := ControlContinue.root_continue_two_any_physical
      code hwalk false head leftTail right physical hroot
    have he : pre' = pre := List.append_cancel_right (hcode'.symm.trans hcode)
    subst pre'
    have hr : ControlContinue.Result code 2 false head leftTail right
        ((EventSystem.mk physical Record285.machine.step).run (continueTwoTime code pre)) :=
      ⟨pre,hcode,hpath,hresult⟩
    simpa only [applyUpdate] using continue_result_effect fields 2 gap code head leftTail _ hgap hr

/-- Every operation in the cofinal run has the executable lexical successor,
and that successor names its complete returned physical tape and bank. -/
theorem operation_step_control_effect (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    ∃ control, controlStep w.edge s.fields w.code = some control ∧
      AtControl control (operationSystem.run (n+1)).fields (operationSystem.run (n+1)).physical := by
  dsimp only
  let s := operationSystem.run n
  let w := chooseStep s
  have hp := exact_control_effect w.edge s.fields w.code w.gap w.duration (-3818) 3 w.head w.leftTail
    s.physical w.leaf (by decide) w.exactDuration
  have hf : (operationSystem.run (n+1)).fields = applyUpdate w.edge s.fields :=
    (operation_step_computable_data n).2.2
  have hphysical : (operationSystem.run (n+1)).physical =
      (EventSystem.mk s.physical Record285.machine.step).run w.duration := rfl
  rw [hf,hphysical]
  exact hp

end Shared.PNP.Record285.GrammarExact
