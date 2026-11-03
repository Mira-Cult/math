import Shared.PNP.Record285.GrammarAnchoredBreak

/-! Both grammar continuations preserve the anchored valid-prefix invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.ControlContinue (peelZeros)

theorem peel_zeros_length (xs : List Bool) (ht : true ∈ xs) :
    xs.length = (peelZeros xs).1+1+(peelZeros xs).2.length := by
  have h := congrArg List.length (ControlContinue.peel_zeros_decomposition xs ht)
  simp only [List.length_append,List.length_replicate,List.length_cons] at h
  omega

theorem continue_anchored (fields : List Nat) (i : Nat) (rootHead anchor head : Int)
    (leftTail gap : Nat) (code : List Bool) (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf fields rootHead anchor (.cont i) code head leftTail gap physical) :
    ∃ steps, 0 < steps ∧
      AnchoredRoot fields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  let bank := IncrementSelector.blocksBits fields 0
  have hbank : bitVal false+2*(2*runPattern false gap true (2*bank)) =
      runPattern false (gap+2) true (2*bank) := by
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  obtain ⟨steps,hpos,hresult,hquiet⟩ := ControlContinue.root_continue_complete code i hwalk false
    head leftTail (2*runPattern false gap true (2*bank)) physical hroot
  obtain ⟨pre,hcode,hresult⟩ := hresult
  have hw : walk 162 (pre++[true]) = some (.cont i) := by simpa only [hcode,rootIndex] using hwalk
  have hlen : code.length = pre.length+1 := by simp [hcode]
  let p := peelZeros pre.reverse
  let q := peelZeros p.2
  refine ⟨steps,hpos,?_,hquiet⟩
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

end Shared.PNP.Record285.GrammarReady
