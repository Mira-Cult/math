import Shared.PNP.Record285.GrammarAnchoredDecrement

/-! Native half preserves anchored valid control in every parity case. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.CleanBank

theorem even_config_anchored (code : List Bool) (i gap : Nat) (fields : List Nat)
    (rootHead anchor head : Int) (leftTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hwalk : walk rootIndex code = some (.half i)) (hhead : head-code.length = rootHead)
    (hanchor : head+2+gap = anchor) (hcontrol : HalfComplete.evenControl code)
    (hroot : Rel (HalfComplete.evenConfig code gap (IncrementSelector.blocksBits fields 0) head leftTail) physical) :
    AnchoredRoot fields rootHead anchor physical := by
  let p := peel code.reverse
  let q := peel p.2
  have hz := HalfEven.half_reverse_zeros code i hwalk
  have hl1 := peel_length code.reverse hz.1
  have hl2 := peel_length p.2 hz.2
  simp only [List.length_reverse] at hl1
  change code.length = p.1+1+p.2.length at hl1
  change p.2.length = q.1+1+q.2.length at hl2
  have hv : valid (q.2.reverse++[true]) := return_skip_one_valid code _ _ hwalk hcontrol
  have hehead : head-p.1-q.1-2-q.2.reverse.length = rootHead := by
    simp only [List.length_reverse]
    omega
  have heanchor : head-p.1-q.1-2+2+(p.1+q.1+gap+2 : Nat) = anchor := by omega
  exact ⟨q.2.reverse,true,head-p.1-q.1-2,leftTail,p.1+q.1+gap+2,hv,hehead,heanchor,hroot⟩

theorem odd_config_anchored (code : List Bool) (i gap : Nat) (fields : List Nat)
    (rootHead anchor head : Int) (leftTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hwalk : walk rootIndex code = some (.half i)) (hhead : head-code.length = rootHead)
    (hanchor : head+2+gap = anchor) (hcontrol : HalfComplete.oddControl code)
    (hroot : Rel (HalfComplete.oddConfig code gap (IncrementSelector.blocksBits fields 0) head leftTail) physical) :
    AnchoredRoot fields rootHead anchor physical := by
  let p := peel code.reverse
  have hz := (HalfEven.half_reverse_zeros code i hwalk).1
  have hl := peel_length code.reverse hz
  simp only [List.length_reverse] at hl
  change code.length = p.1+1+p.2.length at hl
  have hv : valid (p.2.reverse++[true]) := return_path_valid code _ _ hwalk hcontrol
  have hehead : head-p.1-1-p.2.reverse.length = rootHead := by
    simp only [List.length_reverse]
    omega
  have heanchor : head-p.1-1+2+(p.1+gap+1 : Nat) = anchor := by omega
  exact ⟨p.2.reverse,true,head-p.1-1,leftTail,p.1+gap+1,hv,hehead,heanchor,hroot⟩

/-- All natural targets, with blank exterior, complete half silently and
return an exactly specified bank to the same root and anchor. -/
theorem half_anchored (before fields : List Nat) (target : Nat)
    (rootHead anchor head : Int) (leftTail gap : Nat) (code : List Bool)
    (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf (before++[target]++fields) rootHead anchor (.half before.length)
      code head leftTail gap physical) :
    ∃ steps newFields, 0 < steps ∧ HalfFields before fields target newFields ∧
      AnchoredRoot newFields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  rw [split_bank] at hroot
  have hlayout : (2*runPattern false gap true
      (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0))) =
      if false then 2*pushBit (gap+1) true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields (2^(target/2)*0)))
      else 2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields (2^(target/2)*0))) := by
    simp only [Bool.false_eq_true,if_false,Nat.mul_zero]
  obtain ⟨steps,hpos,hresult,hquiet⟩ := PreparedHalf.half_both_markers code gap target before fields
    hwalk false head leftTail _ 0 hlayout physical hroot
  rcases hresult with h | h | h | h
  · rcases h with ⟨rfl,hcontrol,hr⟩
    refine ⟨steps,_,hpos,HalfFields.zero,?_,hquiet⟩
    apply even_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hcontrol
    simpa only [suffix_blank,IncrementMeaning.blocks_append] using hr
  · rcases h with ⟨rfl,hcontrol,hr⟩
    refine ⟨steps,_,hpos,HalfFields.one,?_,hquiet⟩
    exact odd_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hcontrol hr
  · rcases h with ⟨n,rfl,hcontrol,hr⟩
    refine ⟨steps,_,hpos,HalfFields.even n,?_,hquiet⟩
    apply even_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hcontrol
    simpa only [Nat.mul_zero] using hr
  · rcases h with ⟨n,rfl,hcontrol,hr⟩
    refine ⟨steps,_,hpos,HalfFields.odd n,?_,hquiet⟩
    exact odd_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hcontrol hr

end Shared.PNP.Record285.GrammarReady
