import Shared.PNP.Record285.GrammarPrefix
import Shared.PNP.Record285.CleanBankStep

/-! A valid grammar control prefix with enough actual blank cells before the
bank anchor admits a checked physical instruction. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.CleanBank

/-- Control and anchor are represented at their actual positions; the large
zero margin prevents grammar dispatch from reaching the anchor or bank. -/
def GoodRoot (fields : List Nat) (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ word marker origin leftTail gap,
    valid (word++[marker]) ∧ 164 ≤ gap ∧
    Rel (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false gap true (2*IncrementSelector.blocksBits fields 0))) physical

/-- The fixed dispatcher coordinate and bank-anchor coordinate are retained
alongside the valid control prefix. -/
def AnchoredRoot (fields : List Nat) (rootHead anchor : Int)
    (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ (word : List Bool) (marker : Bool) (origin : Int) (leftTail gap : Nat),
    valid (word++[marker]) ∧ origin-word.length = rootHead ∧ origin+2+gap = anchor ∧
    Rel (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false gap true (2*IncrementSelector.blocksBits fields 0))) physical

/-- A valid control path consumes at most 163 cells; hence a fixed 328-cell
root-to-anchor separation always leaves the required actual blank margin. -/
theorem anchored_is_good (fields : List Nat) (rootHead anchor : Int)
    (physical : Shared.Beeping.Machines.Config 285) (h : AnchoredRoot fields rootHead anchor physical)
    (hspace : rootHead+328 ≤ anchor) : GoodRoot fields physical := by
  obtain ⟨word,marker,origin,leftTail,gap,hvalid,hhead,hanchor,hroot⟩ := h
  have hlen := valid_length_bound (word++[marker]) hvalid
  simp only [List.length_append,List.length_singleton] at hlen
  refine ⟨word,marker,origin,leftTail,gap,hvalid,?_,hroot⟩
  omega

theorem zeros_bits (n : Nat) (tail : Nat) :
    bits (List.replicate n false) tail = 2^n*tail := by
  induction n with
  | zero => simp [bits]
  | succ n ih =>
    simp only [List.replicate_succ,bits,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,ih,Nat.pow_succ]
    ac_rfl

theorem zeros_pattern (n gap tail : Nat) :
    runPattern false (n+gap) true tail = 2^n*runPattern false gap true tail := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : n+1+gap = (n+gap)+1 := by omega
    rw [h,runPattern,ih,Nat.pow_succ]
    simp only [bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    ac_rfl

/-- Extending a represented prefix through zero cells is a change of view of
one and the same complete two-way tape. -/
theorem extend_through_zeros (word : List Bool) (marker : Bool) (zeros gap : Nat)
    (origin : Int) (leftTail bank : Nat) :
    let code := word++[marker]++List.replicate zeros false
    denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false (zeros+gap+1) true (2*bank)) =
    denote (rightWord treeRoot (-(code.length:Int)) code false rootLeft [])
      (origin+1+zeros) leftTail (2*runPattern false gap true (2*bank)) := by
  dsimp only
  let code := word++[marker]++List.replicate zeros false
  let base := origin-word.length
  have hw := root_word_repr word marker base leftTail
    (bits [false] (runPattern false (zeros+gap+1) true (2*bank)))
  have hc := root_word_repr code false base leftTail (2*runPattern false gap true (2*bank))
  dsimp only at hw hc
  have ht : bits [false] (runPattern false (zeros+gap+1) true (2*bank)) =
      bits (List.replicate zeros false++[false]) (2*runPattern false gap true (2*bank)) := by
    rw [bits_append,zeros_bits]
    have hgap : zeros+gap+1 = zeros+(gap+1) := by omega
    rw [hgap,zeros_pattern,runPattern]
    simp only [bits,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    ac_rfl
  have hbits : bits (word++[marker])
      (bits [false] (runPattern false (zeros+gap+1) true (2*bank))) =
      bits (code++[false]) (2*runPattern false gap true (2*bank)) := by
    rw [ht,← bits_append]
    congr 1
    simp [code,List.append_assoc]
  have hhead : base+word.length = origin := by dsimp [base]; omega
  have hhead' : base+code.length = origin+1+zeros := by
    simp only [code,List.length_append,List.length_singleton,List.length_replicate]
    dsimp [base]
    omega
  rw [hhead,← root_word_tail word marker [false]] at hw
  rw [hhead'] at hc
  rw [hbits] at hw
  exact hw.symm.trans hc

theorem fields_split (fields : List Nat) (i : Nat) (hi : i < fields.length) :
    ∃ before target after, fields = before++[target]++after ∧ before.length = i := by
  induction fields generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨[],x,xs,by simp,by simp⟩
    | succ i =>
      have hi' : i < xs.length := by simp only [List.length_cons] at hi; omega
      obtain ⟨before,target,after,heq,hlen⟩ := ih i hi'
      exact ⟨x::before,target,after,by simp [heq],by simp [hlen]⟩

theorem split_bank (before after : List Nat) (target : Nat) :
    IncrementSelector.blocksBits (before++[target]++after) 0 =
      IncrementSelector.blocksBits (before++[target]) (suffixBits after 0) := by
  rw [suffix_blank,IncrementMeaning.blocks_append]

/-- Complete action-ready tape, with both physical coordinates accounted for. -/
def ZeroLeaf (fields : List Nat) (rootHead anchor : Int) (e : Edge) (code : List Bool)
    (head : Int) (leftTail gap : Nat) (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  walk rootIndex code = some e ∧ head-code.length = rootHead ∧ head+2+gap = anchor ∧
  Rel (denote (rightWord treeRoot (-(code.length:Int)) code false rootLeft []) head leftTail
    (2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0))) physical

/-- A sufficiently spacious anchored root has a real next leaf, reached by
reading only the specified blank cells and without moving the anchor. -/
theorem anchored_zero_leaf (fields : List Nat) (rootHead anchor : Int)
    (physical : Shared.Beeping.Machines.Config 285) (h : AnchoredRoot fields rootHead anchor physical)
    (hspace : rootHead+328 ≤ anchor) :
    ∃ e code head leftTail gap, ZeroLeaf fields rootHead anchor e code head leftTail gap physical := by
  obtain ⟨word,marker,origin,leftTail,gap,hvalid,hhead,hanchor,hroot⟩ := h
  have hlen := valid_length_bound (word++[marker]) hvalid
  simp only [List.length_append,List.length_singleton] at hlen
  have hmargin : 164 ≤ gap := by omega
  obtain ⟨zeros,e,hzeros,_,hwalk⟩ := valid_zero_completion (word++[marker]) hvalid
  let remaining := gap-zeros-1
  let code := word++[marker]++List.replicate zeros false
  have heq : gap = zeros+remaining+1 := by dsimp [remaining]; omega
  rw [heq,extend_through_zeros] at hroot
  refine ⟨e,code,origin+1+zeros,leftTail,remaining,hwalk,?_,?_,hroot⟩
  · simp only [code,List.length_append,List.length_singleton,List.length_replicate]
    omega
  · dsimp [remaining] at *
    omega

/-- Each established bank update preserves or increases the number of
explicit fields, including all four cases of native half. -/
theorem update_length (e : Edge) (before after : List Nat) (h : Update e before after) :
    before.length ≤ after.length := by
  cases h with
  | inc before fields target => simp
  | dec before fields target =>
    cases target <;> simp [decrementFields,List.length_append]
  | half before fields newFields target hh =>
    cases hh <;> simp [List.length_append,List.length_replicate] <;> omega
  | beep fields => exact Nat.le_refl _
  | brk i fields => exact Nat.le_refl _
  | cont i fields => exact Nat.le_refl _

/-- A grammar-valid prefix, a finite actual zero margin, and at least fifteen
explicit fields imply that the next physical grammar action is enabled.
No assumption about the source algorithm is used. -/
theorem ready_of_good_root (fields : List Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hlen : 15 ≤ fields.length) (hgood : GoodRoot fields physical) :
    ∃ e, Ready e fields physical := by
  obtain ⟨word,marker,origin,leftTail,gap,hvalid,hgap,hroot⟩ := hgood
  obtain ⟨zeros,e,hzeros,hleaf,hwalk⟩ := valid_zero_completion (word++[marker]) hvalid
  let remaining := gap-zeros-1
  let code := word++[marker]++List.replicate zeros false
  have heq : gap = zeros+remaining+1 := by dsimp [remaining]; omega
  rw [heq,extend_through_zeros] at hroot
  change walk rootIndex code = some e at hwalk
  change Rel (denote (rightWord treeRoot (-(code.length:Int)) code false rootLeft [])
    (origin+1+zeros) leftTail
    (2*runPattern false remaining true (2*IncrementSelector.blocksBits fields 0))) physical at hroot
  cases e with
  | node i => simp [isLeaf] at hleaf
  | inc i =>
    have hi := (producer_increment_route code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    rw [split_bank] at hroot
    rw [← hbefore] at hwalk
    exact ⟨_,Ready.inc remaining target before after code false (origin+1+zeros) leftTail
      (2*runPattern false remaining true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits after 0)))
      physical hwalk rfl hroot⟩
  | dec i =>
    have hi := (producer_decrement_safe code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    rw [split_bank] at hroot
    rw [← hbefore] at hwalk
    exact ⟨_,Ready.dec remaining target before after code false (origin+1+zeros) leftTail
      (2*runPattern false remaining true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits after 0)))
      physical hwalk rfl hroot⟩
  | half i =>
    have hi := (producer_half_safe code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    rw [split_bank] at hroot
    rw [← hbefore] at hwalk
    exact ⟨_,Ready.half remaining target before after code false (origin+1+zeros) leftTail
      (2*runPattern false remaining true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits after 0)))
      physical hwalk rfl hroot⟩
  | beep =>
    exact ⟨_,Ready.beep remaining fields code false (origin+1+zeros) leftTail
      (2*runPattern false remaining true (2*IncrementSelector.blocksBits fields 0))
      physical hwalk rfl hroot⟩
  | brk i =>
    have hanchor : bitVal false+2*(2*runPattern false remaining true (2*IncrementSelector.blocksBits fields 0)) =
        runPattern false (remaining+2) true (2*IncrementSelector.blocksBits fields 0) := by
      simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    exact ⟨_,Ready.brk (remaining+2) i fields code false (origin+1+zeros) leftTail
      (2*runPattern false remaining true (2*IncrementSelector.blocksBits fields 0))
      physical hwalk hanchor hroot⟩
  | cont i =>
    have hanchor : bitVal false+2*(2*runPattern false remaining true (2*IncrementSelector.blocksBits fields 0)) =
        runPattern false (remaining+2) true (2*IncrementSelector.blocksBits fields 0) := by
      simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    exact ⟨_,Ready.cont (remaining+2) i fields code false (origin+1+zeros) leftTail
      (2*runPattern false remaining true (2*IncrementSelector.blocksBits fields 0))
      physical hwalk hanchor hroot⟩

end Shared.PNP.Record285.GrammarReady
