import Shared.PNP.Record285.GrammarExactDuration

/-! Bind the generic anchored invariant to exact physical operation times. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.CleanBank

theorem increment_exact (before fields : List Nat) (target : Nat)
    (rootHead anchor head : Int) (leftTail gap : Nat) (code : List Bool)
    (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf (before++[target]++fields) rootHead anchor (.inc before.length)
      code head leftTail gap physical) :
    let steps := incTime code gap target before fields
    0 < steps ∧
      AnchoredRoot (before++[target+1]++fields) rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  rw [split_bank] at hroot
  have hp := increment_returns_root_physical gap target before fields code hwalk head leftTail 0 physical hroot
  let p := peel code.reverse
  let word := p.2.reverse
  have hpath := (increment_return_path code before.length hwalk).1
  have hvalid : valid (word++[true]) := return_path_valid code _ _ hwalk hpath
  have hlen := (increment_return_path code before.length hwalk).2.2
  have hehead : head-p.1-1-word.length = rootHead := by
    dsimp [word,p] at *
    simp only [List.length_append,List.length_singleton] at hlen
    omega
  have heanchor : head-p.1-1+2+(p.1+gap+1 : Nat) = anchor := by omega
  refine ⟨hp.2.2,⟨word,true,head-p.1-1,leftTail,p.1+gap+1,hvalid,hehead,heanchor,?_⟩,hp.2.1⟩
  simpa only [incTime,IncrementMeaning.blocks_append] using hp.1

theorem decrement_exact (before fields : List Nat) (target : Nat)
    (rootHead anchor head : Int) (leftTail gap : Nat) (code : List Bool)
    (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf (before++[target]++fields) rootHead anchor (.dec before.length)
      code head leftTail gap physical) :
    ∃ steps, Duration (.dec before.length) (before++[target]++fields) code gap steps ∧
      0 < steps ∧ AnchoredRoot (decrementFields before fields target) rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  rw [split_bank] at hroot
  let p := peel code.reverse
  let q := peel p.2
  have hz := decrement_reverse_zeros code before.length hwalk
  have hl1 := peel_length code.reverse hz.1
  have hl2 := peel_length p.2 hz.2
  simp only [List.length_reverse] at hl1
  change code.length = p.1+1+p.2.length at hl1
  change p.2.length = q.1+1+q.2.length at hl2
  cases target with
  | zero =>
    have hp := DecrementZeroRoot.bound_root_zero_returns_root_physical code gap before hwalk
      head leftTail (suffixBits fields 0) physical hroot
    have hv : valid (q.2.reverse++[true]) := return_skip_one_valid code _ _ hwalk hp.2.1
    have hehead : head-p.1-q.1-2-q.2.reverse.length = rootHead := by
      simp only [List.length_reverse]; omega
    have heanchor : head-p.1-q.1-2+2+(p.1+q.1+gap+2 : Nat) = anchor := by omega
    refine ⟨decZeroTime code gap before,Duration.decZero before fields code gap,hp.2.2.2.2,
      ⟨q.2.reverse,true,head-p.1-q.1-2,leftTail,p.1+q.1+gap+2,hv,hehead,heanchor,?_⟩,hp.2.2.2.1⟩
    simpa only [decZeroTime,decrementFields,suffix_blank,IncrementMeaning.blocks_append] using hp.2.2.1
  | succ k =>
    have hp := DecrementNonzeroRoot.bound_root_nonzero_returns_root_physical code gap k before fields hwalk
      head leftTail 0 physical hroot
    have hv : valid (p.2.reverse++[true]) := return_path_valid code _ _ hwalk hp.2.1
    have hehead : head-p.1-1-p.2.reverse.length = rootHead := by simp only [List.length_reverse]; omega
    have heanchor : head-p.1-1+2+(p.1+gap+1 : Nat) = anchor := by omega
    refine ⟨decPositiveTime code gap k before fields,Duration.decPositive before fields k code gap,hp.2.2.2.2,
      ⟨p.2.reverse,true,head-p.1-1,leftTail,p.1+gap+1,hv,hehead,heanchor,?_⟩,hp.2.2.2.1⟩
    simpa only [decPositiveTime,decrementFields] using hp.2.2.1

theorem half_exact (before fields : List Nat) (target : Nat)
    (rootHead anchor head : Int) (leftTail gap : Nat) (code : List Bool)
    (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf (before++[target]++fields) rootHead anchor (.half before.length)
      code head leftTail gap physical) :
    ∃ steps newFields, Duration (.half before.length) (before++[target]++fields) code gap steps ∧
      0 < steps ∧ HalfFields before fields target newFields ∧
      AnchoredRoot newFields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  rw [split_bank] at hroot
  cases target with
  | zero =>
    have hp := HalfEven.bound_root_zero_returns_root_physical code gap before fields hwalk
      head leftTail 0 physical hroot
    refine ⟨halfZeroTime code gap before,_,Duration.halfZero before fields code gap,hp.2.2.2,
      HalfFields.zero,?_,hp.2.2.1⟩
    apply even_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hp.1
    simpa only [halfZeroTime,HalfComplete.evenConfig,suffix_blank,IncrementMeaning.blocks_append] using hp.2.1
  | succ target =>
    cases target with
    | zero =>
      have hp := HalfOne.bound_root_one_returns_root_physical code gap before fields hwalk
        head leftTail 0 physical hroot
      refine ⟨halfOneTime code gap before fields,_,Duration.halfOne before fields code gap,hp.2.2.2,
        HalfFields.one,?_,hp.2.2.1⟩
      apply odd_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hp.1
      simpa only [halfOneTime,HalfComplete.oddConfig] using hp.2.1
    | succ k =>
      by_cases heven : k % 2 = 0
      · let n := k/2
        have hk : k = 2*n := by dsimp [n]; omega
        have ht : k+1+1 = 2*n+2 := by omega
        rw [ht] at hroot ⊢
        have hinput : Rel (rootEntry code head leftTail
            (2*runPattern false gap true
              (2*IncrementSelector.blocksBits (before++[2*n+2]) (suffixBits fields (2^n*0))))) physical := by
          simpa only [Nat.mul_zero,rootEntry] using hroot
        have hp := HalfEvenPositive.bound_root_returns_root_physical code gap n before fields hwalk
          head leftTail 0 physical hinput
        refine ⟨halfEvenTime code gap n before fields,_,Duration.halfEven before fields n code gap,hp.2.2.2,
          HalfFields.even n,?_,hp.2.2.1⟩
        apply even_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hp.1
        simpa only [halfEvenTime,HalfComplete.evenConfig] using hp.2.1
      · let n := k/2
        have hk : k = 2*n+1 := by dsimp [n]; omega
        have ht : k+1+1 = 2*n+3 := by omega
        rw [ht] at hroot ⊢
        have hinput : Rel (rootEntry code head leftTail
            (2*runPattern false gap true
              (2*IncrementSelector.blocksBits (before++[2*n+3]) (suffixBits fields (2^n*(2*0)))))) physical := by
          simpa only [Nat.mul_zero,rootEntry] using hroot
        have hp := HalfOdd.bound_root_odd_returns_root_physical code gap n before fields hwalk
          head leftTail 0 physical hinput
        refine ⟨halfOddTime code gap n before fields,_,Duration.halfOdd before fields n code gap,hp.2.2.2.2,
          HalfFields.odd n,?_,hp.2.2.2.1⟩
        apply odd_config_anchored code before.length gap _ rootHead anchor head leftTail _ hwalk hhead hanchor hp.2.1
        simpa only [halfOddTime,HalfComplete.oddConfig] using hp.2.2.1

end Shared.PNP.Record285.GrammarExact
