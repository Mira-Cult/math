import Shared.PNP.Record285.GrammarAnchoredIncrement

/-! Both ordinary decrement outcomes preserve the anchored grammar invariant. -/
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

theorem peel_length (xs : List Bool) (hz : false ∈ xs) :
    xs.length = (peel xs).1+1+(peel xs).2.length := by
  have h := congrArg List.length (peel_decomposition xs hz)
  simp only [List.length_append,List.length_replicate,List.length_cons] at h
  omega

/-- Both zero and positive decrement return a valid control prefix with the
same root and bank-anchor coordinates, including the exact bank update. -/
theorem decrement_anchored (before fields : List Nat) (target : Nat)
    (rootHead anchor head : Int) (leftTail gap : Nat) (code : List Bool)
    (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf (before++[target]++fields) rootHead anchor (.dec before.length)
      code head leftTail gap physical) :
    ∃ steps, 0 < steps ∧
      AnchoredRoot (decrementFields before fields target) rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  rw [split_bank] at hroot
  obtain ⟨hpath,steps,hpos,hresult,hquiet⟩ := PreparedDecrement.decrement_both_markers
    code gap target before fields hwalk false head leftTail
    (2*runPattern false gap true
      (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
    0 rfl physical hroot
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
    have hv : valid (q.2.reverse++[true]) := return_skip_one_valid code _ _ hwalk hpath
    have hehead : head-p.1-q.1-2-q.2.reverse.length = rootHead := by
      simp only [List.length_reverse]
      omega
    have heanchor : head-p.1-q.1-2+2+(p.1+q.1+gap+2 : Nat) = anchor := by omega
    refine ⟨steps,hpos,⟨q.2.reverse,true,head-p.1-q.1-2,leftTail,p.1+q.1+gap+2,
      hv,hehead,heanchor,?_⟩,hquiet⟩
    simpa only [DecrementComplete.resultConfig,decrementFields,suffix_blank,
      IncrementMeaning.blocks_append] using hresult
  | succ k =>
    have hv : valid (p.2.reverse++[true]) := return_path_valid code _ _ hwalk hpath
    have hehead : head-p.1-1-p.2.reverse.length = rootHead := by
      simp only [List.length_reverse]
      omega
    have heanchor : head-p.1-1+2+(p.1+gap+1 : Nat) = anchor := by omega
    refine ⟨steps,hpos,⟨p.2.reverse,true,head-p.1-1,leftTail,p.1+gap+1,
      hv,hehead,heanchor,?_⟩,hquiet⟩
    simpa only [DecrementComplete.resultConfig,decrementFields] using hresult

end Shared.PNP.Record285.GrammarReady
