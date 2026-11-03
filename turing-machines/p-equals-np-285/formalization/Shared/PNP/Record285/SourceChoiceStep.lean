import Shared.PNP.Record285.SourceVirtualLoop

/-! The positive-clock virtual-step prefix: consume one clock unit and the
low choice bit, with exact full-bank effects and no events. The remaining
record decoding and transition update are not proved here. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceChoiceStep
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch

def choiceBank (bank : Nat → Nat) : Nat → Nat :=
  let b := update (.half 0) (update (.dec 20) bank)
  if bank 0 % 2 = 0 then b else update (.inc 3) b

def choiceTime (bank : Nat → Nat) : Nat := if bank 0 % 2 = 0 then 2 else 3

/-- The actual checked graph implements the positive-clock choice prefix for
arbitrary banks and either parity. -/
theorem choice_prefix (bank : Nat → Nat) (hp : 0 < bank 20) :
    Silent originalRows ⟨35,bank⟩ ⟨38,choiceBank bank⟩ (choiceTime bank) := by
  let b1 := update (.dec 20) bank
  let b2 := update (.half 0) b1
  have hn : bank 20 ≠ 0 := by omega
  have h35 : step originalRows ⟨35,bank⟩ = (⟨36,b1⟩,false) := by
    simp [step,originalRows,observe,hn,b1]
  have h35s : Silent originalRows ⟨35,bank⟩ ⟨36,b1⟩ 1 := silent_one _ _ _ h35
  have hv : b1 0 = bank 0 := by simp [b1,update]
  by_cases he : bank 0 % 2 = 0
  · have h36 : step originalRows ⟨36,b1⟩ = (⟨38,b2⟩,false) := by
      simp [step,originalRows,observe,hv,he,b2]
    have h := silent_trans originalRows _ _ _ 1 1 h35s (silent_one _ _ _ h36)
    simpa [choiceTime,choiceBank,he,b2,b1] using h
  · have h36 : step originalRows ⟨36,b1⟩ = (⟨37,b2⟩,false) := by
      simp [step,originalRows,observe,hv,he,b2]
    have h37 : step originalRows ⟨37,b2⟩ = (⟨38,update (.inc 3) b2⟩,false) := by
      simp [step,originalRows,observe]
    have h := silent_trans originalRows _ _ _ 1 1 h35s (silent_one _ _ _ h36)
    have h := silent_trans originalRows _ _ _ 2 1 h (silent_one _ _ _ h37)
    simpa [choiceTime,choiceBank,he,b2,b1] using h

/-- Exact effects on the complete bank, including arbitrary retained cells. -/
theorem choiceBank_read (bank : Nat → Nat) (j : Nat) :
    choiceBank bank j = if j = 20 then bank 20-1 else if j = 0 then bank 0/2
      else if j = 3 then bank 3 + bank 0%2 else bank j := by
  by_cases he : bank 0 % 2 = 0
  · by_cases h20 : j = 20
    · subst j; simp [choiceBank,he,update]
    · by_cases h0 : j = 0
      · subst j; simp [choiceBank,he,update]
      · by_cases h3 : j = 3
        · subst j; simp [choiceBank,he,update]
        · simp [choiceBank,he,update,h20,h0,h3]
  · have ho : bank 0 % 2 = 1 := by omega
    by_cases h20 : j = 20
    · subst j; simp [choiceBank,he,update]
    · by_cases h0 : j = 0
      · subst j; simp [choiceBank,he,update]
      · by_cases h3 : j = 3
        · subst j; simp [choiceBank,ho,update]
        · simp [choiceBank,he,update,h20,h0,h3]

/-- The decoded selector and remaining choice stream match the input to
`Source.simStep`; the clock is decreased once. -/
theorem choice_matches_virtual (bank : Nat → Nat) :
    choiceBank bank 20 = bank 20-1 ∧
    choiceBank bank 0 = (referenceSimState bank).choices/2 ∧
    choiceBank bank 3 = (referenceSimState bank).selector + (referenceSimState bank).choices%2 ∧
    (∀ j, j ≠ 20 → j ≠ 0 → j ≠ 3 → choiceBank bank j = bank j) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa using choiceBank_read bank 20
  · simpa [referenceSimState] using choiceBank_read bank 0
  · simpa [referenceSimState] using choiceBank_read bank 3
  · intro j h20 h0 h3
    simpa [h20,h0,h3] using choiceBank_read bank j

/-- A reachable positive-clock prefix transfers to the exact grammar with a
strictly advancing boundary, full-bank equality and no marked event. -/
theorem choice_prefix_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20) :
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+choiceTime bank))
    r.boundary t < r.boundary (t+choiceTime bank) ∧
    r.boundary (t+choiceTime bank) ≤ r.boundary t + 32*choiceTime bank ∧
    PreControlGrammar.positions[38]? = some g.pc ∧ g.bank = choiceBank bank ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+choiceTime bank) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have ht : 0 < choiceTime bank := by unfold choiceTime; split <;> omega
  exact transfer_silent_graph t (choiceTime bank) 35 38 bank (choiceBank bank)
    hstate ht (choice_prefix bank hp)

end Shared.PNP.Record285.SourceChoiceStep
