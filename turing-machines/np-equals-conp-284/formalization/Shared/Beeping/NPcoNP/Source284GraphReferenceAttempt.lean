import Shared.Beeping.NPcoNP.Source284GraphReferenceBranch
import Shared.Beeping.NPcoNP.Source284GraphAttemptInit

/-! Compose a nonempty reference-certificate branch with the graph's
bounded-attempt initialization. This is a supplied-register result; no
physical reachability or evaluator-loop correctness is assumed. -/

namespace Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphReferenceBranch

abbrev Bank := PASoundness.RegisterMachine.Bank 12

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The source's attempted reference configuration after choosing the next
descending certificate, clearing its right half and installing state one. -/
def ready (b : Bank) : Bank :=
  let cert := b 7 - 1
  write (write (write (write (write b 7 cert) 8 cert) 1 0) 2 1) 11 (b 5)

theorem ready_registers (b : Bank) :
    ready b 7 = b 7 - 1 ∧ ready b 8 = b 7 - 1 ∧
    ready b 1 = 0 ∧ ready b 2 = 1 ∧ ready b 11 = b 5 ∧
    (∀ i, i ≠ 1 → i ≠ 2 → i ≠ 7 → i ≠ 8 → i ≠ 11 → ready b i = b i) := by
  simp only [ready, write]
  refine ⟨by simp, by simp, by simp, by simp, by simp, ?_⟩
  intro i h1 h2 h7 h8 h11
  simp [h1,h2,h7,h8,h11]

/-- A positive certificate counter yields the next reference attempt in a
positive silent segment. The zero clock-accumulator premise prevents earlier
data from being silently folded into this attempt's source clock. -/
theorem reference_attempt (b : Bank) (h : 0 < b 7)
    (h9 : b 9 = 0) (h10 : b 10 = 0) (h11 : b 11 = 0) :
    let d := (7*(b 7-1)+b 8+5) + (b 1+b 2+7*b 5+6)
    0 < d ∧ target.system.advance ⟨31,b⟩ d = ⟨50,ready b⟩ ∧
      target.system.wordFrom ⟨31,b⟩ d = [] := by
  let m := b 7 - 1
  let mid := Source284GraphReferenceBranch.bank b m m 0 0
  let d₁ := 7*m+b 8+5
  let d₂ := b 1+b 2+7*b 5+6
  have hs : SilentSegment ⟨31,b⟩ ⟨40,mid⟩ d₁ :=
    (branch_nonzero b h h9 h10).2
  have hi := Source284GraphAttemptInit.attempt_init mid
  have hmid1 : mid 1 = b 1 := by simp [mid, Source284GraphReferenceBranch.bank]
  have hmid2 : mid 2 = b 2 := by simp [mid, Source284GraphReferenceBranch.bank]
  have hmid5 : mid 5 = b 5 := by simp [mid, Source284GraphReferenceBranch.bank]
  have hmid9 : mid 9 = 0 := by simp [mid, Source284GraphReferenceBranch.bank]
  have hmid10 : mid 10 = 0 := by simp [mid, Source284GraphReferenceBranch.bank]
  have hmid11 : mid 11 = 0 := by simp [mid, Source284GraphReferenceBranch.bank, h11]
  have hout : Source284GraphAttemptInit.bank (write (write mid 1 0) 2 1)
      (mid 9 + mid 5) 0 0 (mid 11 + (mid 10 + mid 5)) = ready b := by
    funext i
    fin_cases i <;> simp [mid, m, Source284GraphReferenceBranch.bank,
      Source284GraphAttemptInit.bank, ready, write, h9, h10, h11]
  have ht : mid 1+mid 2+7*mid 5+2*mid 9+2*mid 10+6 = d₂ := by
    simp [hmid1,hmid2,hmid5,hmid9,hmid10,d₂]
  have hiSegment : SilentSegment ⟨40,mid⟩ ⟨50,ready b⟩ d₂ := by
    constructor
    · rw [← ht, ← hout]
      exact hi.1
    · rw [← ht]
      exact hi.2.1
  have total := cat hs hiSegment
  exact ⟨by omega, total.1, total.2⟩

end Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
