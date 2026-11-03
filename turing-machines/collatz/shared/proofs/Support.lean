import CollatzTM.Core

namespace CollatzTM

theorem finiteTape_put (t : Tape) (p : Int) (b : Bool)
    (h : FiniteTape t) : FiniteTape (put t p b) := by
  obtain ⟨lo, hi, h⟩ := h
  refine ⟨min lo p, max hi p, ?_⟩
  intro z hz
  have hlo : min lo p ≤ lo := Int.min_le_left _ _
  have hlp : min lo p ≤ p := Int.min_le_right _ _
  have hhi : hi ≤ max hi p := Int.le_max_left _ _
  have hhp : p ≤ max hi p := Int.le_max_right _ _
  have hp : z ≠ p := by omega
  simp only [put, if_neg hp]
  apply h z
  omega

theorem finiteTape_step (δ : S → Bool → Instr S) (c : Config S)
    (h : FiniteTape c.tape) : FiniteTape (step δ c).tape := by
  cases hs : c.state with
  | none => simpa [step, hs] using h
  | some q => simpa [step, hs] using
      finiteTape_put c.tape c.head (δ q (c.tape c.head)).write h

theorem finiteTape_run (δ : S → Bool → Instr S) (n : Nat) (c : Config S)
    (h : FiniteTape c.tape) : FiniteTape (run δ n c).tape := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih => exact ih (step δ c) (finiteTape_step δ c h)

end CollatzTM
