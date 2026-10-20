import CollatzTM.Core
import CollatzTM.Arithmetic

namespace CollatzTM

/-- Any finite halt has a first transition count, with a full configuration
endpoint and no earlier halt. This does not assert any machine halts. -/
theorem halts_first (δ : S → Bool → Instr S) (a : Config S) (h : Halts δ a) :
    ∃ t b, Reaches δ t a b ∧ b.state = none := by
  obtain ⟨t, ht, hfirst⟩ := Arithmetic.first_index h
  exact ⟨t, run δ t a, ⟨rfl, hfirst⟩, ht⟩

end CollatzTM
