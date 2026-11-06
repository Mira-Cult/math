import Shared.ComplexityBridge.TM2Transport

/-! Package exact TM2 time transport into the canonical polynomial-time model.
The finite alphabet choices are mathematical and do not reify numeric code. -/
namespace Shared.ComplexityBridge.TM2Symbols

/-- Normalize all stack alphabets without changing the computed function,
external encodings, or time polynomial. -/
noncomputable def normalizePoly {α β αΓ βΓ : Type} [Finite βΓ]
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) :
    Turing.TM2ComputableInPolyTime ea eb f := by
  letI : Finite (h.tm.Γ h.tm.k₁) := output_finite h.toTM2ComputableAux
  refine ⟨normalizeAux h.toTM2ComputableAux, h.time, ?_⟩
  intro a
  have hh := outputsInTimeIO h.tm (List.map h.inputAlphabet.invFun (ea a))
    (List.map h.outputAlphabet.invFun (eb (f a))) (h.time.eval (ea a).length) (h.outputsFun a)
  have hi : liftInputIO h.tm (List.map h.inputAlphabet.invFun (ea a)) =
      (ea a).map ((inputEquiv h.tm) ∘ h.inputAlphabet.invFun) := by
    change (List.map (inputEquiv h.tm) (List.map h.inputAlphabet.invFun (ea a))) = _
    exact List.map_map
  have ho : liftOutputIO h.tm (List.map h.outputAlphabet.invFun (eb (f a))) =
      (eb (f a)).map ((outputEquiv h.tm) ∘ h.outputAlphabet.invFun) := by
    change (List.map (outputEquiv h.tm) (List.map h.outputAlphabet.invFun (eb (f a)))) = _
    exact List.map_map
  rw [hi, ho] at hh
  exact hh

/-- The normalized witness retains the original polynomial. -/
theorem normalizePoly_time {α β αΓ βΓ : Type} [Finite βΓ]
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) : (normalizePoly h).time = h.time := rfl

/-- Every normalized stack alphabet is finite, including non-I/O stacks. -/
theorem normalizePoly_finite {α β αΓ βΓ : Type} [Finite βΓ]
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) (k : (normalizePoly h).tm.K) :
    Finite ((normalizePoly h).tm.Γ k) := by
  let : Finite (h.tm.Γ h.tm.k₁) := output_finite h.toTM2ComputableAux
  exact finite_alphabetIO h.tm k

/-- Every canonical polynomial-time function admits an all-finite-stack witness. -/
theorem polyTime_finite_witness {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (h : ComplexityTheory.IsPolyTime f) :
    ∃ c : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := α))
        (BitstringEncoding.bitEncode (α := β)) f,
      ∀ k : c.tm.K, Finite (c.tm.Γ k) := by
  obtain ⟨c⟩ := h
  exact ⟨normalizePoly c, normalizePoly_finite c⟩

end Shared.ComplexityBridge.TM2Symbols
