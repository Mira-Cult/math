import Shared.ComplexityBridge.TM2Symbols

/-! Finite-alphabet TM2 construction retaining the full input and output
alphabets when the output alphabet is finite. This is a mathematical
construction, not effective code reification or a polynomial model bridge. -/
namespace Shared.ComplexityBridge.TM2Symbols
open Turing.TM2

/-- Include the entire finite output alphabet as well as the input alphabet.
This enlarges the previous support set only at the designated output stack. -/
def allowedIO (tm : Turing.FinTM2) (k : tm.K) : Set (tm.Γ k) := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  exact allowed tm k ∪ if k = tm.k₁ then Set.univ else ∅

theorem allowedIO_finite (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (k : tm.K) :
    (allowedIO tm k).Finite := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  by_cases h : k = tm.k₁
  · subst k
    exact Set.toFinite _
  · simpa [allowedIO, h] using allowed_finite tm k

theorem finite_alphabetIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (k : tm.K) :
    Finite {a : tm.Γ k // a ∈ allowedIO tm k} := (allowedIO_finite tm k).to_subtype

theorem input_mem (tm : Turing.FinTM2) (a : tm.Γ tm.k₀) : a ∈ allowedIO tm tm.k₀ := by
  left
  simp [allowed]

theorem output_mem (tm : Turing.FinTM2) (a : tm.Γ tm.k₁) : a ∈ allowedIO tm tm.k₁ := by
  right
  simp [allowedIO]

def inputEquiv (tm : Turing.FinTM2) : tm.Γ tm.k₀ ≃ {a : tm.Γ tm.k₀ // a ∈ allowedIO tm tm.k₀} where
  toFun a := ⟨a, input_mem tm a⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

def outputEquiv (tm : Turing.FinTM2) : tm.Γ tm.k₁ ≃ {a : tm.Γ tm.k₁ // a ∈ allowedIO tm tm.k₁} where
  toFun a := ⟨a, output_mem tm a⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

def restrictProgramIO (tm : Turing.FinTM2) (l : tm.Λ) :
    Stmt (fun k => {a : tm.Γ k // a ∈ allowedIO tm k}) tm.Λ tm.σ :=
  restrictStmt (allowedIO tm) (tm.m l)
    (fun k _ ha => Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨l, ha⟩)))

noncomputable def normalizedIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] : Turing.FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := fun k => {a : tm.Γ k // a ∈ allowedIO tm k}
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := @Fintype.ofFinite _ (finite_alphabetIO tm tm.k₀)
  m := restrictProgramIO tm

theorem stepIO (tm : Turing.FinTM2) [Finite (tm.Γ tm.k₁)] (c : (normalizedIO tm).Cfg) :
    ((normalizedIO tm).step c).map (eraseCfg (allowedIO tm)) =
      tm.step (eraseCfg (allowedIO tm) c) := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
    simp only [Turing.FinTM2.step, Turing.TM2.step, Option.map_some, eraseCfg, normalizedIO, restrictProgramIO]
    exact congrArg some (restrict_stepAux (allowedIO tm) (tm.m l) _ v S)


/-- A finite external output alphabet supplies finiteness of the original
output stack alphabet via the bundled alphabet equivalence. -/
theorem output_finite {αΓ βΓ : Type} [Finite βΓ]
    (aux : Turing.TM2ComputableAux αΓ βΓ) : Finite (aux.tm.Γ aux.tm.k₁) :=
  Finite.of_equiv βΓ aux.outputAlphabet.symm

/-- Preserve both external alphabet types while replacing stack alphabets.
No output or running-time theorem is asserted by this auxiliary construction. -/
noncomputable def normalizeAux {αΓ βΓ : Type} [Finite βΓ]
    (aux : Turing.TM2ComputableAux αΓ βΓ) : Turing.TM2ComputableAux αΓ βΓ := by
  letI : Finite (aux.tm.Γ aux.tm.k₁) := output_finite aux
  exact {
    tm := normalizedIO aux.tm
    inputAlphabet := (inputEquiv aux.tm).symm.trans aux.inputAlphabet
    outputAlphabet := (outputEquiv aux.tm).symm.trans aux.outputAlphabet
  }


end Shared.ComplexityBridge.TM2Symbols
