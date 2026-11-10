import PASoundness.PeanoBetaCRTResidueSelect
import PASoundness.PeanoBetaCRTWitnessFresh
import PASoundness.PeanoBetaCRTUseAlignedRow
import PASoundness.PeanoBetaCRTFactorAlignment
import PASoundness.PeanoBetaCRTAlpha
import PASoundness.PeanoBetaCRTPrefixSubst

/-! A concrete conditional CRT successor: selection, rows and factors use
proved PA derivations. The future-inverse component remains an explicit PA
proof premise; no CRT induction or trace-existence theorem is asserted. -/
namespace PASoundness.PeanoBetaCRTConcreteSuccessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic
open PeanoBetaCRTInvariant PeanoBetaCRTAlignment

/-- An extra global condition may supply pairwise inverse facts for future
moduli; the known residue-totality and current-bound conditions are retained. -/
def assumptions (φ G : Peano.Formula) : Peano.Formula :=
  PeanoBetaCRTResidueSelect.assumptions φ ⊓ G

private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- One concrete PA successor update, assuming a separate proof of the future
inverse component. The selected residue and inverse witnesses are chosen within
the current code/product scope. -/
theorem successor (φ G : Peano.Formula) (hφ : NamesSafe φ)
    (hG : ∀ x ∈ ([9,10,13,14,15] : List Nat), x ∉ G.freeVarFinset)
    (hFuture : FormulaProves ((assumptions φ G).imp ((currentMatrix φ).imp
      ((rowAssumptions φ).imp
        (FOL.substAt (FOL.substAt nextFuture 11 alignedCode) 12 alignedProduct))))) :
    FormulaProves ((assumptions φ G).imp ((currentInvariant φ).imp (nextInvariant φ))) := by
  let S := assumptions φ G
  let W := rowAssumptions φ
  have fresh (x : Nat) (hx : x ∈ reservedNames) : x ∉ φ.freeVarFinset := by
    intro h
    exact hφ x h hx
  have hS (x : Nat) (hx : x ∈ ([9,10,13,14,15] : List Nat)) : x ∉ S.freeVarFinset := by
    have hx1 : x ≠ 1 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
    have hx2 : x ≠ 2 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
    have hx3 : x ≠ 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
    have hx7 : x ≠ 7 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
    have hx8 : x ≠ 8 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
    have hxr : x ∈ reservedNames := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [reservedNames]
    have ha := PeanoBetaCRTResidueSelect.assumptions_fresh φ x hx1 hx2 hx3 hx7 hx8 (fresh x hxr)
    simpa [S, assumptions, fv_inf] using And.intro ha (hG x hx)
  have hExists : FormulaProves (S.imp ((currentMatrix φ).imp
      (FOL.existsAt 13 (FOL.existsAt 14 (FOL.existsAt 15 W))))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hc : FOL.Context Peano.Axiom [currentMatrix φ,S] (currentMatrix φ) := FOL.Context.head _ _
    have hs : FOL.Context Peano.Axiom [currentMatrix φ,S] S :=
      FOL.Context.under (FOL.Context.head [] S) (currentMatrix φ)
    have ha : FOL.Context Peano.Axiom [currentMatrix φ,S]
        (PeanoBetaCRTResidueSelect.assumptions φ) := FOL.Context.conjunctionLeft hs
    exact .mp (.mp (.closed (PeanoBetaCRTResidueSelect.selected_exists_in_state φ hφ)) ha) hc
  have hUse := PeanoBetaCRTUseAlignedRow.use_aligned_row φ S hφ
    (PeanoBetaCRTFactorAlignment.factors_component φ S W) hFuture
  have h9 := fresh 9 (by simp [reservedNames])
  have h10 := fresh 10 (by simp [reservedNames])
  have h13 := fresh 13 (by simp [reservedNames])
  have h14 := fresh 14 (by simp [reservedNames])
  have h15 := fresh 15 (by simp [reservedNames])
  have hc13 := PeanoBetaCRTWitnessFresh.current_fresh φ 13 (by simp) h13
  have hc14 := PeanoBetaCRTWitnessFresh.current_fresh φ 14 (by simp) h14
  have hc15 := PeanoBetaCRTWitnessFresh.current_fresh φ 15 (by simp) h15
  have ht13 := PeanoBetaCRTWitnessFresh.next_fresh φ 13 (by simp) h13
  have ht14 := PeanoBetaCRTWitnessFresh.next_fresh φ 14 (by simp) h14
  have ht15 := PeanoBetaCRTWitnessFresh.next_fresh φ 15 (by simp) h15
  exact PeanoBetaCRTDependentLift.dependent_crt_successor φ S W 13 14 15 h9 h10
    (hS 9 (by simp)) (hS 10 (by simp))
    (hS 13 (by simp)) hc13 ht13 (hS 14 (by simp)) hc14 ht14
    (hS 15 (by simp)) hc15 ht15 hExists hUse

/-- Re-express the concrete conditional successor as the literal substitution
instance required by PA induction. The future update remains explicit. -/
theorem literal_successor (φ G : Peano.Formula) (hφ : NamesSafe φ)
    (hG : ∀ x ∈ ([9,10,13,14,15] : List Nat), x ∉ G.freeVarFinset)
    (hFuture : FormulaProves ((assumptions φ G).imp ((currentMatrix φ).imp
      ((rowAssumptions φ).imp
        (FOL.substAt (FOL.substAt nextFuture 11 alignedCode) 12 alignedProduct))))) :
    FormulaProves ((assumptions φ G).imp ((currentInvariant φ).imp
      (FOL.substAt (currentInvariant φ) 7 (succ (.var 7))))) := by
  have fresh (x : Nat) (hx : x ∈ reservedNames) : x ∉ φ.freeVarFinset := by
    intro h; exact hφ x h hx
  have h7 := fresh 7 (by simp [reservedNames])
  have h9 := fresh 9 (by simp [reservedNames])
  have h10 := fresh 10 (by simp [reservedNames])
  have h11 := fresh 11 (by simp [reservedNames])
  have h12 := fresh 12 (by simp [reservedNames])
  have hstep := successor φ G hφ hG hFuture
  have halpha := PeanoBetaCRTAlpha.alpha_next φ h9 h10 h11 h12
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let S := assumptions φ G
  have ha : FOL.Context Peano.Axiom [currentInvariant φ,S] S :=
    FOL.Context.under (FOL.Context.head [] S) (currentInvariant φ)
  have hc : FOL.Context Peano.Axiom [currentInvariant φ,S] (currentInvariant φ) := FOL.Context.head _ _
  have hn : FOL.Context Peano.Axiom [currentInvariant φ,S] (nextInvariant φ) :=
    .mp (.mp (.closed hstep) ha) hc
  have hi : FOL.Context Peano.Axiom [currentInvariant φ,S] (invariantAt φ (succ (.var 7))) :=
    .mp (.closed halpha) hn
  simpa only [currentInvariant, PeanoBetaCRTPrefixSubst.invariant_succ φ h7] using hi

end PASoundness.PeanoBetaCRTConcreteSuccessor
