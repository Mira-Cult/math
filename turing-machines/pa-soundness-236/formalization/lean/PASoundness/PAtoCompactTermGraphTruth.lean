import PASoundness.PAtoCompactTermRenamingSemantics

/-! Standard-HF truth of generated term graphs. This does not establish that
K proves existence of the represented witnesses or arithmetic axioms. -/
namespace PASoundness.PAtoCompactTermGraphTruth

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermRenamingSemantics PASoundness.HFCoding
open PASoundness.CompactMatrix (Environment update)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- A generated domain guard recognizes precisely the finite ordinal codes. -/
theorem domainAt_iff (base x : Nat) (hx : x < base + 2) (ρ : Environment) :
    (domainAt base x).Realize ρ ↔ ∃ n, ρ x = (ordinal n).code := by
  have hc : (domainAt base x).encode =
      PASoundness.PAtoCompactCandidateExact.candidateCode x
        (base+32) (base+33) (base+34) (base+35)
        (base+36) (base+37) (base+38) (base+39) := by rfl
  have hn : [x,base+32,base+33,base+34,base+35,base+36,base+37,base+38,base+39].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    repeat' apply And.intro
    all_goals omega
  rw [← Formula.encode_realize, hc]
  exact PASoundness.PAtoCompactCandidateStandard.candidate_standard_iff x
    (base+32) (base+33) (base+34) (base+35) (base+36) (base+37) (base+38) (base+39)
    ρ hn

theorem andF_realize (a b : Formula) (ρ : Environment) :
    (andF a b).Realize ρ ↔ a.Realize ρ ∧ b.Realize ρ := by
  classical
  simp [andF, CompactNamed.Formula.not, CompactNamed.Formula.Realize]

/-- Every variable of a selected function child occurs in its parent term. -/
theorem child_var {α : Type} [DecidableEq α] {l : Nat}
    (f : Peano.FunctionSymbol l) (ts : Fin l → Peano.language.Term α)
    (i : Fin l) (a : α) (h : a ∈ (ts i).varFinset) :
    a ∈ (FirstOrder.Language.Term.func f ts).varFinset := by
  simp only [FirstOrder.Language.Term.varFinset, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  exact ⟨i,h⟩

/-- The generated graph explicitly guards its result with the candidate
predicate in every source term constructor. -/
theorem termGraph_has_domain {α : Type} (varName : α → Nat)
    (t : Peano.language.Term α) (out base : Nat) (ρ : Environment)
    (h : (termGraph varName t out base).Realize ρ) : (domainAt base out).Realize ρ := by
  cases t with
  | var v => exact ((andF_realize _ _ ρ).mp h).1
  | func f ts =>
    cases f <;> exact ((andF_realize _ _ ρ).mp h).1

/-- Literal variable graph truth for ordinal input/output, with the source
variable name strictly below its result label. -/
theorem variable_graph_truth {α : Type} (varName : α → Nat) (a : α)
    (out base n k : Nat) (ρ : Environment)
    (hname : varName a < out) (hout : out < base)
    (hin : ρ (varName a) = (ordinal n).code) (hresult : ρ out = (ordinal k).code) :
    (termGraph varName (.var a) out base).Realize ρ ↔ k = n := by
  change (andF (domainAt base out) (equivAt base (varName a) out)).Realize ρ ↔ k = n
  rw [andF_realize]
  have hd := domainAt_ordinal base out k (by omega) ρ hresult
  have he := equivAt_ordinal base (varName a) out n k (by omega) (by omega) (by omega) ρ hin hresult
  rw [he]
  simp [hd, eq_comm]

/-- Literal zero graph truth on an ordinal output. -/
theorem zero_graph_truth {α : Type} (varName : α → Nat)
    (out base k : Nat) (ρ : Environment) (hout : out < base)
    (hresult : ρ out = (ordinal k).code) :
    (termGraph varName (.func .zero Fin.elim0) out base).Realize ρ ↔ k = 0 := by
  change (andF (domainAt base out) (zeroAt base out)).Realize ρ ↔ k = 0
  rw [andF_realize, zeroAt_iff base out (by omega) ρ, hresult]
  have hd := domainAt_ordinal base out k (by omega) ρ hresult
  simp only [hd, true_and]
  constructor
  · intro h
    exact ordinal_code_strictMono.injective h
  · intro h
    subst k
    rfl

/-- Successor node truth, given truth of its actual generated child graph at
each possible ordinal witness under the corresponding updated assignment.
The existential witness is shown to be an ordinal using the child's explicit
domain guard. The premise is a child semantic hypothesis, not K totality. -/
theorem successor_graph_truth {α : Type} (varName : α → Nat)
    (child : Peano.language.Term α) (out base n k : Nat) (ρ : Environment)
    (hout : out < base) (hresult : ρ out = (ordinal k).code)
    (childTruth : ∀ j, (termGraph varName child base (base+64)).Realize
        (update ρ base (ordinal j).code) ↔ j = n) :
    (termGraph varName (.func .succ ![child]) out base).Realize ρ ↔ k = n + 1 := by
  change (andF (domainAt base out) (.ex base
    (andF (termGraph varName child base (base+64)) (succAt base base out)))).Realize ρ ↔ _
  rw [andF_realize]
  have hd := domainAt_ordinal base out k (by omega) ρ hresult
  simp only [hd, true_and, CompactNamed.Formula.Realize]
  constructor
  · rintro ⟨w, hw⟩
    have hc : (termGraph varName child base (base+64)).Realize (update ρ base w) :=
      ((andF_realize _ _ _).mp hw).1
    have hs := ((andF_realize _ _ _).mp hw).2
    have guard := termGraph_has_domain varName child base (base+64) _ hc
    obtain ⟨j,hj⟩ := (domainAt_iff (base+64) base (by omega) _).mp guard
    have heq : w = (ordinal j).code := by simpa [update] using hj
    subst w
    have hchild := (childTruth j).mp hc
    have hs' := (succAt_ordinal base base out j k (by omega) (by omega) (by omega)
      (update ρ base (ordinal j).code) (by simp [update]) (by simpa [update, Nat.ne_of_lt hout] using hresult)).mp hs
    omega
  · intro hk
    refine ⟨(ordinal n).code, ?_⟩
    apply (andF_realize _ _ _).mpr
    refine ⟨(childTruth n).mpr rfl, ?_⟩
    apply (succAt_ordinal base base out n k (by omega) (by omega) (by omega)
      (update ρ base (ordinal n).code) (by simp [update]) (by simpa [update, Nat.ne_of_lt hout] using hresult)).mpr
    exact hk

end PASoundness.PAtoCompactTermGraphTruth

#print axioms PASoundness.PAtoCompactTermGraphTruth.domainAt_iff
#print axioms PASoundness.PAtoCompactTermGraphTruth.variable_graph_truth
#print axioms PASoundness.PAtoCompactTermGraphTruth.zero_graph_truth
#print axioms PASoundness.PAtoCompactTermGraphTruth.successor_graph_truth
