import PASoundness.PAtoCompactTermSubstInduction
import PASoundness.PAtoCompactTermSubstSuccLeaf

/-! Graph substitution by a successor term. The graph witness remains inside
the guard, and all changes of allocation base are constructed in K. -/
namespace PASoundness.PAtoCompactTermSubstSuccessorInduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactTermSubstInduction
open PASoundness.PAtoCompactTermSubstSuccLeaf PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def succTerm (u : Peano.Term) : Peano.Term := .func .succ ![u]

def variableSubst (x q : Nat) (a : Nat) : Peano.Term :=
  if a = x then .var q else .var a

def successorSubst (x : Nat) (u : Peano.Term) (a : Nat) : Peano.Term :=
  if a = x then succTerm u else .var a

def retained (g : Formula) (u : Peano.Term) (q d : Nat) : Formula :=
  andF g (termGraph id (succTerm u) q d)

/-- At the replaced variable, rebase the retained graph and candidate
proofs, then use the successor graph's forward transport and functionality.
No target-label freshness is assumed; `q` and `out` may coincide. -/
noncomputable def successor_leaf (g : Formula) (u : Peano.Term) (hu : UnaryTerm u)
    (q d b out : Nat) (hqd : q < d) (hq : q < b) (hout : out < b)
    (hud : ∀ a ∈ u.varFinset, a < d) (hub : ∀ a ∈ u.varFinset, a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode)) :
    Align (retained g u q d) (.var q) (succTerm u) b out := by
  let H := retained g u q d
  let G := (termGraph id (succTerm u) q d).encode
  let Gb := (termGraph id (succTerm u) q b).encode
  let V := (termGraph id (.var q : Peano.Term) out b).encode
  let T := (termGraph id (succTerm u) out b).encode
  have hvd : ∀ a ∈ (succTerm u).varFinset, id a < d := by
    intro a ha; apply hud a; simpa [succTerm, Term.varFinset] using ha
  have hvb : ∀ a ∈ (succTerm u).varFinset, id a < b := by
    intro a ha; apply hub a; simpa [succTerm, Term.varFinset] using ha
  have hmove := (termGraph_base_transport id (succTerm u) d b q hqd hq hvd hvb).1
  have hbdom (a : Nat) (ha : a ∈ u.varFinset) :
      KDerivation (imp g.encode (domainAt b a).encode) :=
    compose (hdom a ha) (domainAt_transport d b a (by have := hud a ha; omega)
      (by have := hub a ha; omega))
  have hf := succ_leaf_forward id u b q out hq hout hub
  have hr := succ_leaf_reverse id g u hu b q out hq hout hub hg hbdom
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [V, H.encode]
    have hH : Context Γ (both g.encode G) := by
      have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
      simpa [H, retained, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hV : Context Γ V := Context.head _ _
    have hGb : Context Γ Gb := .mp (Context.conjunctionRight hH) (.closed hmove)
    exact .mp hV (.mp hGb (.closed hf))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [T, H.encode]
    have hH : Context Γ (both g.encode G) := by
      have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
      simpa [H, retained, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hT : Context Γ T := Context.head _ _
    have hGb : Context Γ Gb := .mp (Context.conjunctionRight hH) (.closed hmove)
    exact .mp hT (.mp hGb (.mp (Context.conjunctionLeft hH) (.closed hr)))

/-- Structural alignment for any PA term under a successor substitution.
The retained graph and the source guard are fixed while all private graph
witnesses are introduced and eliminated. -/
noncomputable def successor_substitution (g : Formula) (u : Peano.Term) (hu : UnaryTerm u)
    (x q d : Nat) (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (s : Peano.Term) (b out : Nat) (hout : out < b)
    (hH : ∀ a ∈ (retained g u q d).free, a < b)
    (hs : ∀ a ∈ (s.subst (variableSubst x q)).varFinset, a < b)
    (ht : ∀ a ∈ (s.subst (successorSubst x u)).varFinset, a < b) :
    Align (retained g u q d) (s.subst (variableSubst x q))
      (s.subst (successorSubst x u)) b out := by
  apply term_subst_align (retained g u q d) (variableSubst x q) (successorSubst x u) s
  · intro a ha base r hr hH' hσ hτ
    by_cases hax : a = x
    · subst a
      have hq : q < base := by apply hσ q; simp [variableSubst, Term.varFinset]
      have hbu : ∀ v ∈ u.varFinset, v < base := by
        intro v hv
        apply hτ v
        simpa [successorSubst, succTerm, Term.varFinset] using hv
      have hbg : ∀ v ∈ g.free, v < base := by
        intro v hv
        apply hH' v
        rw [retained, andF_free]
        exact Finset.mem_union_left _ hv
      simp only [variableSubst, successorSubst, ↓reduceIte]
      exact successor_leaf g u hu q d base r hqd hq hr hud hbu hbg hdom
    · simp only [variableSubst, successorSubst, hax, ↓reduceIte]
      let X := (termGraph id (.var a : Peano.Term) r base).encode
      have weakenProof : KDerivation (imp (imp X X) (imp (retained g u q d).encode (imp X X))) :=
        weakening _ _
      have hi : KDerivation (imp (retained g u q d).encode (imp X X)) := .mp (identity _) weakenProof
      exact ⟨hi, hi⟩
  · exact hout
  · exact hH
  · exact hs
  · exact ht

end PASoundness.PAtoCompactTermSubstSuccessorInduction

#print axioms PASoundness.PAtoCompactTermSubstSuccessorInduction.successor_leaf
#print axioms PASoundness.PAtoCompactTermSubstSuccessorInduction.successor_substitution
