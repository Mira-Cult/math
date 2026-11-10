import PASoundness.PAtoCompactTermTranslation
import PASoundness.CompactDerivations

/-! The variable case of graph output transport for substitution. Candidate
relative transitivity is an explicit finite K proof input. This module does
not establish the corresponding transport for composite terms. -/
namespace PASoundness.PAtoCompactVariableGraphSubstitutionConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation

/-- If the original variable has output q and the variable named q has output
r, then the original variable has output r. The candidate source guard and
the precise K transitivity implication are explicit. The two term graphs use
the same allocation base. -/
def variable_graph_output_transport {α : Type} (v : α → Nat) (a : α)
    (base q r : Nat)
    (trans : KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) q).encode
        (imp (equivAt base q r).encode (equivAt base (v a) r).encode)))) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (termGraph v (.var a) q base).encode
        (imp (termGraph id (.var q : Peano.Term) r base).encode
          (termGraph v (.var a) r base).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := (domainAt base (v a)).encode
  let Q := (termGraph v (.var a) q base).encode
  let R := (termGraph id (.var q : Peano.Term) r base).encode
  let Γ := [R, Q, A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := .hypothesis (by simp [Γ])
  have hr : Context Γ R := Context.head _ _
  have heq : Context Γ (equivAt base (v a) q).encode := Context.conjunctionRight hq
  have hdr : Context Γ (domainAt base r).encode := Context.conjunctionLeft hr
  have hqr : Context Γ (equivAt base q r).encode := Context.conjunctionRight hr
  have her := Context.mp hqr (Context.mp heq (Context.mp ha (Context.closed trans)))
  exact Context.conjunctionIntro hdr her

/-- Reverse output transport uses D(q) explicitly: from a graph for the
variable q at r and a graph for a at r, recover the graph for a at q.
The symmetry and transitivity derivations are finite K proof inputs. -/
def variable_graph_output_transport_reverse {α : Type} (v : α → Nat) (a : α)
    (base q r : Nat)
    (sym : KDerivation (imp (domainAt base q).encode
      (imp (equivAt base q r).encode (equivAt base r q).encode)))
    (trans : KDerivation (imp (domainAt base (v a)).encode
      (imp (equivAt base (v a) r).encode
        (imp (equivAt base r q).encode (equivAt base (v a) q).encode)))) :
    KDerivation (imp (domainAt base (v a)).encode
      (imp (domainAt base q).encode
        (imp (termGraph id (.var q : Peano.Term) r base).encode
          (imp (termGraph v (.var a) r base).encode
            (termGraph v (.var a) q base).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := (domainAt base (v a)).encode
  let D := (domainAt base q).encode
  let Q := (termGraph id (.var q : Peano.Term) r base).encode
  let R := (termGraph v (.var a) r base).encode
  let Γ := [R, Q, D, A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := .hypothesis (by simp [Γ])
  have hr : Context Γ R := Context.head _ _
  have hqr : Context Γ (equivAt base q r).encode := Context.conjunctionRight hq
  have har : Context Γ (equivAt base (v a) r).encode := Context.conjunctionRight hr
  have hrq := Context.mp hqr (Context.mp hd (Context.closed sym))
  have haq := Context.mp hrq (Context.mp har (Context.mp ha (Context.closed trans)))
  exact Context.conjunctionIntro hd haq

end PASoundness.PAtoCompactVariableGraphSubstitutionConditional

#print axioms PASoundness.PAtoCompactVariableGraphSubstitutionConditional.variable_graph_output_transport
#print axioms PASoundness.PAtoCompactVariableGraphSubstitutionConditional.variable_graph_output_transport_reverse
