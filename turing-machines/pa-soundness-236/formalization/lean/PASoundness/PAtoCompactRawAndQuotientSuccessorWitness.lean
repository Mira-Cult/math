import PASoundness.PAtoCompactQuotientSuccessorTotality
import PASoundness.PAtoCompactSuccessorQuotientIntro
import PASoundness.PAtoCompactSuccTermReplacement
import PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity

/-! Construct a candidate successor retaining its raw successor relation and
its quotient-successor relation at the same existential witness. No
multiplication, addition, or PA axiom is claimed. -/
namespace PASoundness.PAtoCompactRawAndQuotientSuccessorWitness

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactQuotientSuccessorTotality PASoundness.PAtoCompactSuccessorQuotientIntro
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The explicit raw and quotient relations share one successor label. -/
def body (b x sx : Nat) : Formula :=
  andF (rawAt b x sx) (andF (domainAt b sx) (succAt b x sx))

/-- A candidate has a candidate raw successor that also satisfies the
allocated quotient-successor relation, with one shared witness. The input and
output *binder labels* must differ; their represented values need not. -/
def successor_exists (b x sx : Nat) (hx : x < b) (hsx : sx < b) (hneq : sx ≠ x) :
    KDerivation (imp (domainAt b x).encode (existsCode sx (body b x sx).encode)) := by
  let D := (domainAt b x).encode
  let P := both (rawAt b x sx).encode (domainAt b sx).encode
  let B := body b x sx
  let E := Formula.ex sx B
  have hD := domain_vacuity b x sx hneq
  have hE : KDerivation (imp E.encode (allCode sx E.encode)) := by
    apply free_vacuity
    simp [E, Formula.free]
  have hraw : sx ∉ (rawAt b x sx).binders := by
    simp [rawAt, Formula.binders, namedSuccessorBody, namedBoth, namedEither,
      show sx ≠ b+10 by omega]
  have hdomain : sx ∉ (domainAt b sx).binders := by
    intro h
    have hh := domainAt_private b sx sx h
    omega
  have hsucc : sx ∉ (succAt b x sx).binders :=
    PASoundness.PAtoCompactSuccTermReplacement.succAt_below_not_binder b x sx sx (by omega)
  have hbody : sx ∉ B.binders := by
    simpa [B, body, andF_binders] using ⟨hraw, hdomain, hsucc⟩
  have hp := quotient_successor_of_raw b x sx (by omega) hsx
  have hex := raw_candidate_exists b x sx hx hsx hneq
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [D]
  have hd : Context Γ D := .head _ _
  have hsource : Context Γ (existsCode sx P) := by
    have h := Context.mp hd (.closed hex)
    simpa [P, rawAt, raw_successor_encode] using h
  apply Context.existsElim hE _ hsource
  apply generalizeOne sx hD
  apply Context.deduction
  let Δ := [P,D]
  have hpair : Context Δ P := .head _ _
  have hdx : Context Δ D := .hypothesis (by simp [Δ])
  have hr := Context.conjunctionLeft hpair
  have hds := Context.conjunctionRight hpair
  have hs : Context Δ (succAt b x sx).encode :=
    .mp hds (.mp (by simpa [P, rawAt, raw_successor_encode] using hr) (.mp hdx (.closed hp)))
  have hboth := Context.conjunctionIntro hr (Context.conjunctionIntro hds hs)
  have hb : Context Δ B.encode := by
    simpa [B, body, P, andF, Formula.not, Formula.encode, both, neg] using hboth
  have hi := existsIntroduce sx B hbody
  have hresult := Context.mp hb (.closed hi)
  simpa [E, Formula.encode, existsCode] using hresult

end PASoundness.PAtoCompactRawAndQuotientSuccessorWitness

#print axioms PASoundness.PAtoCompactRawAndQuotientSuccessorWitness.body
#print axioms PASoundness.PAtoCompactRawAndQuotientSuccessorWitness.successor_exists
