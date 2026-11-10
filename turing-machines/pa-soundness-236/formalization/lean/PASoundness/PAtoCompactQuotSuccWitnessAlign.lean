import PASoundness.PAtoCompactQuotientSuccNeZero
import PASoundness.PAtoCompactQuotientSuccessor

/-! Literal K quotient successor cannot have an empty output. This uses the
actual quotient-successor existential, not semantic truth or quotient
transitivity. The candidate conjuncts are preserved as part of its body. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccWitnessAlign
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactQuotientSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
  PAtoCompactQuotientSuccessor.domainFormula

private def B : Formula := replace 0 7 bijectionFormula
private def O : Formula := replace 0 7 orderFormula
private def E : Formula := replace 0 7 equivalentFormula
private def M : Formula := (B.imp O.not).not
private def conj (a b : Formula) : Formula := (a.imp b.not).not
private theorem encode_conj (a b : Formula) : (conj a b).encode = both a.encode b.encode := by rfl
private def explicitBody : Formula := conj (domainFormula 0)
  (conj (domainFormula 1) (conj (domainFormula 7) (conj rawSuccessorFormula E)))
private theorem body_syntax : successorFormula = .ex 7 explicitBody := by rfl
private def firstBody : Formula := match B with
  | .imp (.imp (.all _ f) _) _ => f
  | _ => .bottom
private def pointBody : Formula := replace 2 0 firstBody
private def witnessBody : Formula := match pointBody with
  | .imp _ (.ex _ f) => f
  | _ => .bottom

private def witness_false : KDerivation (imp (zeroCode 1 12)
    (allCode 3 (imp witnessBody.encode 1))) := by
  let Z := zeroCode 1 12
  apply Context.closeEmpty
  apply Context.deduction
  have hh : Context [Z] (imp witnessBody.encode 1) := by
    apply Context.deduction
    have hw : Context [witnessBody.encode,Z] witnessBody.encode := Context.head _ _
    have hm : Context [witnessBody.encode,Z] (member 1 3) := by
      change Context [witnessBody.encode,Z] (both (member 1 3) _) at hw
      exact Context.conjunctionLeft hw
    have hz : Context [witnessBody.encode,Z] Z := .hypothesis (by simp)
    exact .mp hm (.mp hz (.closed (zero_excludes 1 12 3 (by decide) (by decide))))
  have hv : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = Z := by simpa using hh
    subst h
    exact PAtoCompactEmptyExtrema.zero_vacuity 1 12 3 (by decide) (by decide)
  exact Context.generalize 3 hv hh

private def matrix_false : KDerivation (imp (zeroCode 1 12)
    (imp (member 7 0) (imp M.encode 1))) := by
  let Z := zeroCode 1 12
  let A := member 7 0
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [M.encode,A,Z]
  have hm : Context Γ M.encode := Context.head _ _
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hb : Context Γ B.encode := Context.conjunctionLeft hm
  have hf : Context Γ (allCode 2 firstBody.encode) := by
    change Context Γ (both (allCode 2 firstBody.encode) _) at hb
    exact Context.conjunctionLeft hb
  have hi := universalInstance 2 0 firstBody (by decide) (by decide) (by decide)
  have hp : Context Γ pointBody.encode := .mp hf (.closed hi)
  have hp' : Context Γ (imp A (existsCode 3 witnessBody.encode)) := by
    exact hp
  have hw : Context Γ (existsCode 3 witnessBody.encode) := .mp ha hp'
  have hfals : Context Γ (allCode 3 (imp witnessBody.encode 1)) := .mp hz (.closed witness_false)
  exact Context.existsElim (explosion (allCode 3 1)) hfals hw

/-- An alleged first-input member contradicts the exact isomorphism to zero. -/
def zero_excludes_equivalent_with_member : KDerivation
    (imp (zeroCode 1 12) (imp (member 7 0) (neg E.encode))) := by
  let Z := zeroCode 1 12
  let A := member 7 0
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E.encode,A,Z]
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have he : Context Γ (existsCode 6 M.encode) := Context.head _ _
  have hlocal : Context [A,Z] (imp M.encode 1) :=
    .mp (Context.head [Z] A) (.mp (Context.under (Context.head [] Z) A) (.closed matrix_false))
  have hv : ∀ h, h ∈ [A,Z] → KDerivation (imp h (allCode 6 h)) := by
    intro h hh
    by_cases heq : h = A
    · subst h
      exact Formula.vacuity 6 (.member 7 0) (by decide)
    · have heq' : h = Z := by simpa [heq] using hh
      subst h
      exact PAtoCompactEmptyExtrema.zero_vacuity 1 12 6 (by decide) (by decide)
  have hall : Context [A,Z] (allCode 6 (imp M.encode 1)) := Context.generalize 6 hv hlocal
  exact Context.existsElim (explosion (allCode 6 1)) (Context.under hall E.encode) he

attribute [local irreducible] E PAtoCompactQuotientSuccessor.rawSuccessorFormula

/-- The literal quotient-successor formula contradicts the displayed zero
graph for its output. No candidate transitivity premise is needed. -/
def quotient_successor_not_zero : KDerivation
    (imp successorFormula.encode (imp (zeroCode 1 12) 1)) := by
  let Z := zeroCode 1 12
  let F := successorFormula
  let body : Formula := explicitBody
  have hbody : KDerivation (imp Z (imp body.encode 1)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [body.encode,Z]
    have hb : Context Γ body.encode := Context.head _ _
    rw [show body = explicitBody from rfl, explicitBody, encode_conj, encode_conj,
      encode_conj, encode_conj] at hb
    have hz : Context Γ Z := Context.under (Context.head [] Z) body.encode
    have hb1 : Context Γ (both (domainFormula 1).encode (both (domainFormula 7).encode
        (both rawSuccessorFormula.encode E.encode))) := Context.conjunctionRight hb
    have hb2 : Context Γ (both (domainFormula 7).encode (both rawSuccessorFormula.encode E.encode)) :=
      Context.conjunctionRight hb1
    have htail : Context Γ (both rawSuccessorFormula.encode E.encode) := Context.conjunctionRight hb2
    have hs : Context Γ (successorCode 0 7 8) := by
      simpa only [rawSuccessorFormula, encode_of_code] using Context.conjunctionLeft htail
    have he : Context Γ E.encode := Context.conjunctionRight htail
    have hm : Context Γ (member 7 0) :=
      .mp hs (.closed (successor_contains_input 0 7 8 (by decide) (by decide)))
    have hn : Context Γ (neg E.encode) :=
      .mp hm (.mp hz (.closed zero_excludes_equivalent_with_member))
    exact .mp he hn
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [Z,F.encode]
  have hz : Context Γ Z := Context.head _ _
  have hshape : F.encode = existsCode 7 body.encode := by
    change successorFormula.encode = existsCode 7 explicitBody.encode
    rw [body_syntax]
    rfl
  have hex : Context Γ (existsCode 7 body.encode) := by
    rw [← hshape]
    exact Context.under (Context.head [] F.encode) Z
  have hlocal : Context [Z] (imp body.encode 1) := .mp (Context.head [] Z) (.closed hbody)
  have hv : ∀ h, h ∈ [Z] → KDerivation (imp h (allCode 7 h)) := by
    intro h hh
    have heq : h = Z := by simpa using hh
    subst h
    exact PAtoCompactEmptyExtrema.zero_vacuity 1 12 7 (by decide) (by decide)
  have hall : Context [Z] (allCode 7 (imp body.encode 1)) := Context.generalize 7 hv hlocal
  have hall' : Context Γ (allCode 7 (imp body.encode 1)) := hall.weaken (by
    intro x hx
    have hx' : x = Z := List.mem_singleton.mp hx
    subst x
    exact List.mem_cons_self)
  exact Context.existsElim (explosion (allCode 7 1)) hall' hex

theorem quotient_successor_not_zero_certificate :
    theoremCode (certificate quotient_successor_not_zero) =
      imp successorFormula.encode (imp (zeroCode 1 12) 1) :=
  certificate_correct quotient_successor_not_zero

end PASoundness.PAtoCompactQuotSuccWitnessAlign

#print axioms PASoundness.PAtoCompactQuotSuccWitnessAlign.quotient_successor_not_zero
#print axioms PASoundness.PAtoCompactQuotSuccWitnessAlign.quotient_successor_not_zero_certificate
