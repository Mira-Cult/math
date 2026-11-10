import PASoundness.PAtoCompactDynamicTransitivityFinal
import PASoundness.CompactDerivations

/-! Candidate-relative output transport for a quotient-successor witness
matrix. The raw-successor conjunct is retained unchanged. These are finite
K derivations, not semantic model arguments. -/
namespace PASoundness.PAtoCompactSuccOutputMatrix

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactDynamicTransitivityFinal

/-- Matrix of the quotient-successor relation with an explicitly named
witness; `raw` may be the raw-successor relation for that same witness. -/
def outputMatrix (b a q w : Nat) (raw : Formula) : Formula :=
  andF (domainAt b a) (andF (domainAt b q) (andF (domainAt b w)
    (andF raw (equivAt b w q))))

/-- An equivalent new output can replace the old output in the witness
matrix. All operand names may alias, and `raw` is preserved literally. -/
def output_matrix_transport (b a q r w : Nat) (raw : Formula)
    (hq : q < b+2) (hr : r < b+2) (hw : w < b+2) :
    KDerivation (imp (domainAt b r).encode
      (imp (equivAt b q r).encode
        (imp (outputMatrix b a q w raw).encode (outputMatrix b a r w raw).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt b r).encode
  let E := (equivAt b q r).encode
  let M := (outputMatrix b a q w raw).encode
  let Γ := [M,E,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have hm' : Context Γ (both (domainAt b a).encode
      (both (domainAt b q).encode (both (domainAt b w).encode
        (both raw.encode (equivAt b w q).encode)))) := by
    simpa [M, outputMatrix, andF, Formula.not, Formula.encode, both, neg] using hm
  have ha := Context.conjunctionLeft hm'
  have hrest := Context.conjunctionRight hm'
  have hrest := Context.conjunctionRight hrest
  have hw' := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hraw := Context.conjunctionLeft hrest
  have hwq := Context.conjunctionRight hrest
  have hwr : Context Γ (equivAt b w r).encode :=
    .mp he (.mp hwq (.mp hw' (.closed (dynamic_transitivity b w q r hw hq hr))))
  have hfinal := Context.conjunctionIntro ha
    (Context.conjunctionIntro hd (Context.conjunctionIntro hw'
      (Context.conjunctionIntro hraw hwr)))
  simpa [D, E, M, Γ, outputMatrix, andF, Formula.not, Formula.encode, both, neg] using hfinal

theorem output_matrix_transport_certificate (b a q r w : Nat) (raw : Formula)
    (hq : q < b+2) (hr : r < b+2) (hw : w < b+2) :
    theoremCode (certificate (output_matrix_transport b a q r w raw hq hr hw)) =
      imp (domainAt b r).encode (imp (equivAt b q r).encode
        (imp (outputMatrix b a q w raw).encode (outputMatrix b a r w raw).encode)) :=
  certificate_correct _


/-- The same witness-matrix transformation with a single conjunction guard,
convenient for lifting through an existential witness. -/
def output_matrix_guarded (b a q r w : Nat) (raw : Formula)
    (hq : q < b+2) (hr : r < b+2) (hw : w < b+2) :
    KDerivation (imp (andF (domainAt b r) (equivAt b q r)).encode
      (imp (outputMatrix b a q w raw).encode (outputMatrix b a r w raw).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let G := (andF (domainAt b r) (equivAt b q r)).encode
  let M := (outputMatrix b a q w raw).encode
  let Γ := [M,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have hg' : Context Γ (both (domainAt b r).encode (equivAt b q r).encode) := by
    simpa [G, andF, Formula.not, Formula.encode, both, neg] using hg
  exact .mp hm (.mp (Context.conjunctionRight hg')
    (.mp (Context.conjunctionLeft hg') (.closed (output_matrix_transport b a q r w raw hq hr hw))))

end PASoundness.PAtoCompactSuccOutputMatrix

#print axioms PASoundness.PAtoCompactSuccOutputMatrix.output_matrix_transport
#print axioms PASoundness.PAtoCompactSuccOutputMatrix.output_matrix_transport_certificate
#print axioms PASoundness.PAtoCompactSuccOutputMatrix.output_matrix_guarded
