import PASoundness.PeanoBetaCRTEndpoint

/-! Same-parameter existential packaging for the conditional bounded CRT
endpoint. PA constructs a parameter above the bound satisfying the ordered-pair
condition; relation totality remains an explicit premise. The relation may depend
on the selected parameter. No power trace or full PA bridge is asserted. -/
namespace PASoundness.PeanoBetaCRTParameter
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaEndpointPairs PeanoBetaUniformPairs PeanoBetaCRTFuturePair
open PeanoBetaCRTInvariant PeanoBetaCRTAlignment

/-- One parameter simultaneously satisfies the residue-totality and ordered
pair-inverse hypotheses. The variable C is intentionally bound at name 1. -/
def admissibleParameter (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 1 (PeanoBetaCRTEndpoint.global φ)

/-- One parameter has a code/product satisfying the invariant at N. Any free
occurrence of name 1 in φ intentionally refers to this same parameter. -/
def solvedParameter (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 1 (invariantAt φ (.var 8))

/-- From a single admissible C, PA derives an endpoint for that same C and
then packages it. No independence of φ from C is assumed. -/
theorem same_parameter (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((admissibleParameter φ).imp (solvedParameter φ)) := by
  let G := PeanoBetaCRTEndpoint.global φ
  let I := invariantAt φ (.var 8)
  let T := solvedParameter φ
  have hb : FormulaProves (G.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hg : FOL.Context Peano.Axiom [G] G := FOL.Context.head [] G
    have hi : FOL.Context Peano.Axiom [G] I :=
      .mp (.closed (PeanoBetaCRTEndpoint.conditional_endpoint φ hφ)) hg
    have hex : FormulaProves (I.imp T) := by
      simpa only [T, solvedParameter, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) I 1 (.var 1))
    exact .mp (.closed hex) hi
  have hf : 1 ∉ T.freeVarFinset := by
    simp [T, solvedParameter, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  simpa only [admissibleParameter, G] using PeanoBitPositionReduction.exists_elim 1 hf hb

/-- The selected parameter exceeds the explicit lower bound at name 16 as
well as satisfying the ordered-pair inverse condition. -/
def boundedEndpoint : Peano.Formula :=
  (CompactArithmetic.less (.var 16) (.var 1)) ⊓ PeanoBetaCRTFuturePair.endpointAt8

/-- This totality condition may depend on the same C that is being selected;
it is required only for parameters above the chosen lower bound. -/
def totalityForBoundedEndpoints (φ : Peano.Formula) : Peano.Formula :=
  FOL.allAt 1 (boundedEndpoint.imp (PeanoBetaCRTResidueSelect.totality φ))

/-- Given one bounded endpoint parameter, PA uses that same parameter for
residue totality and the solved CRT invariant. This version retains the lower
bound, avoiding any inference from endpointAt8 at C=0. -/
theorem solution_from_bounded_endpoint (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((totalityForBoundedEndpoints φ).imp
      ((FOL.existsAt 1 boundedEndpoint).imp (solvedParameter φ))) := by
  let F := totalityForBoundedEndpoints φ
  let E := boundedEndpoint
  let T := admissibleParameter φ
  have hb : FormulaProves (E.imp (F.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hf : FOL.Context Peano.Axiom [F,E] F := FOL.Context.head _ _
    have he : FOL.Context Peano.Axiom [F,E] E := FOL.Context.under (FOL.Context.head [] E) F
    have hft : FOL.Context Peano.Axiom [F,E]
        (E.imp (PeanoBetaCRTResidueSelect.totality φ)) := FOL.Context.allSelf hf
    have ht : FOL.Context Peano.Axiom [F,E] (PeanoBetaCRTResidueSelect.totality φ) := .mp hft he
    have hi : FOL.Context Peano.Axiom [F,E] PeanoBetaCRTFuturePair.endpointAt8 :=
      FOL.Context.conjunctionRight he
    have hg : FOL.Context Peano.Axiom [F,E] (PeanoBetaCRTEndpoint.global φ) :=
      FOL.Context.conjunctionIntro ht hi
    have heT : FormulaProves ((PeanoBetaCRTEndpoint.global φ).imp T) := by
      simpa only [T, admissibleParameter, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (PeanoBetaCRTEndpoint.global φ) 1 (.var 1))
    exact .mp (.closed heT) hg
  have hf : 1 ∉ (F.imp T).freeVarFinset := by
    simp [F, T, totalityForBoundedEndpoints, admissibleParameter,
      FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have hex := PeanoBitPositionReduction.exists_elim 1 hf hb
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Q := FOL.existsAt 1 E
  let Γ := [Q,F]
  have hq : FOL.Context Peano.Axiom Γ Q := FOL.Context.head _ _
  have hF : FOL.Context Peano.Axiom Γ F := FOL.Context.under (FOL.Context.head [] F) Q
  have ha : FOL.Context Peano.Axiom Γ (admissibleParameter φ) := .mp (.mp (.closed hex) hq) hF
  exact .mp (.closed (same_parameter φ hφ)) ha

def boundEndpoint : Peano.Formula := (less (.var 8) (.var 1)) ⊓ endpointUniform

/-- The original constructed parameter satisfies both the bound and the
endpoint inverse condition. Both properties refer to the same C witness. -/
theorem bound_endpoint_exists_vars : FormulaProves (FOL.existsAt 1 boundEndpoint) := by
  let A := uniformPairBody ⊓ endpointUniform
  let T := FOL.existsAt 1 boundEndpoint
  have hi : FormulaProves (boundEndpoint.imp T) := by
    simpa only [T, SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) boundEndpoint 1 (.var 1))
  have hbody : FormulaProves (A.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have h : FOL.Context Peano.Axiom [A] A := FOL.Context.head [] A
    have hb : FOL.Context Peano.Axiom [A] (less (.var 8) (.var 1)) :=
      FOL.Context.conjunctionLeft (FOL.Context.conjunctionLeft h)
    have he : FOL.Context Peano.Axiom [A] endpointUniform := FOL.Context.conjunctionRight h
    exact .mp (.closed hi) (FOL.Context.conjunctionIntro hb he)
  have hfresh : 1 ∉ T.freeVarFinset := by decide
  have he := PeanoBitPositionReduction.exists_elim 1 hfresh hbody
  exact .mp he endpoint_pair_parameter_exists_vars

private theorem substAt_inf (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = FOL.substAt φ x t ⊓ FOL.substAt ψ x t := rfl

private theorem endpoint_fresh8 : 8 ∉ endpointUniform.freeVarFinset := by decide
private theorem bound_fresh7 : 7 ∉ (less (.var 16) (.var 1)).freeVarFinset := by decide

/-- Rename R=8 to R=16 before the N=7 to N=8 renaming, avoiding the
name collision between the original bound and the desired new index bound. -/
theorem rename_bound : FOL.substAt (FOL.existsAt 1 boundEndpoint) 8 (.var 16) =
    FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointUniform) := by
  rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 8 16 1 (by decide) (by decide)]
  unfold boundEndpoint
  rw [substAt_inf,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh endpointUniform 8 (.var 16) endpoint_fresh8]
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

/-- After the original bound is out of the way, rename N=7 to N=8. -/
theorem rename_index : FOL.substAt
    (FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointUniform)) 7 (.var 8) =
    FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointAt8) := by
  rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 7 8 1 (by decide) (by decide), substAt_inf,
    PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ 7 (.var 8) bound_fresh7]
  rfl

/-- For every displayed N=8 and R=16, PA constructs C>R satisfying the
ordered endpoint inverse condition for that same C. -/
theorem bound_endpoint_exists : FormulaProves
    (FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointAt8)) := by
  have h1 := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (FOL.existsAt 1 boundEndpoint) 8 (.var 16)))
    (.generalize 8 bound_endpoint_exists_vars)
  have h1' : FormulaProves
      (FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointUniform)) := by
    simpa only [rename_bound] using h1
  have h2 := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim (FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointUniform)) 7 (.var 8)))
    (.generalize 7 h1')
  simpa only [rename_index] using h2


/-- PA constructs a parameter satisfying the CRT endpoint from the explicit
same-parameter totality condition for all suitable C above R. The existence of
such a bounded endpoint parameter is derived internally in PA. -/
theorem solution_of_bounded_totality (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((totalityForBoundedEndpoints φ).imp (solvedParameter φ)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom [totalityForBoundedEndpoints φ]
      (totalityForBoundedEndpoints φ) := FOL.Context.head [] _
  have he : FOL.Context Peano.Axiom [totalityForBoundedEndpoints φ]
      (FOL.existsAt 1 boundedEndpoint) := by
    simpa only [boundedEndpoint] using
      (FOL.Context.closed bound_endpoint_exists : FOL.Context Peano.Axiom [totalityForBoundedEndpoints φ]
        (FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointAt8)))
  exact .mp (.mp (.closed (solution_from_bounded_endpoint φ hφ)) hf) he

/-- A solved parameter together with the original lower bound, both under the
same existential C binder. -/
def boundedSolvedParameter (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ invariantAt φ (.var 8))

/-- The bounded totality assumption yields a solution that retains R<C for
the same selected parameter; no second existential witness is substituted. -/
theorem bounded_solution_from_endpoint (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((totalityForBoundedEndpoints φ).imp
      ((FOL.existsAt 1 boundedEndpoint).imp (boundedSolvedParameter φ))) := by
  let F := totalityForBoundedEndpoints φ
  let E := boundedEndpoint
  let T := boundedSolvedParameter φ
  let H := less (.var 16) (.var 1)
  let I := invariantAt φ (.var 8)
  have hb : FormulaProves (E.imp (F.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hf : FOL.Context Peano.Axiom [F,E] F := FOL.Context.head _ _
    have he : FOL.Context Peano.Axiom [F,E] E := FOL.Context.under (FOL.Context.head [] E) F
    have hft : FOL.Context Peano.Axiom [F,E]
        (E.imp (PeanoBetaCRTResidueSelect.totality φ)) := FOL.Context.allSelf hf
    have ht : FOL.Context Peano.Axiom [F,E] (PeanoBetaCRTResidueSelect.totality φ) := .mp hft he
    have hbound : FOL.Context Peano.Axiom [F,E] H := FOL.Context.conjunctionLeft he
    have hinv : FOL.Context Peano.Axiom [F,E] endpointAt8 := FOL.Context.conjunctionRight he
    have hg : FOL.Context Peano.Axiom [F,E] (PeanoBetaCRTEndpoint.global φ) :=
      FOL.Context.conjunctionIntro ht hinv
    have hi : FOL.Context Peano.Axiom [F,E] I :=
      .mp (.closed (PeanoBetaCRTEndpoint.conditional_endpoint φ hφ)) hg
    have hbody : FOL.Context Peano.Axiom [F,E] (H ⊓ I) :=
      FOL.Context.conjunctionIntro hbound hi
    have hIntro : FormulaProves ((H ⊓ I).imp T) := by
      simpa only [T, H, I, boundedSolvedParameter, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom)
          ((less (.var 16) (.var 1)) ⊓ invariantAt φ (.var 8)) 1 (.var 1))
    exact .mp (.closed hIntro) hbody
  have hf : 1 ∉ (F.imp T).freeVarFinset := by
    simp [F, T, totalityForBoundedEndpoints, boundedSolvedParameter,
      FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have hex := PeanoBitPositionReduction.exists_elim 1 hf hb
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Q := FOL.existsAt 1 E
  let Γ := [Q,F]
  have hq : FOL.Context Peano.Axiom Γ Q := FOL.Context.head _ _
  have hF : FOL.Context Peano.Axiom Γ F := FOL.Context.under (FOL.Context.head [] F) Q
  exact .mp (.mp (.closed hex) hq) hF

/-- Bounded existential CRT endpoint inside PA. The sole object-level premise
is the explicit same-C bounded totality formula. The produced parameter still
satisfies the specified lower bound; no power trace or PA bridge is asserted. -/
theorem bounded_solution_of_totality (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((totalityForBoundedEndpoints φ).imp (boundedSolvedParameter φ)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hf : FOL.Context Peano.Axiom [totalityForBoundedEndpoints φ]
      (totalityForBoundedEndpoints φ) := FOL.Context.head [] _
  have he : FOL.Context Peano.Axiom [totalityForBoundedEndpoints φ]
      (FOL.existsAt 1 boundedEndpoint) := by
    simpa only [boundedEndpoint] using
      (FOL.Context.closed bound_endpoint_exists : FOL.Context Peano.Axiom [totalityForBoundedEndpoints φ]
        (FOL.existsAt 1 ((less (.var 16) (.var 1)) ⊓ endpointAt8)))
  exact .mp (.mp (.closed (bounded_solution_from_endpoint φ hφ)) hf) he

end PASoundness.PeanoBetaCRTParameter
