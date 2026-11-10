import PASoundness.PAtoCompactGeneralizationFreshAlpha
import PASoundness.PAtoCompactGeneralizationGuardAssembly
import PASoundness.PAtoCompactGuardedVacuity
import PASoundness.PAtoCompactGuardedGeneralizationAlignment
import PASoundness.PAtoCompactGuardedModusPonensFull

/-! Conditional unrestricted guarded generalization. The explicit premise
is an actual finite K proof aligning the freshened/replaced guarded body with
the body allocated for the translated PA universal. -/
namespace PASoundness.PAtoCompactGeneralizationConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedVacuity PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGeneralizationFreshAlpha
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGeneralizationGuardAssembly

def guardedBody (φ : Peano.Formula) (x : Nat) : Formula :=
  .imp (domainAt (extraBase φ x) x) (formula φ)

theorem topName_not_universal_free (φ : Peano.Formula) (x : Nat) :
    topName x φ ∉ (FOL.allAt x φ).freeVarFinset := by
  intro h
  have hl := free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 (topName x φ) h
  exact Nat.lt_irrefl _ hl

theorem topName_not_body_free (φ : Peano.Formula) (x : Nat)
    (hne : x ≠ topName x φ) : topName x φ ∉ (guardedBody φ x).free := by
  intro h
  simp only [guardedBody, Formula.free, Finset.mem_union] at h
  rcases h with hd | hf
  · have := domainAt_free (extraBase φ x) x hd
    exact hne ((Finset.mem_singleton.mp this).symm)
  · have hfree := formula_free_subset φ hf
    have hbound : topName x φ ∈ (FOL.allAt x φ).freeVarFinset := by
      simp [PASoundness.SyntaxTransport.allAt_freeVars, hfree, Ne.symm hne]
    exact topName_not_universal_free φ x hbound

/-- Finite proof transformer for any PA generalization, retaining the
explicit K proof aligning its freshened guarded body with the actual generated
body. This does not establish the alignment or the unconditional handler. -/
def generalize_of_guarded_body_alignment (φ : Peano.Formula) (x start : Nat)
    (hn : ∀ v ∈ (guardedBody φ x).names, v < start)
    (hxs : x < start) (hzs : topName x φ < start)
    (halign : KDerivation (imp
      (replace x (topName x φ) (freshen (guardedBody φ x) start hn).formula).encode
      (imp (domainAt (topName x φ + 1) (topName x φ)).encode (topBody x φ).encode)))
    (d : KDerivation (guardedCode φ)) : KDerivation (guardedCode (FOL.allAt x φ)) := by
  have halpha : ProofEquiv (.all x (guardedBody φ x))
      (.all (topName x φ) (replace x (topName x φ)
        (freshen (guardedBody φ x) start hn).formula)) := by
    by_cases he : x = topName x φ
    · rw [← he]
      exact universal_fresh_same (guardedBody φ x) start x hn
    · exact universal_fresh_alpha (guardedBody φ x) start x (topName x φ)
        hn hxs hzs he (topName_not_body_free φ x he)
  have hpre : KDerivation (imp (guardFormula (FOL.allAt x φ)).encode (guardedBody φ x).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(domainAt (extraBase φ x) x).encode, (guardFormula (FOL.allAt x φ)).encode]
    have hg : Context Γ (guardFormula (FOL.allAt x φ)).encode := .hypothesis (by simp [Γ])
    have hx : Context Γ (domainAt (extraBase φ x) x).encode := .hypothesis (by simp [Γ])
    have hguard : Context Γ (guardFormula φ).encode := .mp hx (.mp hg (.closed (guard_assemble φ x)))
    exact .mp hguard (.closed d)
  have hxnot : x ∉ (FOL.allAt x φ).freeVarFinset := by
    simp [PASoundness.SyntaxTransport.allAt_freeVars]
  have hg : KDerivation (imp (guardFormula (FOL.allAt x φ)).encode
      (allCode x (guardedBody φ x).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply generalizeOne x (guardFormula_vacuity (FOL.allAt x φ) x hxnot)
    exact .mp (Context.head [] _) (.closed hpre)
  have hc := compose hg (compose halpha.forward (allCongr (topName x φ) halign))
  simpa only [guardedCode, code_allAt] using hc

theorem generalize_of_guarded_body_alignment_certificate (φ : Peano.Formula) (x start : Nat)
    (hn : ∀ v ∈ (guardedBody φ x).names, v < start)
    (hxs : x < start) (hzs : topName x φ < start)
    (halign : KDerivation (imp
      (replace x (topName x φ) (freshen (guardedBody φ x) start hn).formula).encode
      (imp (domainAt (topName x φ + 1) (topName x φ)).encode (topBody x φ).encode)))
    (d : KDerivation (guardedCode φ)) :
    theoremCode (certificate (generalize_of_guarded_body_alignment φ x start hn hxs hzs halign d)) =
      guardedCode (FOL.allAt x φ) := certificate_correct _

/-- A canonical start above every existing named node and both binder names. -/
def freshStart (φ : Peano.Formula) (x : Nat) : Nat :=
  max ((guardedBody φ x).names.sup id) (max x (topName x φ)) + 1

theorem names_lt_freshStart (φ : Peano.Formula) (x : Nat) :
    ∀ v ∈ (guardedBody φ x).names, v < freshStart φ x := by
  intro v hv
  have hle : v ≤ (guardedBody φ x).names.sup id := Finset.le_sup (f := id) hv
  unfold freshStart
  omega

theorem x_lt_freshStart (φ : Peano.Formula) (x : Nat) : x < freshStart φ x := by
  unfold freshStart
  omega

theorem topName_lt_freshStart (φ : Peano.Formula) (x : Nat) :
    topName x φ < freshStart φ x := by
  unfold freshStart
  omega

/-- The sole remaining obligation for the generalization transformer is
finite K proof data aligning the canonical freshened guarded body with the
actual translated universal body, for every PA formula and source name. -/
structure BodyAlignment where
  align : ∀ φ : Peano.Formula, ∀ x : Nat, KDerivation (imp
    (replace x (topName x φ)
      (freshen (guardedBody φ x) (freshStart φ x) (names_lt_freshStart φ x)).formula).encode
    (imp (domainAt (topName x φ + 1) (topName x φ)).encode (topBody x φ).encode))

/-- Explicit proof transformer under the body-alignment proof-data input. -/
def generalization (h : BodyAlignment) (x : Nat) (φ : Peano.Formula)
    (d : KDerivation (guardedCode φ)) : KDerivation (guardedCode (FOL.allAt x φ)) :=
  generalize_of_guarded_body_alignment φ x (freshStart φ x) (names_lt_freshStart φ x)
    (x_lt_freshStart φ x) (topName_lt_freshStart φ x) (h.align φ x) d

/-- The remaining compiler inputs are the five nonpropositional logical
families, PA axioms including induction, and the displayed body alignment. -/
def handlers (h : BodyAlignment) (logical : PAtoCompactGuardedPropositional.RemainingLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedModusPonensFull.handlers logical arithmetic (generalization h)

end PASoundness.PAtoCompactGeneralizationConditional

#print axioms PASoundness.PAtoCompactGeneralizationConditional.topName_not_universal_free
#print axioms PASoundness.PAtoCompactGeneralizationConditional.topName_not_body_free
#print axioms PASoundness.PAtoCompactGeneralizationConditional.generalize_of_guarded_body_alignment
#print axioms PASoundness.PAtoCompactGeneralizationConditional.generalize_of_guarded_body_alignment_certificate
#print axioms PASoundness.PAtoCompactGeneralizationConditional.names_lt_freshStart
#print axioms PASoundness.PAtoCompactGeneralizationConditional.x_lt_freshStart
#print axioms PASoundness.PAtoCompactGeneralizationConditional.topName_lt_freshStart
#print axioms PASoundness.PAtoCompactGeneralizationConditional.generalization
#print axioms PASoundness.PAtoCompactGeneralizationConditional.handlers
