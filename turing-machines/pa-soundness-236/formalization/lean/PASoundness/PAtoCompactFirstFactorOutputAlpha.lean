import PASoundness.PAtoCompactLiteralCutOutputSyntax
import PASoundness.PAtoCompactMultiplicationOutputAlpha
import PASoundness.PAtoCompactAddTermBody

/-! Capture-safe output-name conversion for a retained first-factor
multiplication successor witness. This transforms a supplied existential K
proof; it does not construct the witness or an arithmetic law. -/
namespace PASoundness.PAtoCompactFirstFactorOutputAlpha

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactVacuousUniversal
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactLiteralCutOutputSyntax
open PASoundness.PAtoCompactMulTermTransportWitness PASoundness.PAtoCompactAddTermBody

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Candidate output, literal cut, ordinary sum and successor product, all at
one common output name. The three free inputs may be assigned the same value. -/
def body (b p y s q : Nat) : Formula := andF (domainAt b q)
  (andF (literalCutAt b p y q) (andF (addAt b p y q) (mulAt b s y q)))

theorem source_not_binder (b p y s q : Nat) (hq : q < b) :
    q ∉ (body b p y s q).binders := by
  intro h
  simp only [body, andF_binders, Finset.mem_union] at h
  rcases h with hd | hc | ha | hm
  · have hh := domainAt_private b q q hd; omega
  · have hh := literalCutAt_private b p y q q hc; omega
  · have hh := addAt_private b p y q q ha; omega
  · have hh := mulAt_private b s y q q hm; omega

theorem target_not_names (b p y s q out : Nat) (ho : out < b+2)
    (hop : out ≠ p) (hoy : out ≠ y) (hos : out ≠ s) (hoq : out ≠ q) :
    out ∉ (body b p y s q).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with hf | hb
  · simp only [body, andF_free, Finset.mem_union] at hf
    rcases hf with hd | hc | ha | hm
    · have hh := domainAt_free b q hd
      simp only [Finset.mem_singleton] at hh
      exact hoq hh
    · have hh := literalCutAt_free b p y q hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hop hh
      · exact hoy hh
      · exact hoq hh
    · have hh := addAt_free b p y q ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hop hh
      · exact hoy hh
      · exact hoq hh
    · have hh := mulAt_free b s y q hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hos hh
      · exact hoy hh
      · exact hoq hh
  · simp only [body, andF_binders, Finset.mem_union] at hb
    rcases hb with hd | hc | ha | hm
    · have hh := domainAt_private b q out hd; omega
    · have hh := literalCutAt_private b p y q out hc; omega
    · have hh := addAt_private b p y q out ha; omega
    · have hh := mulAt_private b s y q out hm; omega

theorem replace_body (b p y s q out : Nat) (hq : q < b)
    (hqp : q ≠ p) (hqy : q ≠ y) (hqs : q ≠ s) :
    replace q out (body b p y s q) = body b p y s out := by
  rw [body, body]
  simp only [andF, Formula.not, replace]
  rw [replace_domainAt b q out hq, replace_literalCutAt b p y q q out (by omega),
    replace_addAt b p y q q out (by omega), replace_mulAt b s y q q out (by omega)]
  simp [rename, Ne.symm hqp, Ne.symm hqy, Ne.symm hqs]

/-- Change the bound output label while preserving the same witness across
all four conjuncts. The old and new output labels must be distinct from the
three free inputs; the inputs themselves may coincide. -/
def output_alpha (b p y s q out : Nat) (hq : q < b) (ho : out < b+2)
    (hqp : q ≠ p) (hqy : q ≠ y) (hqs : q ≠ s) (hqo : q ≠ out)
    (hop : out ≠ p) (hoy : out ≠ y) (hos : out ≠ s) :
    KDerivation (imp (existsCode q (body b p y s q).encode)
      (existsCode out (body b p y s out).encode)) := by
  have h := existentialAlpha q out (body b p y s q) hqo
    (source_not_binder b p y s q hq)
    (target_not_names b p y s q out ho hop hoy hos (Ne.symm hqo))
  rw [replace_body b p y s q out hq hqp hqy hqs] at h
  exact h.1

theorem output_alpha_certificate (b p y s q out : Nat) (hq : q < b) (ho : out < b+2)
    (hqp : q ≠ p) (hqy : q ≠ y) (hqs : q ≠ s) (hqo : q ≠ out)
    (hop : out ≠ p) (hoy : out ≠ y) (hos : out ≠ s) :
    theoremCode (certificate (output_alpha b p y s q out hq ho hqp hqy hqs hqo hop hoy hos)) =
      imp (existsCode q (body b p y s q).encode) (existsCode out (body b p y s out).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactFirstFactorOutputAlpha

#print axioms PASoundness.PAtoCompactFirstFactorOutputAlpha.body
#print axioms PASoundness.PAtoCompactFirstFactorOutputAlpha.source_not_binder
#print axioms PASoundness.PAtoCompactFirstFactorOutputAlpha.target_not_names
#print axioms PASoundness.PAtoCompactFirstFactorOutputAlpha.replace_body
#print axioms PASoundness.PAtoCompactFirstFactorOutputAlpha.output_alpha
#print axioms PASoundness.PAtoCompactFirstFactorOutputAlpha.output_alpha_certificate
