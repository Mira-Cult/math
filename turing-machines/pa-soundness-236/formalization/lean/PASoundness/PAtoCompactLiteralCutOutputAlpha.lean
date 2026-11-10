import PASoundness.PAtoCompactLiteralCutOutputSyntax
import PASoundness.PAtoCompactVacuousUniversal

/-! Existential output-name alpha conversion for the allocated literal-cut
addition relation. The proof only transforms an existing K witness; it does
not establish addition totality, multiplication, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutOutputAlpha
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactVacuousUniversal
open PASoundness.PAtoCompactLiteralCutBaseSyntax PASoundness.PAtoCompactLiteralCutOutputSyntax

def body (b x y q : Nat) : Formula := andF (domainAt b q) (literalCutAt b x y q)

theorem source_not_binder (b x y q : Nat) (hq : q < b) :
    q ∉ (body b x y q).binders := by
  intro h
  simp only [body, andF_binders, Finset.mem_union] at h
  rcases h with h | h
  · have hh := domainAt_private b q q h; omega
  · have hh := literalCutAt_private b x y q q h; omega

theorem target_not_names (b x y q out : Nat) (ho : out < b+2)
    (hxo : out ≠ x) (hyo : out ≠ y) (hqo : out ≠ q) :
    out ∉ (body b x y q).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with h | h
  · simp only [body, andF_free, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_free b q h
      simp only [Finset.mem_singleton] at hh
      exact hqo hh
    · have hh := literalCutAt_free b x y q h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hxo hh
      · exact hyo hh
      · exact hqo hh
  · simp only [body, andF_binders, Finset.mem_union] at h
    rcases h with h | h
    · have hh := domainAt_private b q out h; omega
    · have hh := literalCutAt_private b x y q out h; omega

theorem replace_body (b x y q out : Nat) (hq : q < b) (hqx : q ≠ x) (hqy : q ≠ y) :
    replace q out (body b x y q) = body b x y out := by
  rw [body, body]
  simp only [andF, Formula.not, replace]
  rw [replace_domainAt b q out hq, replace_literalCutAt b x y q q out (by omega)]
  simp [rename, Ne.symm hqx, Ne.symm hqy]

/-- Rename the existential output, preserving both candidate and literal-cut
relations. Inputs may share a name; each output name is fresh for them. -/
def output_alpha (b x y q out : Nat) (hq : q < b) (ho : out < b+2)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqo : q ≠ out)
    (hox : out ≠ x) (hoy : out ≠ y) :
    KDerivation (imp (existsCode q (body b x y q).encode)
      (existsCode out (body b x y out).encode)) := by
  have h := existentialAlpha q out (body b x y q) hqo
    (source_not_binder b x y q hq)
    (target_not_names b x y q out ho hox hoy (Ne.symm hqo))
  rw [replace_body b x y q out hq hqx hqy] at h
  exact h.1

theorem output_alpha_certificate (b x y q out : Nat) (hq : q < b) (ho : out < b+2)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqo : q ≠ out)
    (hox : out ≠ x) (hoy : out ≠ y) :
    theoremCode (certificate (output_alpha b x y q out hq ho hqx hqy hqo hox hoy)) =
      imp (existsCode q (body b x y q).encode) (existsCode out (body b x y out).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactLiteralCutOutputAlpha
#print axioms PASoundness.PAtoCompactLiteralCutOutputAlpha.output_alpha
#print axioms PASoundness.PAtoCompactLiteralCutOutputAlpha.output_alpha_certificate
