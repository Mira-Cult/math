import PASoundness.PAtoCompactSuccTermTransport
import PASoundness.PAtoCompactVariableTermBaseTransport

/-! Finite K base transport for the source fragment consisting of variables,
zero and successor. Addition and multiplication are not in this fragment. -/
namespace PASoundness.PAtoCompactUnaryTermTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactZeroTermBaseTransport PASoundness.PAtoCompactVariableTermBaseTransport
open PASoundness.PAtoCompactSuccTermTransport

/-- Type-valued structural evidence so that the result can construct finite
K derivation data by recursion, without extracting it from an erased proof. -/
inductive UnaryTerm {α : Type} : Peano.language.Term α → Type
  | var (a : α) : UnaryTerm (.var a)
  | zero : UnaryTerm (.func .zero Fin.elim0)
  | succ {t : Peano.language.Term α} : UnaryTerm t → UnaryTerm (.func .succ ![t])

/-- Base transport for every unary-fragment term. Inputs and output are
strictly below both allocation bases; they may coincide with one another.
The declaration is noncomputable; it is not claimed as an executable proof
extractor. -/
noncomputable def unaryTerm_base_transport {α : Type} [DecidableEq α] (v : α → Nat)
    {t : Peano.language.Term α} (h : UnaryTerm t) : ∀ b c out,
    out < b → out < c → (∀ a ∈ t.varFinset, v a < b) →
      (∀ a ∈ t.varFinset, v a < c) →
    KDerivation (imp (termGraph v t out b).encode (termGraph v t out c).encode) ×
    KDerivation (imp (termGraph v t out c).encode (termGraph v t out b).encode) := by
  induction h with
  | var a =>
      intro b c out hob hoc hvb hvc
      have hba : v a < b := hvb a (by simp [Term.varFinset])
      have hca : v a < c := hvc a (by simp [Term.varFinset])
      exact ⟨variableTerm_base_forward v a b c out (by omega) (by omega) (by omega) (by omega),
        variableTerm_base_backward v a b c out (by omega) (by omega) (by omega) (by omega)⟩
  | zero =>
      intro b c out hob hoc hvb hvc
      exact ⟨zeroTerm_base_forward v b c out (by omega) (by omega),
        zeroTerm_base_backward v b c out (by omega) (by omega)⟩
  | @succ t h ih =>
      intro b c out hob hoc hvb hvc
      have hvbt : ∀ a ∈ t.varFinset, v a < b := by
        intro a ha
        apply hvb a
        simp [Term.varFinset, ha]
      have hvct : ∀ a ∈ t.varFinset, v a < c := by
        intro a ha
        apply hvc a
        simp [Term.varFinset, ha]
      have hbd := ih (b + 64) (intermediateBase b c + 64) b (by omega) (by
        unfold intermediateBase; omega)
        (by intro a ha; have := hvbt a ha; omega)
        (by intro a ha; have := hvbt a ha; unfold intermediateBase; omega)
      have hcd := ih (c + 64) (intermediateBase b c + 64) c (by omega) (by
        unfold intermediateBase; omega)
        (by intro a ha; have := hvct a ha; omega)
        (by intro a ha; have := hvct a ha; unfold intermediateBase; omega)
      exact succTerm_base_transport v t b c out hob hoc hvbt hvct
        hbd.1 hbd.2 hcd.1 hcd.2

theorem unaryTerm_base_forward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    {t : Peano.language.Term α} (h : UnaryTerm t) (b c out : Nat)
    (hob : out < b) (hoc : out < c)
    (hvb : ∀ a ∈ t.varFinset, v a < b) (hvc : ∀ a ∈ t.varFinset, v a < c) :
    theoremCode (certificate (unaryTerm_base_transport v h b c out hob hoc hvb hvc).1) =
      imp (termGraph v t out b).encode (termGraph v t out c).encode := certificate_correct _

theorem unaryTerm_base_backward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    {t : Peano.language.Term α} (h : UnaryTerm t) (b c out : Nat)
    (hob : out < b) (hoc : out < c)
    (hvb : ∀ a ∈ t.varFinset, v a < b) (hvc : ∀ a ∈ t.varFinset, v a < c) :
    theoremCode (certificate (unaryTerm_base_transport v h b c out hob hoc hvb hvc).2) =
      imp (termGraph v t out c).encode (termGraph v t out b).encode := certificate_correct _

end PASoundness.PAtoCompactUnaryTermTransport

#print axioms PASoundness.PAtoCompactUnaryTermTransport.unaryTerm_base_transport
#print axioms PASoundness.PAtoCompactUnaryTermTransport.unaryTerm_base_forward_certificate
#print axioms PASoundness.PAtoCompactUnaryTermTransport.unaryTerm_base_backward_certificate
