import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactZeroTermTotality
import PASoundness.PAtoCompactVariableTotalityGeneral
import PASoundness.PAtoCompactUnaryTermTransport
import PASoundness.PAtoCompactGuardBaseTransport

/-! A conditional unary-term totality induction. The source guard provides
candidate proofs for the variables. The only remaining arithmetic input is
an explicit finite K quotient-successor existence family. -/
namespace PASoundness.PAtoCompactUnaryTotalityInduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactUnaryTermTransport

/-- Proof-data input for quotient-successor existence. Names are syntactic
labels; the objects assigned to them may coincide. -/
structure SuccessorExistence where
  next : ∀ (b x out : Nat), x < b → out < b → x ≠ out →
    KDerivation (imp (domainAt (b+64) x).encode
      (existsCode out (andF (domainAt b out) (succAt b x out)).encode))

/-- Every term built from variables, zero, and successor has a graph output
under the supplied candidate guard. The output name exceeds all guard-free and
source variable names, with room for a temporary witness below the allocator.
The successor existence family remains explicit proof data. -/
noncomputable def unary_total {α : Type} [DecidableEq α] (v : α → Nat)
    (next : SuccessorExistence) (g : Formula) {t : Peano.language.Term α}
    (h : UnaryTerm t) : ∀ b out,
    out + 1 < b → (∀ z ∈ g.free, z < out) →
    (∀ a ∈ t.varFinset, v a < out) →
    (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
    KDerivation (imp g.encode (existsCode out (termGraph v t out b).encode)) := by
  induction h with
  | var a =>
      intro b out hb hg hv hd
      have ha : a ∈ (Term.var a : Peano.language.Term α).varFinset := by simp [Term.varFinset]
      have hlt := hv a ha
      exact compose (hd a ha)
        (PAtoCompactVariableTotalityGeneral.variable_graph_total v a b out (by omega) (by omega) (by omega))
  | zero =>
      intro b out hb hg hv hd
      let e := existsCode out (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out b).encode
      exact .mp (PAtoCompactZeroTermTotality.zero_term_total v b out (by omega)) (weakening e g.encode)
  | @succ t h ih =>
      intro b out hb hg hv hd
      let x := out + 1
      have hvars : ∀ a ∈ t.varFinset, v a < out := by
        intro a ha
        apply hv a
        simp [Term.varFinset, ha]
      have hguard : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode) := by
        intro a ha
        apply hd a
        simp [Term.varFinset, ha]
      have hguard' : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt (b+64) (v a)).encode) := by
        intro a ha
        exact compose (hguard a ha)
          (PAtoCompactGuardBaseTransport.domainAt_transport b (b+64) (v a)
            (by have := hvars a ha; omega) (by have := hvars a ha; omega))
      have child := ih (b+64) x (by dsimp [x]; omega)
        (by intro z hz; have := hg z hz; dsimp [x]; omega)
        (by intro a ha; have := hvars a ha; dsimp [x]; omega) hguard'
      apply PAtoCompactSuccTermTotality.succ_total_from_fresh_child v t b out x g
        (by omega) (by dsimp [x]; omega) (by dsimp [x]; omega)
        (by intro a ha; have := hvars a ha; omega)
        (by intro a ha; have := hvars a ha; dsimp [x]; omega)
        (by intro a ha; have := hvars a ha; omega)
        (by intro h; have := hg x h; dsimp [x] at *; omega)
        (by intro h; have := hg out h; omega)
        child
      exact next.next b x out (by dsimp [x]; omega) (by omega) (by dsimp [x]; omega)

theorem unary_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (next : SuccessorExistence) (g : Formula) {t : Peano.language.Term α}
    (h : UnaryTerm t) (b out : Nat) (hb : out + 1 < b)
    (hg : ∀ z ∈ g.free, z < out) (hv : ∀ a ∈ t.varFinset, v a < out)
    (hd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) :
    theoremCode (certificate (unary_total v next g h b out hb hg hv hd)) =
      imp g.encode (existsCode out (termGraph v t out b).encode) := certificate_correct _


end PASoundness.PAtoCompactUnaryTotalityInduction

#print axioms PASoundness.PAtoCompactUnaryTotalityInduction.unary_total
#print axioms PASoundness.PAtoCompactUnaryTotalityInduction.unary_total_certificate
