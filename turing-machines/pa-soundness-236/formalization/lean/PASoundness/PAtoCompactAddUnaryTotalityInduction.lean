import PASoundness.PAtoCompactAdditionGraphFromChildren
import PASoundness.PAtoCompactUnaryTotalityInduction

/-! Conditional construction of generated term graphs for the fragment of PA
terms built from variables, zero, successor and addition. The supplied
successor and addition operation families are finite K proof data. This module
makes no assertion about multiplication, functionality or PA soundness. -/
namespace PASoundness.PAtoCompactAddUnaryTotalityInduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactUnaryTotalityInduction
open PASoundness.PAtoCompactAdditionGraphFromChildren
open PASoundness.PAtoCompactTermZeroGuarded

/-- Type-valued evidence permits structural recursion that constructs finite
K derivations. -/
inductive AddUnaryTerm {α : Type} : Peano.language.Term α → Type
  | var (a : α) : AddUnaryTerm (.var a)
  | zero : AddUnaryTerm (.func .zero Fin.elim0)
  | succ {t : Peano.language.Term α} : AddUnaryTerm t → AddUnaryTerm (.func .succ ![t])
  | add {t u : Peano.language.Term α} : AddUnaryTerm t → AddUnaryTerm u → AddUnaryTerm (.func .add ![t, u])

/-- Source-variable candidate proofs, and operation-existence families, give
an actual graph witness for every term in the addition-unary fragment. The
output name is strictly above all free names of the guard and mapped source
variables, with one spare name below the allocator base. -/
noncomputable def total {α : Type} [DecidableEq α] (v : α → Nat)
    (next : SuccessorExistence) (plus : AdditionExistence) (g : Formula)
    {t : Peano.language.Term α} (h : AddUnaryTerm t) : ∀ b out,
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
  | @add t u ht hu iht ihu =>
      intro b out hb hg hv hd
      have htvars : ∀ a ∈ t.varFinset, v a < out := by
        intro a ha
        apply hv a
        simp [Term.varFinset, ha]
      have huvars : ∀ a ∈ u.varFinset, v a < out := by
        intro a ha
        apply hv a
        simp [Term.varFinset, ha]
      have hguardt : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode) := by
        intro a ha
        apply hd a
        simp [Term.varFinset, ha]
      have hguardu : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode) := by
        intro a ha
        apply hd a
        simp [Term.varFinset, ha]
      have htguard : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt (b+64) (v a)).encode) := by
        intro a ha
        exact compose (hguardt a ha) (PAtoCompactGuardBaseTransport.domainAt_transport b (b+64) (v a)
          (by have := htvars a ha; omega) (by have := htvars a ha; omega))
      have huguard : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt (b+64+termCost t) (v a)).encode) := by
        intro a ha
        exact compose (hguardu a ha) (PAtoCompactGuardBaseTransport.domainAt_transport b (b+64+termCost t) (v a)
          (by have := huvars a ha; omega) (by have := huvars a ha; omega))
      have childt := iht (b+64) b (by omega)
        (by intro z hz; have := hg z hz; omega)
        (by intro a ha; have := htvars a ha; omega) htguard
      have childu := ihu (b+64+termCost t) (b+1) (by omega)
        (by intro z hz; have := hg z hz; omega)
        (by intro a ha; have := huvars a ha; omega) huguard
      simpa [binaryTerm] using add_total_from_children v t u b out g (by omega) hg htvars huvars plus childt childu

theorem total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (next : SuccessorExistence) (plus : AdditionExistence) (g : Formula)
    {t : Peano.language.Term α} (h : AddUnaryTerm t) (b out : Nat)
    (hb : out + 1 < b) (hg : ∀ z ∈ g.free, z < out)
    (hv : ∀ a ∈ t.varFinset, v a < out)
    (hd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) :
    theoremCode (certificate (total v next plus g h b out hb hg hv hd)) =
      imp g.encode (existsCode out (termGraph v t out b).encode) := certificate_correct _
end PASoundness.PAtoCompactAddUnaryTotalityInduction
#print axioms PASoundness.PAtoCompactAddUnaryTotalityInduction.total
#print axioms PASoundness.PAtoCompactAddUnaryTotalityInduction.total_certificate
