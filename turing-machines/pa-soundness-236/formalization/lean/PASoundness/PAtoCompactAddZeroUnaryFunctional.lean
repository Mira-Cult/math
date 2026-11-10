import PASoundness.PAtoCompactAddZeroGraphFunctionalClosed
import PASoundness.PAtoCompactUnaryGraphFunctionalityGuarded
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Guarded finite K functionality for the graph of a unary term plus zero. -/
namespace PASoundness.PAtoCompactAddZeroUnaryFunctional
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactAddZeroGraphFunctionalClosed
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- The actual `t + 0` graph is candidate-relative functional for unary t,
under the formula guard that covers t's variables. -/
noncomputable def unary_add_zero_functional {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (ht : UnaryTerm t)
    (b p q : Nat) (hb : guardBase φ ≤ b) (hp : p < b) (hq : q < b)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
        (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode
          (equivAt b p q).encode))) := by
  let c := b+1
  let d := c+64
  let g := guardFormula φ
  let s : Peano.language.Term α := binaryTerm true t (.func .zero Fin.elim0)
  have hnames : ∀ x ∈ φ.freeVarFinset, x < guardBase φ := by
    intro x hx
    have hh : x ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hx
    unfold guardBase
    omega
  have hv : ∀ a ∈ t.varFinset, v a < b := by
    intro a ha
    have hh := hnames (v a) (hcover a ha)
    omega
  have hvs : ∀ a ∈ s.varFinset, v a < b := by
    intro a ha
    have ha' : a ∈ t.varFinset := by simpa [s, binaryTerm, Term.varFinset] using ha
    exact hv a ha'
  have hgb : b ∉ g.free := by
    intro hh
    have hh' := hnames b (guardFormula_free_subset φ hh)
    omega
  have hgc : c ∉ g.free := by
    intro hh
    have hh' := hnames c (guardFormula_free_subset φ hh)
    dsimp [c] at *
    omega
  have hfirst := (termGraph_base_transport v t (b+64) d b (by omega)
    (by dsimp [d,c]; omega) (by intro a ha; have := hv a ha; omega)
    (by intro a ha; have := hv a ha; dsimp [d,c]; omega)).1
  have hfun := PASoundness.PAtoCompactUnaryGraphFunctionalityGuarded.unary_functional
    v φ ht d b c (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)
    (by dsimp [d]; omega) hcover
  have heq := (equivAt_base_alpha d (c+1) b c
    (by dsimp [d,c]; omega) (by dsimp [d,c]; omega)
    (by dsimp [c]; omega) (by omega)).forward
  have hchild : KDerivation (imp g.encode (imp (termGraph v t b (b+64)).encode
      (imp (termGraph v t c (c+64)).encode (equivAt (c+1) b c).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let A := (termGraph v t b (b+64)).encode
    let B := (termGraph v t c d).encode
    let Γ := [B,A,g.encode]
    have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
    have hA : Context Γ A := .hypothesis (by simp [Γ])
    have hB : Context Γ B := .head _ _
    exact .mp (.mp hB (.mp (.mp hA (.closed hfirst)) (.mp hg (.closed hfun)))) (.closed heq)
  have h := functionality_of_child v t b c p q g (by dsimp [c]; omega) hp hq hv hgb hgc hchild
  have htransport := (termGraph_base_transport v s b c q hq (by dsimp [c]; omega)
    hvs (by intro a ha; have := hvs a ha; dsimp [c]; omega)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v s q b).encode, (termGraph v s p b).encode, g.encode]
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (termGraph v s p b).encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ (termGraph v s q b).encode := .head _ _
  exact .mp (.mp hq' (.closed htransport)) (.mp hp' (.mp hg (.closed h)))

end PASoundness.PAtoCompactAddZeroUnaryFunctional
#print axioms PASoundness.PAtoCompactAddZeroUnaryFunctional.unary_add_zero_functional
