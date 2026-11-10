import PASoundness.PAtoCompactMulZeroAxiomGraphCompose
import PASoundness.PAtoCompactMultiplicationRightZeroOutput
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactAddUnaryTotalityClosed
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! Conditional guarded graph existence for an arbitrary PA term times zero,
retaining the zero graph at the same output. The child graph proof is explicit. -/
namespace PASoundness.PAtoCompactMulZeroAxiomGraphConditional
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTermZeroGuarded PASoundness.PAtoCompactMulZeroAxiomGraphCompose
open PASoundness.PAtoCompactAddUnaryTotalityInduction PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactFormulaTranslation
set_option maxRecDepth 65536
set_option maxHeartbeats 0

noncomputable def mul_zero_total_with_zero {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α}
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset)
    (child : let b := guardBase φ + 2
      KDerivation (imp (guardFormula φ).encode (existsCode b (termGraph v t b (b+64)).encode))) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (guardBase φ) (andF (termGraph v
        (binaryTerm false t (.func .zero Fin.elim0)) (guardBase φ) (guardBase φ+2))
        (zeroAt (guardBase φ+2) (guardBase φ))).encode)) := by
  let out := guardBase φ
  let b := out + 2
  let g := guardFormula φ
  let z : Peano.language.Term α := .func .zero Fin.elim0
  let T := termGraph v t b (b+64)
  let Z := termGraph v z (b+1) (b+64+termCost t)
  let E := Formula.ex out (andF (termGraph v (binaryTerm false t z) out b) (zeroAt b out))
  have hglt : ∀ w ∈ g.free, w < out := by
    intro w hw
    have hm := PAtoCompactGuardedVacuity.guardFormula_free_subset φ hw
    have hl : w ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hm
    dsimp [out, guardBase]
    omega
  have hnames : ∀ w ∈ φ.freeVarFinset, w < out := by
    intro w hw
    have hl : w ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hw
    dsimp [out, guardBase]
    omega
  have hvlt : ∀ a ∈ t.varFinset, v a < out := by
    intro a ha
    exact hnames (v a) (hcover a ha)
  have hG (k : Nat) (hk : out ≤ k) : k ∉ g.free := by
    intro hm
    have hh := hglt k hm
    omega
  have hT (k : Nat) (hk : out ≤ k) (hkb : k ≠ b) : k ∉ T.free := by
    intro hm
    have hh := termGraph_free_subset v t b (b+64) hm
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
      have hl := hvlt a ha
      omega
    · exact hkb (Finset.mem_singleton.mp hh)
  have hZ (k : Nat) (hk : k ≠ b+1) : k ∉ Z.free := by
    intro hm
    have hh := termGraph_free_subset v z (b+1) (b+64+termCost t) hm
    apply hk
    simpa [z, Term.varFinset] using hh
  have hE (k : Nat) (hk : out ≤ k) : k ∉ E.free := by
    intro hm
    have he : k ≠ out ∧ k ∈ (andF (termGraph v (binaryTerm false t z) out b) (zeroAt b out)).free := by
      simpa [E, Formula.free] using hm
    simp only [andF_free, Finset.mem_union] at he
    rcases he.2 with htfree | hzfree
    · have hh := termGraph_free_subset v (binaryTerm false t z) out b htfree
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hh
        have ha' : a ∈ t.varFinset := by simpa [binaryTerm, z, Term.varFinset] using ha
        have hl := hvlt a ha'
        omega
      · exact he.1 (Finset.mem_singleton.mp hh)
    · have hh := zeroAt_free b out hzfree
      exact he.1 (Finset.mem_singleton.mp hh)
  have child1 : KDerivation (imp g.encode (existsCode b T.encode)) := by
    exact child
  have child2 : KDerivation (imp g.encode (existsCode (b+1) Z.encode)) := by
    have hz := PAtoCompactZeroTermTotality.zero_term_total v (b+64+termCost t) (b+1) (by omega)
    exact .mp hz (PASoundness.CompactHilbertBasis.weakening _ _)
  have op : KDerivation (imp T.encode (imp Z.encode
      (existsCode out (andF (domainAt b out) (andF (zeroAt b out) (binaryRel false b b (b+1) out))).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [Z.encode, T.encode]
    have hZ' : Context Γ Z.encode := .hypothesis (by simp [Γ])
    have hz0 : Context Γ (zeroAt (b+64+termCost t) (b+1)).encode := by
      have hboth : Context Γ (both (domainAt (b+64+termCost t) (b+1)).encode
          (zeroAt (b+64+termCost t) (b+1)).encode) := by
        simpa [Z, z, termGraph, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hZ'
      exact Context.conjunctionRight hboth
    have hz : Context Γ (zeroAt b (b+1)).encode := .mp hz0
      (.closed (PAtoCompactZeroBaseTransport.zeroAt_base_forward _ _ _ (by omega) (by omega)))
    have hz2 : Context Γ (zeroAt (b+2) (b+1)).encode := .mp hz
      (.closed (PAtoCompactZeroBaseTransport.zeroAt_base_forward b (b+2) (b+1) (by omega) (by omega)))
    have hres := PAtoCompactMultiplicationRightZeroOutput.right_zero_output (b+2) b (b+1) out
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hbody : KDerivation (imp
        (andF (domainAt (b+2) out) (andF (zeroAt (b+2) out) (mulAt (b+2) b (b+1) out))).encode
        (andF (domainAt b out) (andF (zeroAt b out) (mulAt b b (b+1) out))).encode) := by
      apply Context.closeEmpty
      apply Context.deduction
      let A := (domainAt (b+2) out).encode
      let B := (zeroAt (b+2) out).encode
      let C := (mulAt (b+2) b (b+1) out).encode
      let Γ' := [(andF (domainAt (b+2) out) (andF (zeroAt (b+2) out) (mulAt (b+2) b (b+1) out))).encode]
      have hp : Context Γ' (both A (both B C)) := by
        have hh := Context.head [] (andF (domainAt (b+2) out) (andF (zeroAt (b+2) out) (mulAt (b+2) b (b+1) out))).encode
        simpa [Γ', A, B, C, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
      have hda : Context Γ' (domainAt b out).encode := .mp (Context.conjunctionLeft hp)
        (.closed (PAtoCompactGuardBaseTransport.domainAt_transport (b+2) b out (by omega) (by omega)))
      have hma : Context Γ' (mulAt b b (b+1) out).encode := .mp (Context.conjunctionRight (Context.conjunctionRight hp))
        (.closed (PAtoCompactMulBaseMultiAlpha.mulAt_base_alpha (b+2) b b (b+1) out
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).forward)
      have hza : Context Γ' (zeroAt b out).encode := .mp (Context.conjunctionLeft (Context.conjunctionRight hp))
        (.closed (PAtoCompactZeroBaseTransport.zeroAt_base_forward (b+2) b out (by omega) (by omega)))
      have hh := Context.conjunctionIntro hda (Context.conjunctionIntro hza hma)
      simpa [Γ', andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
    have hc := existsCongr out hbody
    simpa [binaryRel] using (Context.mp (Context.mp hz2 (.closed hres)) (.closed hc))
  have result := binary_total_with_zero_from_children v false t z b out g (by dsimp [b]; omega)
    child1 child2 op
    (free_vacuity b g (hG b (by dsimp [b]; omega)))
    (free_vacuity (b+1) g (hG (b+1) (by dsimp [b]; omega)))
    (free_vacuity out g (hG out (by omega)))
    (free_vacuity (b+1) T (hT (b+1) (by dsimp [b]; omega) (by omega)))
    (free_vacuity out T (hT out (by omega) (by dsimp [b]; omega)))
    (free_vacuity out Z (hZ out (by dsimp [b]; omega)))
    (by simpa [E, Formula.encode] using free_vacuity b E (hE b (by dsimp [b]; omega)))
    (by simpa [E, Formula.encode] using free_vacuity (b+1) E (hE (b+1) (by dsimp [b]; omega)))
    (by simpa [E, Formula.encode] using free_vacuity out E (hE out (by omega)))
  exact result


/-- The certificate has exactly the guarded same-output graph and zero code. -/
theorem mul_zero_total_with_zero_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α}
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset)
    (child : let b := guardBase φ + 2
      KDerivation (imp (guardFormula φ).encode (existsCode b (termGraph v t b (b+64)).encode))) :
    theoremCode (certificate (mul_zero_total_with_zero v φ hcover child)) =
      imp (guardFormula φ).encode
        (existsCode (guardBase φ) (andF (termGraph v
          (binaryTerm false t (.func .zero Fin.elim0)) (guardBase φ) (guardBase φ+2))
          (zeroAt (guardBase φ+2) (guardBase φ))).encode) := certificate_correct _

end PASoundness.PAtoCompactMulZeroAxiomGraphConditional

#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphConditional.mul_zero_total_with_zero
#print axioms PASoundness.PAtoCompactMulZeroAxiomGraphConditional.mul_zero_total_with_zero_certificate
