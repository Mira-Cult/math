import PASoundness.PAtoCompactMulZeroAxiomGraphCompose
import PASoundness.PAtoCompactFirstZeroRetainedOutput
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! Shared zero output for the graph of `0 * t`. The term-graph existence
proof for `t` is supplied explicitly in this module. The result uses finite K
proof transformations and does not assume multiplication functionality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFirstFactorZeroGraph

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTermZeroGuarded PASoundness.PAtoCompactMulZeroAxiomGraphCompose
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactFormulaTranslation

/-- Given a guarded graph output for the arbitrary right factor, produce a
single graph output for `0 * t` which also satisfies zero. -/
noncomputable def first_zero_total_with_zero {α : Type} [DecidableEq α]
    (v : α → Nat) (φ : Peano.Formula) {t : Peano.language.Term α}
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset)
    (child : let b := guardBase φ + 2
      KDerivation (imp (guardFormula φ).encode
        (existsCode (b+1) (termGraph v t (b+1)
          (b+64+termCost (.func .zero Fin.elim0 : Peano.language.Term α))).encode))) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (guardBase φ) (andF (termGraph v
        (binaryTerm false (.func .zero Fin.elim0) t) (guardBase φ) (guardBase φ+2))
        (zeroAt (guardBase φ+2) (guardBase φ))).encode)) := by
  let out := guardBase φ
  let b := out + 2
  let g := guardFormula φ
  let z : Peano.language.Term α := .func .zero Fin.elim0
  let Z := termGraph v z b (b+64)
  let T := termGraph v t (b+1) (b+64+termCost z)
  let E := Formula.ex out (andF (termGraph v (binaryTerm false z t) out b) (zeroAt b out))
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
  have hZ (k : Nat) (hk : k ≠ b) : k ∉ Z.free := by
    intro hm
    have hh := termGraph_free_subset v z b (b+64) hm
    apply hk
    simpa [z, Term.varFinset] using hh
  have hT (k : Nat) (hk : out ≤ k) (hkb : k ≠ b+1) : k ∉ T.free := by
    intro hm
    have hh := termGraph_free_subset v t (b+1) (b+64+termCost z) hm
    rcases Finset.mem_union.mp hh with hh | hh
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
      have hl := hvlt a ha
      omega
    · exact hkb (Finset.mem_singleton.mp hh)
  have hE (k : Nat) (hk : out ≤ k) : k ∉ E.free := by
    intro hm
    have he : k ≠ out ∧ k ∈ (andF (termGraph v (binaryTerm false z t) out b) (zeroAt b out)).free := by
      simpa [E, Formula.free] using hm
    simp only [andF_free, Finset.mem_union] at he
    rcases he.2 with htfree | hzfree
    · have hh := termGraph_free_subset v (binaryTerm false z t) out b htfree
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hh
        have ha' : a ∈ t.varFinset := by simpa [binaryTerm, z, Term.varFinset] using ha
        have hl := hvlt a ha'
        omega
      · exact he.1 (Finset.mem_singleton.mp hh)
    · have hh := zeroAt_free b out hzfree
      exact he.1 (Finset.mem_singleton.mp hh)
  have child1 : KDerivation (imp g.encode (existsCode b Z.encode)) := by
    have hz := PAtoCompactZeroTermTotality.zero_term_total v (b+64) b (by omega)
    exact .mp hz (PASoundness.CompactHilbertBasis.weakening _ _)
  have child2 : KDerivation (imp g.encode (existsCode (b+1) T.encode)) := by
    exact child
  have op : KDerivation (imp Z.encode (imp T.encode
      (existsCode out (andF (domainAt b out)
        (andF (zeroAt b out) (binaryRel false b b (b+1) out))).encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [T.encode, Z.encode]
    have hZ' : Context Γ Z.encode := .hypothesis (by simp [Γ])
    have hz0 : Context Γ (zeroAt (b+64) b).encode := by
      have hboth : Context Γ (both (domainAt (b+64) b).encode
          (zeroAt (b+64) b).encode) := by
        simpa [Z, z, termGraph, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hZ'
      exact Context.conjunctionRight hboth
    have hz : Context Γ (zeroAt (b+2) b).encode := .mp hz0
      (.closed (PAtoCompactZeroBaseTransport.zeroAt_base_forward (b+64) (b+2) b (by omega) (by omega)))
    have hres := PAtoCompactFirstZeroRetainedOutput.retained_output (b+2) b (b+1) out
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hbody : KDerivation (imp
        (andF (domainAt (b+2) out) (andF (zeroAt (b+2) out) (mulAt (b+2) b (b+1) out))).encode
        (andF (domainAt b out) (andF (zeroAt b out) (mulAt b b (b+1) out))).encode) := by
      apply Context.closeEmpty
      apply Context.deduction
      let A := (domainAt (b+2) out).encode
      let B := (zeroAt (b+2) out).encode
      let C := (mulAt (b+2) b (b+1) out).encode
      let Δ := [(andF (domainAt (b+2) out) (andF (zeroAt (b+2) out) (mulAt (b+2) b (b+1) out))).encode]
      have hp : Context Δ (both A (both B C)) := by
        have hh := Context.head [] (andF (domainAt (b+2) out) (andF (zeroAt (b+2) out) (mulAt (b+2) b (b+1) out))).encode
        simpa [Δ, A, B, C, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
      have hda : Context Δ (domainAt b out).encode := .mp (Context.conjunctionLeft hp)
        (.closed (PAtoCompactGuardBaseTransport.domainAt_transport (b+2) b out (by omega) (by omega)))
      have hma : Context Δ (mulAt b b (b+1) out).encode := .mp (Context.conjunctionRight (Context.conjunctionRight hp))
        (.closed (PAtoCompactMulBaseMultiAlpha.mulAt_base_alpha (b+2) b b (b+1) out
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).forward)
      have hza : Context Δ (zeroAt b out).encode := .mp (Context.conjunctionLeft (Context.conjunctionRight hp))
        (.closed (PAtoCompactZeroBaseTransport.zeroAt_base_forward (b+2) b out (by omega) (by omega)))
      have hh := Context.conjunctionIntro hda (Context.conjunctionIntro hza hma)
      simpa [Δ, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hh
    have hc := existsCongr out hbody
    simpa [binaryRel] using (Context.mp (Context.mp hz (.closed hres)) (.closed hc))
  exact binary_total_with_zero_from_children v false z t b out g (by dsimp [b]; omega)
    child1 child2 op
    (free_vacuity b g (hG b (by dsimp [b]; omega)))
    (free_vacuity (b+1) g (hG (b+1) (by dsimp [b]; omega)))
    (free_vacuity out g (hG out (by omega)))
    (free_vacuity (b+1) Z (hZ (b+1) (by omega)))
    (free_vacuity out Z (hZ out (by dsimp [b]; omega)))
    (free_vacuity out T (hT out (by omega) (by dsimp [b]; omega)))
    (by simpa [E, Formula.encode] using free_vacuity b E (hE b (by dsimp [b]; omega)))
    (by simpa [E, Formula.encode] using free_vacuity (b+1) E (hE (b+1) (by dsimp [b]; omega)))
    (by simpa [E, Formula.encode] using free_vacuity out E (hE out (by omega)))

end PASoundness.PAtoCompactFirstFactorZeroGraph

#print axioms PASoundness.PAtoCompactFirstFactorZeroGraph.first_zero_total_with_zero
