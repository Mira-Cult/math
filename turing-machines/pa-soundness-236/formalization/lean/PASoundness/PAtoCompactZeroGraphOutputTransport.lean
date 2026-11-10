import PASoundness.PAtoCompactZeroGraphOutput

/-! Candidate-relative finite-K output transport for the zero term graph.
The output labels may coincide; allocator bounds prevent name capture. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactZeroGraphOutputTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryGraphFunctional
open PASoundness.PAtoCompactZeroGraphOutput PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactEquivNoShadow
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def outputFrame (b x y : Nat) : Formula :=
  .imp (zeroAt b x) (.imp (equivAt b x y) (zeroAt b y))

/-- Transport the canonical fixed-label output proof to one high private block. -/
def canonical_high (b : Nat) (hb : 40 ≤ b) : KDerivation (outputFrame b 0 1).encode := by
  have hz0 := zeroAt_base_forward b 33 0 (by omega) (by omega)
  have hz1 := zeroAt_base_forward 34 b 1 (by omega) (by omega)
  have h0 : KDerivation (imp (zeroAt b 0).encode (zeroCode 0 36)) := by
    have he : (zeroAt 33 0).encode = zeroCode 0 36 := rfl
    rw [← he]
    exact hz0
  have h1 : KDerivation (imp (zeroCode 1 37) (zeroAt b 1).encode) := by
    have he : (zeroAt 34 1).encode = zeroCode 1 37 := rfl
    rw [← he]
    exact hz1
  have he : KDerivation (imp (equivAt b 0 1).encode equivalentFormula.encode) := by
    have hh := (canonical_equiv_alpha b hb).backward
    change KDerivation (imp (equivAt b 0 1).encode (normalizeBottom equivalentFormula).encode) at hh
    rw [normalizeBottom_encode] at hh
    exact hh
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let A := (zeroAt b 0).encode
  let E := (equivAt b 0 1).encode
  let Γ := [E,A]
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have hz : Context Γ (zeroCode 0 36) := .mp hA (.closed h0)
  have heq : Context Γ equivalentFormula.encode := .mp hE (.closed he)
  have hresult : Context Γ (zeroCode 1 37) :=
    .mp heq (.mp hz (.closed canonical_zero_output))
  exact .mp hresult (.closed h1)

theorem frame_not_binder (b x y a : Nat) (ha : a < b) :
    a ∉ (outputFrame b x y).binders := by
  simp only [outputFrame, Formula.binders, Finset.mem_union, not_or]
  constructor
  · simp [zeroAt_shape, Formula.binders]; omega
  constructor
  · intro h
    have ht := equivAt_private b x y a h
    omega
  · simp [zeroAt_shape, Formula.binders]; omega

theorem frame_replace (b x y a z : Nat) (ha : a < b) :
    replace a z (outputFrame b x y) = outputFrame b (rename a z x) (rename a z y) := by
  have hf : ∀ i < 64, rename a z (b+i) = b+i := by
    intro i hi
    simp [rename, show b+i ≠ a by omega]
  have hzx : replace a z (zeroAt b x) = zeroAt b (rename a z x) := by
    rw [← map_eq_replace a z _ (by simp [zeroAt_shape, Formula.binders]; omega)]
    exact zeroAt_shift (rename a z) b b x hf
  have hzy : replace a z (zeroAt b y) = zeroAt b (rename a z y) := by
    rw [← map_eq_replace a z _ (by simp [zeroAt_shape, Formula.binders]; omega)]
    exact zeroAt_shift (rename a z) b b y hf
  have he : replace a z (equivAt b x y) = equivAt b (rename a z x) (rename a z y) := by
    rw [← map_eq_replace a z _ (by intro h; have := equivAt_private b x y a h; omega)]
    exact equivAt_shift (rename a z) b b x y hf
  simp only [outputFrame, replace, hzx, hzy, he]

/-- Instantiate both operands with allocator-safe names, including aliases. -/
def output_high (b x y : Nat) (hb : 40 ≤ b) (hx : x < b) (hy : y < b)
    (hspace : max x y + 2 < b) : KDerivation (outputFrame b x y).encode := by
  let q := max x y + 2
  have hq : q < b := hspace
  have h0 := replace_derivation 0 q (outputFrame b 0 1)
    (frame_not_binder b 0 1 0 (by omega)) (frame_not_binder b 0 1 q hq) (canonical_high b hb)
  have hs0 : replace 0 q (outputFrame b 0 1) = outputFrame b q 1 := by
    simpa [rename] using frame_replace b 0 1 0 q (by omega)
  rw [hs0] at h0
  have h1 := replace_derivation 1 y (outputFrame b q 1)
    (frame_not_binder b q 1 1 (by omega)) (frame_not_binder b q 1 y hy) h0
  have hs1 : replace 1 y (outputFrame b q 1) = outputFrame b q y := by
    have hq1 : q ≠ 1 := by dsimp [q]; omega
    simpa [rename, hq1] using frame_replace b q 1 1 y (by omega)
  rw [hs1] at h1
  have h2 := replace_derivation q x (outputFrame b q y)
    (frame_not_binder b q y q hq) (frame_not_binder b q y x hx) h1
  have hs2 : replace q x (outputFrame b q y) = outputFrame b x y := by
    have hyq : y ≠ q := by dsimp [q]; omega
    simpa [rename, hyq] using frame_replace b q y q x hq
  simpa only [hs2] using h2

/-- Rebase the fixed-label output theorem to arbitrary allocated names.
The two operand labels may coincide. -/
def zero_output (b x y : Nat) (hx : x < b+2) (hy : y < b+2) :
    KDerivation (imp (zeroAt b x).encode
      (imp (equivAt b x y).encode (zeroAt b y).encode)) := by
  let d := max b (max x y) + 100
  have hdx : x < d := by dsimp [d]; omega
  have hdy : y < d := by dsimp [d]; omega
  have hspace : max x y + 2 < d := by dsimp [d]; omega
  have hz0 := zeroAt_base_forward b d x (by omega) (by omega)
  have hz1 := zeroAt_base_forward d b y (by omega) (by omega)
  have he := (equivAt_base_alpha b d x y hx hy (by omega) (by omega)).forward
  have hi := output_high d x y (by dsimp [d]; omega) hdx hdy hspace
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let A := (zeroAt b x).encode
  let E := (equivAt b x y).encode
  let Γ := [E,A]
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have ha := Context.mp hA (.closed hz0)
  have heq := Context.mp hE (.closed he)
  have hzd : Context Γ (zeroAt d y).encode := .mp heq (.mp ha (.closed hi))
  exact .mp hzd (.closed hz1)

/-- The zero term graph is preserved when its output is quotient-equivalent
to another candidate. Names may alias, with both below the private block. -/
def zero_graph_output {α : Type} (v : α → Nat) (b q r : Nat) (hq : q < b) (hr : r < b) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (.func .zero Fin.elim0) q b).encode
        (imp (equivAt b q r).encode
          (termGraph v (.func .zero Fin.elim0) r b).encode))) := by
  have ho := zero_output b q r (by omega) (by omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt b r).encode
  let T := (termGraph v (.func .zero Fin.elim0) q b).encode
  let E := (equivAt b q r).encode
  let Γ := [E,T,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hz : Context Γ (zeroAt b q).encode := Context.conjunctionRight ht
  have hz' : Context Γ (zeroAt b r).encode := .mp he (.mp hz (.closed ho))
  exact Context.conjunctionIntro hd hz'

theorem zero_graph_output_certificate {α : Type} (v : α → Nat) (b q r : Nat) (hq : q < b) (hr : r < b) :
    theoremCode (certificate (zero_graph_output v b q r hq hr)) =
      imp (domainAt b r).encode
        (imp (termGraph v (.func .zero Fin.elim0) q b).encode
          (imp (equivAt b q r).encode
            (termGraph v (.func .zero Fin.elim0) r b).encode)) := certificate_correct _

end PASoundness.PAtoCompactZeroGraphOutputTransport

#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.canonical_high
#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.frame_not_binder
#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.frame_replace
#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.output_high
#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.zero_output
#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.zero_graph_output
#print axioms PASoundness.PAtoCompactZeroGraphOutputTransport.zero_graph_output_certificate
