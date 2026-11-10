import PASoundness.PAtoCompactOrderIsoZero
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactTemplateBlockShift
import PASoundness.PAtoCompactTermGraphBinderRange

/-! Finite K proof data toward unary graph functionality. -/
namespace PASoundness.PAtoCompactUnaryGraphFunctional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrderIsoZero
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactEquivNoShadow PASoundness.PAtoCompactEquivStepsSyntax
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactEquivMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def rawSteps (b : Nat) : List (Nat × Nat) := offsets.map (fun k => (k, b+2+k))

theorem raw_template_names : equivTemplate.names = {0,1,2,3,4,5,6,19,20,21,22} := by decide
theorem raw_template_free : equivTemplate.free = {0,1} := by decide

theorem raw_initial_safe (b : Nat) (hb : 40 ≤ b) :
    InitialSafe (rawSteps b) equivTemplate := by
  refine ⟨?_, ?_, template_allNoShadow⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hk' : k ∈ ({2,3,4,5,6,19,20,21,22} : Finset Nat) := by simpa [offsets] using hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [raw_template_free, raw_template_names]
    all_goals omega
  · simp [rawSteps, offsets, List.nodup_cons]

theorem raw_step_hit (b k : Nat) (hb : 40 ≤ b) (hk : k ∈ offsets) :
    applySteps (rawSteps b) k = b+2+k := by
  apply applySteps_hit
  · exact List.mem_map.mpr ⟨k, hk, rfl⟩
  · intro z hz
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hz
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only at h1 h2
    omega
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hj' := offsets_lt j hj
    omega

theorem raw_steps_shape (b : Nat) (hb : 40 ≤ b) :
    renameSteps (rawSteps b) equivTemplate = equivAt b 0 1 := by
  rw [renameSteps_eq_map]
  unfold equivAt
  change mapNames (applySteps (rawSteps b)) equivTemplate =
    mapNames (twoMap b 0 1 0 1) equivTemplate
  apply mapNames_congr
  intro k hk
  rw [raw_template_names] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply applySteps_avoid; intro p hp; simp [rawSteps, offsets] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply applySteps_avoid; intro p hp; simp [rawSteps, offsets] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  all_goals simp only [twoMap, Nat.reduceEqDiff, if_false]; exact raw_step_hit b _ hb (by decide)

/-- Alpha-allocate the canonical equivalence proof without changing operands. -/
def canonical_equiv_alpha (b : Nat) (hb : 40 ≤ b) :
    ProofEquiv equivTemplate (equivAt b 0 1) := by
  have hs := initial_safe_steps (rawSteps b) equivTemplate (raw_initial_safe b hb)
  have h := multiAlpha (rawSteps b) equivTemplate hs
  rw [raw_steps_shape b hb] at h
  exact h

/-- Two zero graphs at the canonical operand labels have equivalent outputs.
The allocator is arbitrary above the fixed source labels. -/
def zero_graph_functional_01 {α : Type} (v : α → Nat) (b : Nat) (hb : 40 ≤ b) :
    KDerivation (imp (termGraph v (.func .zero Fin.elim0) 0 b).encode
      (imp (termGraph v (.func .zero Fin.elim0) 1 b).encode (equivAt b 0 1).encode)) := by
  have hz0 := zeroAt_base_forward b 4 0 (by omega) (by omega)
  have hz1 := zeroAt_base_forward b 4 1 (by omega) (by omega)
  have h0 : KDerivation (imp (zeroAt b 0).encode (zeroCode 0 7)) := by
    simpa [zeroAt_shape, Formula.encode, zeroCode, neg, allCode] using hz0
  have h1 : KDerivation (imp (zeroAt b 1).encode (zeroCode 1 7)) := by
    simpa [zeroAt_shape, Formula.encode, zeroCode, neg, allCode] using hz1
  have he : KDerivation (imp equivalentFormula.encode (equivAt b 0 1).encode) := by
    simpa [equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha b hb).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let G0 := (termGraph v (.func .zero Fin.elim0) 0 b).encode
  let G1 := (termGraph v (.func .zero Fin.elim0) 1 b).encode
  let Γ := [G1, G0]
  have hg0 : Context Γ G0 := Context.under (Context.head [] G0) G1
  have hg1 : Context Γ G1 := .head _ _
  have hz0' : Context Γ (zeroAt b 0).encode := Context.conjunctionRight hg0
  have hz1' : Context Γ (zeroAt b 1).encode := Context.conjunctionRight hg1
  have z0 : Context Γ (zeroCode 0 7) := .mp hz0' (.closed h0)
  have z1 : Context Γ (zeroCode 1 7) := .mp hz1' (.closed h1)
  have step : Context Γ (imp (zeroCode 1 7) equivalentFormula.encode) :=
    .mp z0 (.closed two_zeros_equivalent)
  have heq : Context Γ equivalentFormula.encode := .mp z1 step
  exact .mp heq (.closed he)

theorem zero_graph_functional_01_certificate {α : Type} (v : α → Nat) (b : Nat) (hb : 40 ≤ b) :
    theoremCode (certificate (zero_graph_functional_01 v b hb)) =
      imp (termGraph v (.func .zero Fin.elim0) 0 b).encode
        (imp (termGraph v (.func .zero Fin.elim0) 1 b).encode (equivAt b 0 1).encode) :=
  certificate_correct _

def zeroEquivFrame (b x y : Nat) : Formula :=
  .imp (zeroAt b x) (.imp (zeroAt b y) (equivAt b x y))

def zero_equiv_01 (b : Nat) (hb : 40 ≤ b) : KDerivation (zeroEquivFrame b 0 1).encode := by
  have hz0 := zeroAt_base_forward b 4 0 (by omega) (by omega)
  have hz1 := zeroAt_base_forward b 4 1 (by omega) (by omega)
  have h0 : KDerivation (imp (zeroAt b 0).encode (zeroCode 0 7)) := by
    simpa [zeroAt_shape, Formula.encode, zeroCode, neg, allCode] using hz0
  have h1 : KDerivation (imp (zeroAt b 1).encode (zeroCode 1 7)) := by
    simpa [zeroAt_shape, Formula.encode, zeroCode, neg, allCode] using hz1
  have he : KDerivation (imp equivalentFormula.encode (equivAt b 0 1).encode) := by
    simpa [equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha b hb).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let A := (zeroAt b 0).encode
  let B := (zeroAt b 1).encode
  let Γ := [B,A]
  have a : Context Γ A := Context.under (Context.head [] A) B
  have b' : Context Γ B := Context.head _ _
  have z0 : Context Γ (zeroCode 0 7) := .mp a (.closed h0)
  have z1 : Context Γ (zeroCode 1 7) := .mp b' (.closed h1)
  have step : Context Γ (imp (zeroCode 1 7) equivalentFormula.encode) :=
    .mp z0 (.closed two_zeros_equivalent)
  have heq : Context Γ equivalentFormula.encode := .mp z1 step
  exact .mp heq (.closed he)

theorem frame_not_binder (b x y a : Nat) (ha : a < b) :
    a ∉ (zeroEquivFrame b x y).binders := by
  simp only [zeroEquivFrame, Formula.binders, Finset.mem_union, not_or]
  constructor
  · simp [zeroAt_shape, Formula.binders]; omega
  constructor
  · simp [zeroAt_shape, Formula.binders]; omega
  · intro h
    have ht := equivAt_private b x y a h
    omega

theorem frame_replace (b x y a z : Nat) (ha : a < b) :
    replace a z (zeroEquivFrame b x y) = zeroEquivFrame b (rename a z x) (rename a z y) := by
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
  simp only [zeroEquivFrame, replace, hzx, hzy, he]

/-- Allocator-safe simultaneous instantiation permits coinciding operands. -/
def zero_equiv_high (b x y : Nat) (hb : 40 ≤ b) (hx : x < b) (hy : y < b)
    (hspace : max x y + 2 < b) :
    KDerivation (zeroEquivFrame b x y).encode := by
  let q := max x y + 2
  by_cases hq : q < b
  · have h0 := replace_derivation 0 q (zeroEquivFrame b 0 1)
      (frame_not_binder b 0 1 0 (by omega)) (frame_not_binder b 0 1 q hq) (zero_equiv_01 b hb)
    have hs0 : replace 0 q (zeroEquivFrame b 0 1) = zeroEquivFrame b q 1 := by
      simpa [rename] using frame_replace b 0 1 0 q (by omega)
    rw [hs0] at h0
    have h1 := replace_derivation 1 y (zeroEquivFrame b q 1)
      (frame_not_binder b q 1 1 (by omega)) (frame_not_binder b q 1 y hy) h0
    have hs1 : replace 1 y (zeroEquivFrame b q 1) = zeroEquivFrame b q y := by
      have hq1 : q ≠ 1 := by dsimp [q]; omega
      simpa [rename, hq1] using frame_replace b q 1 1 y (by omega)
    rw [hs1] at h1
    have h2 := replace_derivation q x (zeroEquivFrame b q y)
      (frame_not_binder b q y q hq) (frame_not_binder b q y x hx) h1
    have hs2 : replace q x (zeroEquivFrame b q y) = zeroEquivFrame b x y := by
      have hyq : y ≠ q := by dsimp [q]; omega
      simpa [rename, hyq] using frame_replace b q y q x hq
    simpa only [hs2] using h2
  · exact False.elim (hq hspace)

/-- Arbitrary allocator and output labels, including aliased outputs. -/
def zero_graph_functional {α : Type} (v : α → Nat) (b x y : Nat)
    (hx : x < b+2) (hy : y < b+2) :
    KDerivation (imp (termGraph v (.func .zero Fin.elim0) x b).encode
      (imp (termGraph v (.func .zero Fin.elim0) y b).encode (equivAt b x y).encode)) := by
  let d := max b (max x y) + 100
  have hdx : x < d := by dsimp [d]; omega
  have hdy : y < d := by dsimp [d]; omega
  have hspace : max x y + 2 < d := by dsimp [d]; omega
  have hz0 := zeroAt_base_forward b d x (by omega) (by omega)
  have hz1 := zeroAt_base_forward b d y (by omega) (by omega)
  have he := (equivAt_base_alpha d b x y (by omega) (by omega) hx hy).forward
  have hz := zero_equiv_high d x y (by dsimp [d]; omega) hdx hdy hspace
  change KDerivation (imp (termGraph v (.func .zero Fin.elim0) x b).encode
    (imp (termGraph v (.func .zero Fin.elim0) y b).encode (equivAt b x y).encode))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Gx := (termGraph v (.func .zero Fin.elim0) x b).encode
  let Gy := (termGraph v (.func .zero Fin.elim0) y b).encode
  let Γ := [Gy,Gx]
  have hgx : Context Γ Gx := Context.under (Context.head [] Gx) Gy
  have hgy : Context Γ Gy := .head _ _
  have hx0 : Context Γ (zeroAt b x).encode := Context.conjunctionRight hgx
  have hy0 : Context Γ (zeroAt b y).encode := Context.conjunctionRight hgy
  have hxd : Context Γ (zeroAt d x).encode := .mp hx0 (.closed hz0)
  have hyd : Context Γ (zeroAt d y).encode := .mp hy0 (.closed hz1)
  have step : Context Γ (imp (zeroAt d y).encode (equivAt d x y).encode) :=
    .mp hxd (.closed hz)
  have hd : Context Γ (equivAt d x y).encode := .mp hyd step
  exact .mp hd (.closed he)

theorem zero_graph_functional_certificate {α : Type} (v : α → Nat) (b x y : Nat)
    (hx : x < b+2) (hy : y < b+2) :
    theoremCode (certificate (zero_graph_functional v b x y hx hy)) =
      imp (termGraph v (.func .zero Fin.elim0) x b).encode
        (imp (termGraph v (.func .zero Fin.elim0) y b).encode (equivAt b x y).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactUnaryGraphFunctional

#print axioms PASoundness.PAtoCompactUnaryGraphFunctional.zero_graph_functional_01
#print axioms PASoundness.PAtoCompactUnaryGraphFunctional.zero_graph_functional_01_certificate
#print axioms PASoundness.PAtoCompactUnaryGraphFunctional.zero_graph_functional
#print axioms PASoundness.PAtoCompactUnaryGraphFunctional.zero_graph_functional_certificate
