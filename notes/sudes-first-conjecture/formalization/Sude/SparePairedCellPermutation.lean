import Sude.SpareGreedySignBalance
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Realizing finite balanced pair choices as one permutation. This is an
abstract cell statement; no CY, network, line-sum or prime conclusion is made. -/

namespace Sude
noncomputable section

/-- Flip each Boolean fibre according to an independently supplied choice. -/
def sparePairChoicePerm {ι : Type*} (choose : ι → Bool) : Equiv.Perm (ι × Bool) where
  toFun x := (x.1, if choose x.1 then x.2 else !x.2)
  invFun x := (x.1, if choose x.1 then x.2 else !x.2)
  left_inv := by
    intro ⟨i, b⟩
    cases h : choose i <;> cases b <;> simp [h]
  right_inv := by
    intro ⟨i, b⟩
    cases h : choose i <;> cases b <;> simp [h]

/-- Injectively supplied cell pairs can be swapped by a single permutation,
balancing their selected value difference within `X`. The input explicitly
requires that a line meet the union of pair cells in at most one point; hence
the permutation changes at most one point per supplied line. The finite index
type may be empty. -/
theorem spare_paired_cell_permutation {ι α κ : Type*} [Fintype ι]
    (cells : ι × Bool → α) (hinj : Function.Injective cells)
    (value : α → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (hvalue : ∀ i b, 0 ≤ value (cells (i,b)) ∧ value (cells (i,b)) ≤ X)
    (line : κ → α → Prop)
    (hline : ∀ l x y, line l x → line l y → x ∈ Set.range cells →
      y ∈ Set.range cells → x = y) :
    ∃ σ : Equiv.Perm α,
      (∀ x, x ∉ Set.range cells → σ x = x) ∧
      (∀ i, (σ (cells (i,true)) = cells (i,true) ∧
          σ (cells (i,false)) = cells (i,false)) ∨
        (σ (cells (i,true)) = cells (i,false) ∧
          σ (cells (i,false)) = cells (i,true))) ∧
      |(∑ i, value (σ (cells (i,true)))) -
        (∑ i, value (σ (cells (i,false))))| ≤ X ∧
      (∀ l x y, line l x → line l y → σ x ≠ x → σ y ≠ y → x = y) := by
  classical
  obtain ⟨choose, hbalance⟩ := spare_greedy_pair_balance (Finset.univ : Finset ι)
    (fun i => value (cells (i,true))) (fun i => value (cells (i,false))) X hX
    (fun i _ => hvalue i true) (fun i _ => hvalue i false)
  let emb : ι × Bool ↪ α := ⟨cells, hinj⟩
  let σ : Equiv.Perm α := (sparePairChoicePerm choose).viaEmbedding emb
  have hσ (i : ι) (b : Bool) : σ (cells (i,b)) =
      cells (i, if choose i then b else !b) := by
    change (sparePairChoicePerm choose).viaEmbedding emb (emb (i,b)) = _
    rw [Equiv.Perm.viaEmbedding_apply]
    rfl
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Equiv.Perm.viaEmbedding_apply_of_notMem _ emb x hx
  · intro i
    by_cases hc : choose i = true
    · left; simpa [hc] using And.intro (hσ i true) (hσ i false)
    · have hc' : choose i = false := Bool.eq_false_iff.mpr hc
      right; simpa [hc'] using And.intro (hσ i true) (hσ i false)
  · have heq : (∑ i, value (σ (cells (i,true)))) -
        (∑ i, value (σ (cells (i,false)))) =
      ∑ i ∈ (Finset.univ : Finset ι),
        ((if choose i then value (cells (i,true)) else value (cells (i,false))) -
          (if choose i then value (cells (i,false)) else value (cells (i,true)))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hσ, hσ]
      cases choose i <;> simp
    rw [heq]
    exact hbalance
  · intro l x y hx hy hxm hym
    apply hline l x y hx hy
    · by_contra hx'
      exact hxm (Equiv.Perm.viaEmbedding_apply_of_notMem _ emb x hx')
    · by_contra hy'
      exact hym (Equiv.Perm.viaEmbedding_apply_of_notMem _ emb y hy')

end
end Sude
