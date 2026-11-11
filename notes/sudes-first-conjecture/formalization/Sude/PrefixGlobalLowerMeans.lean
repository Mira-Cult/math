import Sude.PrefixLocalBalancedMeanSplit
import Sude.PrefixLowerChoices

/-! Synchronized lower-label selection and child means at one DP3 depth.
Slot selection and recursive assignment remain separate. -/
namespace Sude
noncomputable section

/-- Labels in a current value group. -/
def prefixValueFiber {V G : Type*} [DecidableEq G]
    (values : Finset V) (key : V → G) (g : G) : Finset V :=
  values.filter (fun v => key v = g)

/-- The lower labels of a current value group. -/
def prefixLowerFiber {V G : Type*} [DecidableEq V] [DecidableEq G]
    (values lower : Finset V) (key : V → G) (g : G) : Finset V :=
  (prefixValueFiber values key g).filter (fun v => v ∈ lower)

/-- The totalized arithmetic mean of a labelled fiber. -/
def prefixFiberMean {V : Type*} (fiber : Finset V) (x : V → ℝ) : ℝ :=
  (∑ v ∈ fiber, x v) / fiber.card

/-- All value groups may be split simultaneously into sorted lower halves,
with child means and a single width bound. Empty and singleton groups use
harmless dummy child means; nonempty children have their actual means. -/
theorem prefix_global_lower_means {V G : Type*} [DecidableEq V] [DecidableEq G]
    (values : Finset V) (key : V → G) (x : V → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hwidth : ∀ g, ∀ a ∈ prefixValueFiber values key g,
      ∀ b ∈ prefixValueFiber values key g, x b - x a ≤ C) :
    ∃ (lower : Finset V) (low high : G → ℝ), lower ⊆ values ∧
      (∀ g, (prefixLowerFiber values lower key g).card =
        (prefixValueFiber values key g).card / 2) ∧
      (∀ g, (prefixLowerFiber values lower key g).Nonempty →
        low g = prefixFiberMean (prefixLowerFiber values lower key g) x) ∧
      (∀ g, (prefixValueFiber values key g \ prefixLowerFiber values lower key g).Nonempty →
        high g = prefixFiberMean (prefixValueFiber values key g \ prefixLowerFiber values lower key g) x) ∧
      (∀ g, 0 ≤ high g - low g ∧ high g - low g ≤ C) ∧
      (∀ g, prefixFiberMean (prefixValueFiber values key g) x =
        (((prefixValueFiber values key g).card / 2 : ℕ) : ℝ) /
            (prefixValueFiber values key g).card * low g +
          (1 - (((prefixValueFiber values key g).card / 2 : ℕ) : ℝ) /
            (prefixValueFiber values key g).card) * high g) := by
  classical
  obtain ⟨lower, hsub, hcard, horder⟩ := prefix_global_sorted_lower_choices values key x
  have hlocal : ∀ g, ∃ low high : ℝ,
      ((prefixLowerFiber values lower key g).Nonempty →
        low = prefixFiberMean (prefixLowerFiber values lower key g) x) ∧
      ((prefixValueFiber values key g \ prefixLowerFiber values lower key g).Nonempty →
        high = prefixFiberMean (prefixValueFiber values key g \ prefixLowerFiber values lower key g) x) ∧
      0 ≤ high - low ∧ high - low ≤ C ∧
      prefixFiberMean (prefixValueFiber values key g) x =
        (((prefixValueFiber values key g).card / 2 : ℕ) : ℝ) /
            (prefixValueFiber values key g).card * low +
          (1 - (((prefixValueFiber values key g).card / 2 : ℕ) : ℝ) /
            (prefixValueFiber values key g).card) * high := by
    intro g
    let A := prefixValueFiber values key g
    let T := prefixLowerFiber values lower key g
    have hTA : T ⊆ A := Finset.filter_subset _ _
    have htc : T.card = A.card / 2 := hcard g
    have hcomp : A \ T = A \ lower := by
      ext v
      simp only [T, prefixLowerFiber, Finset.mem_sdiff, Finset.mem_filter]
      tauto
    have hord : ∀ a ∈ T, ∀ b ∈ A \ T, x a ≤ x b := by
      intro a ha b hb
      apply horder g a ha b
      rwa [hcomp] at hb
    have hw : ∀ a ∈ A, ∀ b ∈ A, x b - x a ≤ C := hwidth g
    simpa [A, T, prefixFiberMean] using
      prefix_local_balanced_mean_split A T x C hC hTA htc hord hw
  choose low high hlow hhigh hgap0 hgap1 hmean using hlocal
  refine ⟨lower, low, high, hsub, hcard, hlow, hhigh, ?_, hmean⟩
  exact fun g => ⟨hgap0 g, hgap1 g⟩

end
end Sude
