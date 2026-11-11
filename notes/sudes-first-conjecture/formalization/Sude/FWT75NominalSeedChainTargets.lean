import Sude.FWT75NominalTwoClassTargets
import Sude.T75UniformSeedGrid
namespace Sude
noncomputable section
set_option maxHeartbeats 2000000

/-- Select nominal targets using a supplied uniform seed and fresh gap chain.
Prime supply, seed/chain existence and controlled endpoint conditions remain inputs. -/
theorem fw_t75_nominal_targets_from_seed_chain {β : Type*} [DecidableEq β]
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n m h : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hn : Odd n)
    (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (narrow wide : Finset β) (low gap : β → ℕ)
    (hdis : Disjoint narrow wide) (hcount : 2*narrow.card+5 ≤ wide.card)
    (hlen : m + (narrow ∪ wide).card = n)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hDnominal : D = y / 1240)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D)
    (hprime : ∀ i ∈ narrow ∪ wide, Nat.Prime (low i) ∧ Nat.Prime (low i+gap i))
    (hwindow : ∀ i ∈ narrow ∪ wide, y-D ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ y+D)
    (seed : Finset β) (labels : List β)
    (hS : seed ∪ labels.toFinset = narrow ∪ wide)
    (hseed : ∀ i ∈ seed, gap i = h)
    (hnodup : labels.Nodup) (hfresh : ∀ i ∈ labels, i ∉ seed)
    (hchain : StepGapChain gap h (∑ i ∈ seed, gap i) labels)
    (hnarrow : ∀ i ∈ narrow, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/2)
    (hwide : ∀ i ∈ wide, |(low i : ℝ) + (gap i : ℝ)/2 - y| ≤ D/4)
    (hgap : ∀ i ∈ wide, D ≤ (gap i : ℝ)) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ)
      (values : List ℕ) (chosen : Finset β),
      xs.length = m ∧ chosen ⊆ narrow ∪ wide ∧
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      let targets := values ++ (narrow ∪ wide).toList.map (fun i => if i ∈ chosen then low i+gap i else low i)
      ∃ ht : targets.length = n, ∃ f : Fin n → ℕ,
        (∀ i, f i = targets.get ((finCongr ht.symm) i)) ∧
        (∑ i, f i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ)-y| ≤ D) := by
  have hpositive : 0 < h := by
    have hh' := hh
    simp only [t75FavorableGaps, Finset.mem_insert, Finset.mem_singleton] at hh'
    omega
  have hgrid := t75_uniform_seed_extend gap h seed labels hpositive hseed hnodup hfresh hchain
  rw [hS] at hgrid
  exact fw_t75_nominal_two_class_targets bmor lower upper hnlo hnhi hn hm hh narrow wide low gap
    hdis hcount hlen y D hy hDnominal hsupply hprime hwindow hgrid hnarrow hwide hgap

end
end Sude
