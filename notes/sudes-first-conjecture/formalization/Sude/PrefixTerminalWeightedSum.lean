import Sude.PrefixFiberKeyEquivalence

/-! Terminal weighted sum transport for a key-preserving assignment.
Existence of a singleton-leaf recursion and error bounds are separate. -/
namespace Sude
noncomputable section

/-- When each assigned label has its terminal key's conditional mean, the
line-weighted actual assignment sum equals the terminal conditional-mean
sum over the original slot set. One assignment works for every line. -/
theorem prefix_terminal_weighted_sum {S T G L : Type*} [DecidableEq S] [DecidableEq T]
    (slots : Finset S) (labels : Finset T) (slotKey : S → G)
    (w : L → S → ℝ) (value : T → ℝ) (mean : G → ℝ)
    (e : {s // s ∈ slots} ≃ {t // t ∈ labels})
    (hmean : ∀ s, value (e s).val = mean (slotKey s.val)) (l : L) :
    (∑ s : {s // s ∈ slots}, w l s.val * value (e s).val) =
      ∑ s ∈ slots, w l s * mean (slotKey s) := by
  classical
  calc
    _ = ∑ s : {s // s ∈ slots}, w l s.val * mean (slotKey s.val) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hmean s]
    _ = _ := by
      simpa using Finset.sum_attach slots (fun s => w l s * mean (slotKey s))

end
end Sude
