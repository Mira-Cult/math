import Sude.CentralWindow

/-! Depth and size control for balanced finite-group splitting. This does not
construct the stage-preserving assignments or select physical slots. -/
namespace Sude

/-- The size of the largest possible descendant after `k` balanced splits,
where a group of size `q` splits into `q/2` and `q-q/2`. -/
def prefixBalancedMax : ℕ → ℕ → ℕ
  | q, 0 => q
  | q, k + 1 => prefixBalancedMax (q - q / 2) k

/-- Both children of a nonsingleton group are nonempty, their sizes add to the
parent, and neither exceeds the upper child. -/
theorem prefix_balanced_split_sizes (q : ℕ) (hq : 2 ≤ q) :
    0 < q / 2 ∧ 0 < q - q / 2 ∧
    q / 2 + (q - q / 2) = q ∧ q / 2 ≤ q - q / 2 := by
  omega

/-- When `q` fits in `2^(k+1)`, both children fit in `2^k`. -/
theorem prefix_balanced_split_pow_bound (q k : ℕ) (hq : q ≤ 2 ^ (k + 1)) :
    q / 2 ≤ 2 ^ k ∧ q - q / 2 ≤ 2 ^ k := by
  rw [pow_succ] at hq
  omega

/-- Increasing the initial size cannot decrease the upper bound on a
balanced descendant. -/
theorem prefix_balanced_max_mono (k : ℕ) {a b : ℕ} (hab : a ≤ b) :
    prefixBalancedMax a k ≤ prefixBalancedMax b k := by
  induction k generalizing a b with
  | zero => simpa [prefixBalancedMax] using hab
  | succ k ih =>
    have hchild : a - a / 2 ≤ b - b / 2 := by omega
    simpa [prefixBalancedMax] using ih hchild

/-- Any chain of child sizes bounded by the upper balanced half is bounded
by `prefixBalancedMax`, even when a branch terminates as an empty group. -/
theorem prefix_balanced_path_bound (q : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, q (i + 1) ≤ q i - q i / 2) :
    q k ≤ prefixBalancedMax (q 0) k := by
  induction k generalizing q with
  | zero => simp [prefixBalancedMax]
  | succ k ih =>
    have hstep' : ∀ i < k, (fun j => q (j + 1)) (i + 1) ≤
        (fun j => q (j + 1)) i - (fun j => q (j + 1)) i / 2 := by
      intro i hi
      have h := hstep (i + 1) (by omega)
      simpa [Nat.add_assoc] using h
    have hp := ih (fun j => q (j + 1)) hstep'
    have hf : q 1 ≤ q 0 - q 0 / 2 := by simpa using hstep 0 (by omega)
    have hm := prefix_balanced_max_mono k hf
    simpa [prefixBalancedMax, Nat.add_comm] using hp.trans hm

/-- After `k` balanced levels, any group of initial size at most `2^k` has
largest descendant size at most one. This includes the empty group. -/
theorem prefix_balanced_max_le_one (k q : ℕ) (hq : q ≤ 2 ^ k) :
    prefixBalancedMax q k ≤ 1 := by
  induction k generalizing q with
  | zero => simpa [prefixBalancedMax] using hq
  | succ k ih =>
    have hchild := (prefix_balanced_split_pow_bound q k hq).2
    simpa [prefixBalancedMax] using ih (q - q / 2) hchild


/-- A chain of balanced descendants has size at most one after any `k`
levels satisfying the power-of-two capacity bound. -/
theorem prefix_balanced_path_terminal (q : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, q (i + 1) ≤ q i - q i / 2)
    (hq : q 0 ≤ 2 ^ k) : q k ≤ 1 := by
  exact (prefix_balanced_path_bound q k hstep).trans (prefix_balanced_max_le_one k (q 0) hq)

/-- The integer ceiling logarithm gives a sufficient depth, including
`Q = 0` and `Q = 1`. -/
theorem prefix_balanced_path_terminal_clog (q : ℕ → ℕ) (Q : ℕ)
    (hstart : q 0 ≤ Q)
    (hstep : ∀ i < Nat.clog 2 Q, q (i + 1) ≤ q i - q i / 2) :
    q (Nat.clog 2 Q) ≤ 1 := by
  apply prefix_balanced_path_terminal q (Nat.clog 2 Q) hstep
  exact hstart.trans (Nat.le_pow_clog (by norm_num) Q)

end Sude
