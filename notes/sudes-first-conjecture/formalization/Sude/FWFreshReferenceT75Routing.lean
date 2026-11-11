import Sude.FWT75CenteredPrimeTargetRouting

/-! Conditional T75 routing from the active-preserving fresh-reference
continuation. The supplied target and reference hypotheses remain unchanged. -/
namespace Sude
noncomputable section

/-- Reorder the fresh-network continuation while retaining both its
outside-active and active-value-image invariants on the same supplied source. -/
theorem fw_fresh_active_flow_interface {n N : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (source b₀ : Cell n ≃ Fin (n*n)) (reserved active : Finset (Cell n))
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        (∀ c ∉ active, entry b c = entry source c) ∧
        active.image (entry b) = active.image (entry source) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b)) :
    ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
        ((∀ c ∉ active, entry b c = entry source c) ∧
          active.image (entry b) = active.image (entry source)) := by
  intro fr hfr fc hfc
  obtain ⟨b, hr, hc, hm, ha, hreserved, houtside, himage, hpool, hinj⟩ := hflows fr hfr fc hfc
  exact ⟨b, hr, hc, hm, ha, hreserved, hpool, hinj, houtside, himage⟩

/-- Route the exact T75-selected vector on both axes of the supplied fresh
reference, retaining active-image and outside-active invariants. Prime diagonals
and all analytic, window, expansion and physical-flow inputs remain explicit. -/
theorem fw_t75_fresh_active_reference_routing {α β : Type*} [DecidableEq β]
    {n N : ℕ} (hnodd : Odd n) (p : Fin 3 → Equiv.Perm (Fin n))
    (source b₀ : Cell n ≃ Fin (n*n)) (reserved active : Finset (Cell n))
    (xs : List α) (freeLo freeHi : α → ℕ) (S : Finset β) (low gap : β → ℕ)
    (h : ℕ) (y U D : ℝ) (hD : 0 ≤ D)
    (hbracket : ∀ x ∈ xs, y - D ≤ (freeLo x : ℝ) ∧ (freeLo x : ℝ) ≤ y ∧
      y ≤ (freeHi x : ℝ) ∧ (freeHi x : ℝ) ≤ y + D)
    (hclass : ∀ x ∈ xs, freeLo x % h = freeHi x % h)
    (hfreePrime : ∀ x ∈ xs, Nat.Prime (freeLo x) ∧ Nat.Prime (freeHi x))
    (hcontrolledPrime : ∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hwindow : ∀ i ∈ S, y - D ≤ (low i : ℝ) ∧ ((low i + gap i : ℕ) : ℝ) ≤ y + D)
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hcong : ((∑ i ∈ S, low i) + (xs.map freeLo).sum) % h = Lucas.poolTotal n % h)
    (htotal : (Lucas.poolTotal n : ℝ) = ((xs.length : ℝ) + (S.card : ℝ)) * y)
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) +
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - (S.card : ℝ) * y| + D ≤
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2)
    (hlen : xs.length + S.card = n) (habove : (2 : ℝ) < y - D)
    (hN : 3000 ≤ N)
    (hrow : ∀ i, |(rowSum b₀ i : ℝ) - y| ≤ U)
    (hcol : ∀ i, |(columnSum b₀ i : ℝ) - y| ≤ U)
    (hbudget : U + D ≤ (518481 / 500000 : ℝ) * N)
    (hexp : ∀ A : Finset (Fin n),
      519 * min A.card (n - A.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) A).card)
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n,
            edgeTransfer (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n,
            edgeTransfer (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        (∀ c ∉ active, entry b c = entry source c) ∧
        active.image (entry b) = active.image (entry source) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b)) :
    ∃ values : List ℕ, ∃ chosen : Finset β,
      chosen ⊆ S ∧ List.Forall₂ (fun x v => v = freeLo x ∨ v = freeHi x) xs values ∧
      let targets := values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
      ∃ hlen' : targets.length = n, ∃ f : Fin n → ℕ,
        (∀ i, f i = targets.get ((finCongr hlen'.symm) i)) ∧
        (∑ i, f i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) ∧
        ∃ b : Cell n ≃ Fin (n*n),
          (∀ i, rowSum b i = f i ∧ Nat.Prime (rowSum b i)) ∧
          (∀ i, columnSum b i = f i ∧ Nat.Prime (columnSum b i)) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
          (∀ c ∉ active, entry b c = entry source c) ∧
          active.image (entry b) = active.image (entry source) ∧
          ((Nat.Prime (mainSum b₀) ∧ Nat.Prime (antiSum b₀)) → Valid b) := by
  simpa only [and_assoc] using fw_t75_centered_prime_target_of_supplied_flows hnodd p b₀ reserved
    (fun b => (∀ c ∉ active, entry b c = entry source c) ∧
      active.image (entry b) = active.image (entry source))
    xs freeLo freeHi S low gap h y U D hD hbracket hclass hfreePrime
    hcontrolledPrime hwindow hgrid hcong htotal hmargin hlen habove hN hrow hcol
    hbudget hexp (fw_fresh_active_flow_interface p source b₀ reserved active hflows)

end
end Sude
