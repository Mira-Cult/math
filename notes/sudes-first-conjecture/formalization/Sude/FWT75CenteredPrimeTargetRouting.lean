import Sude.T75TargetRadius
import Sude.FWCenteredPrimeTargetRouting

/-! Conditional T75 target selection followed by same-reference flow routing.
The endpoint supplies, line-scale bounds, graph and physical flows are inputs. -/
namespace Sude
noncomputable section

/-- The same T75-selected odd-prime vector can be routed to rows and columns
of one supplied reference square. The selected list and arbitrary physical-flow
predicate `P` are retained. No target supply, baseline estimate, flow
interface or diagonal primality is established by this composition. -/
theorem fw_t75_centered_prime_target_of_supplied_flows {α β : Type*} [DecidableEq β]
    {n N : ℕ} (hnodd : Odd n) (p : Fin 3 → Equiv.Perm (Fin n))
    (b₀ : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (P : (Cell n ≃ Fin (n*n)) → Prop)
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
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧ P b) :
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
          Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧ P b ∧
          ((Nat.Prime (mainSum b₀) ∧ Nat.Prime (antiSum b₀)) → Valid b) := by
  obtain ⟨values, chosen, hsub, hchoice, hlen', f, hf, hsum, hprops⟩ :=
    t75_conditional_indexed_prime_targets xs freeLo freeHi S low gap h
      (Lucas.poolTotal n) n y D hD hbracket hclass hfreePrime hcontrolledPrime
      hwindow hgrid hcong htotal hmargin hlen habove
  obtain ⟨b, hbr, hbc, hm, ha, hfixed, hpool, hinj, hp⟩ :=
    fw_centered_prime_target_of_supplied_flows hnodd p b₀ reserved P f hN
      (fun i => (hprops i).1) (fun i => (hprops i).2.1) hsum
      (fun i => (hprops i).2.2) hrow hcol hbudget hexp hflows
  refine ⟨values, chosen, hsub, hchoice, hlen', f, hf, hsum, hprops,
    b, hbr, hbc, hm, ha, hfixed, hpool, hinj, hp, ?_⟩
  rintro ⟨hmain, hanti⟩
  refine ⟨fun i => (hbr i).2, fun i => (hbc i).2, ?_, ?_⟩
  · simpa only [hm] using hmain
  · simpa only [ha] using hanti

end
end Sude
