import Sude.FWFreshReferenceT75Routing
import Sude.PackedPrimeDiagonalRepair

/-! Conditional same-reference T75 routing followed by physical prime-diagonal
repair. The final rectangle trades preserve routed line sums; the earlier
active-image guarantee is retained only for the intermediate routed square. -/
namespace Sude
noncomputable section

/-- Route the exact selected T75 vector, then conditionally repair both
physical diagonals using one of those same primes. The bounds for the
controller-selected centered reference are deliberately not assumed before it
is chosen; they appear as the premise of the returned continuation. -/
theorem fw_t75_fresh_routing_with_diagonal_repair {α β : Type*} [DecidableEq β]
    {L n N : ℕ} (hnodd : Odd n) (p : Fin 3 → Equiv.Perm (Fin n))
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
        Set.range (entry b) = pool n ∧ Function.Injective (entry b))
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (diagGap : Fin L → ℕ) (labels : Finset (Fin L))
    (Rm Ra : ℕ) (keep : Finset (Cell n))
    (hmainGrid : CompleteEvenGrid (labels.filter fun i => choice i = true) diagGap Rm)
    (hantiGrid : CompleteEvenGrid (labels.filter fun i => choice i = false) diagGap Ra)
    (hgaps : ∀ i ∈ labels,
      entry source (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry source (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + diagGap i ∧
      entry source (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry source (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + diagGap i)
    (hkeep : ∀ c ∈ keep, ∀ i ∈ labels,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i))
    (hrectsub : packedLabelSupport hs choice labels ⊆ reserved)
    (hrectref : ∀ z ∈ packedLabelSupport hs choice labels, entry b₀ z = entry source z)
    (hmainref : mainSum b₀ = mainSum source) (hantiref : antiSum b₀ = antiSum source)
    (Udiag : ℝ) :
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
          ∃ before : Finset (Fin L), before ⊆ labels ∧
            let reference := packedTradeSequence hs choice source before.toList
            (|(mainSum reference : ℝ) - y| ≤ Udiag →
             |(antiSum reference : ℝ) - y| ≤ Udiag →
             Udiag + D ≤ (evenGridCenter Rm : ℝ) →
             Udiag + D ≤ (evenGridCenter Ra : ℝ) →
             ∃ (q : ℕ) (result : Cell n ≃ Fin (n*n)),
               Nat.Prime q ∧ (∃ i, q = f i) ∧
               (∀ r, rowSum result r = rowSum b r) ∧
               (∀ c, columnSum result c = columnSum b c) ∧
               mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
               Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
               (∀ c ∈ keep, entry result c = entry b c)) := by
  obtain ⟨values, chosen, hsub, hchoice, hlen', f, hf, hsum, hprops,
    b, hr, hc, hmain, hanti, hfixed, hpool, hinj, hout, himage, _⟩ :=
    fw_t75_fresh_active_reference_routing hnodd p source b₀ reserved active
      xs freeLo freeHi S low gap h y U D hD hbracket hclass hfreePrime
      hcontrolledPrime hwindow hgrid hcong htotal hmargin hlen habove hN hrow hcol
      hbudget hexp hflows
  have hagree : ∀ z ∈ packedLabelSupport hs choice labels, entry b z = entry source z := by
    intro z hz
    exact (hfixed z (hrectsub hz)).trans (hrectref z hz)
  obtain ⟨before, hbefore, hrepair⟩ := packed_prime_diagonal_repair
    hs hL hnodd choice diagGap labels Rm Ra source b keep hmainGrid hantiGrid hgaps hkeep
    hagree (hmain.trans hmainref) (hanti.trans hantiref)
    (fun r => (hr r).2) (fun c => (hc c).2) f y Udiag D hprops
  exact ⟨values, chosen, hsub, hchoice, hlen', f, hf, hsum, hprops,
    b, hr, hc, hmain, hanti, hfixed, hpool, hinj, hout, himage, before, hbefore, hrepair⟩

end
end Sude
