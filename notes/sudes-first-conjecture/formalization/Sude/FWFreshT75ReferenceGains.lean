import Sude.FWFreshT75PackedPrimeRepair

/-! Companion interfaces preserving the exact gains of the controller-selected
reference. Installed grids, physical gaps and baseline estimates remain explicit. -/
namespace Sude
noncomputable section

/-- Given prime rows and columns on a routed square which still agrees with the
installed rectangle support and diagonal sums, select one already-supplied
prime target for both diagonals. After the controller chooses its common
center, a bound around that exact centered reference and two radius budgets
suffice for a valid square. No prime supply or baseline estimate is asserted. This companion also exposes
the exact center gains of the same reference used in the continuation. -/
theorem packed_prime_diagonal_repair_with_reference_gains {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : Odd n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (active : Finset (Fin L))
    (Rm Ra : ℕ) (a b : Cell n ≃ Fin (n*n)) (keep : Finset (Cell n))
    (hm : CompleteEvenGrid (active.filter fun i => choice i = true) gap Rm)
    (ha : CompleteEvenGrid (active.filter fun i => choice i = false) gap Ra)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i)
    (hprotect : ∀ c ∈ keep, ∀ i ∈ active,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i))
    (hagree : ∀ z ∈ packedLabelSupport hs choice active, entry b z = entry a z)
    (hmain : mainSum b = mainSum a) (hanti : antiSum b = antiSum a)
    (hrows : ∀ r, Nat.Prime (rowSum b r)) (hcols : ∀ c, Nat.Prime (columnSum b c))
    (f : Fin n → ℕ) (y U D : ℝ)
    (hf : ∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) :
    ∃ before : Finset (Fin L), before ⊆ active ∧
      let reference := packedTradeSequence hs choice a before.toList
      (mainSum reference : ℤ) - (mainSum a : ℤ) = evenGridCenter Rm ∧
      (antiSum reference : ℤ) - (antiSum a : ℤ) = evenGridCenter Ra ∧
      (|(mainSum reference : ℝ) - y| ≤ U →
       |(antiSum reference : ℝ) - y| ≤ U →
       U + D ≤ (evenGridCenter Rm : ℝ) →
       U + D ≤ (evenGridCenter Ra : ℝ) →
       ∃ (q : ℕ) (result : Cell n ≃ Fin (n*n)),
         Nat.Prime q ∧ (∃ i, q = f i) ∧
         (∀ r, rowSum result r = rowSum b r) ∧
         (∀ c, columnSum result c = columnSum b c) ∧
         mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
         Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
         (∀ c ∈ keep, entry result c = entry b c)) := by
  classical
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  obtain ⟨before, hbefore, hmgain, hagain, hcontroller⟩ :=
    packed_centered_diagonal_adapter_with_reference_gains hs hL hnpos choice gap active Rm Ra a keep hm ha hgaps hprotect
  refine ⟨before, hbefore, hmgain, hagain, ?_⟩
  intro hmr har hbudgetm hbudgeta
  let reference := packedTradeSequence hs choice a before.toList
  have hi : 0 < n := hnpos
  let i : Fin n := ⟨0, hi⟩
  have hq := hf i
  -- Use one explicit vector entry for both diagonals.
  have hmEven : (2 : ℤ) ∣ ((f i : ℤ) - mainSum reference) := by
    exact ⟨halfLineDemand (f i) (mainSum reference),
      (halfLineDemand_exact _ _ hq.2.1 (mainSum_odd_of_odd_order hn reference)).symm⟩
  have haEven : (2 : ℤ) ∣ ((f i : ℤ) - antiSum reference) := by
    exact ⟨halfLineDemand (f i) (antiSum reference),
      (halfLineDemand_exact _ _ hq.2.1 (antiSum_odd_of_odd_order hn reference)).symm⟩
  have hdistm' : |(f i : ℝ) - (mainSum reference : ℝ)| ≤ U + D := by
    have h := abs_add_le ((f i : ℝ) - y) (y - (mainSum reference : ℝ))
    have hy : |y - (mainSum reference : ℝ)| ≤ U := by simpa only [abs_sub_comm] using hmr
    have heq : (f i : ℝ) - (mainSum reference : ℝ) =
        ((f i : ℝ) - y) + (y - (mainSum reference : ℝ)) := by ring
    rw [heq]; linarith [hq.2.2]
  have hdista' : |(f i : ℝ) - (antiSum reference : ℝ)| ≤ U + D := by
    have h := abs_add_le ((f i : ℝ) - y) (y - (antiSum reference : ℝ))
    have hy : |y - (antiSum reference : ℝ)| ≤ U := by simpa only [abs_sub_comm] using har
    have heq : (f i : ℝ) - (antiSum reference : ℝ) =
        ((f i : ℝ) - y) + (y - (antiSum reference : ℝ)) := by ring
    rw [heq]; linarith [hq.2.2]
  have hmbound : |((f i : ℤ) - mainSum reference)| ≤ (evenGridCenter Rm : ℤ) := by
    exact_mod_cast hdistm'.trans hbudgetm
  have habound : |((f i : ℤ) - antiSum reference)| ≤ (evenGridCenter Ra : ℤ) := by
    exact_mod_cast hdista'.trans hbudgeta
  obtain ⟨hml, hmu⟩ := abs_le.mp hmbound
  obtain ⟨hal, hau⟩ := abs_le.mp habound
  obtain ⟨result, hr, hc, hmd, had, hpool, hinj, hcenter, hfixed⟩ :=
    hcontroller b hagree hmain hanti ((f i : ℤ) - mainSum reference)
      ((f i : ℤ) - antiSum reference) hmEven haEven hml hmu hal hau
  change (mainSum result : ℤ) - (mainSum reference : ℤ) =
    (f i : ℤ) - (mainSum reference : ℤ) at hmd
  change (antiSum result : ℤ) - (antiSum reference : ℤ) =
    (f i : ℤ) - (antiSum reference : ℤ) at had
  have hmainq : mainSum result = f i := by exact_mod_cast (by omega : (mainSum result : ℤ) = f i)
  have hantiq : antiSum result = f i := by exact_mod_cast (by omega : (antiSum result : ℤ) = f i)
  refine ⟨f i, result, hq.1, ⟨i, rfl⟩, hr, hc, hmainq, hantiq, ?_, hpool, hinj, hfixed⟩
  exact ⟨fun r => by rw [hr r]; exact hrows r,
    fun c => by rw [hc c]; exact hcols c,
    by rw [hmainq]; exact hq.1, by rw [hantiq]; exact hq.1⟩


/-- Route the exact selected T75 vector, then conditionally repair both
physical diagonals using one of those same primes. The bounds for the
controller-selected centered reference are deliberately not assumed before it
is chosen; they appear as the premise of the returned continuation. The
same selected reference also carries its exact two center-gain equations. -/
theorem fw_t75_fresh_routing_with_diagonal_repair_and_reference_gains {α β : Type*} [DecidableEq β]
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
            (mainSum reference : ℤ) - (mainSum source : ℤ) = evenGridCenter Rm ∧
            (antiSum reference : ℤ) - (antiSum source : ℤ) = evenGridCenter Ra ∧
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
  obtain ⟨before, hbefore, hmgain, hagain, hrepair⟩ := packed_prime_diagonal_repair_with_reference_gains
    hs hL hnodd choice diagGap labels Rm Ra source b keep hmainGrid hantiGrid hgaps hkeep
    hagree (hmain.trans hmainref) (hanti.trans hantiref)
    (fun r => (hr r).2) (fun c => (hc c).2) f y Udiag D hprops
  exact ⟨values, chosen, hsub, hchoice, hlen', f, hf, hsum, hprops,
    b, hr, hc, hmain, hanti, hfixed, hpool, hinj, hout, himage, before, hbefore, hmgain, hagain, hrepair⟩

end
end Sude
