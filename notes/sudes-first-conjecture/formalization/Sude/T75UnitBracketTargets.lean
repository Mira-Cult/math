import Sude.T75FreeUnitResidues
import Sude.T75PoolParity
import Sude.T75TargetRadius

namespace Sude
noncomputable section
set_option maxHeartbeats 1000000

/-- Choose free residues and actual supplied prime brackets with exact T75
    congruence. The reduced-class prime supply is an explicit hypothesis. -/
theorem t75_free_prime_brackets_from_unit_supply {β : Type*} [DecidableEq β]
    {n m h : ℕ} (hn : Odd n) (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (S : Finset β) (low : β → ℕ) (hlen : m + S.card = n)
    (hodd : ∀ i ∈ S, Odd (low i)) (y D : ℝ)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ),
      xs.length = m ∧
      (∀ x ∈ xs, Nat.Prime (lo x) ∧ Nat.Prime (hi x)) ∧
      (∀ x ∈ xs, y-D ≤ (lo x : ℝ) ∧ (lo x : ℝ) ≤ y ∧
        y ≤ (hi x : ℝ) ∧ (hi x : ℝ) ≤ y+D) ∧
      (∀ x ∈ xs, lo x % h = hi x % h) ∧
      ((∑ i ∈ S, low i) + (xs.map lo).sum) % h = Lucas.poolTotal n % h := by
  classical
  have hcases : h = 2 ∨ h = 4 ∨ h = 6 ∨ h = 8 ∨ h = 10 ∨ h = 12 ∨
      h = 14 ∨ h = 16 ∨ h = 18 ∨ h = 20 ∨ h = 22 ∨ h = 24 ∨ h = 26 ∨
      h = 28 ∨ h = 30 ∨ h = 36 ∨ h = 42 := by simpa [t75FavorableGaps] using hh
  have hp : 0 < h := by
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  let L := ∑ i ∈ S, low i
  have hLmod : L % 2 = S.card % 2 := by
    dsimp [L]
    rw [Finset.sum_nat_mod]
    have heq : (∑ i ∈ S, low i % 2) = S.card := by
      calc
        _ = ∑ _i ∈ S, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Nat.odd_iff.mp (hodd i hi)
        _ = _ := by simp
    rw [heq]
  have htmod : Lucas.poolTotal n % 2 = n % 2 := t75_pool_total_mod_two hn
  let c := ((Lucas.poolTotal n % h) + h - (L % h)) % h
  have hclt : c < h := Nat.mod_lt _ hp
  have hcpar : c % 2 = m % 2 := by
    dsimp [c]
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  obtain ⟨rs, hrslen, hrsunit, hrssum⟩ := t75_free_unit_residues hh hm hclt hcpar
  have hsupply' : ∀ r : {r : ℕ // r < h ∧ Nat.Coprime r h},
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r.val ∧ q % h = r.val ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D := by
    intro r
    exact hsupply r.val r.property.1 r.property.2
  choose lo hi hspec using hsupply'
  let xs : List {r : ℕ // r < h ∧ Nat.Coprime r h} :=
    rs.attach.map (fun x => ⟨x.val, hrsunit x.val x.property⟩)
  have hxslen : xs.length = m := by simpa [xs] using hrslen
  have hvals : (xs.map (fun x => x.val)) = rs := by simp [xs, List.map_map]
  have hmap : ((xs.map lo).map (fun x => x % h)) = xs.map (fun x => x.val) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact (hspec x).2.2.1
  have hlomod : (xs.map lo).sum % h = rs.sum % h := by
    calc
      _ = (((xs.map lo).map (fun x => x % h)).sum) % h := List.sum_nat_mod _ _
      _ = _ := by rw [hmap, hvals]
  have hcong : (L + (xs.map lo).sum) % h = Lucas.poolTotal n % h := by
    rw [Nat.add_mod, hlomod, hrssum]
    dsimp [c]
    rcases hcases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  refine ⟨xs, lo, hi, hxslen, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hspec x).1, (hspec x).2.1⟩
  · intro x hx
    exact (hspec x).2.2.2.2
  · intro x hx
    exact (hspec x).2.2.1.trans (hspec x).2.2.2.1.symm
  · exact hcong


/-- Given reduced-class bracket supply and a controlled prime grid, select an
    exact-total vector without separately assuming its free-list congruence. -/
theorem t75_targets_from_unit_bracket_supply {β : Type*} [DecidableEq β]
    {n m h : ℕ} (hn : Odd n) (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (S : Finset β) (low gap : β → ℕ) (hlen : m + S.card = n)
    (y D : ℝ) (hD : 0 ≤ D)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D)
    (hcontrolledPrime : ∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hwindow : ∀ i ∈ S, y-D ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ y+D)
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hcenter : (Lucas.poolTotal n : ℝ) = (n : ℝ)*y)
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ)/2 -
      (S.card : ℝ)*y| + D ≤ ((∑ i ∈ S, gap i : ℕ) : ℝ)/2)
    (habove : (2 : ℝ) < y-D) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ)
      (values : List ℕ) (chosen : Finset β),
      xs.length = m ∧ chosen ⊆ S ∧
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      let targets := values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
      ∃ ht : targets.length = n, ∃ f : Fin n → ℕ,
        (∀ i, f i = targets.get ((finCongr ht.symm) i)) ∧
        (∑ i, f i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ)-y| ≤ D) := by
  have hodd : ∀ i ∈ S, Odd (low i) := by
    intro i hi
    have hp := (hcontrolledPrime i hi).1
    have hl := (hwindow i hi).1
    have hne : low i ≠ 2 := by
      intro heq
      rw [heq] at hl
      norm_num at hl
      linarith
    exact Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hne)
  obtain ⟨xs, lo, hi, hlen', hprime, hbracket, hclass, hcong⟩ :=
    t75_free_prime_brackets_from_unit_supply hn hm hh S low hlen hodd y D hsupply
  have hcount : xs.length + S.card = n := by omega
  have hcountR : (xs.length : ℝ) + (S.card : ℝ) = (n : ℝ) := by exact_mod_cast hcount
  have htotal : (Lucas.poolTotal n : ℝ) = ((xs.length : ℝ) + (S.card : ℝ))*y := by
    rw [hcountR]
    exact hcenter
  obtain ⟨values, chosen, hsub, hchoice, ht, f, hget, hsum, htarget⟩ :=
    t75_conditional_indexed_prime_targets xs lo hi S low gap h (Lucas.poolTotal n) n y D hD
      hbracket hclass hprime hcontrolledPrime hwindow hgrid hcong htotal hmargin hcount habove
  exact ⟨xs, lo, hi, values, chosen, hlen', hsub, hchoice, ht, f, hget, hsum, htarget⟩

end
end Sude
