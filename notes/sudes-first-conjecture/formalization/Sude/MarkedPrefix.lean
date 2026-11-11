import Sude.MarkedSieve
import Sude.PrimePrefixSpec

/-! Link the odd-index progression marking sieve to exact pool identities. -/
namespace Sude
noncomputable section

/-- An odd endpoint X corresponds to exactly the candidates 3,5,...,X. -/
theorem markedSieve_prefix (base : Finset ℕ) (bound X : ℕ)
    (hbase : CompletePrimeBase base bound) (hX : 3 ≤ X) (hodd : X % 2 = 1)
    (hbound : X + 2 ≤ (bound + 1) * (bound + 1)) :
    markedSieveValues base 3 ((X - 3) / 2 + 1) = oddPrimePrefix X := by
  have hend : 3 + 2 * ((X - 3) / 2 + 1) = X + 2 := by omega
  rw [markedSieveValues_spec base bound 3 ((X - 3) / 2 + 1) hbase (by decide)
    (by decide) (by omega), hend]
  ext p
  simp only [oddPrimeSegment, oddPrimePrefix, Finset.mem_filter, Finset.mem_Ico,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp, hne⟩
    have hpodd := hp.eq_two_or_odd.resolve_left hne
    exact ⟨by omega, hp, hne⟩
  · rintro ⟨hhi, hp, hne⟩
    have hpodd := hp.eq_two_or_odd.resolve_left hne
    have hpos := hp.two_le
    exact ⟨⟨by omega, by omega⟩, hp, hne⟩

/-- A kernel-checked count and sum from the marking sieve identify the
exact prescribed pool. Acceptance remains a separate proof obligation. -/
theorem markedSieve_pool_identities (base : Finset ℕ) (bound n X T : ℕ)
    (hbase : CompletePrimeBase base bound) (hX : Nat.Prime X) (hX3 : 3 ≤ X)
    (hodd : X % 2 = 1) (hbound : X + 2 ≤ (bound + 1) * (bound + 1))
    (hcount : (markedSieveValues base 3 ((X - 3) / 2 + 1)).card = n * n)
    (hsum : (∑ p ∈ markedSieveValues base 3 ((X - 3) / 2 + 1), p) = T) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  have hset := markedSieve_prefix base bound X hbase hX3 hodd hbound
  rw [hset] at hcount hsum
  exact pool_identities_of_oddPrefix_certificate hX hcount hsum

end
end Sude
