import Sude.PrimePrefixSpec
import Sude.PrimeSegmentSieve
import Sude.FirstPrefixEndpoint

/-! Composition of the verified segment checker with the exact pool index
and sum. Tail-sized checker acceptance remains an explicit obligation. -/
namespace Sude
noncomputable section

/-- An accepted endpoint, count and sum from a verified checker segment
identify the exact prime pool. No output is trusted without its proof. -/
theorem checked_prefix_pool_identities (base : Finset ℕ) (bound n X T : ℕ)
    (hbase : CompletePrimeBase base bound)
    (hbound : X + 1 ≤ (bound + 1) * (bound + 1))
    (hX : X ∈ checkedOddSegment base 0 (X + 1))
    (hcount : (checkedOddSegment base 0 (X + 1)).card = n * n)
    (hsum : (∑ p ∈ checkedOddSegment base 0 (X + 1), p) = T) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  have hsegment := checkedOddSegment_prefix base bound X hbase hbound
  rw [hsegment] at hX hcount hsum
  have hp : Nat.Prime X := (Finset.mem_filter.mp hX).2.1
  exact pool_identities_of_oddPrefix_certificate hp hcount hsum

/-- The first frozen endpoint is prime in Lean. Its exact count and sum are
still separate finite numerical obligations. -/
theorem first_ftt_pool_identities_of_verified_prefix
    (hcount : (oddPrimePrefix 67939607).card = 2001 * 2001)
    (hsum : (∑ p ∈ oddPrimePrefix 67939607, p) = 131735066271767) :
    poolMaximum 2001 = Lucas.Generated.R0000.row_2001.maxEntry ∧
    Lucas.poolTotal 2001 = Lucas.Generated.R0000.row_2001.total := by
  have hp : Nat.Prime 67939607 := Lucas.Generated.first_ftt_max_prime
  exact pool_identities_of_oddPrefix_certificate hp hcount hsum

end
end Sude
