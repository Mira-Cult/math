import Sude.MarkedPrefix
import Sude.GeneratedPrefix.FirstTailSegment

/-! Cross-check the new marking sieve against the independently checked
factor/Lucas certificate for the actual first-tail endpoint segment. -/
namespace Sude
noncomputable section

theorem firstTailMarked_count_sum :
    (markedSieveValues (canonicalPrimeBase 8242) 67939501 54).card = 7 ∧
    (∑ p ∈ markedSieveValues (canonicalPrimeBase 8242) 67939501 54, p) = 475576967 := by
  rw [markedSieveValues_spec (canonicalPrimeBase 8242) 8242 67939501 54
    (canonicalPrimeBase_complete 8242) (by decide) (by decide) (by decide)]
  exact GeneratedPrefix.firstTailPrimeSegment_count_sum

end
end Sude
