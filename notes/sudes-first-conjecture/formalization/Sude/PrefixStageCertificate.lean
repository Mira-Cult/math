import Sude.LucasCertificate
import Sude.PrimePairMatching
import Sude.FinitePrefixPoolBound

/-! Composable finite FPF stage certificates. Acceptance is separate. -/
namespace Sude
noncomputable section

/-- Untrusted block data: sorted lower endpoints, interval bounds, and
references to Lucas nodes for both endpoints of every pair. -/
def PrefixStageBlockData (nodes : List Lucas.Node) (gap bound lo hi : ℕ) (xs : List ℕ) : Prop :=
  xs.Pairwise (· < ·) ∧ ∀ p ∈ xs,
    lo ≤ p ∧ p ≤ hi ∧ 3 < p ∧ p + gap ≤ bound ∧
      p ∈ nodes.map Lucas.Node.value ∧ p + gap ∈ nodes.map Lucas.Node.value

instance (nodes : List Lucas.Node) (gap bound lo hi : ℕ) (xs : List ℕ) :
    Decidable (PrefixStageBlockData nodes gap bound lo hi xs) := by
  unfold PrefixStageBlockData
  infer_instance

/-- Mathematical meaning of a block, with every referenced endpoint prime. -/
structure PrefixStageBlock (gap bound lo hi : ℕ) (xs : List ℕ) : Prop where
  sorted : xs.Pairwise (· < ·)
  entries : ∀ p ∈ xs, lo ≤ p ∧ p ≤ hi ∧ 3 < p ∧ p + gap ≤ bound ∧
    Nat.Prime p ∧ Nat.Prime (p + gap)

/-- Only checked Lucas nodes and checked block data are used to establish
the block's prime-pair specification. -/
theorem prefixStageBlock_of_certificate (nodes : List Lucas.Node)
    (gap bound lo hi : ℕ) (xs : List ℕ)
    (hnodes : Lucas.checkCertificate nodes = true)
    (hdata : PrefixStageBlockData nodes gap bound lo hi xs) :
    PrefixStageBlock gap bound lo hi xs := by
  refine ⟨hdata.1, ?_⟩
  intro p hp
  obtain ⟨hlo, hhi, hgt, hbound, hlow, hhigh⟩ := hdata.2 p hp
  obtain ⟨l, hl, hlval⟩ := List.mem_map.mp hlow
  obtain ⟨r, hr, hrval⟩ := List.mem_map.mp hhigh
  refine ⟨hlo, hhi, hgt, hbound, ?_, ?_⟩
  · rw [← hlval]
    exact Lucas.checkCertificate_sound nodes hnodes l hl
  · rw [← hrval]
    exact Lucas.checkCertificate_sound nodes hnodes r hr

/-- Independently accepted blocks compose when their actual endpoint ranges
are strictly separated. No cross-block distinctness oracle is assumed. -/
theorem PrefixStageBlock.append {gap bound lo₁ hi₁ lo₂ hi₂ : ℕ} {xs ys : List ℕ}
    (hx : PrefixStageBlock gap bound lo₁ hi₁ xs) (hy : PrefixStageBlock gap bound lo₂ hi₂ ys)
    (hfirst : lo₁ ≤ hi₁) (hsep : hi₁ < lo₂) (hsecond : lo₂ ≤ hi₂) :
    PrefixStageBlock gap bound lo₁ hi₂ (xs ++ ys) := by
  refine ⟨List.pairwise_append.mpr ⟨hx.sorted, hy.sorted, ?_⟩, ?_⟩
  · intro a ha b hb
    have ha' := (hx.entries a ha).2.1
    have hb' := (hy.entries b hb).1
    omega
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hlo, hhi, hgt, hbound, hprime, hprime'⟩ := hx.entries p hp
      refine ⟨hlo, ?_, hgt, hbound, hprime, hprime'⟩
      omega
    · obtain ⟨hlo, hhi, hgt, hbound, hprime, hprime'⟩ := hy.entries p hp
      exact ⟨by omega, hhi, hgt, hbound, hprime, hprime'⟩

/-- A completely certified sorted binary-gap stage gives an actual matching
in the prescribed pool, with its exact endpoint count. -/
theorem PrefixStageBlock.L_pool_matching {n j bound lo hi : ℕ} {xs : List ℕ}
    (lower : RSIndexLower) (hn : 2000 ≤ n) (hbound : bound ≤ 60000000)
    (hstage : PrefixStageBlock (2 ^ (j + 1)) bound lo hi xs) :
    (∀ p ∈ xs.toFinset, p ∈ pool n ∧ p + 2 ^ (j + 1) ∈ pool n) ∧
      PairwiseDisjointPairs xs.toFinset (2 ^ (j + 1)) ∧
      (pairFootprint xs.toFinset (2 ^ (j + 1))).card = 2 * xs.length := by
  have hprime : ∀ p ∈ xs.toFinset,
      3 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2 ^ (j + 1)) := by
    intro p hp
    have he := hstage.entries p (List.mem_toFinset.mp hp)
    exact ⟨he.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
  have hmatch := binary_prime_family_disjoint xs.toFinset (j + 1) hprime
  refine ⟨?_, hmatch, ?_⟩
  · intro p hp
    obtain ⟨_, _, hgt, hmax, hp0, hp1⟩ := hstage.entries p (List.mem_toFinset.mp hp)
    have hne : p ≠ 2 := by omega
    have hne' : p + 2 ^ (j + 1) ≠ 2 := by
      have : 3 < p + 2 ^ (j + 1) := lt_of_lt_of_le hgt (Nat.le_add_right p _)
      omega
    have hpbound : p ≤ 60000000 := (Nat.le_add_right p _).trans (hmax.trans hbound)
    exact ⟨finitePrefix_L_prime_in_pool lower hn hp0 hne hpbound,
      finitePrefix_L_prime_in_pool lower hn hp1 hne' (hmax.trans hbound)⟩
  · rw [pairFootprint_card _ _ (Nat.two_pow_pos _) hmatch,
      List.toFinset_card_of_nodup hstage.sorted.nodup]

end
end Sude
