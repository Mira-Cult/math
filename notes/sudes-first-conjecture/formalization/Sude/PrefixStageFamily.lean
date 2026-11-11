import Sude.PrefixStageIndex

/-! Assemble certified stages into the population interface used by the
physical allocator. Cross-stage separation is an explicit input. -/
namespace Sude
noncomputable section

structure CertifiedPrefixFamily (P Q n : ℕ) where
  lows : Fin P → List ℕ
  length : ∀ j, (lows j).length = Q
  nodup : ∀ j, (lows j).Nodup
  pool : ∀ j p, p ∈ (lows j).toFinset →
    p ∈ pool n ∧ p + 2 ^ (j.val + 1) ∈ pool n
  matching : ∀ j, PairwiseDisjointPairs (lows j).toFinset (2 ^ (j.val + 1))
  separated : ∀ j k, j ≠ k → Disjoint
    (pairFootprint (lows j).toFinset (2 ^ (j.val + 1)))
    (pairFootprint (lows k).toFinset (2 ^ (k.val + 1)))

namespace CertifiedPrefixFamily

/-- Build the family interface from accepted stage certificates and actual
cross-stage footprint separation. -/
def ofLStages {P Q n : ℕ} (lower : RSIndexLower) (hn : 2000 ≤ n)
    (lows : Fin P → List ℕ) (bound lo hi : Fin P → ℕ)
    (hlen : ∀ j, (lows j).length = Q)
    (hbound : ∀ j, bound j ≤ 60000000)
    (hstage : ∀ j, PrefixStageBlock (2 ^ (j.val + 1)) (bound j) (lo j) (hi j) (lows j))
    (hseparate : ∀ j k, j ≠ k → Disjoint
      (pairFootprint (lows j).toFinset (2 ^ (j.val + 1)))
      (pairFootprint (lows k).toFinset (2 ^ (k.val + 1)))) :
    CertifiedPrefixFamily P Q n where
  lows := lows
  length := hlen
  nodup := fun j => (hstage j).sorted.nodup
  pool := fun j => (PrefixStageBlock.L_pool_matching lower hn (hbound j) (hstage j)).1
  matching := fun j => (PrefixStageBlock.L_pool_matching lower hn (hbound j) (hstage j)).2.1
  separated := hseparate

/-- The value at each stage, source-order pair index and side. -/
def values {P Q n : ℕ} (F : CertifiedPrefixFamily P Q n) :
    (Fin P × Fin Q) × Bool → Sude.pool n := fun x =>
  stagePairPoolValues (F.lows x.1.1) (2 ^ (x.1.1.val + 1)) (F.pool x.1.1)
    (Fin.cast (F.length x.1.1).symm x.1.2, x.2)

theorem values_gap {P Q n : ℕ} (F : CertifiedPrefixFamily P Q n)
    (j : Fin P) (i : Fin Q) :
    (F.values ((j, i), true)).val =
      (F.values ((j, i), false)).val + 2 ^ (j.val + 1) :=
  stagePairPoolValues_gap (F.lows j) (2 ^ (j.val + 1)) (F.pool j)
    (Fin.cast (F.length j).symm i)

theorem values_injective {P Q n : ℕ} (F : CertifiedPrefixFamily P Q n) :
    Function.Injective F.values := by
  rintro ⟨⟨j, i⟩, s⟩ ⟨⟨k, m⟩, t⟩ heq
  by_cases hjk : j = k
  · subst k
    have h : (Fin.cast (F.length j).symm i, s) =
        (Fin.cast (F.length j).symm m, t) :=
      stagePairPoolValues_injective (F.lows j) (2 ^ (j.val + 1)) (F.pool j)
        (F.nodup j) (Nat.two_pow_pos _) (F.matching j) heq
    have hi := Fin.cast_injective (F.length j).symm (congrArg Prod.fst h)
    have hs := congrArg Prod.snd h
    exact Prod.ext (Prod.ext rfl hi) hs
  · have hj := stagePairEndpoint_mem_footprint (F.lows j) (2 ^ (j.val + 1))
      (Fin.cast (F.length j).symm i, s)
    have hk := stagePairEndpoint_mem_footprint (F.lows k) (2 ^ (k.val + 1))
      (Fin.cast (F.length k).symm m, t)
    have hv : stagePairEndpoint (F.lows j) (2 ^ (j.val + 1))
        (Fin.cast (F.length j).symm i, s) =
        stagePairEndpoint (F.lows k) (2 ^ (k.val + 1))
          (Fin.cast (F.length k).symm m, t) := congrArg Subtype.val heq
    rw [← hv] at hk
    exact False.elim (Finset.disjoint_left.mp (F.separated j k hjk) hj hk)

end CertifiedPrefixFamily
end
end Sude
