import Sude.PrimeSegmentSieve
import Sude.LucasCertificate

/-! Kernel-checkable segment certificates: one proper divisor per composite
and a shared Lucas graph for all prime survivors. -/
namespace Sude
noncomputable section

/-- A zero divisor marks a certified prime; any other value must be a
proper divisor of the candidate. -/
def checkFactorRow (known : List ℕ) (candidate divisor : ℕ) : Bool :=
  if divisor = 0 then known.contains candidate
  else decide (2 ≤ divisor ∧ divisor < candidate ∧ candidate % divisor = 0)

def checkFactorRows (known : List ℕ) (start : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => checkFactorRow known start d && checkFactorRows known (start + 2) ds

def factorSurvivors (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => if d = 0 then start :: factorSurvivors (start + 2) ds
      else factorSurvivors (start + 2) ds

/-- Each accepted row classifies its candidate exactly, provided every
listed survivor is actually prime. -/
theorem checkFactorRow_spec (known : List ℕ) (candidate divisor : ℕ)
    (hknown : ∀ p ∈ known, Nat.Prime p) (hcheck : checkFactorRow known candidate divisor = true) :
    (divisor = 0 ↔ Nat.Prime candidate) := by
  unfold checkFactorRow at hcheck
  split_ifs at hcheck with hd
  · constructor
    · intro _
      exact hknown candidate (List.contains_iff_mem.mp hcheck)
    · intro _; exact hd
  · have hdiv : 2 ≤ divisor ∧ divisor < candidate ∧ candidate % divisor = 0 :=
      of_decide_eq_true hcheck
    have hnot : ¬Nat.Prime candidate :=
      Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hdiv.2.2) hdiv.1 hdiv.2.1
    exact ⟨fun h => (hd h).elim, fun h => (hnot h).elim⟩

/-- Accepted consecutive rows list precisely the prime odd candidates in
their half-open interval. -/
theorem factorSurvivors_spec (known : List ℕ) (start : ℕ) (ds : List ℕ)
    (hknown : ∀ p ∈ known, Nat.Prime p) (hcheck : checkFactorRows known start ds = true)
    (hodd : start % 2 = 1) :
    ∀ n, n ∈ factorSurvivors start ds ↔
      start ≤ n ∧ n < start + 2 * ds.length ∧ n % 2 = 1 ∧ Nat.Prime n := by
  induction ds generalizing start with
  | nil =>
    intro n
    simp [factorSurvivors]
    omega
  | cons d ds ih =>
    simp only [checkFactorRows, Bool.and_eq_true] at hcheck
    have hrow := checkFactorRow_spec known start d hknown hcheck.1
    have hodd' : (start + 2) % 2 = 1 := by omega
    have htail := ih (start + 2) hcheck.2 hodd'
    intro n
    by_cases hd : d = 0
    · have hp : Nat.Prime start := hrow.mp hd
      simp only [factorSurvivors, hd, if_true, List.mem_cons, htail, List.length_cons]
      constructor
      · rintro (rfl | ⟨hlo, hhi, hnodd, hnprime⟩)
        · exact ⟨by omega, by omega, hodd, hp⟩
        · exact ⟨by omega, by omega, hnodd, hnprime⟩
      · rintro ⟨hlo, hhi, hnodd, hnprime⟩
        by_cases heq : n = start
        · exact Or.inl heq
        · exact Or.inr ⟨by omega, by omega, hnodd, hnprime⟩
    · have hnp : ¬Nat.Prime start := fun hp => hd (hrow.mpr hp)
      simp only [factorSurvivors, hd, if_false, htail, List.length_cons]
      constructor
      · rintro ⟨hlo, hhi, hnodd, hnprime⟩
        exact ⟨by omega, by omega, hnodd, hnprime⟩
      · rintro ⟨hlo, hhi, hnodd, hnprime⟩
        have hne : n ≠ start := by intro h; subst n; exact hnp hnprime
        exact ⟨by omega, by omega, hnodd, hnprime⟩

/-- Every survivor is at least the starting candidate. -/
theorem factorSurvivors_ge (start : ℕ) (ds : List ℕ) :
    ∀ x ∈ factorSurvivors start ds, start ≤ x := by
  induction ds generalizing start with
  | nil => simp [factorSurvivors]
  | cons e es ih =>
    intro x hx
    by_cases he : e = 0
    · simp only [factorSurvivors, he, if_true, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · have hh := ih (start + 2) x hx; omega
    · simp only [factorSurvivors, he, if_false] at hx
      have hh := ih (start + 2) x hx; omega

/-- The candidate list contains no duplicate values. -/
theorem factorSurvivors_nodup (start : ℕ) (ds : List ℕ) :
    (factorSurvivors start ds).Nodup := by
  induction ds generalizing start with
  | nil => simp [factorSurvivors]
  | cons d ds ih =>
    by_cases hd : d = 0
    · simp only [factorSurvivors, hd, if_true, List.nodup_cons]
      refine ⟨?_, ih (start + 2)⟩
      intro hm
      have := factorSurvivors_ge (start + 2) ds start hm
      omega
    · simpa [factorSurvivors, hd] using ih (start + 2)

/-- A complete Lucas graph and accepted factor rows reconstruct exactly the
mathematical odd-prime segment. -/
theorem factor_certificate_segment (nodes : List Lucas.Node) (start : ℕ) (ds : List ℕ)
    (hprime : Lucas.checkCertificate nodes = true)
    (hcheck : checkFactorRows (nodes.map Lucas.Node.value) start ds = true)
    (hodd : start % 2 = 1) :
    (factorSurvivors start ds).toFinset = oddPrimeSegment start (start + 2 * ds.length) := by
  classical
  have hknown : ∀ p ∈ nodes.map Lucas.Node.value, Nat.Prime p := by
    intro p hp
    obtain ⟨node, hn, rfl⟩ := List.mem_map.mp hp
    exact Lucas.checkCertificate_sound nodes hprime node hn
  ext n
  simp only [List.mem_toFinset, oddPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
  rw [factorSurvivors_spec _ _ _ hknown hcheck hodd]
  constructor
  · rintro ⟨hlo, hhi, hno, hp⟩
    exact ⟨⟨hlo, hhi⟩, hp, by omega⟩
  · rintro ⟨⟨hlo, hhi⟩, hp, hne⟩
    exact ⟨hlo, hhi, hp.eq_two_or_odd.resolve_left hne, hp⟩

/-- Accepted certificates give exact cardinality and sum of the mathematical
prime segment, not merely statistics of the supplied list. -/
theorem factor_certificate_count_sum (nodes : List Lucas.Node) (start : ℕ) (ds : List ℕ)
    (hprime : Lucas.checkCertificate nodes = true)
    (hcheck : checkFactorRows (nodes.map Lucas.Node.value) start ds = true)
    (hodd : start % 2 = 1) :
    (oddPrimeSegment start (start + 2 * ds.length)).card =
        (factorSurvivors start ds).length ∧
    (∑ p ∈ oddPrimeSegment start (start + 2 * ds.length), p) =
        (factorSurvivors start ds).sum := by
  rw [← factor_certificate_segment nodes start ds hprime hcheck hodd]
  exact ⟨List.toFinset_card_of_nodup (factorSurvivors_nodup start ds), by
    simpa using List.sum_toFinset id (factorSurvivors_nodup start ds)⟩

end
end Sude
