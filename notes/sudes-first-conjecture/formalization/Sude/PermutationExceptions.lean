import Sude.PermutationContainment
import Sude.PermutationCutUnion
import Sude.BinomialEntropy
import Sude.PermutationEntropyMax
import Mathlib.Algebra.Order.Field.GeomSum

/-! Small-cut exception patterns for the finite permutation sample. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The `3s` labelled inputs originating on a cut. -/
def permutationCutPositions {n : ℕ} (S : Finset (Fin n)) : Finset (Fin 3 × Fin n) :=
  Finset.univ.product S

/-- Inputs that must stay inside after excluding a proposed exception set. -/
def permutationKeptInputs {n : ℕ} (S : Finset (Fin n)) (E : Finset (Fin 3 × Fin n))
    (i : Fin 3) : Finset (Fin n) := S.filter (fun x => (i, x) ∉ E)

/-- All allowed exception patterns of size at most the supplied budget. -/
def permutationExceptionPatterns {n : ℕ} (S : Finset (Fin n)) (q : ℕ) :
    Finset (Finset (Fin 3 × Fin n)) :=
  (permutationCutPositions S).powerset.filter (fun E => E.card ≤ q)

/-- The actual outgoing labels are genuine cut positions. -/
theorem permutationOutgoing_cutPositions_subset {n : ℕ} (S : Finset (Fin n))
    (p : Fin 3 → Equiv.Perm (Fin n)) :
    permutationOutgoing (permutationFamilyEdgePerm p) (permutationCutPositions S) ⊆
      permutationCutPositions S := Finset.filter_subset _ _

/-- If the actual outgoing labels are excluded, every remaining specified
input maps into the cut. -/
theorem permutation_actual_exceptions_contained {n : ℕ} (S : Finset (Fin n))
    (p : Fin 3 → Equiv.Perm (Fin n)) :
    p ∈ permutationFamilyContainmentEvent
      (permutationKeptInputs S (permutationOutgoing (permutationFamilyEdgePerm p)
        (permutationCutPositions S))) S := by
  classical
  simp only [permutationFamilyContainmentEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxS, hxnot⟩ := Finset.mem_filter.mp hx
  by_contra hn
  apply hxnot
  simp [permutationOutgoing, permutationCutPositions, permutationFamilyEdgePerm, hxS, hn]

/-- Every failed cut is covered by a containment event for an actual
exception pattern, with the strict integer threshold retained. -/
theorem permutationFixedCutBad_subset_exception_union {n : ℕ} (S : Finset (Fin n)) :
    permutationFixedCutBad S ⊆
      (permutationExceptionPatterns S (199 * S.card / 400)).biUnion
        (fun E => permutationFamilyContainmentEvent (permutationKeptInputs S E) S) := by
  classical
  intro p hp
  let E := permutationOutgoing (permutationFamilyEdgePerm p) (permutationCutPositions S)
  have hfail : permutationCutFailure p S := (Finset.mem_filter.mp hp).2
  have hout : 400 * E.card < 199 * S.card := by
    have hcut := permutationFamily_cut_card p S
    have hE : E = permutationOutgoing (permutationFamilyEdgePerm p)
        (Finset.univ.filter (fun e : Fin 3 × Fin n => e.2 ∈ S)) := by
      dsimp [E]
      congr 1
      ext e
      change e ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ S) ↔
        e ∈ Finset.univ.filter (fun x : Fin 3 × Fin n => x.2 ∈ S)
      simp
    rw [← hE] at hcut
    unfold permutationCutFailure at hfail
    rw [hcut] at hfail
    have hmin : min S.card (n - S.card) ≤ S.card := Nat.min_le_left _ _
    omega
  have hEpat : E ∈ permutationExceptionPatterns S (199 * S.card / 400) := by
    simp only [permutationExceptionPatterns, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨permutationOutgoing_cutPositions_subset S p, by omega⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨E, hEpat, permutation_actual_exceptions_contained S p⟩

/-- The union bound over exception patterns does not assume the events are
disjoint. -/
theorem permutationFixedCutBad_exception_union_bound {n : ℕ} (S : Finset (Fin n)) :
    (permutationFixedCutBad S).card ≤
      ∑ E ∈ permutationExceptionPatterns S (199 * S.card / 400),
        (permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card := by
  exact (Finset.card_le_card (permutationFixedCutBad_subset_exception_union S)).trans Finset.card_biUnion_le

/-- Every cut-position label is either kept or an exception. In particular,
all three permutation indices and every vertex on the cut are counted. -/
theorem permutationKeptInputs_card_sum {n : ℕ} (S : Finset (Fin n))
    (E : Finset (Fin 3 × Fin n)) (hE : E ⊆ permutationCutPositions S) :
    (∑ i, (permutationKeptInputs S E i).card) + E.card = 3 * S.card := by
  classical
  let kept := permutationCutPositions S \ E
  have hmap : ∀ e ∈ kept, e.1 ∈ (Finset.univ : Finset (Fin 3)) := by simp
  have hsum : kept.card = ∑ i, (permutationKeptInputs S E i).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    apply Finset.sum_congr rfl
    intro i hi
    have hset : kept.filter (fun e => e.1 = i) =
        (permutationKeptInputs S E i).image (fun x => (i, x)) := by
      ext ⟨k, x⟩
      simp only [kept, Finset.mem_filter, Finset.mem_sdiff, permutationKeptInputs,
        Finset.mem_image, Prod.mk.injEq]
      change (((k, x) ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ S) ∧ (k, x) ∉ E) ∧ k = i) ↔ _
      simp only [Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hx, hn⟩, rfl⟩
        exact ⟨x, ⟨hx, hn⟩, rfl, rfl⟩
      · rintro ⟨y, ⟨hy, hn⟩, rfl, rfl⟩
        exact ⟨⟨hy, hn⟩, rfl⟩
    rw [hset, Finset.card_image_of_injective _ (fun x y h => Prod.mk.inj h |>.2)]
  have hpart := Finset.card_sdiff_add_card_eq_card hE
  have hpos : (permutationCutPositions S).card = 3 * S.card := by
    change (((Finset.univ : Finset (Fin 3)) ×ˢ S)).card = _
    simp
  change kept.card + E.card = _ at hpart
  rw [hsum, hpos] at hpart
  exact hpart

/-- The number of possible exception sets is exactly the lower binomial
sum on the `3 * |S|` labelled positions. -/
theorem permutationExceptionPatterns_card {n : ℕ} (S : Finset (Fin n)) (q : ℕ) :
    (permutationExceptionPatterns S q).card =
      ∑ k ∈ Finset.range (q + 1), (3 * S.card).choose k := by
  classical
  let A := permutationCutPositions S
  let P := permutationExceptionPatterns S q
  have hmap : ∀ E ∈ P, E.card ∈ Finset.range (q + 1) := by
    intro E hE
    have hq := (Finset.mem_filter.mp hE).2
    simp only [Finset.mem_range]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ q := by simpa using Finset.mem_range.mp hk
  have hfiber : P.filter (fun E => E.card = k) = A.powersetCard k := by
    ext E
    simp only [P, permutationExceptionPatterns, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard, A]
    constructor
    · rintro ⟨⟨hsub, _⟩, heq⟩
      exact ⟨hsub, heq⟩
    · rintro ⟨hsub, heq⟩
      exact ⟨⟨hsub, by omega⟩, heq⟩
  rw [hfiber, Finset.card_powersetCard]
  have hA : A.card = 3 * S.card := by
    change (((Finset.univ : Finset (Fin 3)) ×ˢ S)).card = _
    simp
  rw [hA]

/-- Each proposed exception pattern leaves at least `3|S|-q` constrained
inputs, and its containment probability is bounded by the corresponding
power of `|S|/n`. -/
theorem permutationException_containment_bound {n q : ℕ} (S : Finset (Fin n))
    (hn : 0 < n) (hs : 0 < S.card) (hq : q ≤ 3 * S.card)
    (E : Finset (Fin 3 × Fin n)) (hE : E ∈ permutationExceptionPatterns S q) :
    ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
      (n.factorial : ℝ)^3 ≤ ((S.card : ℝ) / n)^(3 * S.card - q) := by
  classical
  have hE' := Finset.mem_filter.mp hE
  have hsub : E ⊆ permutationCutPositions S := Finset.mem_powerset.mp hE'.1
  have hEcard : E.card ≤ q := hE'.2
  have hkeep := permutationKeptInputs_card_sum S E hsub
  let L := ∑ i, (permutationKeptInputs S E i).card
  have hL : 3 * S.card - q ≤ L := by dsimp [L]; omega
  have hJS : ∀ i, (permutationKeptInputs S E i).card ≤ S.card := by
    intro i
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hnat := permutationFamilyContainment_power_bound (permutationKeptInputs S E) S hJS
  change n^L * (permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card ≤
    n.factorial^3 * S.card^L at hnat
  have hreal : (n : ℝ)^L * ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) ≤
      (n.factorial : ℝ)^3 * (S.card : ℝ)^L := by exact_mod_cast hnat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hnP : 0 < (n : ℝ)^L := pow_pos hnR _
  have hbase0 : 0 ≤ (S.card : ℝ) / n := by positivity
  have hbase1 : (S.card : ℝ) / n ≤ 1 := by
    apply (div_le_one hnR).2
    exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
  have hratio : ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
      (n.factorial : ℝ)^3 ≤ ((S.card : ℝ) / n)^L := by
    rw [div_pow]
    apply (div_le_div_iff₀ hF hnP).2
    nlinarith [hreal]
  exact hratio.trans (pow_le_pow_of_le_one hbase0 hbase1 hL)

/-- Small-cut fixed-event bound after union over all exception patterns. -/
theorem permutationFixedCutBad_exception_entropy_bound {n : ℕ} (S : Finset (Fin n))
    (hn : 0 < n) (hs : 0 < S.card) :
    ((permutationFixedCutBad S).card : ℝ) / (n.factorial : ℝ)^3 ≤
      Real.exp ((3 * S.card : ℕ) * Real.binEntropy ((199 : ℝ) / 1200)) *
        ((S.card : ℝ) / n)^(3 * S.card - (199 * S.card / 400)) := by
  classical
  let q := 199 * S.card / 400
  let A := permutationExceptionPatterns S q
  let B : ℝ := ((S.card : ℝ) / n)^(3 * S.card - q)
  have hq : q ≤ 3 * S.card := by dsimp [q]; omega
  have hqsource : 400 * q ≤ 199 * S.card := by dsimp [q]; omega
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hunion := permutationFixedCutBad_exception_union_bound S
  have hunionR : ((permutationFixedCutBad S).card : ℝ) ≤
      ∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) := by
    exact_mod_cast hunion
  have hsum : (∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
      (n.factorial : ℝ)^3) ≤ (A.card : ℝ) * B := by
    have h := Finset.sum_le_card_nsmul A
      (fun E => ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
        (n.factorial : ℝ)^3) B (by
          intro E hE
          exact permutationException_containment_bound S hn hs hq E hE)
    simpa using h
  have hnorm : ((permutationFixedCutBad S).card : ℝ) / (n.factorial : ℝ)^3 ≤ (A.card : ℝ) * B := by
    calc
      _ ≤ (∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ)) /
          (n.factorial : ℝ)^3 := div_le_div_of_nonneg_right hunionR hF.le
      _ = ∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
          (n.factorial : ℝ)^3 := Finset.sum_div ..
      _ ≤ _ := hsum
  have hcount : (A.card : ℝ) ≤
      Real.exp ((3 * S.card : ℕ) * Real.binEntropy ((199 : ℝ) / 1200)) := by
    rw [show A.card = ∑ k ∈ Finset.range (q + 1), (3 * S.card).choose k by
      exact permutationExceptionPatterns_card S q]
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using fc2k_exception_binomial_bound S.card q hqsource
  have hB : 0 ≤ B := by dsimp [B]; positivity
  exact hnorm.trans (mul_le_mul_of_nonneg_right hcount hB)

/-- A binomial coefficient has the convenient one-sided entropy bound
`choose n s ≤ exp(s * (1 - log(s/n)))` for an interior index. -/
theorem choose_le_exp_one_sub_log {n s : ℕ} (hs : 0 < s) (hsn : s < n) :
    (n.choose s : ℝ) ≤ Real.exp ((s : ℝ) * (1 - Real.log ((s : ℝ) / n))) := by
  let t : ℝ := (s : ℝ) / n
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsnR : (s : ℝ) < n := by exact_mod_cast hsn
  have ht0 : 0 < t := div_pos hsR hn
  have ht1 : t < 1 := (div_lt_one hn).2 hsnR
  have hrem := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < 1 - t))
  rw [Real.log_inv] at hrem
  have hmul := mul_le_mul_of_nonneg_left hrem (show 0 ≤ 1 - t by linarith)
  have hrest : -(1 - t) * Real.log (1 - t) ≤ t := by
    have heq : (1 - t) * ((1 - t)⁻¹ - 1) = t := by
      field_simp [show 1 - t ≠ 0 by linarith]
      ring
    rw [heq] at hmul
    nlinarith
  have hH : Real.binEntropy t ≤ t * (1 - Real.log t) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    nlinarith
  have hnH := mul_le_mul_of_nonneg_left hH hn.le
  have hnt : (n : ℝ) * t = s := by dsimp [t]; field_simp
  have hscale : (n : ℝ) * Real.binEntropy t ≤ (s : ℝ) * (1 - Real.log t) := by
    calc
      _ ≤ (n : ℝ) * (t * (1 - Real.log t)) := hnH
      _ = (s : ℝ) * (1 - Real.log t) := by rw [← mul_assoc, hnt]
  exact (binomial_choose_le_exp_entropy_all (show s ≤ n by omega)).trans ((Real.exp_le_exp).2 hscale)

/-- Common geometric base for the finite controller's small cuts. -/
noncomputable def fc2kSmallCutBase : ℝ :=
  Real.exp (1 + 3 * Real.binEntropy ((199 : ℝ) / 1200) +
    (601 / 400 : ℝ) * Real.log (1 / 256))

theorem fc2k_smallCutBase_lt : fc2kSmallCutBase < 1 / 216 := by
  have hg := fc2k_small_cut_gate
  have he := (Real.exp_lt_exp).2 hg
  have he3 : Real.exp (3 * Real.log 3) = 27 := by
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have he8 : Real.exp (Real.log (1 / 8)) = (1 : ℝ) / 8 := Real.exp_log (by norm_num)
  have hid : 1 + 3 * Real.binEntropy ((199 : ℝ) / 1200) +
      (3 - (199 : ℝ) / 400 - 1) * Real.log (1 / 256) + 3 * Real.log 3 =
      (1 + 3 * Real.binEntropy ((199 : ℝ) / 1200) +
        (601 / 400 : ℝ) * Real.log (1 / 256)) + 3 * Real.log 3 := by ring
  rw [hid, Real.exp_add, he3, he8] at he
  dsimp [fc2kSmallCutBase]
  linarith

/-- One small-cut size contributes at most the corresponding power of the
source's geometric base, after the exact subset multiplicity is included. -/
theorem fc2k_small_cut_summand_bound {n s : ℕ} (hs : 0 < s) (hsmall : 256 * s < n) :
    ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 ≤
      fc2kSmallCutBase ^ s := by
  let S := permutationCanonicalCut n s
  let t : ℝ := (s : ℝ) / n
  let q : ℕ := 199 * s / 400
  let K : ℕ := 3 * s - q
  let C : ℝ := 1 + 3 * Real.binEntropy ((199 : ℝ) / 1200) +
    (601 / 400 : ℝ) * Real.log (1 / 256)
  have hslt : s < n := by omega
  have hcard : S.card = s := permutationCanonicalCut_card (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have ht0 : 0 < t := div_pos hsR hnR
  have hsmallR : (256 : ℝ) * s ≤ n := by exact_mod_cast (show 256 * s ≤ n by omega)
  have htbound : t ≤ 1 / 256 := by
    dsimp [t]
    apply (div_le_iff₀ hnR).2
    linarith
  have hlog : Real.log t ≤ Real.log (1 / 256) := Real.log_le_log ht0 htbound
  have hlog0 : Real.log t ≤ 0 := le_trans hlog (Real.log_nonpos (by norm_num) (by norm_num))
  have hq : 400 * q ≤ 199 * s := by dsimp [q]; omega
  have hqR : (400 : ℝ) * q ≤ 199 * s := by exact_mod_cast hq
  have hq2 : q ≤ 2 * s := by dsimp [q]; omega
  have hK : ((K : ℕ) : ℝ) - s ≥ (601 / 400 : ℝ) * s := by
    dsimp [K]
    rw [Nat.cast_sub (by omega : q ≤ 3 * s)]
    push_cast
    linarith
  have hprod1 := mul_le_mul_of_nonpos_right hK hlog0
  have hprod2 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (601 / 400 : ℝ) * s by positivity)
  have hexponent : (s : ℝ) * (1 - Real.log t) +
      (3 * (s : ℝ)) * Real.binEntropy ((199 : ℝ) / 1200) + (K : ℝ) * Real.log t ≤
        (s : ℝ) * C := by
    dsimp [C]
    nlinarith
  have hchoose := choose_le_exp_one_sub_log hs hslt
  have hfixed := permutationFixedCutBad_exception_entropy_bound S (show 0 < n by omega) (by simpa [hcard] using hs)
  have hfixed' : (permutationFixedCutCount n s : ℝ) / (n.factorial : ℝ)^3 ≤
      Real.exp ((3 * (s : ℝ)) * Real.binEntropy ((199 : ℝ) / 1200)) * t^K := by
    simpa [permutationFixedCutCount, S, t, K, q, hcard, Nat.cast_mul] using hfixed
  have hmul := mul_le_mul hchoose hfixed' (by positivity) (Real.exp_nonneg _)
  have hexp : Real.exp ((s : ℝ) * (1 - Real.log t)) *
      (Real.exp ((3 * (s : ℝ)) * Real.binEntropy ((199 : ℝ) / 1200)) * t^K) =
        Real.exp ((s : ℝ) * (1 - Real.log t) +
          (3 * (s : ℝ)) * Real.binEntropy ((199 : ℝ) / 1200) + (K : ℝ) * Real.log t) := by
    have hKexp : Real.exp ((K : ℝ) * Real.log t) = t^K := by
      rw [Real.exp_nat_mul, Real.exp_log ht0]
    rw [Real.exp_add, Real.exp_add, hKexp]
    ring
  calc
    _ = (n.choose s : ℝ) * ((permutationFixedCutCount n s : ℝ) / (n.factorial : ℝ)^3) := by ring
    _ ≤ _ := hmul
    _ = _ := hexp
    _ ≤ Real.exp ((s : ℝ) * C) := (Real.exp_le_exp).2 hexponent
    _ = fc2kSmallCutBase ^ s := by
      rw [Real.exp_nat_mul]
      rfl

/-- The empty cut can never fail expansion. -/
theorem permutationFixedCutCount_zero (n : ℕ) : permutationFixedCutCount n 0 = 0 := by
  classical
  have hcanon : permutationCanonicalCut n 0 = ∅ := by
    ext x
    simp [permutationCanonicalCut]
  have hbad : permutationFixedCutBad (∅ : Finset (Fin n)) = ∅ := by
    ext p
    simp [permutationFixedCutBad, permutationCutFailure, cutEdges]
  simp [permutationFixedCutCount, hcanon, hbad]

/-- The small-cut union is bounded by a geometric series, with the empty
cut removed explicitly. -/
theorem fc2k_small_cut_sum_bound {n : ℕ} (_hn : 0 < n) :
    ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * permutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 ≤ 1 / 215 := by
  classical
  let A := (permutationSmallSizes n).filter (fun s => 0 < s)
  let term : ℕ → ℝ := fun s => ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) /
    (n.factorial : ℝ)^3
  have hzero : ∀ s ∈ permutationSmallSizes n, s ∉ A → term s = 0 := by
    intro s hs hnot
    have hs0 : s = 0 := by
      have hnot' : ¬ 0 < s := by
        intro hp
        apply hnot
        exact Finset.mem_filter.mpr ⟨hs, hp⟩
      omega
    subst s
    simp [term, permutationFixedCutCount_zero]
  have hrestrict : (∑ s ∈ permutationSmallSizes n, term s) = ∑ s ∈ A, term s := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    exact hzero s hs hnot
  have hbase0 : 0 ≤ fc2kSmallCutBase := by unfold fc2kSmallCutBase; positivity
  have hbase : fc2kSmallCutBase ≤ (1 : ℝ) / 216 := fc2k_smallCutBase_lt.le
  have hpoint : ∀ s ∈ A, term s ≤ ((1 : ℝ) / 216)^s := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hrange := (Finset.mem_filter.mp hs'.1).2
    exact (fc2k_small_cut_summand_bound hs'.2 hrange.2).trans (pow_le_pow_left₀ hbase0 hbase s)
  have hsubset : A ⊆ Finset.Ico 1 (n + 1) := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hrange := (Finset.mem_filter.mp hs'.1).1
    have hslt : s < n + 1 := Finset.mem_range.mp hrange
    exact Finset.mem_Ico.mpr ⟨by omega, hslt⟩
  have hsum : (∑ s ∈ A, term s) ≤ ∑ s ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / 216)^s := by
    calc
      _ ≤ ∑ s ∈ A, ((1 : ℝ) / 216)^s := Finset.sum_le_sum hpoint
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intro i hi hi'; positivity)
  have hgeom : (∑ s ∈ Finset.Ico 1 (n + 1), ((1 : ℝ) / 216)^s) ≤ 1 / 215 := by
    have h := geom_sum_Ico_le_of_lt_one (x := (1 : ℝ) / 216) (m := 1) (n := n + 1)
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcast : ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * permutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 = ∑ s ∈ permutationSmallSizes n, term s := by
    dsimp [term]
    push_cast
    rw [Finset.sum_div]
  rw [hcast, hrestrict]
  exact hsum.trans hgeom

/-- The small-cut event fits inside one seventh of the one-in-27
conditioning budget for every positive order. -/
theorem fc2k_small_cut_integer_budget {n : ℕ} (hn : 0 < n) :
    189 * (∑ s ∈ permutationSmallSizes n, Nat.choose n s * permutationFixedCutCount n s) <
      (n.factorial)^3 := by
  have h := fc2k_small_cut_sum_bound hn
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hreal : (189 : ℝ) *
      ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * permutationFixedCutCount n s : ℕ) : ℝ) <
      (n.factorial : ℝ)^3 := by
    have h' := (div_le_iff₀ hF).1 h
    nlinarith
  exact_mod_cast hreal

/-- The complete FC2K degree-six expansion graph exists for every order at
least 2001. The theorem constructs three derangements whose labelled
permutation edges satisfy the exact routing cut inequality. -/
theorem fc2k_permutation_expander_exists {n : ℕ} (hn : 2001 ≤ n) :
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      ∀ S : Finset (Fin n),
        199 * min S.card (n - S.card) ≤
          200 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card := by
  apply exists_permutation_expander_of_cut_sums (show 2 ≤ n by omega)
  have hsmall := fc2k_small_cut_integer_budget (show 0 < n by omega)
  have hlarge := fc2k_large_cut_integer_budget hn
  omega

end
end Sude
