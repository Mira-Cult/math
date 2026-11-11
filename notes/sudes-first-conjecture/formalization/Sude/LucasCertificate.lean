import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Tactic

/-! FTT recursive Lucas certificate arithmetic. This file proves a checker
sound, but acceptance of the frozen 69,609-node table is a separate obligation. -/
namespace Sude.Lucas

def powMod (a e m : ℕ) : ℕ :=
  if e = 0 then 1 % m
  else
    let r := powMod a (e / 2) m
    if e % 2 = 0 then (r * r) % m else (r * r * a) % m
termination_by e
decreasing_by omega

/-- Binary modular powering computes the ordinary power residue. -/
theorem powMod_correct (a e m : ℕ) : powMod a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [powMod]
    split_ifs with hz heven
    · subst e
      simp
    · have hlt : e / 2 < e := by omega
      rw [ih (e / 2) hlt]
      have hs : e / 2 * 2 = e := by omega
      rw [← hs, pow_mul]
      simp [pow_two, Nat.mul_mod]
    · have hlt : e / 2 < e := by omega
      rw [ih (e / 2) hlt]
      have hs : e / 2 * 2 + 1 = e := by omega
      conv_rhs => rw [← hs, pow_add, pow_mul]
      simp [pow_two, Nat.mul_mod]

structure Node where
  value : ℕ
  witness : ℕ
  factors : List (ℕ × ℕ)
  deriving DecidableEq, Repr

def factorProduct (fs : List (ℕ × ℕ)) : ℕ :=
  (fs.map (fun f => f.1 ^ f.2)).prod

/-- Exact arithmetic conditions from an FTT Lucas node. Factor references
must already be present in the previously checked list. -/
def NodeValid (known : List ℕ) (x : Node) : Prop :=
  (x.value = 2 ∧ x.witness = 1 ∧ x.factors = []) ∨
  (2 < x.value ∧ x.value % 2 = 1 ∧ 1 < x.witness ∧ x.witness < x.value ∧
    x.factors ≠ [] ∧
    x.factors.Pairwise (fun f g => f.1 < g.1) ∧
    factorProduct x.factors = x.value - 1 ∧
    powMod x.witness (x.value - 1) x.value = 1 ∧
    ∀ f ∈ x.factors,
      f.1 ∈ known ∧ f.1 < x.value ∧ 1 ≤ f.2 ∧ f.2 ≤ 64 ∧
      (x.value - 1) % f.1 = 0 ∧
      Int.gcd ((powMod x.witness ((x.value - 1) / f.1) x.value : ℤ) - 1)
        (x.value : ℤ) = 1)

instance (known : List ℕ) (x : Node) : Decidable (NodeValid known x) := by
  unfold NodeValid
  infer_instance

def checkNode (known : List ℕ) (x : Node) : Bool := decide (NodeValid known x)

def checkNodes (known : List ℕ) : List Node → Bool
  | [] => true
  | x :: rest => checkNode known x && checkNodes (x.value :: known) rest

/-- Prime divisors of a product of certified prime powers occur as one of
its listed bases. Multiplicities need not be inferred or trusted. -/
theorem prime_divisor_in_factor_bases (q : ℕ) (hq : Nat.Prime q)
    (fs : List (ℕ × ℕ)) (hprime : ∀ f ∈ fs, Nat.Prime f.1)
    (hdiv : q ∣ factorProduct fs) : ∃ f ∈ fs, f.1 = q := by
  induction fs with
  | nil =>
    simp [factorProduct] at hdiv
    have := hq.one_lt
    omega
  | cons f fs ih =>
    have hd : q ∣ f.1 ^ f.2 * factorProduct fs := by simpa [factorProduct] using hdiv
    rcases (hq.dvd_mul.mp hd) with hf | ht
    · have hqf := hq.dvd_of_dvd_pow hf
      have hfprime : Nat.Prime f.1 := hprime f (by simp)
      have heq := (Nat.prime_dvd_prime_iff_eq hq hfprime).mp hqf
      exact ⟨f, by simp, heq.symm⟩
    · obtain ⟨g, hg, heq⟩ := ih (by
        intro g hg; exact hprime g (by simp [hg])) ht
      exact ⟨g, by simp [hg], heq⟩

/-- Accepted node data imply primality when all prior referenced nodes are
actually prime. This is mathlib's Lucas theorem, not an imported axiom. -/
theorem nodeValid_prime (known : List ℕ) (x : Node)
    (hknown : ∀ q ∈ known, Nat.Prime q) (hvalid : NodeValid known x) :
    Nat.Prime x.value := by
  rcases hvalid with ⟨h2, _, _⟩ | h
  · simpa [h2] using Nat.prime_two
  · rcases h with ⟨hval, hodd, ha1, hap, hnonempty, hsorted, hprod, hpow, hfactors⟩
    apply lucas_primality x.value (x.witness : ZMod x.value)
    · rw [powMod_correct] at hpow
      have hmod : (x.witness ^ (x.value - 1)) % x.value = 1 % x.value := by
        simpa [Nat.mod_eq_of_lt (show 1 < x.value by omega)] using hpow
      have hcast := (ZMod.natCast_eq_natCast_iff' (x.witness ^ (x.value - 1)) 1 x.value).2 hmod
      simpa only [Nat.cast_pow, Nat.cast_one] using hcast
    · intro q hq hqd
      have hfprime : ∀ f ∈ x.factors, Nat.Prime f.1 := by
        intro f hf
        exact hknown f.1 (hfactors f hf).1
      have hd : q ∣ factorProduct x.factors := by rwa [hprod]
      obtain ⟨f, hf, heq⟩ := prime_divisor_in_factor_bases q hq x.factors hfprime hd
      have hgcd := (hfactors f hf).2.2.2.2.2
      rw [heq] at hgcd
      intro hequal
      have heq' : (x.witness ^ ((x.value - 1) / q)) % x.value = 1 % x.value := by
        apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
        simpa only [Nat.cast_pow, Nat.cast_one] using hequal
      have hres : powMod x.witness ((x.value - 1) / q) x.value = 1 := by
        rw [powMod_correct]
        simpa [Nat.mod_eq_of_lt (show 1 < x.value by omega)] using heq'
      rw [hres] at hgcd
      simp at hgcd
      omega

/-- Every node in an accepted ordered chain is prime, provided the initial
known list contains only primes. Earlier factors are checked before use. -/
theorem checkNodes_sound (known : List ℕ) (nodes : List Node)
    (hknown : ∀ q ∈ known, Nat.Prime q) (hcheck : checkNodes known nodes = true) :
    ∀ x ∈ nodes, Nat.Prime x.value := by
  induction nodes generalizing known with
  | nil => simp
  | cons x xs ih =>
    simp only [checkNodes, Bool.and_eq_true] at hcheck
    have hv : NodeValid known x := of_decide_eq_true hcheck.1
    have hp : Nat.Prime x.value := nodeValid_prime known x hknown hv
    have hknown' : ∀ q ∈ (x.value :: known), Nat.Prime q := by
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hp
      · exact hknown q hq
    have hrest := ih (x.value :: known) hknown' hcheck.2
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hp
    · exact hrest y hy

/-- The complete checker starts with no assumed prime facts. -/
def checkCertificate (nodes : List Node) : Bool := checkNodes [] nodes

theorem checkCertificate_sound (nodes : List Node)
    (hcheck : checkCertificate nodes = true) :
    ∀ x ∈ nodes, Nat.Prime x.value :=
  checkNodes_sound [] nodes (by simp) hcheck

end Sude.Lucas
