import Sude.FastTwinStrideSixScan
import Sude.FastSwarPopcount
import Sude.FiniteTwinFilteredBase
import Sude.PrefixTruncation
import Mathlib.Data.Finset.Sort

/-!
# Fast Binary-Tree Word-Parallel Prefix Scanner

Kernel-friendly certificate verifier for multi-stage power-of-two prime-pair
prefix populations (`gap = 2 ^ (j + 1)` for `j : Fin P`) in `[5, 32769^2]`:
1. Sieves `524,288`-bit stride-six super-chunks once per `3,145,728` integers using
   `fastLanePrimeMask` over `finiteTwinOddBase.tail`.
2. Splits each super-chunk via a balanced depth-6 binary tree into `64` inverted
   `8,192`-bit availability words (`1` = available prime, `0` = composite or used).
3. Stores all `(laneA, laneB)` words in a pure functional `Braun` binary tree
   giving `O(log N)` random access in Lean's kernel without `Array` list copies.
4. Executes each stage word-parallel across `[startWord, endWord]` using bitwise
   operations and `fastSetCount 10`, verifying exact pair counts, global endpoint
   disjointness, stagewise strict monotonicity, per-stage span bounds, and
   sliding-window consumption caps.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-- Force `x : ℕ` to a kernel literal via `Nat.casesOn` so constructor fields retain
zero AST references to prior expressions during `decide +kernel` reduction. -/
def forceNat {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn x (k 0) (fun p => k (Nat.succ p))

theorem forceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    forceNat x k = k x := by
  cases x <;> rfl

/-- Force both `ℕ` components of a pair to kernel literals before constructing `Prod.mk`. -/
def seqPair {α : Type} (p : ℕ × ℕ) (k : ℕ × ℕ → α) : α :=
  Prod.casesOn p (fun a b => forceNat a fun a' => forceNat b fun b' => k (a', b'))

theorem seqPair_eq {α : Type} (p : ℕ × ℕ) (k : ℕ × ℕ → α) :
    seqPair p k = k p := by
  rcases p with ⟨a, b⟩
  simp [seqPair, forceNat_eq]

/-- Force a list spine step to WHNF before passing to `k`. -/
def seqList {α β : Type} (xs : List α) (k : List α → β) : β :=
  List.casesOn xs (k []) (fun x rest => k (x :: rest))

theorem seqList_eq {α β : Type} (xs : List α) (k : List α → β) :
    seqList xs k = k xs := by
  cases xs <;> rfl

/-- Pure functional Braun binary tree providing `O(log N)` random-access `get` and `set`
in Lean's kernel without `Array` list-traversal overhead. -/
inductive Braun (α : Type) : Type where
  | leaf : Braun α
  | node : α → Braun α → Braun α → Braun α

/-- Force a `Braun` constructor to WHNF before passing to `k`. -/
def seqBraun {α β : Type} (t : Braun α) (k : Braun α → β) : β :=
  Braun.casesOn t (k .leaf) (fun v l r => k (.node v l r))

theorem seqBraun_eq {α β : Type} (t : Braun α) (k : Braun α → β) :
    seqBraun t k = k t := by
  cases t <;> rfl

/-- Read index `i` from a `Braun` tree, returning `d` out of bounds. -/
def Braun.get {α : Type} (d : α) : Braun α → ℕ → α
  | .leaf, _ => d
  | .node v _ _, 0 => v
  | .node _ l r, i + 1 =>
      if i % 2 = 0 then l.get d (i / 2) else r.get d (i / 2)

/-- Structural-recursion helper for `Braun.set` using explicit bit-depth fuel (`0` axioms). -/
def Braun.setAux {α : Type} (d : α) : ℕ → Braun α → ℕ → α → Braun α
  | 0, .leaf, _, x => .node x .leaf .leaf
  | 0, .node _ l r, _, x => .node x l r
  | _ + 1, .leaf, 0, x => .node x .leaf .leaf
  | fuel + 1, .leaf, i + 1, x =>
      if i % 2 = 0 then seqBraun (Braun.setAux d fuel .leaf (i / 2) x) (fun l' => .node d l' .leaf)
      else seqBraun (Braun.setAux d fuel .leaf (i / 2) x) (fun r' => .node d .leaf r')
  | _ + 1, .node _ l r, 0, x => .node x l r
  | fuel + 1, .node v l r, i + 1, x =>
      if i % 2 = 0 then seqBraun (Braun.setAux d fuel l (i / 2) x) (fun l' => .node v l' r)
      else seqBraun (Braun.setAux d fuel r (i / 2) x) (fun r' => .node v l r')

/-- Update index `i` to `x` in a `Braun` tree, extending with `d` if needed. -/
def Braun.set {α : Type} (d : α) (t : Braun α) (i : ℕ) (x : α) : Braun α :=
  Braun.setAux d (i.log2 + 1) t i x

theorem Braun.leaf_get {α : Type} (d : α) (j : ℕ) :
    (Braun.leaf : Braun α).get d j = d := by
  cases j <;> rfl

theorem Braun.get_setAux {α : Type} (d : α) (fuel : ℕ) (t : Braun α) (i j : ℕ) (x : α)
    (hi : i < 2 ^ fuel) :
    (Braun.setAux d fuel t i x).get d j = if j = i then x else t.get d j := by
  induction fuel generalizing t i j with
  | zero =>
    have hi0 : i = 0 := by simp at hi; exact hi
    subst hi0
    cases t <;> cases j <;> simp [Braun.setAux, Braun.get]
  | succ fuel ih =>
    cases i with
    | zero =>
      cases t <;> cases j <;> simp [Braun.setAux, Braun.get]
    | succ i =>
      have hdiv_lt : i / 2 < 2 ^ fuel := by
        rw [pow_succ] at hi
        omega
      cases t with
      | leaf =>
        cases j with
        | zero =>
          by_cases hpar : i % 2 = 0 <;> simp [Braun.setAux, seqBraun_eq, Braun.get, hpar]
        | succ j =>
          by_cases hpar : i % 2 = 0 <;> by_cases hj : j % 2 = 0
          · simp only [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, if_true, Nat.succ_inj]
            rw [ih .leaf (i / 2) (j / 2) hdiv_lt, Braun.leaf_get]
            have heq : (j / 2 = i / 2) ↔ (j = i) := by omega
            simp [heq]
          · have hne : j ≠ i := by omega
            simp [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, hne]
          · have hne : j ≠ i := by omega
            simp [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, hne]
          · simp only [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, if_false, Nat.succ_inj]
            rw [ih .leaf (i / 2) (j / 2) hdiv_lt, Braun.leaf_get]
            have heq : (j / 2 = i / 2) ↔ (j = i) := by omega
            simp [heq]
      | node v l r =>
        cases j with
        | zero =>
          by_cases hpar : i % 2 = 0 <;> simp [Braun.setAux, seqBraun_eq, Braun.get, hpar]
        | succ j =>
          by_cases hpar : i % 2 = 0 <;> by_cases hj : j % 2 = 0
          · simp only [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, if_true, Nat.succ_inj]
            rw [ih l (i / 2) (j / 2) hdiv_lt]
            have heq : (j / 2 = i / 2) ↔ (j = i) := by omega
            simp [heq]
          · have hne : j ≠ i := by omega
            simp [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, hne]
          · have hne : j ≠ i := by omega
            simp [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, hne]
          · simp only [Braun.setAux, seqBraun_eq, Braun.get, hpar, hj, if_false, Nat.succ_inj]
            rw [ih r (i / 2) (j / 2) hdiv_lt]
            have heq : (j / 2 = i / 2) ↔ (j = i) := by omega
            simp [heq]

theorem Braun.get_set {α : Type} (d : α) (t : Braun α) (i j : ℕ) (x : α) :
    (t.set d i x).get d j = if j = i then x else t.get d j :=
  Braun.get_setAux d (i.log2 + 1) t i j x Nat.lt_log2_self

/-- Write consecutive list elements into a `Braun` tree starting at `k`. -/
def Braun.setList {α : Type} (d : α) : ℕ → List α → Braun α → Braun α
  | _, [], t => t
  | k, x :: xs, t => seqBraun (t.set d k x) (Braun.setList d (k + 1) xs)

/-- Strictly write consecutive `(ℕ × ℕ)` word pairs into a `Braun` tree starting at `k`. -/
def setStrictPairList : ℕ → List (ℕ × ℕ) → Braun (ℕ × ℕ) → Braun (ℕ × ℕ)
  | _, [], t => t
  | k, p :: ps, t =>
      seqPair p fun p' =>
        seqBraun (t.set (0, 0) k p') (setStrictPairList (k + 1) ps)

theorem setStrictPairList_eq (k : ℕ) (ps : List (ℕ × ℕ)) (t : Braun (ℕ × ℕ)) :
    setStrictPairList k ps t = Braun.setList (0, 0) k ps t := by
  induction ps generalizing k t with
  | nil => rfl
  | cons p ps ih =>
    simp [setStrictPairList, seqPair_eq, seqBraun_eq, Braun.setList, ih]

theorem Braun.get_setList {α : Type} (d : α) (k : ℕ) (xs : List α) (t : Braun α) (j : ℕ) :
    (Braun.setList d k xs t).get d j =
      if h : k ≤ j ∧ j < k + xs.length then xs[j - k]'(by omega) else t.get d j := by
  induction xs generalizing k t with
  | nil =>
    simp [Braun.setList]
  | cons x xs ih =>
    simp only [Braun.setList, seqBraun_eq, List.length_cons]
    rw [ih (k + 1) (t.set d k x), Braun.get_set]
    by_cases hkj : j = k
    · subst hkj
      have h2 : j ≤ j ∧ j < j + (xs.length + 1) := by omega
      simp [h2]
    · by_cases hrange : k + 1 ≤ j ∧ j < k + 1 + xs.length
      · have h2 : k ≤ j ∧ j < k + (xs.length + 1) := by omega
        have hsub : j - k = (j - (k + 1)) + 1 := by omega
        rw [dif_pos hrange, dif_pos h2]
        simp [hsub]
      · have h2 : ¬ (k ≤ j ∧ j < k + (xs.length + 1)) := by omega
        rw [dif_neg hrange, dif_neg h2, if_neg hkj]

/-- Single-lane compressed composite mask using `fastLanePrimeMask`. -/
def fastListSingleLaneMask (base : List ℕ) (lo width : ℕ) : ℕ :=
  base.foldr (fun p bits => fastLanePrimeMask p lo width ||| bits) 0

theorem fastListSingleLaneMask_eq (base : List ℕ) (lo width : ℕ)
    (hbase : ∀ p ∈ base, p % 2 = 1 ∧ p % 3 ≠ 0) :
    fastListSingleLaneMask base lo width = strideSixLaneMask base lo width := by
  induction base with
  | nil => simp [fastListSingleLaneMask, strideSixLaneMask]
  | cons p ps ih =>
    have hp : p % 2 = 1 ∧ p % 3 ≠ 0 := hbase p List.mem_cons_self
    have hps' : ∀ q ∈ ps, q % 2 = 1 ∧ q % 3 ≠ 0 :=
      fun q hq => hbase q (List.mem_cons_of_mem p hq)
    change fastLanePrimeMask p lo width ||| fastListSingleLaneMask ps lo width =
      if p % 2 = 1 ∧ p % 3 ≠ 0 then
        strideSixLanePrimeMask p lo width ||| strideSixLaneMask ps lo width
      else strideSixLaneMask ps lo width
    rw [if_pos hp, ih hps', fastLanePrimeMask_eq]

/-- Fast single-lane composite mask over `finiteTwinOddBase.tail` truncated to `bound`. -/
def fastBoundedSingleLaneMask (bound lo width : ℕ) : ℕ :=
  fastListSingleLaneMask (finiteTwinOddBase.tail.filter (· ≤ bound)) lo width

private theorem strideSixLaneMask_filter_two_three (ps : List ℕ) (bound lo width : ℕ) :
    strideSixLaneMask ((2 :: 3 :: ps).filter (· ≤ bound)) lo width =
      strideSixLaneMask (ps.filter (· ≤ bound)) lo width := by
  simp only [List.filter_cons]
  by_cases h2 : 2 ≤ bound <;> by_cases h3 : 3 ≤ bound <;>
    simp [h2, h3, strideSixLaneMask]

theorem strideSixLaneMask_filtered_checked_eq_tail (bound lo width : ℕ) :
    strideSixLaneMask (finiteTwinCheckedBase.filter (· ≤ bound)) lo width =
      strideSixLaneMask (finiteTwinOddBase.tail.filter (· ≤ bound)) lo width := by
  rw [finiteTwinCheckedBase, finiteTwinOddBase_head_eq]
  exact strideSixLaneMask_filter_two_three finiteTwinOddBase.tail bound lo width

theorem fastBoundedSingleLaneMask_clear_iff_prime (bound lo width i : ℕ)
    (hb32 : bound ≤ 32768)
    (hlo : 3 ≤ lo) (hodd : lo % 2 = 1) (hlo3 : lo % 3 ≠ 0)
    (hi : i < width) (hbound : lo + 6 * width ≤ (bound + 1) * (bound + 1)) :
    (fastBoundedSingleLaneMask bound lo width).testBit i = false ↔ Nat.Prime (lo + 6 * i) := by
  have hcomp := finite_twin_filtered_base_complete bound hb32
  have hprime : ∀ p ∈ finiteTwinCheckedBase.filter (· ≤ bound), Nat.Prime p :=
    fun p hp => ((hcomp p).mp (List.mem_toFinset.mpr hp)).1
  have hvalid : ∀ p ∈ finiteTwinOddBase.tail.filter (· ≤ bound), p % 2 = 1 ∧ p % 3 ≠ 0 :=
    fun p hp => finiteTwinOddBase_tail_valid p (List.mem_filter.mp hp).1
  rw [fastBoundedSingleLaneMask, fastListSingleLaneMask_eq _ lo width hvalid,
    ← strideSixLaneMask_filtered_checked_eq_tail bound lo width,
    strideSixLaneMask_eq_old _ lo width i hprime hodd hlo3]
  have hp0 := segment_clear_iff_prime (finiteTwinCheckedBase.filter (· ≤ bound)) bound lo
    (3 * width) (3 * i) hcomp hlo hodd (by omega) (by omega)
  have heq : lo + 2 * (3 * i) = lo + 6 * i := by omega
  rw [heq] at hp0
  exact hp0

/-- Bits per word (`8,192 = 8 <<< 10`) and bits per super-chunk (`524,288 = 64 * 8,192`). -/
abbrev prefixWordBits : ℕ := 8192
abbrev prefixSuperWords : ℕ := 64
abbrev prefixSuperBits : ℕ := 524288
abbrev prefixWordSpan : ℕ := 49152

/-- All-ones `8,192`-bit mask. -/
def fullWordMask : ℕ := (1 <<< 8192) - 1

theorem two_pow_sub_one_testBit (w b : ℕ) :
    ((1 <<< w) - 1).testBit b = decide (b < w) := by
  rw [Nat.one_shiftLeft]
  exact Nat.testBit_two_pow_sub_one w b

theorem fullWordMask_testBit (b : ℕ) :
    fullWordMask.testBit b = decide (b < 8192) :=
  two_pow_sub_one_testBit 8192 b

theorem and_two_pow_sub_one_testBit (x w b : ℕ) :
    (x &&& ((1 <<< w) - 1)).testBit b = (x.testBit b && decide (b < w)) := by
  rw [Nat.testBit_and, two_pow_sub_one_testBit]

/-- Unconditionally clear the `1`-bits of `m` from an `8,192`-bit word `a`. -/
def clearWordBits (a m : ℕ) : ℕ :=
  (a &&& fullWordMask) &&& (fullWordMask ^^^ (m &&& fullWordMask))

theorem clearWordBits_testBit (a m b : ℕ) :
    (clearWordBits a m).testBit b = (a.testBit b && decide (b < 8192) && !m.testBit b) := by
  unfold clearWordBits
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, fullWordMask_testBit]
  cases a.testBit b <;> cases m.testBit b <;> cases decide (b < 8192) <;> rfl

/-- Balanced binary-tree split of `(8192 <<< d)` composite bits into `2 ^ d`
inverted `8,192`-bit availability words (`1` = available prime, `0` = composite),
forced to kernel literals at the leaves so sieve ASTs are freed immediately. -/
def splitAvailWords : ℕ → ℕ → List ℕ
  | 0, bits => forceNat (fullWordMask ^^^ (bits &&& fullWordMask)) (fun w => [w])
  | d + 1, bits =>
      let half := 8192 <<< d
      forceNat (bits &&& ((1 <<< half) - 1)) fun bLo =>
      forceNat (bits >>> half) fun bHi =>
        splitAvailWords d bLo ++ splitAvailWords d bHi

theorem splitAvailWords_length (d bits : ℕ) :
    (splitAvailWords d bits).length = 2 ^ d := by
  induction d generalizing bits with
  | zero => simp [splitAvailWords, forceNat_eq]
  | succ d ih =>
    simp only [splitAvailWords, forceNat_eq, List.length_append, ih, pow_succ]
    omega

theorem splitAvailWords_testBit (d bits k b : ℕ) (hk : k < 2 ^ d) :
    ((splitAvailWords d bits)[k]'(by rw [splitAvailWords_length]; exact hk)).testBit b =
      (decide (b < 8192) && !bits.testBit (8192 * k + b)) := by
  induction d generalizing bits k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [splitAvailWords, forceNat_eq, List.getElem_cons_zero, Nat.mul_zero, Nat.zero_add,
      Nat.testBit_and, Nat.testBit_xor, fullWordMask_testBit]
    cases decide (b < 8192) <;> cases bits.testBit b <;> rfl
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; omega
    have hhalf : 8192 <<< d = 8192 * 2 ^ d := by rw [Nat.shiftLeft_eq]
    by_cases hlow : k < 2 ^ d
    · have hget : (splitAvailWords (d + 1) bits)[k]'(by rw [splitAvailWords_length]; exact hk) =
          (splitAvailWords d (bits &&& ((1 <<< (8192 <<< d)) - 1)))[k]'(by
            rw [splitAvailWords_length]; exact hlow) := by
        simp only [splitAvailWords, forceNat_eq]
        rw [List.getElem_append_left]
      rw [hget, ih _ k hlow]
      by_cases hb : b < 8192
      · have hidx : 8192 * k + b < 8192 <<< d := by rw [hhalf]; nlinarith
        rw [and_two_pow_sub_one_testBit]
        simp [hb, hidx]
      · simp [hb]
    · have hk' : k - 2 ^ d < 2 ^ d := by omega
      have hget : (splitAvailWords (d + 1) bits)[k]'(by rw [splitAvailWords_length]; exact hk) =
          (splitAvailWords d (bits >>> (8192 <<< d)))[k - 2 ^ d]'(by
            rw [splitAvailWords_length]; exact hk') := by
        simp only [splitAvailWords, forceNat_eq]
        rw [List.getElem_append_right (by rw [splitAvailWords_length]; omega)]
        congr 1
        rw [splitAvailWords_length]
      rw [hget, ih _ (k - 2 ^ d) hk']
      by_cases hb : b < 8192
      · rw [Nat.testBit_shiftRight]
        have hidx : (8192 <<< d) + (8192 * (k - 2 ^ d) + b) = 8192 * k + b := by
          rw [hhalf]
          have hle : 2 ^ d ≤ k := by omega
          calc
            8192 * 2 ^ d + (8192 * (k - 2 ^ d) + b)
                = 8192 * (2 ^ d + (k - 2 ^ d)) + b := by ring
            _ = 8192 * k + b := by rw [Nat.add_sub_of_le hle]
        rw [hidx]
      · simp [hb]

/-- Per-super-chunk sieve bound `min 32768 ⌊√(scLo + 6 * 524288 + 1)⌋`. -/
def superChunkPrimeBound (scLo : ℕ) : ℕ :=
  min 32768 (Nat.sqrt (scLo + 6 * 524288 + 1))

/-- Build the `64` `(availA, availB)` word pairs for super-chunk `c`. -/
def buildSuperChunkWords (corrLo c : ℕ) : List (ℕ × ℕ) :=
  let scLo := corrLo + 6 * 524288 * c
  let scB := superChunkPrimeBound scLo
  forceNat (fastBoundedSingleLaneMask scB scLo 524288) fun bitsA =>
  forceNat (fastBoundedSingleLaneMask scB (scLo + 2) 524288) fun bitsB =>
    (splitAvailWords 6 bitsA).zip (splitAvailWords 6 bitsB)

theorem buildSuperChunkWords_length (corrLo c : ℕ) :
    (buildSuperChunkWords corrLo c).length = 64 := by
  unfold buildSuperChunkWords
  rw [forceNat_eq, forceNat_eq, List.length_zip, splitAvailWords_length, splitAvailWords_length]
  rfl

/-- Populate active super-chunks (`activeMask.testBit c = true`) among `0 .. numSuperChunks - 1`
into a `Braun` bank; inactive super-chunks remain `(0, 0)` without sieving. -/
def buildInitialBankAux (corrLo activeMask : ℕ) : ℕ → ℕ → Braun (ℕ × ℕ) → Braun (ℕ × ℕ)
  | _, 0, bank => bank
  | c, rem + 1, bank =>
      if activeMask.testBit c then
        seqBraun (setStrictPairList (64 * c) (buildSuperChunkWords corrLo c) bank)
          (buildInitialBankAux corrLo activeMask (c + 1) rem)
      else
        buildInitialBankAux corrLo activeMask (c + 1) rem bank

def buildInitialBank (corrLo activeMask numSuperChunks : ℕ) : Braun (ℕ × ℕ) :=
  buildInitialBankAux corrLo activeMask 0 numSuperChunks .leaf

theorem buildInitialBankAux_get (corrLo activeMask c rem : ℕ) (bank : Braun (ℕ × ℕ)) (w : ℕ) :
    (buildInitialBankAux corrLo activeMask c rem bank).get (0, 0) w =
      if 64 * c ≤ w ∧ w < 64 * (c + rem) ∧ activeMask.testBit (w / 64) = true then
        (buildSuperChunkWords corrLo (w / 64)).getD (w % 64) (0, 0)
      else bank.get (0, 0) w := by
  induction rem generalizing c bank with
  | zero =>
    rw [buildInitialBankAux]
    have hf : ¬ (64 * c ≤ w ∧ w < 64 * (c + 0) ∧ activeMask.testBit (w / 64) = true) := by omega
    rw [if_neg hf]
  | succ rem ih =>
    rw [buildInitialBankAux]
    have hlen64 : (buildSuperChunkWords corrLo c).length = 64 := buildSuperChunkWords_length corrLo c
    by_cases hact : activeMask.testBit c = true
    · rw [if_pos hact, seqBraun_eq, setStrictPairList_eq, ih (c + 1), Braun.get_setList]
      by_cases hhi : 64 * (c + 1) ≤ w ∧ w < 64 * (c + 1 + rem) ∧ activeMask.testBit (w / 64) = true
      · have hall : 64 * c ≤ w ∧ w < 64 * (c + (rem + 1)) ∧ activeMask.testBit (w / 64) = true :=
          ⟨by omega, by omega, hhi.2.2⟩
        rw [if_pos hhi, if_pos hall]
      · rw [if_neg hhi]
        by_cases hcur : 64 * c ≤ w ∧ w < 64 * c + (buildSuperChunkWords corrLo c).length
        · have hdiv : w / 64 = c := by omega
          have hall : 64 * c ≤ w ∧ w < 64 * (c + (rem + 1)) ∧ activeMask.testBit (w / 64) = true := by
            rw [hdiv]; exact ⟨by omega, by omega, hact⟩
          rw [dif_pos hcur, if_pos hall]
          have hmod : w % 64 = w - 64 * c := by omega
          have hlt_sub : w - 64 * c < (buildSuperChunkWords corrLo c).length := by omega
          rw [hdiv, hmod, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hlt_sub, Option.getD_some]
        · have hall : ¬ (64 * c ≤ w ∧ w < 64 * (c + (rem + 1)) ∧ activeMask.testBit (w / 64) = true) := by
            intro ⟨h1, h2, h3⟩
            exact hhi ⟨by omega, by omega, h3⟩
          rw [dif_neg hcur, if_neg hall]
    · rw [if_neg hact, ih (c + 1)]
      by_cases hhi : 64 * (c + 1) ≤ w ∧ w < 64 * (c + 1 + rem) ∧ activeMask.testBit (w / 64) = true
      · have hall : 64 * c ≤ w ∧ w < 64 * (c + (rem + 1)) ∧ activeMask.testBit (w / 64) = true :=
          ⟨by omega, by omega, hhi.2.2⟩
        rw [if_pos hhi, if_pos hall]
      · have hall : ¬ (64 * c ≤ w ∧ w < 64 * (c + (rem + 1)) ∧ activeMask.testBit (w / 64) = true) := by
          intro ⟨h1, h2, h3⟩
          by_cases hw_hi : 64 * (c + 1) ≤ w
          · exact hhi ⟨hw_hi, by omega, h3⟩
          · have hdiv : w / 64 = c := by omega
            rw [hdiv] at h3
            exact hact h3
        rw [if_neg hhi, if_neg hall]

theorem buildInitialBank_get (corrLo activeMask numSuperChunks w : ℕ) :
    (buildInitialBank corrLo activeMask numSuperChunks).get (0, 0) w =
      if w < 64 * numSuperChunks ∧ activeMask.testBit (w / 64) = true then
        (buildSuperChunkWords corrLo (w / 64))[w % 64]'(by
          rw [buildSuperChunkWords_length]; exact Nat.mod_lt w (by decide))
      else (0, 0) := by
  unfold buildInitialBank
  rw [buildInitialBankAux_get, Braun.leaf_get]
  by_cases hw : w < 64 * numSuperChunks ∧ activeMask.testBit (w / 64) = true
  · have h : 64 * 0 ≤ w ∧ w < 64 * (0 + numSuperChunks) ∧ activeMask.testBit (w / 64) = true :=
      ⟨by omega, by omega, hw.2⟩
    rw [if_pos h, if_pos hw]
    have hlt : w % 64 < (buildSuperChunkWords corrLo (w / 64)).length := by
      rw [buildSuperChunkWords_length]; exact Nat.mod_lt w (by decide)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  · have h : ¬ (64 * 0 ≤ w ∧ w < 64 * (0 + numSuperChunks) ∧ activeMask.testBit (w / 64) = true) := by
      intro ⟨_, h2, h3⟩
      exact hw ⟨by omega, h3⟩
    rw [if_neg h, if_neg hw]

/-- Read one lane (`false` = Lane A `corrLo + 6*idx`, `true` = Lane B `corrLo + 2 + 6*idx`) at word `w`. -/
def getBankLane (bank : Braun (ℕ × ℕ)) (lane : Bool) (w : ℕ) : ℕ :=
  let p := bank.get (0, 0) w
  if lane then p.2 else p.1

/-- Write one lane at word `w`, preserving the opposite lane. -/
def setBankLane (bank : Braun (ℕ × ℕ)) (lane : Bool) (w val : ℕ) : Braun (ℕ × ℕ) :=
  let p := bank.get (0, 0) w
  let p' := if lane then (p.1, val) else (val, p.2)
  bank.set (0, 0) w p'

theorem getBankLane_setBankLane (bank : Braun (ℕ × ℕ)) (l₁ l₂ : Bool) (w₁ w₂ val : ℕ) :
    getBankLane (setBankLane bank l₁ w₁ val) l₂ w₂ =
      if l₂ = l₁ ∧ w₂ = w₁ then val else getBankLane bank l₂ w₂ := by
  unfold getBankLane setBankLane
  dsimp only
  rw [Braun.get_set]
  by_cases hw : w₂ = w₁
  · subst hw
    cases l₁ <;> cases l₂ <;> simp
  · simp [hw]

/-- Bit-level query in a `(laneA, laneB)` bank at global stride-six index `idx`. -/
def bankBit (bank : Braun (ℕ × ℕ)) (lane : Bool) (idx : ℕ) : Bool :=
  (getBankLane bank lane (idx / 8192)).testBit (idx % 8192)

/-- Integer value represented by `(lane, idx)`: `corrLo + (2 if lane else 0) + 6 * idx`. -/
def laneVal (corrLo : ℕ) (lane : Bool) (idx : ℕ) : ℕ :=
  corrLo + (if lane then 2 else 0) + 6 * idx

theorem laneVal_inj {corrLo : ℕ}
    {l₁ l₂ : Bool} {i₁ i₂ : ℕ} (heq : laneVal corrLo l₁ i₁ = laneVal corrLo l₂ i₂) :
    l₁ = l₂ ∧ i₁ = i₂ := by
  unfold laneVal at heq
  cases l₁ <;> cases l₂ <;> simp at heq ⊢ <;> omega

theorem laneVal_superChunk (corrLo : ℕ) (lane : Bool) (idx : ℕ) :
    (laneVal corrLo lane idx - corrLo) / 3145728 = idx / 524288 := by
  unfold laneVal
  cases lane <;> simp <;> omega

theorem buildInitialBank_bit_prime {corrLo activeMask numSuperChunks : ℕ}
    (hlo : 5 ≤ corrLo) (hmod : corrLo % 6 = 5)
    (hsieve : corrLo + 6 * 524288 * numSuperChunks + 2 ≤ 32769 * 32769)
    (lane : Bool) (idx : ℕ)
    (hbit : bankBit (buildInitialBank corrLo activeMask numSuperChunks) lane idx = true) :
    idx < 524288 * numSuperChunks ∧
      activeMask.testBit ((laneVal corrLo lane idx - corrLo) / 3145728) = true ∧
      Nat.Prime (laneVal corrLo lane idx) ∧
      5 ≤ laneVal corrLo lane idx ∧
      corrLo ≤ laneVal corrLo lane idx := by
  unfold bankBit getBankLane at hbit
  dsimp only at hbit
  rw [buildInitialBank_get] at hbit
  set w := idx / 8192
  set b := idx % 8192
  have hb : b < 8192 := Nat.mod_lt idx (by decide)
  by_cases hw : w < 64 * numSuperChunks ∧ activeMask.testBit (w / 64) = true
  · rw [if_pos hw] at hbit
    set c := w / 64
    set kw := w % 64
    have hkw : kw < 64 := Nat.mod_lt w (by decide)
    have hc : c < numSuperChunks := by omega
    have hidx_lt : idx < 524288 * numSuperChunks := by omega
    have hsc_lt : 8192 * kw + b < 524288 := by omega
    have hact_val : activeMask.testBit ((laneVal corrLo lane idx - corrLo) / 3145728) = true := by
      rw [laneVal_superChunk]
      have hdiv_eq : idx / 524288 = w / 64 := by omega
      rw [hdiv_eq]
      exact hw.2
    set scLo := corrLo + 6 * 524288 * c
    set scB := superChunkPrimeBound scLo
    have hscB32 : scB ≤ 32768 := Nat.min_le_left 32768 _
    have hscB_sq : (scLo + 2) + 6 * 524288 ≤ (scB + 1) * (scB + 1) := by
      dsimp [scB, superChunkPrimeBound]
      set s := Nat.sqrt (scLo + 6 * 524288 + 1)
      by_cases hmin : 32768 ≤ s
      · rw [Nat.min_eq_left hmin]
        have hc1 : c + 1 ≤ numSuperChunks := by omega
        have hmul : 6 * 524288 * (c + 1) ≤ 6 * 524288 * numSuperChunks :=
          Nat.mul_le_mul_left _ hc1
        dsimp [scLo]
        omega
      · rw [Nat.min_eq_right (le_of_not_ge hmin)]
        have hsq : scLo + 6 * 524288 + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
        omega
    have hbw_eq : buildSuperChunkWords corrLo c =
        List.zip (splitAvailWords 6 (fastBoundedSingleLaneMask scB scLo 524288))
          (splitAvailWords 6 (fastBoundedSingleLaneMask scB (scLo + 2) 524288)) := by
      unfold buildSuperChunkWords
      rw [forceNat_eq, forceNat_eq]
    cases lane with
    | false =>
      simp only [Bool.false_eq_true, if_false, hbw_eq] at hbit
      have hfst : ((List.zip (splitAvailWords 6 (fastBoundedSingleLaneMask scB scLo 524288))
          (splitAvailWords 6 (fastBoundedSingleLaneMask scB (scLo + 2) 524288)))[kw]'(by
            rw [List.length_zip, splitAvailWords_length, splitAvailWords_length]; exact hkw)).1 =
          (splitAvailWords 6 (fastBoundedSingleLaneMask scB scLo 524288))[kw]'(by
            rw [splitAvailWords_length]; exact hkw) := by
        simp only [List.getElem_zip]
      rw [hfst, splitAvailWords_testBit 6 _ kw b hkw] at hbit
      simp only [hb, decide_true, Bool.true_and, Bool.not_eq_true'] at hbit
      have hpr := (fastBoundedSingleLaneMask_clear_iff_prime scB scLo 524288 (8192 * kw + b)
        hscB32 (by omega) (by omega) (by omega) hsc_lt (by omega)).mp hbit
      have hval_eq : scLo + 6 * (8192 * kw + b) = laneVal corrLo false idx := by
        unfold laneVal
        dsimp [scLo]
        omega
      rw [hval_eq] at hpr
      exact ⟨hidx_lt, hact_val, hpr, by unfold laneVal; omega, by unfold laneVal; omega⟩
    | true =>
      simp only [if_true, hbw_eq] at hbit
      have hsnd : ((List.zip (splitAvailWords 6 (fastBoundedSingleLaneMask scB scLo 524288))
          (splitAvailWords 6 (fastBoundedSingleLaneMask scB (scLo + 2) 524288)))[kw]'(by
            rw [List.length_zip, splitAvailWords_length, splitAvailWords_length]; exact hkw)).2 =
          (splitAvailWords 6 (fastBoundedSingleLaneMask scB (scLo + 2) 524288))[kw]'(by
            rw [splitAvailWords_length]; exact hkw) := by
        simp only [List.getElem_zip]
      rw [hsnd, splitAvailWords_testBit 6 _ kw b hkw] at hbit
      simp only [hb, decide_true, Bool.true_and, Bool.not_eq_true'] at hbit
      have hpr := (fastBoundedSingleLaneMask_clear_iff_prime scB (scLo + 2) 524288 (8192 * kw + b)
        hscB32 (by omega) (by omega) (by omega) hsc_lt hscB_sq).mp hbit
      have hval_eq : (scLo + 2) + 6 * (8192 * kw + b) = laneVal corrLo true idx := by
        unfold laneVal
        dsimp [scLo]
        omega
      rw [hval_eq] at hpr
      exact ⟨hidx_lt, hact_val, hpr, by unfold laneVal; omega, by unfold laneVal; omega⟩
  · rw [if_neg hw] at hbit
    cases lane <;> simp at hbit

/-- Per-stage word-parallel specification. -/
structure PrefixStageSpec where
  startWord : ℕ
  endWord : ℕ
  endBitCutoff : ℕ
  subMod : ℕ
  deriving DecidableEq, Repr

/-- Source lane of stage `j`: Lane A (`false`) for even `j`, Lane B (`true`) for odd `j`. -/
def stageSrcLane (j : ℕ) : Bool := decide (j % 2 = 1)

/-- Destination lane of stage `j`: opposite lane `!stageSrcLane j`. -/
def stageDstLane (j : ℕ) : Bool := !(stageSrcLane j)

/-- Stride-six bit shift `S_j` corresponding to integer gap `2 ^ (j + 1)`. -/
def stageBitShift (j : ℕ) : ℕ :=
  if j % 2 = 0 then (2 ^ (j + 1) - 2) / 6
  else (2 ^ (j + 1) - 4) / 6 + 1

private theorem two_pow_mod_six_even (k : ℕ) : 2 ^ (2 * k + 1) % 6 = 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
    rw [h, Nat.mul_mod, ih]

private theorem two_pow_mod_six_odd (k : ℕ) : 2 ^ (2 * k + 2) % 6 = 4 := by
  have h : 2 ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) := by ring
  rw [h, Nat.mul_mod, two_pow_mod_six_even]

theorem stageBitShift_laneVal (corrLo j idx : ℕ) :
    laneVal corrLo (stageDstLane j) (idx + stageBitShift j) =
      laneVal corrLo (stageSrcLane j) idx + 2 ^ (j + 1) := by
  by_cases hj : j % 2 = 0
  · have hsrc : stageSrcLane j = false := by unfold stageSrcLane; simp [hj]
    have hdst : stageDstLane j = true := by unfold stageDstLane; simp [hsrc]
    have hsh : stageBitShift j = (2 ^ (j + 1) - 2) / 6 := by unfold stageBitShift; simp [hj]
    rw [hsrc, hdst, hsh]
    unfold laneVal
    simp only [if_true, Bool.false_eq_true, if_false]
    set P2 := 2 ^ (j + 1)
    have hmod6 : P2 % 6 = 2 := by
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      dsimp [P2]; rw [hk]; exact two_pow_mod_six_even k
    have hge : 2 ≤ P2 := by
      dsimp [P2]
      have : 2 ^ 1 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    omega
  · have hj1 : j % 2 = 1 := by omega
    have hsrc : stageSrcLane j = true := by unfold stageSrcLane; simp [hj1]
    have hdst : stageDstLane j = false := by unfold stageDstLane; simp [hsrc]
    have hsh : stageBitShift j = (2 ^ (j + 1) - 4) / 6 + 1 := by unfold stageBitShift; simp [hj]
    rw [hsrc, hdst, hsh]
    unfold laneVal
    simp only [if_true, Bool.false_eq_true, if_false]
    set P2 := 2 ^ (j + 1)
    have hmod6 : P2 % 6 = 4 := by
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
      dsimp [P2]; rw [hk]; exact two_pow_mod_six_odd k
    have hge : 4 ≤ P2 := by
      dsimp [P2]
      have : 2 ^ 2 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    omega

/-- Word-level thinning mask for `subMod ≥ 1`. -/
def stageSubMask (subMod j : ℕ) : ℕ :=
  if subMod ≤ 1 then fullWordMask
  else
    let rem := j % subMod
    fastProgressionMask subMod rem ((8191 - rem) / subMod + 1)

/-- Aligned `8,192`-bit destination availability mask for source word `w` at stage `j`. -/
def alignedDstWord (bank : Braun (ℕ × ℕ)) (j w : ℕ) : ℕ :=
  let s := stageBitShift j
  let q := s / 8192
  let r := s % 8192
  let dstL := stageDstLane j
  let dstLo := getBankLane bank dstL (w + q) &&& fullWordMask
  if r = 0 then dstLo
  else
    let dstHi := getBankLane bank dstL (w + q + 1) &&& ((1 <<< r) - 1)
    (dstLo >>> r) ||| (dstHi <<< (8192 - r))

theorem alignedDstWord_testBit (bank : Braun (ℕ × ℕ)) (j w b : ℕ) (hb : b < 8192) :
    (alignedDstWord bank j w).testBit b =
      bankBit bank (stageDstLane j) (8192 * w + b + stageBitShift j) := by
  unfold alignedDstWord bankBit
  dsimp only
  set s := stageBitShift j
  set q := s / 8192
  set r := s % 8192
  have hr_lt : r < 8192 := Nat.mod_lt s (by decide)
  have hs_eq : s = 8192 * q + r := by omega
  by_cases hr0 : r = 0
  · rw [if_pos hr0, Nat.testBit_and, fullWordMask_testBit]
    have hdiv : (8192 * w + b + s) / 8192 = w + q := by omega
    have hmod : (8192 * w + b + s) % 8192 = b := by omega
    rw [hdiv, hmod]
    simp [hb]
  · rw [if_neg hr0, Nat.testBit_lor, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    by_cases hlow : b < 8192 - r
    · have hge : ¬ (8192 - r ≤ b) := by omega
      have hbr : r + b < 8192 := by omega
      have hdiv : (8192 * w + b + s) / 8192 = w + q := by omega
      have hmod : (8192 * w + b + s) % 8192 = r + b := by omega
      rw [hdiv, hmod, Nat.testBit_and, fullWordMask_testBit]
      simp [hge, hbr]
    · have hge : 8192 - r ≤ b := by omega
      have hbr : ¬ (r + b < 8192) := by omega
      have hsub_lt : b - (8192 - r) < r := by omega
      have hdiv : (8192 * w + b + s) / 8192 = w + q + 1 := by omega
      have hmod : (8192 * w + b + s) % 8192 = b - (8192 - r) := by omega
      rw [hdiv, hmod, Nat.testBit_and, fullWordMask_testBit]
      simp [hge, hbr, two_pow_sub_one_testBit, hsub_lt]

/-- Selected `8,192`-bit pair mask in source word `w` (`startWord ≤ w ≤ endWord`). -/
def wordTakeMask (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) (w : ℕ) : ℕ :=
  let srcAvail := getBankLane bank (stageSrcLane j) w &&& fullWordMask
  let raw := (srcAvail &&& alignedDstWord bank j w) &&& stageSubMask sp.subMod j
  if w = sp.endWord then raw &&& ((1 <<< sp.endBitCutoff) - 1) else raw

theorem wordTakeMask_spec (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) (w b : ℕ)
    (htb : (wordTakeMask bank j sp w).testBit b = true) :
    b < 8192 ∧
      (w = sp.endWord → b < sp.endBitCutoff) ∧
      bankBit bank (stageSrcLane j) (8192 * w + b) = true ∧
      bankBit bank (stageDstLane j) (8192 * w + b + stageBitShift j) = true := by
  unfold wordTakeMask at htb
  dsimp only at htb
  by_cases hw : w = sp.endWord
  · subst hw
    rw [if_pos rfl] at htb
    simp only [Nat.testBit_and, two_pow_sub_one_testBit, fullWordMask_testBit,
      Bool.and_eq_true, decide_eq_true_eq] at htb
    rcases htb with ⟨⟨⟨⟨hsrc, hb⟩, hdst⟩, _⟩, hbc⟩
    rw [alignedDstWord_testBit bank j sp.endWord b hb] at hdst
    have hdiv : (8192 * sp.endWord + b) / 8192 = sp.endWord := by omega
    have hmod : (8192 * sp.endWord + b) % 8192 = b := by omega
    refine ⟨hb, fun _ => hbc, ?_, hdst⟩
    unfold bankBit
    rw [hdiv, hmod]
    exact hsrc
  · rw [if_neg hw] at htb
    simp only [Nat.testBit_and, fullWordMask_testBit,
      Bool.and_eq_true, decide_eq_true_eq] at htb
    rcases htb with ⟨⟨⟨hsrc, hb⟩, hdst⟩, _⟩
    rw [alignedDstWord_testBit bank j w b hb] at hdst
    have hdiv : (8192 * w + b) / 8192 = w := by omega
    have hmod : (8192 * w + b) % 8192 = b := by omega
    refine ⟨hb, fun h => False.elim (hw h), ?_, hdst⟩
    unfold bankBit
    rw [hdiv, hmod]
    exact hsrc

/-- In-place single-traversal lane bit clear on `Braun (ℕ × ℕ)` with `forceNat` and `seqBraun`
so updated words retain zero references to prior banks or masks. -/
def clearBankLane : Braun (ℕ × ℕ) → Bool → ℕ → ℕ → Braun (ℕ × ℕ)
  | .leaf, _, _, _ => .leaf
  | .node (a, b) l r, lane, 0, m =>
      if lane then forceNat (clearWordBits b m) fun bw => .node (a, bw) l r
      else forceNat (clearWordBits a m) fun aw => .node (aw, b) l r
  | .node p l r, lane, i + 1, m =>
      if i % 2 = 0 then seqBraun (clearBankLane l lane (i / 2) m) fun l' => .node p l' r
      else seqBraun (clearBankLane r lane (i / 2) m) fun r' => .node p l r'

private theorem clearWordBits_zero (m : ℕ) : clearWordBits 0 m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [clearWordBits_testBit]
  simp

theorem clearBankLane_eq_setBankLane (bank : Braun (ℕ × ℕ)) (l₁ l₂ : Bool) (w₁ w₂ m : ℕ) :
    getBankLane (clearBankLane bank l₁ w₁ m) l₂ w₂ =
      getBankLane (setBankLane bank l₁ w₁ (clearWordBits (getBankLane bank l₁ w₁) m)) l₂ w₂ := by
  induction bank generalizing w₁ w₂ with
  | leaf =>
    rw [getBankLane_setBankLane]
    unfold clearBankLane getBankLane
    simp [Braun.leaf_get, clearWordBits_zero]
  | node p l r ihL ihR =>
    rw [getBankLane_setBankLane]
    rcases p with ⟨a, b⟩
    cases w₁ with
    | zero =>
      cases w₂ with
      | zero =>
        cases l₁ <;> cases l₂ <;>
          simp [clearBankLane, forceNat_eq, getBankLane, Braun.get]
      | succ w₂ =>
        cases l₁ <;> simp [clearBankLane, forceNat_eq, getBankLane, Braun.get]
    | succ w₁ =>
      cases w₂ with
      | zero =>
        by_cases hp1 : w₁ % 2 = 0 <;> simp [clearBankLane, seqBraun_eq, getBankLane, Braun.get, hp1]
      | succ w₂ =>
        by_cases hp1 : w₁ % 2 = 0 <;> by_cases hp2 : w₂ % 2 = 0
        · have hlhs : getBankLane (clearBankLane (.node (a, b) l r) l₁ (w₁ + 1) m) l₂ (w₂ + 1) =
              getBankLane (clearBankLane l l₁ (w₁ / 2) m) l₂ (w₂ / 2) := by
            simp [clearBankLane, seqBraun_eq, getBankLane, Braun.get, hp1, hp2]
          have hr1 : getBankLane (.node (a, b) l r) l₁ (w₁ + 1) = getBankLane l l₁ (w₁ / 2) := by
            simp [getBankLane, Braun.get, hp1]
          have hr2 : getBankLane (.node (a, b) l r) l₂ (w₂ + 1) = getBankLane l l₂ (w₂ / 2) := by
            simp [getBankLane, Braun.get, hp2]
          rw [hlhs, hr1, hr2, ihL (w₁ / 2) (w₂ / 2), getBankLane_setBankLane]
          have heq : (w₂ / 2 = w₁ / 2) ↔ (w₂ + 1 = w₁ + 1) := by omega
          simp [heq]
        · have hne : w₂ ≠ w₁ := by omega
          simp [clearBankLane, seqBraun_eq, getBankLane, Braun.get, hp1, hp2, hne]
        · have hne : w₂ ≠ w₁ := by omega
          simp [clearBankLane, seqBraun_eq, getBankLane, Braun.get, hp1, hp2, hne]
        · have hlhs : getBankLane (clearBankLane (.node (a, b) l r) l₁ (w₁ + 1) m) l₂ (w₂ + 1) =
              getBankLane (clearBankLane r l₁ (w₁ / 2) m) l₂ (w₂ / 2) := by
            simp [clearBankLane, seqBraun_eq, getBankLane, Braun.get, hp1, hp2]
          have hr1 : getBankLane (.node (a, b) l r) l₁ (w₁ + 1) = getBankLane r l₁ (w₁ / 2) := by
            simp [getBankLane, Braun.get, hp1]
          have hr2 : getBankLane (.node (a, b) l r) l₂ (w₂ + 1) = getBankLane r l₂ (w₂ / 2) := by
            simp [getBankLane, Braun.get, hp2]
          rw [hlhs, hr1, hr2, ihR (w₁ / 2) (w₂ / 2), getBankLane_setBankLane]
          have heq : (w₂ / 2 = w₁ / 2) ↔ (w₂ + 1 = w₁ + 1) := by omega
          simp [heq]

/-- Clear source word `w`'s taken mask `m` from both `stageSrcLane j` and `stageDstLane j`. -/
def applyWordClear (bank : Braun (ℕ × ℕ)) (j w m : ℕ) : Braun (ℕ × ℕ) :=
  forceNat (m &&& fullWordMask) fun mClean =>
    let srcL := stageSrcLane j
    let dstL := stageDstLane j
    let s := stageBitShift j
    let q := s / 8192
    let r := s % 8192
    seqBraun (clearBankLane bank srcL w mClean) fun b1 =>
    forceNat ((mClean <<< r) &&& fullWordMask) fun mLo =>
    seqBraun (clearBankLane b1 dstL (w + q) mLo) fun b2 =>
    if r = 0 then b2
    else
      forceNat (mClean >>> (8192 - r)) fun mHi =>
        clearBankLane b2 dstL (w + q + 1) mHi

private theorem clearWordBits_mask_rhs (a m : ℕ) :
    clearWordBits a (m &&& fullWordMask) = clearWordBits a m := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [clearWordBits_testBit, clearWordBits_testBit, Nat.testBit_and, fullWordMask_testBit]
  cases a.testBit b <;> cases m.testBit b <;> cases decide (b < 8192) <;> rfl

theorem applyWordClear_bankBit (bank : Braun (ℕ × ℕ)) (j w m : ℕ) (lane : Bool) (idx : ℕ) :
    bankBit (applyWordClear bank j w m) lane idx =
      (bankBit bank lane idx &&
        decide (idx % 8192 < 8192) &&
        !(if lane = stageSrcLane j then
            decide (idx / 8192 = w) && (m &&& fullWordMask).testBit (idx % 8192)
          else
            decide (8192 * w + stageBitShift j ≤ idx ∧ idx < 8192 * (w + 1) + stageBitShift j) &&
              (m &&& fullWordMask).testBit (idx - (8192 * w + stageBitShift j)))) := by
  have hb_lt : idx % 8192 < 8192 := Nat.mod_lt idx (by decide)
  have hlanes_ne : stageDstLane j ≠ stageSrcLane j := by
    unfold stageDstLane
    cases stageSrcLane j <;> decide
  unfold bankBit applyWordClear
  simp only [forceNat_eq, seqBraun_eq]
  set mClean := m &&& fullWordMask
  set srcL := stageSrcLane j
  set dstL := stageDstLane j
  set s := stageBitShift j
  set q := s / 8192
  set r := s % 8192
  have hr_lt : r < 8192 := Nat.mod_lt s (by decide)
  have hs_eq : s = 8192 * q + r := by omega
  set wi := idx / 8192
  set bi := idx % 8192
  have hidx_eq : idx = 8192 * wi + bi := by omega
  by_cases hls : lane = srcL
  · subst hls
    have hne_ld : srcL ≠ dstL := hlanes_ne.symm
    by_cases hr0 : r = 0
    · rw [if_pos hr0, clearBankLane_eq_setBankLane, getBankLane_setBankLane,
        if_neg (by simp [hne_ld]), clearBankLane_eq_setBankLane, getBankLane_setBankLane]
      by_cases hwi : wi = w
      · subst hwi
        simp [clearWordBits_testBit, hb_lt]
      · simp [hwi, hb_lt]
    · rw [if_neg hr0, clearBankLane_eq_setBankLane, getBankLane_setBankLane,
        if_neg (by simp [hne_ld]), clearBankLane_eq_setBankLane, getBankLane_setBankLane,
        if_neg (by simp [hne_ld]), clearBankLane_eq_setBankLane, getBankLane_setBankLane]
      by_cases hwi : wi = w
      · subst hwi
        simp [clearWordBits_testBit, hb_lt]
      · simp [hwi, hb_lt]
  · have hld : lane = dstL := by
      dsimp [dstL, srcL, stageDstLane] at hls ⊢
      cases lane <;> cases h : stageSrcLane j <;> simp_all
    subst hld
    rw [if_neg hls]
    by_cases hr0 : r = 0
    · rw [if_pos hr0, clearBankLane_eq_setBankLane, getBankLane_setBankLane]
      by_cases hwi : wi = w + q
      · rw [if_pos ⟨rfl, hwi⟩, clearBankLane_eq_setBankLane, getBankLane_setBankLane,
          if_neg (by simp [hls]), clearWordBits_mask_rhs, clearWordBits_testBit, hr0, Nat.shiftLeft_zero]
        have hrange : 8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s := by omega
        have hsub : idx - (8192 * w + s) = bi := by omega
        rw [ ← hwi ]
        simp [hb_lt, hrange, hsub]
      · rw [if_neg (by simp [hwi]), clearBankLane_eq_setBankLane, getBankLane_setBankLane,
          if_neg (by simp [hls])]
        have hrange : ¬ (8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s) := by omega
        simp [hrange, hb_lt]
    · rw [if_neg hr0, clearBankLane_eq_setBankLane, getBankLane_setBankLane]
      by_cases hwi1 : wi = w + q + 1
      · have hwi0 : w + q + 1 ≠ w + q := by omega
        rw [if_pos ⟨rfl, hwi1⟩, clearBankLane_eq_setBankLane, getBankLane_setBankLane,
          if_neg (fun h => hwi0 h.2), clearBankLane_eq_setBankLane, getBankLane_setBankLane,
          if_neg (by simp [hls]), clearWordBits_testBit, Nat.testBit_shiftRight, ← hwi1]
        by_cases hbi : bi < r
        · have hrange : 8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s := by omega
          have hsub : 8192 - r + bi = idx - (8192 * w + s) := by omega
          simp [hb_lt, hrange, hsub]
        · have hrange : ¬ (8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s) := by omega
          have hout : ¬ (8192 - r + bi < 8192) := by omega
          have hm0 : mClean.testBit (8192 - r + bi) = false := by
            dsimp [mClean]
            rw [Nat.testBit_and, fullWordMask_testBit]
            simp [hout]
          simp [hb_lt, hrange, hm0]
      · rw [if_neg (by simp [hwi1]), clearBankLane_eq_setBankLane, getBankLane_setBankLane]
        by_cases hwi0 : wi = w + q
        · rw [if_pos ⟨rfl, hwi0⟩, clearBankLane_eq_setBankLane, getBankLane_setBankLane,
            if_neg (by simp [hls]), clearWordBits_mask_rhs, clearWordBits_testBit, Nat.testBit_shiftLeft, ← hwi0]
          by_cases hbi : r ≤ bi
          · have hrange : 8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s := by omega
            have hsub : bi - r = idx - (8192 * w + s) := by omega
            simp [hb_lt, hbi, hrange, hsub]
          · have hrange : ¬ (8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s) := by omega
            simp [hb_lt, hbi, hrange]
        · rw [if_neg (by simp [hwi0]), clearBankLane_eq_setBankLane, getBankLane_setBankLane,
            if_neg (by simp [hls])]
          have hrange : ¬ (8192 * w + s ≤ idx ∧ idx < 8192 * (w + 1) + s) := by omega
          simp [hrange, hb_lt]

theorem applyWordClear_mono (bank : Braun (ℕ × ℕ)) (j w m : ℕ) (lane : Bool) (idx : ℕ) :
    bankBit (applyWordClear bank j w m) lane idx = true → bankBit bank lane idx = true := by
  rw [applyWordClear_bankBit]
  simp only [Bool.and_eq_true]
  exact fun h => h.1.1

theorem applyWordClear_clears_src (bank : Braun (ℕ × ℕ)) (j w m b : ℕ)
    (hb : b < 8192) (hm : m.testBit b = true) :
    bankBit (applyWordClear bank j w m) (stageSrcLane j) (8192 * w + b) = false := by
  rw [applyWordClear_bankBit]
  have hdiv : (8192 * w + b) / 8192 = w := by omega
  have hmod : (8192 * w + b) % 8192 = b := by omega
  have hmc : (m &&& fullWordMask).testBit b = true := by
    rw [Nat.testBit_and, fullWordMask_testBit]
    simp [hb, hm]
  simp [hdiv, hmod, hmc]

theorem applyWordClear_clears_dst (bank : Braun (ℕ × ℕ)) (j w m b : ℕ)
    (hb : b < 8192) (hm : m.testBit b = true) :
    bankBit (applyWordClear bank j w m) (stageDstLane j) (8192 * w + b + stageBitShift j) = false := by
  have hlanes_ne : stageDstLane j ≠ stageSrcLane j := by
    unfold stageDstLane
    cases stageSrcLane j <;> decide
  rw [applyWordClear_bankBit]
  have hrange : 8192 * w + stageBitShift j ≤ 8192 * w + b + stageBitShift j ∧
      8192 * w + b + stageBitShift j < 8192 * (w + 1) + stageBitShift j := by omega
  have hsub : 8192 * w + b + stageBitShift j - (8192 * w + stageBitShift j) = b := by omega
  have hmc : (m &&& fullWordMask).testBit b = true := by
    rw [Nat.testBit_and, fullWordMask_testBit]
    simp [hb, hm]
  simp [hlanes_ne, hrange, hsub, hmc]

/-- Apply a list of `(w, mask)` word clears sequentially with spine forcing. -/
def applyWordClearList (j : ℕ) : List (ℕ × ℕ) → Braun (ℕ × ℕ) → Braun (ℕ × ℕ)
  | [], bank => bank
  | wm :: rest, bank =>
      seqPair wm fun wm' =>
        seqBraun (applyWordClear bank j wm'.1 wm'.2) (applyWordClearList j rest)

theorem applyWordClearList_mono (j : ℕ) (wms : List (ℕ × ℕ)) (bank : Braun (ℕ × ℕ))
    (lane : Bool) (idx : ℕ) :
    bankBit (applyWordClearList j wms bank) lane idx = true → bankBit bank lane idx = true := by
  induction wms generalizing bank with
  | nil => exact id
  | cons wm rest ih =>
    simp only [applyWordClearList, seqPair_eq, seqBraun_eq]
    intro h
    exact applyWordClear_mono bank j wm.1 wm.2 lane idx (ih _ h)

theorem applyWordClearList_false_preserved (j : ℕ) (wms : List (ℕ × ℕ)) (bank : Braun (ℕ × ℕ))
    (lane : Bool) (idx : ℕ) (hf : bankBit bank lane idx = false) :
    bankBit (applyWordClearList j wms bank) lane idx = false := by
  cases h : bankBit (applyWordClearList j wms bank) lane idx
  · rfl
  · have ht := applyWordClearList_mono j wms bank lane idx h
    rw [hf] at ht
    cases ht

theorem applyWordClearList_clears_mem (j : ℕ) (wms : List (ℕ × ℕ)) (bank : Braun (ℕ × ℕ))
    (w m b : ℕ) (hmem : (w, m) ∈ wms) (hb : b < 8192) (hm : m.testBit b = true) :
    bankBit (applyWordClearList j wms bank) (stageSrcLane j) (8192 * w + b) = false ∧
      bankBit (applyWordClearList j wms bank) (stageDstLane j)
        (8192 * w + b + stageBitShift j) = false := by
  induction wms generalizing bank with
  | nil => cases hmem
  | cons wm rest ih =>
    simp only [applyWordClearList, seqPair_eq, seqBraun_eq]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact ⟨applyWordClearList_false_preserved j rest _ _ _
        (applyWordClear_clears_src bank j w m b hb hm),
      applyWordClearList_false_preserved j rest _ _ _
        (applyWordClear_clears_dst bank j w m b hb hm)⟩
    · exact ih (applyWordClear bank j wm.1 wm.2) hrest

/-- Strictly evaluate `(w, takeMask)` pairs over a range so `wms` holds zero references to `bank`. -/
def strictWordMasksAux (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) :
    ℕ → ℕ → List (ℕ × ℕ)
  | _, 0 => []
  | w, rem + 1 =>
      forceNat w fun w' =>
      forceNat (wordTakeMask bank j sp w') fun mw =>
        seqList (strictWordMasksAux bank j sp (w' + 1) rem) fun rest => (w', mw) :: rest

private theorem strictWordMasksAux_eq_map (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec)
    (w rem : ℕ) :
    strictWordMasksAux bank j sp w rem =
      (List.range rem).map (fun off => (w + off, wordTakeMask bank j sp (w + off))) := by
  induction rem generalizing w with
  | zero => simp [strictWordMasksAux]
  | succ rem ih =>
    simp only [strictWordMasksAux, forceNat_eq, seqList_eq, ih, List.range_succ_eq_map,
      List.map_cons, Nat.add_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro off _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 off]

/-- Compute the `(w, takeMask)` pairs for `w = sp.startWord .. sp.endWord` from `bank`. -/
def stageWordMasks (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) : List (ℕ × ℕ) :=
  strictWordMasksAux bank j sp sp.startWord (sp.endWord - sp.startWord + 1)

private theorem swarPop8192_eq_fastSetCount10_all (x : ℕ) :
    swarPop8192 swarMask0 swarMask1 swarMask2 swarMask3 x = fastSetCount 10 x := by
  have h1 := fastSetCount_spec 10 (x &&& ((1 <<< 8192) - 1))
  have h2 := fastSetCount_spec 10 x
  have h8 : (8 <<< 10) = 8192 := by decide
  rw [h8] at h1 h2
  rw [swarPop8192_eq_fastSetCount10, h1, h2]
  apply Finset.sum_congr rfl
  intro b hb
  rw [and_two_pow_sub_one_testBit]
  simp [Finset.mem_range.mp hb]

/-- Strict sum of `swarPop8192 m0 m1 m2 m3` over `(w, mask)` pairs. -/
def sumMaskSetCounts (m0 m1 m2 m3 acc : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => acc
  | wm :: rest =>
      forceNat (acc + swarPop8192 m0 m1 m2 m3 wm.2)
        (fun acc' => sumMaskSetCounts m0 m1 m2 m3 acc' rest)

private theorem sumMaskSetCounts_eq (acc : ℕ) (wms : List (ℕ × ℕ)) :
    sumMaskSetCounts swarMask0 swarMask1 swarMask2 swarMask3 acc wms =
      acc + (wms.map (fun wm => fastSetCount 10 wm.2)).sum := by
  induction wms generalizing acc with
  | nil => simp [sumMaskSetCounts]
  | cons wm rest ih =>
    simp only [sumMaskSetCounts, forceNat_eq, swarPop8192_eq_fastSetCount10_all, ih,
      List.map_cons, List.sum_cons]
    omega

/-- Execute stage `j` with pair count `quota`, checking `startWord ≤ endWord`,
`endBitCutoff ≤ 8192`, `1 ≤ subMod`, and exact pair count `quota`. -/
def runStage (m0 m1 m2 m3 quota : ℕ) (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) :
    Option (Braun (ℕ × ℕ)) :=
  if sp.startWord ≤ sp.endWord ∧ sp.endBitCutoff ≤ 8192 ∧ 1 ≤ sp.subMod then
    seqList (stageWordMasks bank j sp) fun wms =>
      if sumMaskSetCounts m0 m1 m2 m3 0 wms = quota then
        seqBraun (applyWordClearList j wms bank) some
      else none
  else none

/-- Mathematical `Finset` of stride-six source bit indices selected by stage `j` on `bank`. -/
noncomputable def stageSelectedBits (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) : Finset ℕ :=
  ((Finset.Icc sp.startWord sp.endWord ×ˢ Finset.range 8192).filter
    (fun wb => (wordTakeMask bank j sp wb.1).testBit wb.2 = true)).image
      (fun wb => 8192 * wb.1 + wb.2)

private theorem word_bit_encode_injOn (s : Set (ℕ × ℕ))
    (hs : ∀ x ∈ s, x.2 < 8192) :
    Set.InjOn (fun wb : ℕ × ℕ => 8192 * wb.1 + wb.2) s := by
  intro ⟨w₁, b₁⟩ h₁ ⟨w₂, b₂⟩ h₂ heq
  have hb₁ : b₁ < 8192 := hs ⟨w₁, b₁⟩ h₁
  have hb₂ : b₂ < 8192 := hs ⟨w₂, b₂⟩ h₂
  dsimp at heq
  ext <;> omega

private theorem fastSetCount10_eq_filter_card (m : ℕ) :
    fastSetCount 10 m = ((Finset.range 8192).filter (fun b => m.testBit b = true)).card := by
  have h := fastSetCount_spec 10 m
  have h8 : (8 <<< 10) = 8192 := by decide
  rw [h8] at h
  rw [h, Finset.card_filter]

private theorem list_range_map_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem stageWordMasks_eq_old (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec) :
    stageWordMasks bank j sp =
      (List.range (sp.endWord - sp.startWord + 1)).map fun off =>
        (sp.startWord + off, wordTakeMask bank j sp (sp.startWord + off)) :=
  strictWordMasksAux_eq_map bank j sp sp.startWord (sp.endWord - sp.startWord + 1)

private theorem stageWordMasks_sum_eq_card (bank : Braun (ℕ × ℕ)) (j : ℕ) (sp : PrefixStageSpec)
    (hle : sp.startWord ≤ sp.endWord) :
    ((stageWordMasks bank j sp).map (fun wm => fastSetCount 10 wm.2)).sum =
      (stageSelectedBits bank j sp).card := by
  unfold stageSelectedBits
  have hinj : Set.InjOn (fun wb : ℕ × ℕ => 8192 * wb.1 + wb.2)
      ((Finset.Icc sp.startWord sp.endWord ×ˢ Finset.range 8192).filter
        (fun wb => (wordTakeMask bank j sp wb.1).testBit wb.2 = true) : Set (ℕ × ℕ)) := by
    apply word_bit_encode_injOn
    intro wb hwb
    have hmem := (Finset.mem_filter.mp hwb).1
    exact Finset.mem_range.mp (Finset.mem_product.mp hmem).2
  rw [Finset.card_image_of_injOn hinj]
  have hprod : ((Finset.Icc sp.startWord sp.endWord ×ˢ Finset.range 8192).filter
      (fun wb => (wordTakeMask bank j sp wb.1).testBit wb.2 = true)).card =
      ∑ w ∈ Finset.Icc sp.startWord sp.endWord,
        ((Finset.range 8192).filter (fun b => (wordTakeMask bank j sp w).testBit b = true)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  rw [hprod]
  simp_rw [← fastSetCount10_eq_filter_card]
  rw [stageWordMasks_eq_old, List.map_map, list_range_map_sum]
  apply Finset.sum_bij (fun off _ => sp.startWord + off)
  · intro off hoff
    have hoff' := Finset.mem_range.mp hoff
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro o₁ _ o₂ _ heq; omega
  · intro w hw
    have hw' := Finset.mem_Icc.mp hw
    exact ⟨w - sp.startWord, Finset.mem_range.mpr (by omega), by omega⟩
  · intro off _; rfl

theorem runStage_spec {quota : ℕ} {bank bank' : Braun (ℕ × ℕ)} {j : ℕ} {sp : PrefixStageSpec}
    (hrun : runStage swarMask0 swarMask1 swarMask2 swarMask3 quota bank j sp = some bank') :
    sp.startWord ≤ sp.endWord ∧
      sp.endBitCutoff ≤ 8192 ∧
      (stageSelectedBits bank j sp).card = quota ∧
      (∀ lane idx, bankBit bank' lane idx = true → bankBit bank lane idx = true) ∧
      (∀ bit ∈ stageSelectedBits bank j sp,
        8192 * sp.startWord ≤ bit ∧
        bit < 8192 * (sp.endWord + 1) ∧
        bankBit bank (stageSrcLane j) bit = true ∧
        bankBit bank (stageDstLane j) (bit + stageBitShift j) = true ∧
        bankBit bank' (stageSrcLane j) bit = false ∧
        bankBit bank' (stageDstLane j) (bit + stageBitShift j) = false) := by
  unfold runStage at hrun
  simp only [seqList_eq, seqBraun_eq, sumMaskSetCounts_eq, Nat.zero_add] at hrun
  by_cases hcond : sp.startWord ≤ sp.endWord ∧ sp.endBitCutoff ≤ 8192 ∧ 1 ≤ sp.subMod
  · rw [if_pos hcond] at hrun
    by_cases hcnt : ((stageWordMasks bank j sp).map (fun wm => fastSetCount 10 wm.2)).sum = quota
    · rw [if_pos hcnt] at hrun
      injection hrun with hbank'
      subst hbank'
      rcases hcond with ⟨hle, hcut, _⟩
      rw [stageWordMasks_sum_eq_card bank j sp hle] at hcnt
      refine ⟨hle, hcut, hcnt, ?_, ?_⟩
      · intro lane idx h
        exact applyWordClearList_mono j (stageWordMasks bank j sp) bank lane idx h
      · intro bit hbit
        obtain ⟨⟨w, b⟩, hwb, rfl⟩ := Finset.mem_image.mp hbit
        obtain ⟨hprod, htb⟩ := Finset.mem_filter.mp hwb
        have hw := Finset.mem_Icc.mp (Finset.mem_product.mp hprod).1
        have hb := Finset.mem_range.mp (Finset.mem_product.mp hprod).2
        have hts := wordTakeMask_spec bank j sp w b htb
        have hmem : (w, wordTakeMask bank j sp w) ∈ stageWordMasks bank j sp := by
          rw [stageWordMasks_eq_old]
          apply List.mem_map.mpr
          refine ⟨w - sp.startWord, List.mem_range.mpr (by omega), ?_⟩
          have heq : sp.startWord + (w - sp.startWord) = w := by omega
          simp [heq]
        have hclr := applyWordClearList_clears_mem j (stageWordMasks bank j sp) bank
          w (wordTakeMask bank j sp w) b hmem hb htb
        exact ⟨by omega, by omega, hts.2.2.1, hts.2.2.2, hclr.1, hclr.2⟩
    · rw [if_neg hcnt] at hrun
      cases hrun
  · rw [if_neg hcond] at hrun
    cases hrun

/-- Execute a list of `(stageIndex, quota, stageSpec)` triples sequentially. -/
def runStagesList (m0 m1 m2 m3 : ℕ) :
    Braun (ℕ × ℕ) → List (ℕ × ℕ × PrefixStageSpec) → Option (Braun (ℕ × ℕ))
  | bank, [] => some bank
  | bank, (j, quota, sp) :: rest =>
      match runStage m0 m1 m2 m3 quota bank j sp with
      | none => none
      | some bank' => runStagesList m0 m1 m2 m3 bank' rest

theorem runStagesList_mono {bank finalBank : Braun (ℕ × ℕ)}
    {stages : List (ℕ × ℕ × PrefixStageSpec)}
    (hrun : runStagesList swarMask0 swarMask1 swarMask2 swarMask3 bank stages = some finalBank)
    (lane : Bool) (idx : ℕ) :
    bankBit finalBank lane idx = true → bankBit bank lane idx = true := by
  induction stages generalizing bank with
  | nil =>
    injection hrun with h
    subst h
    exact id
  | cons js rest ih =>
    rcases js with ⟨j, quota, sp⟩
    unfold runStagesList at hrun
    cases hs : runStage swarMask0 swarMask1 swarMask2 swarMask3 quota bank j sp with
    | none => simp [hs] at hrun
    | some bank' =>
      simp only [hs] at hrun
      have hspec := runStage_spec hs
      intro hf
      exact hspec.2.2.2.1 lane idx (ih hrun hf)

/-- Per-stage selected source-bit sets extracted along `runStagesList`. -/
noncomputable def stagesSelectedSets :
    Braun (ℕ × ℕ) → List (ℕ × ℕ × PrefixStageSpec) → List (ℕ × Finset ℕ)
  | _, [] => []
  | bank, (j, quota, sp) :: rest =>
      match runStage swarMask0 swarMask1 swarMask2 swarMask3 quota bank j sp with
      | none => []
      | some bank' => (j, stageSelectedBits bank j sp) :: stagesSelectedSets bank' rest

theorem stagesSelectedSets_length {bank finalBank : Braun (ℕ × ℕ)}
    {stages : List (ℕ × ℕ × PrefixStageSpec)}
    (hrun : runStagesList swarMask0 swarMask1 swarMask2 swarMask3 bank stages = some finalBank) :
    (stagesSelectedSets bank stages).length = stages.length := by
  induction stages generalizing bank with
  | nil => rfl
  | cons js rest ih =>
    rcases js with ⟨j, quota, sp⟩
    unfold runStagesList at hrun
    unfold stagesSelectedSets
    cases hs : runStage swarMask0 swarMask1 swarMask2 swarMask3 quota bank j sp with
    | none => simp [hs] at hrun
    | some b' =>
      simp only [hs] at hrun
      simp [ih hrun]

theorem runStagesList_sound {bank finalBank : Braun (ℕ × ℕ)}
    {stages : List (ℕ × ℕ × PrefixStageSpec)}
    (hrun : runStagesList swarMask0 swarMask1 swarMask2 swarMask3 bank stages = some finalBank) :
    let sel := stagesSelectedSets bank stages
    sel.map Prod.fst = stages.map Prod.fst ∧
      sel.length = stages.length ∧
      (∀ k (hk : k < stages.length),
        let j := (stages[k]'hk).1
        let quota := (stages[k]'hk).2.1
        let sp := (stages[k]'hk).2.2
        let S := (sel[k]'((stagesSelectedSets_length hrun).symm ▸ hk)).2
        sp.startWord ≤ sp.endWord ∧
        S.card = quota ∧
        (∀ bit ∈ S,
          8192 * sp.startWord ≤ bit ∧
          bit < 8192 * (sp.endWord + 1) ∧
          bankBit bank (stageSrcLane j) bit = true ∧
          bankBit bank (stageDstLane j) (bit + stageBitShift j) = true ∧
          bankBit finalBank (stageSrcLane j) bit = false ∧
          bankBit finalBank (stageDstLane j) (bit + stageBitShift j) = false)) ∧
      (∀ k₁ k₂ (hk₁ : k₁ < sel.length) (hk₂ : k₂ < sel.length), k₁ < k₂ →
        let j₁ := (sel[k₁]'hk₁).1
        let S₁ := (sel[k₁]'hk₁).2
        let j₂ := (sel[k₂]'hk₂).1
        let S₂ := (sel[k₂]'hk₂).2
        ∀ b₁ ∈ S₁, ∀ b₂ ∈ S₂, ∀ s₁ s₂ : Bool,
          (if s₁ then stageDstLane j₁ else stageSrcLane j₁,
            if s₁ then b₁ + stageBitShift j₁ else b₁) ≠
          (if s₂ then stageDstLane j₂ else stageSrcLane j₂,
            if s₂ then b₂ + stageBitShift j₂ else b₂)) := by
  induction stages generalizing bank with
  | nil =>
    simp [stagesSelectedSets]
  | cons js rest ih =>
    rcases js with ⟨j, quota, sp⟩
    unfold runStagesList at hrun
    cases hs : runStage swarMask0 swarMask1 swarMask2 swarMask3 quota bank j sp with
    | none => simp [hs] at hrun
    | some bank' =>
      simp only [hs] at hrun
      obtain ⟨hle, _, hcard, hmono1, hbits1⟩ := runStage_spec hs
      obtain ⟨hmap_rest, hlen_rest, hstage_rest, hdisj_rest⟩ := ih hrun
      have hsel_eq : stagesSelectedSets bank ((j, quota, sp) :: rest) =
          (j, stageSelectedBits bank j sp) :: stagesSelectedSets bank' rest := by
        simp [stagesSelectedSets, hs]
      have hfalse_final : ∀ lane idx, bankBit bank' lane idx = false →
          bankBit finalBank lane idx = false := by
        intro lane idx hf
        cases hfin : bankBit finalBank lane idx
        · rfl
        · have ht := runStagesList_mono hrun lane idx hfin
          rw [hf] at ht
          cases ht
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [hsel_eq, hmap_rest]
      · simp [hsel_eq, hlen_rest]
      · intro k hk
        cases k with
        | zero =>
          simp only [List.getElem_cons_zero, hsel_eq]
          refine ⟨hle, hcard, ?_⟩
          intro bit hbit
          obtain ⟨hlo, hhi, hbt1, hbt2, hbf1, hbf2⟩ := hbits1 bit hbit
          exact ⟨hlo, hhi, hbt1, hbt2, hfalse_final _ _ hbf1, hfalse_final _ _ hbf2⟩
        | succ k =>
          have hk' : k < rest.length := by simp at hk; exact hk
          simp only [List.getElem_cons_succ, hsel_eq]
          obtain ⟨hle', hcard', hbits'⟩ := hstage_rest k hk'
          refine ⟨hle', hcard', ?_⟩
          intro bit hbit
          obtain ⟨hlo, hhi, hbt1, hbt2, hbf1, hbf2⟩ := hbits' bit hbit
          exact ⟨hlo, hhi, hmono1 _ _ hbt1, hmono1 _ _ hbt2, hbf1, hbf2⟩
      · intro k₁ k₂ hk₁ hk₂ hlt
        simp only [hsel_eq] at hk₁ hk₂ ⊢
        cases k₂ with
        | zero => omega
        | succ k₂ =>
          cases k₁ with
          | zero =>
            simp only [List.getElem_cons_zero, List.getElem_cons_succ]
            have hk₂_rest : k₂ < rest.length := by simp [hlen_rest] at hk₂; exact hk₂
            have hmap_k₂ : ((stagesSelectedSets bank' rest)[k₂]'
                (by rw [hlen_rest]; exact hk₂_rest)).1 = (rest[k₂]'hk₂_rest).1 := by
              have := congrArg (fun l => l[k₂]?) hmap_rest
              simp [hk₂_rest, hlen_rest] at this
              exact this
            obtain ⟨_, _, hbits2⟩ := hstage_rest k₂ hk₂_rest
            intro b₁ hb₁ b₂ hb₂ s₁ s₂ heq
            obtain ⟨_, _, _, _, hclr_src, hclr_dst⟩ := hbits1 b₁ hb₁
            obtain ⟨_, _, htrue_src, htrue_dst, _, _⟩ := hbits2 b₂ hb₂
            rw [← hmap_k₂] at htrue_src htrue_dst
            have h1_false : bankBit bank'
                (if s₁ then stageDstLane j else stageSrcLane j)
                (if s₁ then b₁ + stageBitShift j else b₁) = false := by
              cases s₁ <;> simp [hclr_src, hclr_dst]
            have h2_true : bankBit bank'
                (if s₂ then stageDstLane ((stagesSelectedSets bank' rest)[k₂]).1
                  else stageSrcLane ((stagesSelectedSets bank' rest)[k₂]).1)
                (if s₂ then b₂ + stageBitShift ((stagesSelectedSets bank' rest)[k₂]).1
                  else b₂) = true := by
              cases s₂ <;> simp [htrue_src, htrue_dst]
            have hpair1 := congrArg Prod.fst heq
            have hpair2 := congrArg Prod.snd heq
            dsimp at hpair1 hpair2
            rw [hpair1, hpair2, h2_true] at h1_false
            cases h1_false
          | succ k₁ =>
            simp only [List.getElem_cons_succ]
            exact hdisj_rest k₁ k₂ (by simp at hk₁; exact hk₁)
              (by simp at hk₂; exact hk₂) (by omega)

/-- Count consumed primes per `8,192`-bit word (`49,152` integers) between `initBank` and `finalBank`. -/
def usedInWord (initBank finalBank : Braun (ℕ × ℕ)) (w : ℕ) : ℕ :=
  let diffA := (getBankLane initBank false w &&& fullWordMask) &&&
    (fullWordMask ^^^ (getBankLane finalBank false w &&& fullWordMask))
  let diffB := (getBankLane initBank true w &&& fullWordMask) &&&
    (fullWordMask ^^^ (getBankLane finalBank true w &&& fullWordMask))
  fastSetCount 10 diffA + fastSetCount 10 diffB

/-- SWAR-accelerated word usage counter. -/
def usedInWordSwar (m0 m1 m2 m3 : ℕ) (initBank finalBank : Braun (ℕ × ℕ)) (w : ℕ) : ℕ :=
  let diffA := (getBankLane initBank false w &&& fullWordMask) &&&
    (fullWordMask ^^^ (getBankLane finalBank false w &&& fullWordMask))
  let diffB := (getBankLane initBank true w &&& fullWordMask) &&&
    (fullWordMask ^^^ (getBankLane finalBank true w &&& fullWordMask))
  swarPop8192 m0 m1 m2 m3 diffA + swarPop8192 m0 m1 m2 m3 diffB

private theorem usedInWordSwar_eq (initBank finalBank : Braun (ℕ × ℕ)) (w : ℕ) :
    usedInWordSwar swarMask0 swarMask1 swarMask2 swarMask3 initBank finalBank w =
      usedInWord initBank finalBank w := by
  unfold usedInWordSwar usedInWord
  simp only [swarPop8192_eq_fastSetCount10_all]

def usedPerWordList (initBank finalBank : Braun (ℕ × ℕ)) (totalWords : ℕ) : List ℕ :=
  (List.range totalWords).map (usedInWord initBank finalBank)

/-- Strictly evaluate per-word consumed prime counts, skipping inactive super-chunks in `O(1)`. -/
def strictUsedWordsAux (m0 m1 m2 m3 activeMask : ℕ) (initBank finalBank : Braun (ℕ × ℕ)) :
    ℕ → ℕ → List ℕ
  | _, 0 => []
  | w, rem + 1 =>
      let cnt := if activeMask.testBit (w / 64) then
        usedInWordSwar m0 m1 m2 m3 initBank finalBank w
      else 0
      forceNat cnt fun cnt' =>
        seqList (strictUsedWordsAux m0 m1 m2 m3 activeMask initBank finalBank (w + 1) rem)
          (fun rest => cnt' :: rest)

private theorem usedInWord_inactive {corrLo activeMask numSuperChunks : ℕ}
    (finalBank : Braun (ℕ × ℕ)) (w : ℕ)
    (hinact : activeMask.testBit (w / 64) = false) :
    usedInWord (buildInitialBank corrLo activeMask numSuperChunks) finalBank w = 0 := by
  have hget : (buildInitialBank corrLo activeMask numSuperChunks).get (0, 0) w = (0, 0) := by
    rw [buildInitialBank_get]
    simp [hinact]
  unfold usedInWord getBankLane
  dsimp only
  rw [hget]
  simp only [if_true, Bool.false_eq_true, if_false, Nat.zero_and]
  decide +kernel

private theorem strictUsedWordsAux_eq {corrLo activeMask numSuperChunks : ℕ}
    (finalBank : Braun (ℕ × ℕ)) (w rem : ℕ) :
    strictUsedWordsAux swarMask0 swarMask1 swarMask2 swarMask3 activeMask
      (buildInitialBank corrLo activeMask numSuperChunks) finalBank w rem =
      (List.range rem).map (fun off =>
        usedInWord (buildInitialBank corrLo activeMask numSuperChunks) finalBank (w + off)) := by
  induction rem generalizing w with
  | zero => simp [strictUsedWordsAux]
  | succ rem ih =>
    rw [strictUsedWordsAux, forceNat_eq, seqList_eq, ih (w + 1)]
    have hhead : (if activeMask.testBit (w / 64) then
        usedInWordSwar swarMask0 swarMask1 swarMask2 swarMask3
          (buildInitialBank corrLo activeMask numSuperChunks) finalBank w
      else 0) =
        usedInWord (buildInitialBank corrLo activeMask numSuperChunks) finalBank w := by
      cases hact : activeMask.testBit (w / 64)
      · simp [usedInWord_inactive finalBank w hact]
      · simp [usedInWordSwar_eq]
    rw [hhead, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro off _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 off]

/-- Tail-recursive `O(N)` prefix-sum window-difference checker. -/
def checkAllWindowsFromPsum (cap : ℕ) : List ℕ → List ℕ → Bool
  | _, [] => true
  | p0 :: ps, q :: qs =>
      decide (q - p0 ≤ cap) && checkAllWindowsFromPsum cap ps qs
  | [], _ => true

/-- Build cumulative prefix sums `[0, x₀, x₀ + x₁, ...]`. -/
def prefixSumsAux (acc : ℕ) : List ℕ → List ℕ
  | [] => [acc]
  | x :: xs => forceNat (acc + x) (fun acc' => acc :: prefixSumsAux acc' xs)

def prefixSums (xs : List ℕ) : List ℕ := prefixSumsAux 0 xs

theorem prefixSumsAux_length (acc : ℕ) (xs : List ℕ) :
    (prefixSumsAux acc xs).length = xs.length + 1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [prefixSumsAux, forceNat_eq, ih]

theorem prefixSumsAux_getElem (acc : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < xs.length + 1) :
    (prefixSumsAux acc xs)[i]'(by rw [prefixSumsAux_length]; exact hi) =
      acc + (xs.take i).sum := by
  induction xs generalizing acc i with
  | nil =>
    have hi0 : i = 0 := by simp at hi; exact hi
    subst hi0
    simp [prefixSumsAux]
  | cons x xs ih =>
    cases i with
    | zero => simp [prefixSumsAux, forceNat_eq]
    | succ i =>
      simp only [prefixSumsAux, forceNat_eq, List.getElem_cons_succ, List.take_succ_cons, List.sum_cons]
      rw [ih (acc + x) i (by simp at hi; omega)]
      omega

theorem prefixSums_length (xs : List ℕ) : (prefixSums xs).length = xs.length + 1 :=
  prefixSumsAux_length 0 xs

theorem prefixSums_getElem (xs : List ℕ) (i : ℕ) (hi : i < xs.length + 1) :
    (prefixSums xs)[i]'(by rw [prefixSums_length]; exact hi) = (xs.take i).sum := by
  simpa [prefixSums] using prefixSumsAux_getElem 0 xs i hi

/-- `O(N)` check that every contiguous slice of at most `spanWords` elements in `xs` sums to `≤ cap`. -/
def checkMaxWindowSum (xs : List ℕ) (spanWords cap : ℕ) : Bool :=
  if xs.length ≤ spanWords then
    decide (xs.sum ≤ cap)
  else
    let ps := prefixSums xs
    checkAllWindowsFromPsum cap ps (ps.drop spanWords)

private theorem checkAllWindowsFromPsum_spec (cap : ℕ) (ps qs : List ℕ)
    (hok : checkAllWindowsFromPsum cap ps qs = true)
    (i : ℕ) (hi : i < qs.length) (hip : i < ps.length) :
    qs[i] - ps[i] ≤ cap := by
  induction ps generalizing qs i with
  | nil => cases hip
  | cons p0 ps ih =>
    cases qs with
    | nil => cases hi
    | cons q qs =>
      simp only [checkAllWindowsFromPsum, Bool.and_eq_true, decide_eq_true_eq] at hok
      cases i with
      | zero => exact hok.1
      | succ i =>
        exact ih qs hok.2 i (by simp at hi; exact hi) (by simp at hip; exact hip)

private theorem take_sub_take_eq_slice_sum (xs : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    (xs.take b).sum - (xs.take a).sum = ((xs.drop a).take (b - a)).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [List.take_succ_cons, List.sum_cons, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
        rw [Nat.add_sub_add_left]
        exact ih a b (by omega)

private theorem take_sum_mono (xs : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    (xs.take a).sum ≤ (xs.take b).sum := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [List.take_succ_cons, List.sum_cons]
        exact Nat.add_le_add_left (ih (by omega)) x

private theorem take_sum_le_sum (xs : List ℕ) (len : ℕ) :
    (xs.take len).sum ≤ xs.sum := by
  have h := take_sum_mono xs (Nat.le_add_right len xs.length)
  rwa [List.take_of_length_le (Nat.le_add_left xs.length len)] at h

private theorem drop_sum_le_sum (xs : List ℕ) (k : ℕ) :
    (xs.drop k).sum ≤ xs.sum := by
  have h := List.take_append_drop k xs
  have hs := congrArg List.sum h
  rw [List.sum_append] at hs
  omega

theorem checkMaxWindowSum_spec (xs : List ℕ) (spanWords cap i len : ℕ)
    (hok : checkMaxWindowSum xs spanWords cap = true) (hlen : len ≤ spanWords) :
    ((xs.drop i).take len).sum ≤ cap := by
  unfold checkMaxWindowSum at hok
  split_ifs at hok with hshort
  · have hcap : xs.sum ≤ cap := of_decide_eq_true hok
    have h1 : ((xs.drop i).take len).sum ≤ (xs.drop i).sum := take_sum_le_sum (xs.drop i) len
    have h2 : (xs.drop i).sum ≤ xs.sum := drop_sum_le_sum xs i
    omega
  · dsimp only at hok
    by_cases hi : xs.length - spanWords ≤ i
    · set start := xs.length - spanWords
      have hps_len : (prefixSums xs).length = xs.length + 1 := prefixSums_length xs
      have hqs_len : ((prefixSums xs).drop spanWords).length = xs.length + 1 - spanWords := by
        rw [List.length_drop, hps_len]
      have hidx_q : start < ((prefixSums xs).drop spanWords).length := by omega
      have hidx_p : start < (prefixSums xs).length := by omega
      have hstep := checkAllWindowsFromPsum_spec cap
        (prefixSums xs) ((prefixSums xs).drop spanWords) hok start hidx_q hidx_p
      have hq_val : ((prefixSums xs).drop spanWords)[start]'hidx_q =
          (prefixSums xs)[spanWords + start]'(by omega) := List.getElem_drop
      rw [hq_val, prefixSums_getElem xs (spanWords + start) (by omega),
        prefixSums_getElem xs start (by omega)] at hstep
      have htot : spanWords + start = xs.length := by omega
      rw [htot, take_sub_take_eq_slice_sum xs start xs.length (by omega)] at hstep
      have hfull : ((xs.drop start).take (xs.length - start)).sum = (xs.drop start).sum := by
        rw [List.take_of_length_le (by simp)]
      rw [hfull] at hstep
      have hsub1 : ((xs.drop i).take len).sum ≤ (xs.drop i).sum := take_sum_le_sum (xs.drop i) len
      have hsub2 : (xs.drop i).sum ≤ (xs.drop start).sum := by
        have hd : xs.drop i = (xs.drop start).drop (i - start) := by
          rw [List.drop_drop, Nat.add_sub_of_le hi]
        rw [hd]
        exact drop_sum_le_sum (xs.drop start) (i - start)
      omega
    · have hps_len : (prefixSums xs).length = xs.length + 1 := prefixSums_length xs
      have hqs_len : ((prefixSums xs).drop spanWords).length = xs.length + 1 - spanWords := by
        rw [List.length_drop, hps_len]
      have hidx_q : i < ((prefixSums xs).drop spanWords).length := by omega
      have hidx_p : i < (prefixSums xs).length := by omega
      have hstep := checkAllWindowsFromPsum_spec cap
        (prefixSums xs) ((prefixSums xs).drop spanWords) hok i hidx_q hidx_p
      have hq_val : ((prefixSums xs).drop spanWords)[i]'hidx_q =
          (prefixSums xs)[spanWords + i]'(by omega) := List.getElem_drop
      rw [hq_val, prefixSums_getElem xs (spanWords + i) (by omega),
        prefixSums_getElem xs i (by omega),
        take_sub_take_eq_slice_sum xs i (spanWords + i) (by omega)] at hstep
      have hadd_sub : spanWords + i - i = spanWords := by omega
      rw [hadd_sub] at hstep
      exact (take_sum_mono (xs.drop i) hlen).trans hstep

/-- Restricted sliding-window usage cap starting at `minWordIdx`. -/
structure PrefixWindowCap where
  minWordIdx : ℕ
  spanWords : ℕ
  cap : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Key lookup in an association list `(bucketIdx, count)` defaulting to `0`. -/
def lookupNat (b : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (k, v) :: rest => if k = b then v else lookupNat b rest

/-- Downstream-facing verified multi-stage prefix profile (`P` stages of `qCert` pairs in `[corrLo, maxHi]`). -/
structure GeneralPrefixProfile (P qCert corrLo maxHi : ℕ) where
  values : (Fin P × Fin qCert) × Bool → ℕ
  injective : Function.Injective values
  strictMono_low : ∀ j : Fin P, StrictMono (fun i : Fin qCert => values ((j, i), false))
  gap : ∀ (j : Fin P) (i : Fin qCert),
    values ((j, i), true) = values ((j, i), false) + 2 ^ (j.val + 1)
  prime_and_ge_five : ∀ x, Nat.Prime (values x) ∧ 5 ≤ values x
  bounds : ∀ x, corrLo ≤ values x ∧ values x ≤ maxHi
  totalSpanWords : ℕ
  stageSpanWords : Fin P → ℕ
  sum_stageSpanWords : (∑ j : Fin P, stageSpanWords j) = totalSpanWords
  stage_span : ∀ (j : Fin P) (i₁ i₂ : Fin qCert),
    values ((j, i₂), false) - values ((j, i₁), false) ≤ stageSpanWords j * 49152
  windowCaps : List PrefixWindowCap
  window_cap : ∀ wc ∈ windowCaps, ∀ u v : ℕ,
    corrLo + 49152 * wc.minWordIdx ≤ u →
    v - u ≤ 49152 * (wc.spanWords - 1) →
    ((Finset.univ.image values) ∩ Finset.Ioc u v).card ≤ wc.cap
  octWindowCaps : List PrefixWindowCap
  oct_window_cap : ∀ wc ∈ octWindowCaps, ∀ u v : ℕ,
    corrLo + 393216 * wc.minWordIdx ≤ u →
    v - u ≤ 393216 * (wc.spanWords - 1) →
    ((Finset.univ.image values) ∩ Finset.Ioc u v).card ≤ wc.cap

/-- Sparse-chunk prefix sub-certificate (`decide +kernel` target). -/
structure PrefixSubCert where
  corrLo : ℕ
  numSuperChunks : ℕ
  activeChunkMask : ℕ
  numChunks : ℕ
  qSub : ℕ
  maxHi : ℕ
  chunks : List (ℕ × PrefixStageSpec)
  windowCaps : List PrefixWindowCap
  octCounts : List (ℕ × ℕ)
  deriving DecidableEq, Repr, Inhabited

def scChunkStage (sc : PrefixSubCert) (k : ℕ) : ℕ :=
  match sc.chunks[k]? with
  | none => 0
  | some (j, _) => j

def scChunkStartWord (sc : PrefixSubCert) (k : ℕ) : ℕ :=
  match sc.chunks[k]? with
  | none => 0
  | some (_, sp) => sp.startWord

def scChunkEndWord (sc : PrefixSubCert) (k : ℕ) : ℕ :=
  match sc.chunks[k]? with
  | none => 0
  | some (_, sp) => sp.endWord

/-- Executable sparse sub-certificate checker (`decide +kernel` target). -/
def checkPrefixSubCert (sc : PrefixSubCert) : Bool :=
  let totalWords := 64 * sc.numSuperChunks
  decide (5 ≤ sc.corrLo) &&
  decide (sc.corrLo % 6 = 5) &&
  decide (0 < sc.qSub) &&
  decide (sc.chunks.length = sc.numChunks) &&
  decide (sc.corrLo + 6 * 524288 * sc.numSuperChunks + 2 ≤ 32769 * 32769) &&
  (sc.chunks.all fun (j, sp) =>
    let maxDstWord := sp.endWord + stageBitShift j / 8192 + 1
    decide (maxDstWord < totalWords) &&
    decide (sc.corrLo + 2 + 6 * (8192 * (sp.endWord + 1) + stageBitShift j) ≤ sc.maxHi)) &&
  (forceNat swarMask0 fun m0 =>
   forceNat swarMask1 fun m1 =>
   forceNat swarMask2 fun m2 =>
   forceNat swarMask3 fun m3 =>
   seqBraun (buildInitialBank sc.corrLo sc.activeChunkMask sc.numSuperChunks) fun initBank =>
   let runList := sc.chunks.map fun (j, sp) => (j, sc.qSub, sp)
   match runStagesList m0 m1 m2 m3 initBank runList with
   | none => false
   | some finalBank =>
       seqList (strictUsedWordsAux m0 m1 m2 m3 sc.activeChunkMask initBank finalBank 0 totalWords)
         fun usedList =>
           (sc.windowCaps.all fun wc =>
             decide (1 ≤ wc.spanWords) &&
             checkMaxWindowSum (usedList.drop wc.minWordIdx) wc.spanWords wc.cap) &&
           ((List.range (8 * sc.numSuperChunks)).all fun b =>
             decide (sc.activeChunkMask.testBit (b / 8) = true →
               ((usedList.drop (8 * b)).take 8).sum ≤ lookupNat b sc.octCounts)))

/-- Verified profile output extracted from a kernel-checked `PrefixSubCert`. -/
structure VerifiedSubCertProfile (sc : PrefixSubCert) where
  bitAt : Fin sc.numChunks → Fin sc.qSub → ℕ
  values : (Fin sc.numChunks × Fin sc.qSub) × Bool → ℕ
  values_low_eq : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
    values ((k, r), false) = laneVal sc.corrLo (stageSrcLane (scChunkStage sc k.val)) (bitAt k r)
  gap : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
    values ((k, r), true) = values ((k, r), false) + 2 ^ (scChunkStage sc k.val + 1)
  strictMono_bit : ∀ k : Fin sc.numChunks, StrictMono (bitAt k)
  bit_bounds : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
    8192 * scChunkStartWord sc k.val ≤ bitAt k r ∧
    bitAt k r < 8192 * (scChunkEndWord sc k.val + 1)
  injective : Function.Injective values
  active_chunk : ∀ x, sc.activeChunkMask.testBit ((values x - sc.corrLo) / 3145728) = true
  prime_and_ge_five : ∀ x, Nat.Prime (values x) ∧ 5 ≤ values x
  bounds : ∀ x, sc.corrLo ≤ values x ∧ values x ≤ sc.maxHi
  window_cap : ∀ wc ∈ sc.windowCaps, ∀ u v : ℕ,
    sc.corrLo + 49152 * wc.minWordIdx ≤ u →
    v - u ≤ 49152 * (wc.spanWords - 1) →
    ((Finset.univ.image values) ∩ Finset.Ioc u v).card ≤ wc.cap
  oct_used_bound : ∀ b : ℕ,
    ((Finset.univ.image values) ∩
      Finset.Ico (sc.corrLo + 393216 * b) (sc.corrLo + 393216 * (b + 1))).card ≤
    lookupNat b sc.octCounts

private theorem list_drop_take_sum_eq_Ico_getD (xs : List ℕ) (w₀ S : ℕ) :
    ((xs.drop w₀).take S).sum = ∑ w ∈ Finset.Ico w₀ (w₀ + S), xs.getD w 0 := by
  induction S generalizing w₀ with
  | zero => simp
  | succ S ih =>
    have hsplit : ∑ w ∈ Finset.Ico w₀ (w₀ + (S + 1)), xs.getD w 0 =
        xs.getD w₀ 0 + ∑ w ∈ Finset.Ico (w₀ + 1) (w₀ + 1 + S), xs.getD w 0 := by
      have heq_set : Finset.Ico w₀ (w₀ + (S + 1)) = insert w₀ (Finset.Ico (w₀ + 1) (w₀ + 1 + S)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [heq_set, Finset.sum_insert (by simp)]
    rw [hsplit, ← ih (w₀ + 1)]
    by_cases hlt : w₀ < xs.length
    · rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons, List.sum_cons]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    · have hge : xs.length ≤ w₀ := by omega
      have hge1 : xs.length ≤ w₀ + 1 := by omega
      simp [List.drop_of_length_le hge, List.drop_of_length_le hge1,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]

/-- Soundness theorem for `checkPrefixSubCert`. -/
theorem checkPrefixSubCert_sound (sc : PrefixSubCert)
    (hcheck : checkPrefixSubCert sc = true) :
    Nonempty (VerifiedSubCertProfile sc) := by
  unfold checkPrefixSubCert at hcheck
  simp only [forceNat_eq, seqBraun_eq, seqList_eq] at hcheck
  set totalWords := 64 * sc.numSuperChunks
  set initBank := buildInitialBank sc.corrLo sc.activeChunkMask sc.numSuperChunks
  set runList := sc.chunks.map fun (j, sp) => (j, sc.qSub, sp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨⟨⟨hlo5, hmod6⟩, hqpos⟩, hlenC⟩, hsieve⟩, hallChunks⟩, hrunBlock⟩
  cases hrun : runStagesList swarMask0 swarMask1 swarMask2 swarMask3 initBank runList with
  | none => simp [hrun] at hrunBlock
  | some finalBank =>
    simp only [hrun, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hrunBlock
    rcases hrunBlock with ⟨hwinBlock, hoctBlock⟩
    have hallChunks' := List.all_eq_true.mp hallChunks
    obtain ⟨hmap_sel, hlen_sel, hstage_sel, hdisj_sel⟩ := runStagesList_sound hrun
    set sel := stagesSelectedSets initBank runList
    have hrun_len : runList.length = sc.numChunks := by simp [runList, hlenC]
    have hsel_len : sel.length = sc.numChunks := hlen_sel.trans hrun_len
    have hrun_get : ∀ k : Fin sc.numChunks,
        runList[k.val]'(by rw [hrun_len]; exact k.isLt) =
          let p := sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)
          (p.1, sc.qSub, p.2) := by
      intro k
      simp [runList]
    have hchunk_opt : ∀ k : Fin sc.numChunks,
        sc.chunks[k.val]? = some (sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)) :=
      fun k => List.getElem?_eq_getElem (by rw [hlenC]; exact k.isLt)
    have hstg_eq : ∀ k : Fin sc.numChunks,
        scChunkStage sc k.val = (sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)).1 := by
      intro k; unfold scChunkStage; rw [hchunk_opt k]
    have hsw_eq : ∀ k : Fin sc.numChunks,
        scChunkStartWord sc k.val = (sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)).2.startWord := by
      intro k; unfold scChunkStartWord; rw [hchunk_opt k]
    have hew_eq : ∀ k : Fin sc.numChunks,
        scChunkEndWord sc k.val = (sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)).2.endWord := by
      intro k; unfold scChunkEndWord; rw [hchunk_opt k]
    let S_fin : Fin sc.numChunks → Finset ℕ :=
      fun k => (sel[k.val]'(by rw [hsel_len]; exact k.isLt)).2
    have hS_card : ∀ k : Fin sc.numChunks, (S_fin k).card = sc.qSub := by
      intro k
      have hc := (hstage_sel k.val (by rw [hrun_len]; exact k.isLt)).2.1
      have hrg := hrun_get k
      have hq : (runList[k.val]'(by rw [hrun_len]; exact k.isLt)).2.1 = sc.qSub := by
        rw [hrg]
      exact hc.trans hq
    let bitAt : Fin sc.numChunks → Fin sc.qSub → ℕ :=
      fun k r => Finset.orderEmbOfFin (S_fin k) (hS_card k) r
    let laneAt : ((Fin sc.numChunks × Fin sc.qSub) × Bool) → Bool :=
      fun x => if x.2 then stageDstLane (scChunkStage sc x.1.1.val)
               else stageSrcLane (scChunkStage sc x.1.1.val)
    let idxAt : ((Fin sc.numChunks × Fin sc.qSub) × Bool) → ℕ :=
      fun x => if x.2 then bitAt x.1.1 x.1.2 + stageBitShift (scChunkStage sc x.1.1.val)
               else bitAt x.1.1 x.1.2
    let values : (Fin sc.numChunks × Fin sc.qSub) × Bool → ℕ :=
      fun x => laneVal sc.corrLo (laneAt x) (idxAt x)
    have hbit_mem : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub), bitAt k r ∈ S_fin k :=
      fun k r => Finset.orderEmbOfFin_mem (S_fin k) (hS_card k) r
    have hstage_props : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
        scChunkStartWord sc k.val ≤ scChunkEndWord sc k.val ∧
        8192 * scChunkStartWord sc k.val ≤ bitAt k r ∧
        bitAt k r < 8192 * (scChunkEndWord sc k.val + 1) ∧
        bankBit initBank (stageSrcLane (scChunkStage sc k.val)) (bitAt k r) = true ∧
        bankBit initBank (stageDstLane (scChunkStage sc k.val))
          (bitAt k r + stageBitShift (scChunkStage sc k.val)) = true ∧
        bankBit finalBank (stageSrcLane (scChunkStage sc k.val)) (bitAt k r) = false ∧
        bankBit finalBank (stageDstLane (scChunkStage sc k.val))
          (bitAt k r + stageBitShift (scChunkStage sc k.val)) = false := by
      intro k r
      have hst := hstage_sel k.val (by rw [hrun_len]; exact k.isLt)
      have hrg := hrun_get k
      have hr1 : (runList[k.val]'(by rw [hrun_len]; exact k.isLt)).1 = scChunkStage sc k.val := by
        rw [hrg, hstg_eq k]
      have hr2 : (runList[k.val]'(by rw [hrun_len]; exact k.isLt)).2.2 =
          (sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)).2 := by
        rw [hrg]
      obtain ⟨hle, _, hb⟩ := hst
      have hb' := hb (bitAt k r) (hbit_mem k r)
      rw [hr1] at hb'
      rw [hr2, ← hsw_eq k, ← hew_eq k] at hle hb'
      exact ⟨hle, hb'.1, hb'.2.1, hb'.2.2.1, hb'.2.2.2.1, hb'.2.2.2.2.1, hb'.2.2.2.2.2⟩
    have hpair_inj : Function.Injective (fun x : (Fin sc.numChunks × Fin sc.qSub) × Bool =>
        (laneAt x, idxAt x)) := by
      intro x₁ x₂ heq
      rcases x₁ with ⟨⟨k₁, r₁⟩, s₁⟩
      rcases x₂ with ⟨⟨k₂, r₂⟩, s₂⟩
      by_cases hk : k₁ = k₂
      · subst hk
        set j := scChunkStage sc k₁.val
        have hlanes_ne : stageDstLane j ≠ stageSrcLane j := by
          unfold stageDstLane; cases stageSrcLane j <;> decide
        have hs : s₁ = s₂ := by
          have hl := congrArg Prod.fst heq
          dsimp [laneAt] at hl
          cases s₁ <;> cases s₂
          · rfl
          · exact False.elim (hlanes_ne hl.symm)
          · exact False.elim (hlanes_ne hl)
          · rfl
        subst hs
        have hidx := congrArg Prod.snd heq
        dsimp [idxAt] at hidx
        have hbit_eq : bitAt k₁ r₁ = bitAt k₁ r₂ := by
          cases s₁ <;> simp at hidx <;> omega
        have hr : r₁ = r₂ := (Finset.orderEmbOfFin (S_fin k₁) (hS_card k₁)).injective hbit_eq
        subst hr
        rfl
      · exfalso
        have hsel_fst : ∀ k : Fin sc.numChunks,
            (sel[k.val]'(by rw [hsel_len]; exact k.isLt)).1 = scChunkStage sc k.val := by
          intro k
          have hm := congrArg (fun l => l[k.val]?) hmap_sel
          have hk_sel : k.val < sel.length := by rw [hsel_len]; exact k.isLt
          have hk_run : k.val < runList.length := by rw [hrun_len]; exact k.isLt
          simp [hk_sel, hk_run] at hm
          rw [hm, hrun_get k, hstg_eq k]
        have hne_val : k₁.val ≠ k₂.val := fun h => hk (Fin.ext h)
        rcases lt_or_gt_of_ne hne_val with hlt | hgt
        · have hne := hdisj_sel k₁.val k₂.val (by rw [hsel_len]; exact k₁.isLt)
            (by rw [hsel_len]; exact k₂.isLt) hlt
            (bitAt k₁ r₁) (hbit_mem k₁ r₁) (bitAt k₂ r₂) (hbit_mem k₂ r₂) s₁ s₂
          rw [hsel_fst k₁, hsel_fst k₂] at hne
          exact hne heq
        · have hne := hdisj_sel k₂.val k₁.val (by rw [hsel_len]; exact k₂.isLt)
            (by rw [hsel_len]; exact k₁.isLt) hgt
            (bitAt k₂ r₂) (hbit_mem k₂ r₂) (bitAt k₁ r₁) (hbit_mem k₁ r₁) s₂ s₁
          rw [hsel_fst k₂, hsel_fst k₁] at hne
          exact hne heq.symm
    have hinj : Function.Injective values := by
      intro x₁ x₂ heq
      have hli := laneVal_inj heq
      exact hpair_inj (Prod.ext hli.1 hli.2)
    have hlow_eq : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
        values ((k, r), false) = laneVal sc.corrLo (stageSrcLane (scChunkStage sc k.val)) (bitAt k r) := by
      intro k r; rfl
    have hgap : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
        values ((k, r), true) = values ((k, r), false) + 2 ^ (scChunkStage sc k.val + 1) := by
      intro k r
      exact stageBitShift_laneVal sc.corrLo (scChunkStage sc k.val) (bitAt k r)
    have hmono_bit : ∀ k : Fin sc.numChunks, StrictMono (bitAt k) :=
      fun k => (Finset.orderEmbOfFin (S_fin k) (hS_card k)).strictMono
    have hbit_bounds : ∀ (k : Fin sc.numChunks) (r : Fin sc.qSub),
        8192 * scChunkStartWord sc k.val ≤ bitAt k r ∧
        bitAt k r < 8192 * (scChunkEndWord sc k.val + 1) :=
      fun k r => ⟨(hstage_props k r).2.1, (hstage_props k r).2.2.1⟩
    have hx_bank : ∀ x : (Fin sc.numChunks × Fin sc.qSub) × Bool,
        bankBit initBank (laneAt x) (idxAt x) = true ∧
        bankBit finalBank (laneAt x) (idxAt x) = false := by
      rintro ⟨⟨k, r⟩, side⟩
      have hp := hstage_props k r
      cases side
      · exact ⟨hp.2.2.2.1, hp.2.2.2.2.2.1⟩
      · exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2.2⟩
    have hact_chunk : ∀ x, sc.activeChunkMask.testBit ((values x - sc.corrLo) / 3145728) = true := by
      intro x
      exact (buildInitialBank_bit_prime hlo5 hmod6 hsieve (laneAt x) (idxAt x) (hx_bank x).1).2.1
    have hprime : ∀ x, Nat.Prime (values x) ∧ 5 ≤ values x := by
      intro x
      have hb := buildInitialBank_bit_prime hlo5 hmod6 hsieve (laneAt x) (idxAt x) (hx_bank x).1
      exact ⟨hb.2.2.1, hb.2.2.2.1⟩
    have hbounds : ∀ x, sc.corrLo ≤ values x ∧ values x ≤ sc.maxHi := by
      rintro ⟨⟨k, r⟩, side⟩
      have hp := hstage_props k r
      set ch := sc.chunks[k.val]'(by rw [hlenC]; exact k.isLt)
      have hmem_ch : ch ∈ sc.chunks := List.getElem_mem _
      have hch_bound := hallChunks' ch hmem_ch
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hch_bound
      have hj_eq : scChunkStage sc k.val = ch.1 := hstg_eq k
      have hew_ch : scChunkEndWord sc k.val = ch.2.endWord := hew_eq k
      cases side
      · dsimp [values, laneAt, idxAt]
        unfold laneVal
        rw [hj_eq]
        have hp2 : bitAt k r < 8192 * (ch.2.endWord + 1) := by rw [← hew_ch]; exact hp.2.2.1
        have : (if stageSrcLane ch.1 then 2 else 0) ≤ 2 := by cases stageSrcLane ch.1 <;> decide
        exact ⟨by omega, by omega⟩
      · dsimp [values, laneAt, idxAt]
        unfold laneVal
        rw [hj_eq]
        have hp2 : bitAt k r < 8192 * (ch.2.endWord + 1) := by rw [← hew_ch]; exact hp.2.2.1
        have : (if stageDstLane ch.1 then 2 else 0) ≤ 2 := by cases stageDstLane ch.1 <;> decide
        exact ⟨by omega, by omega⟩
    have hstrict_eq : strictUsedWordsAux swarMask0 swarMask1 swarMask2 swarMask3
        sc.activeChunkMask initBank finalBank 0 totalWords =
        usedPerWordList initBank finalBank totalWords := by
      dsimp only [initBank]
      rw [strictUsedWordsAux_eq, usedPerWordList]
      apply List.map_congr_left
      intro off _; rw [Nat.zero_add]
    have hwindow : ∀ wc ∈ sc.windowCaps, ∀ u v : ℕ,
        sc.corrLo + 49152 * wc.minWordIdx ≤ u →
        v - u ≤ 49152 * (wc.spanWords - 1) →
        ((Finset.univ.image values) ∩ Finset.Ioc u v).card ≤ wc.cap := by
      intro wc hwc u v hu hvu
      obtain ⟨hspan1, hmaxWin⟩ := hwinBlock wc hwc
      rw [hstrict_eq] at hmaxWin
      set usedList := usedPerWordList initBank finalBank totalWords
      have hused_len : usedList.length = totalWords := by
        simp [usedList, usedPerWordList]
      set w₀ := (u - sc.corrLo) / 49152
      have hw₀_ge : wc.minWordIdx ≤ w₀ := by omega
      let diffMask (lane : Bool) (w : ℕ) : ℕ :=
        (getBankLane initBank lane w &&& fullWordMask) &&&
          (fullWordMask ^^^ (getBankLane finalBank lane w &&& fullWordMask))
      let wordDiffSet : Finset (Bool × ℕ × ℕ) :=
        ((Finset.univ : Finset Bool) ×ˢ
          ((Finset.Ico w₀ (w₀ + wc.spanWords)).filter (fun w => w < totalWords) ×ˢ
            Finset.range 8192)).filter
          (fun lwb => (diffMask lwb.1 lwb.2.1).testBit lwb.2.2 = true)
      have hval_injOn : Set.InjOn (fun lwb : Bool × ℕ × ℕ =>
          laneVal sc.corrLo lwb.1 (8192 * lwb.2.1 + lwb.2.2)) (wordDiffSet : Set (Bool × ℕ × ℕ)) := by
        intro ⟨l₁, w₁, b₁⟩ h₁ ⟨l₂, w₂, b₂⟩ h₂ heq
        have hb₁ : b₁ < 8192 := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₁).1).2).2
        have hb₂ : b₂ < 8192 := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₂).1).2).2
        dsimp at heq
        obtain ⟨hl, hidx⟩ := laneVal_inj heq
        subst hl
        have hw_eq : w₁ = w₂ := by omega
        have hb_eq : b₁ = b₂ := by omega
        subst hw_eq hb_eq
        rfl
      have hsub : (Finset.univ.image values) ∩ Finset.Ioc u v ⊆
          wordDiffSet.image (fun lwb => laneVal sc.corrLo lwb.1 (8192 * lwb.2.1 + lwb.2.2)) := by
        intro y hy
        obtain ⟨himg, hioc⟩ := Finset.mem_inter.mp hy
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp himg
        obtain ⟨huy, hyv⟩ := Finset.mem_Ioc.mp hioc
        set l := laneAt x
        set idx := idxAt x
        set w := idx / 8192
        set b := idx % 8192
        have hb_lt : b < 8192 := Nat.mod_lt idx (by decide)
        have hidx_eq : 8192 * w + b = idx := by omega
        obtain ⟨hinit_t, hfin_f⟩ := hx_bank x
        have hidx_tot : idx < 524288 * sc.numSuperChunks :=
          (buildInitialBank_bit_prime hlo5 hmod6 hsieve l idx hinit_t).1
        have hw_tot : w < totalWords := by dsimp [w, totalWords]; omega
        have hval_y : values x = sc.corrLo + (if l then 2 else 0) + 6 * (8192 * w + b) := by
          dsimp [values, l, idx]
          rw [hidx_eq]
          rfl
        have h_off : (if l then 2 else 0) ≤ 2 := by cases l <;> decide
        have hw_lo : w₀ ≤ w := by dsimp [w₀] at *; omega
        have hw_hi : w < w₀ + wc.spanWords := by dsimp [w₀] at *; omega
        have hdiff_tb : (diffMask l w).testBit b = true := by
          dsimp [diffMask]
          unfold bankBit at hinit_t hfin_f
          change (getBankLane initBank l w).testBit b = true at hinit_t
          change (getBankLane finalBank l w).testBit b = false at hfin_f
          rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, fullWordMask_testBit]
          simp [hb_lt, hinit_t, hfin_f]
        apply Finset.mem_image.mpr
        refine ⟨(l, w, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ l,
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hw_lo, hw_hi⟩, hw_tot⟩,
            Finset.mem_range.mpr hb_lt⟩⟩, hdiff_tb⟩, ?_⟩
        rw [hidx_eq]
      have hcard_le1 : ((Finset.univ.image values) ∩ Finset.Ioc u v).card ≤ wordDiffSet.card := by
        calc
          ((Finset.univ.image values) ∩ Finset.Ioc u v).card
              ≤ (wordDiffSet.image _).card := Finset.card_le_card hsub
          _ = wordDiffSet.card := Finset.card_image_of_injOn hval_injOn
      have hcard_eq_sum : wordDiffSet.card =
          ∑ w ∈ (Finset.Ico w₀ (w₀ + wc.spanWords)).filter (fun w => w < totalWords),
            usedInWord initBank finalBank w := by
        dsimp [wordDiffSet]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
        simp_rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.sum_comm, Finset.sum_pair (by decide), Nat.add_comm]
        simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, ← fastSetCount10_eq_filter_card]
        rfl
      have hsum_le_drop :
          (∑ w ∈ (Finset.Ico w₀ (w₀ + wc.spanWords)).filter (fun w => w < totalWords),
            usedInWord initBank finalBank w) ≤
          (((usedList.drop wc.minWordIdx).drop (w₀ - wc.minWordIdx)).take wc.spanWords).sum := by
        rw [List.drop_drop, Nat.add_sub_of_le hw₀_ge, list_drop_take_sum_eq_Ico_getD,
          ← Finset.sum_filter_add_sum_filter_not (Finset.Ico w₀ (w₀ + wc.spanWords)) (fun w => w < totalWords)]
        have heq_in : (∑ w ∈ (Finset.Ico w₀ (w₀ + wc.spanWords)).filter (fun w => w < totalWords),
            usedList.getD w 0) =
            ∑ w ∈ (Finset.Ico w₀ (w₀ + wc.spanWords)).filter (fun w => w < totalWords),
              usedInWord initBank finalBank w := by
          apply Finset.sum_congr rfl
          intro w hw
          have hwt : w < totalWords := (Finset.mem_filter.mp hw).2
          have hlt : w < usedList.length := by rw [hused_len]; exact hwt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
          simp [usedList, usedPerWordList]
        rw [heq_in]
        exact Nat.le_add_right _ _
      have hwin_cap := checkMaxWindowSum_spec (usedList.drop wc.minWordIdx)
        wc.spanWords wc.cap (w₀ - wc.minWordIdx) wc.spanWords hmaxWin le_rfl
      omega
    have hoct_bound : ∀ b : ℕ,
        ((Finset.univ.image values) ∩
          Finset.Ico (sc.corrLo + 393216 * b) (sc.corrLo + 393216 * (b + 1))).card ≤
        lookupNat b sc.octCounts := by
      intro b
      by_cases hact : b < 8 * sc.numSuperChunks ∧ sc.activeChunkMask.testBit (b / 8) = true
      · have hoct_le := hoctBlock b hact.1 hact.2
        rw [hstrict_eq] at hoct_le
        set usedList := usedPerWordList initBank finalBank totalWords
        have hused_len : usedList.length = totalWords := by
          simp [usedList, usedPerWordList]
        let diffMask (lane : Bool) (w : ℕ) : ℕ :=
          (getBankLane initBank lane w &&& fullWordMask) &&&
            (fullWordMask ^^^ (getBankLane finalBank lane w &&& fullWordMask))
        let octDiffSet : Finset (Bool × ℕ × ℕ) :=
          ((Finset.univ : Finset Bool) ×ˢ
            ((Finset.Ico (8 * b) (8 * b + 8)).filter (fun w => w < totalWords) ×ˢ
              Finset.range 8192)).filter
            (fun lwb => (diffMask lwb.1 lwb.2.1).testBit lwb.2.2 = true)
        have hval_injOn : Set.InjOn (fun lwb : Bool × ℕ × ℕ =>
            laneVal sc.corrLo lwb.1 (8192 * lwb.2.1 + lwb.2.2)) (octDiffSet : Set (Bool × ℕ × ℕ)) := by
          intro ⟨l₁, w₁, b₁⟩ h₁ ⟨l₂, w₂, b₂⟩ h₂ heq
          have hb₁ : b₁ < 8192 := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₁).1).2).2
          have hb₂ : b₂ < 8192 := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₂).1).2).2
          dsimp at heq
          obtain ⟨hl, hidx⟩ := laneVal_inj heq
          subst hl
          have hw_eq : w₁ = w₂ := by omega
          have hb_eq : b₁ = b₂ := by omega
          subst hw_eq hb_eq
          rfl
        have hsub : (Finset.univ.image values) ∩
            Finset.Ico (sc.corrLo + 393216 * b) (sc.corrLo + 393216 * (b + 1)) ⊆
            octDiffSet.image (fun lwb => laneVal sc.corrLo lwb.1 (8192 * lwb.2.1 + lwb.2.2)) := by
          intro y hy
          obtain ⟨himg, hico⟩ := Finset.mem_inter.mp hy
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp himg
          obtain ⟨hlo_y, hhi_y⟩ := Finset.mem_Ico.mp hico
          set l := laneAt x
          set idx := idxAt x
          set w := idx / 8192
          set bit := idx % 8192
          have hb_lt : bit < 8192 := Nat.mod_lt idx (by decide)
          have hidx_eq : 8192 * w + bit = idx := by omega
          obtain ⟨hinit_t, hfin_f⟩ := hx_bank x
          have hidx_tot : idx < 524288 * sc.numSuperChunks :=
            (buildInitialBank_bit_prime hlo5 hmod6 hsieve l idx hinit_t).1
          have hw_tot : w < totalWords := by dsimp [w, totalWords]; omega
          have hval_y : values x = sc.corrLo + (if l then 2 else 0) + 6 * (8192 * w + bit) := by
            dsimp [values, l, idx]; rw [hidx_eq]; rfl
          have h_off : (if l then 2 else 0) ≤ 2 := by cases l <;> decide
          have hw_lo : 8 * b ≤ w := by omega
          have hw_hi : w < 8 * b + 8 := by omega
          have hdiff_tb : (diffMask l w).testBit bit = true := by
            dsimp [diffMask]
            unfold bankBit at hinit_t hfin_f
            change (getBankLane initBank l w).testBit bit = true at hinit_t
            change (getBankLane finalBank l w).testBit bit = false at hfin_f
            rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and, fullWordMask_testBit]
            simp [hb_lt, hinit_t, hfin_f]
          apply Finset.mem_image.mpr
          refine ⟨(l, w, bit), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ l,
            Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hw_lo, hw_hi⟩, hw_tot⟩,
              Finset.mem_range.mpr hb_lt⟩⟩, hdiff_tb⟩, ?_⟩
          rw [hidx_eq]
        have hcard_le1 : ((Finset.univ.image values) ∩
            Finset.Ico (sc.corrLo + 393216 * b) (sc.corrLo + 393216 * (b + 1))).card ≤ octDiffSet.card := by
          calc
            _ ≤ (octDiffSet.image _).card := Finset.card_le_card hsub
            _ = octDiffSet.card := Finset.card_image_of_injOn hval_injOn
        have hcard_eq_sum : octDiffSet.card =
            ∑ w ∈ (Finset.Ico (8 * b) (8 * b + 8)).filter (fun w => w < totalWords),
              usedInWord initBank finalBank w := by
          dsimp [octDiffSet]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
          simp_rw [Finset.sum_product]
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.sum_comm, Finset.sum_pair (by decide), Nat.add_comm]
          simp_rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, ← fastSetCount10_eq_filter_card]
          rfl
        have hsum_le_drop :
            (∑ w ∈ (Finset.Ico (8 * b) (8 * b + 8)).filter (fun w => w < totalWords),
              usedInWord initBank finalBank w) ≤
            ((usedList.drop (8 * b)).take 8).sum := by
          rw [list_drop_take_sum_eq_Ico_getD,
            ← Finset.sum_filter_add_sum_filter_not (Finset.Ico (8 * b) (8 * b + 8)) (fun w => w < totalWords)]
          have heq_in : (∑ w ∈ (Finset.Ico (8 * b) (8 * b + 8)).filter (fun w => w < totalWords),
              usedList.getD w 0) =
              ∑ w ∈ (Finset.Ico (8 * b) (8 * b + 8)).filter (fun w => w < totalWords),
                usedInWord initBank finalBank w := by
            apply Finset.sum_congr rfl
            intro w hw
            have hwt : w < totalWords := (Finset.mem_filter.mp hw).2
            have hlt : w < usedList.length := by rw [hused_len]; exact hwt
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
            simp [usedList, usedPerWordList]
          rw [heq_in]
          exact Nat.le_add_right _ _
        omega
      · have hempty : (Finset.univ.image values) ∩
            Finset.Ico (sc.corrLo + 393216 * b) (sc.corrLo + 393216 * (b + 1)) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro y hy
          obtain ⟨himg, hico⟩ := Finset.mem_inter.mp hy
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp himg
          obtain ⟨hlo_y, hhi_y⟩ := Finset.mem_Ico.mp hico
          have hp := buildInitialBank_bit_prime hlo5 hmod6 hsieve (laneAt x) (idxAt x) (hx_bank x).1
          have hidx_tot := hp.1
          have hact_x := hp.2.1
          have hval_x : values x = sc.corrLo + (if laneAt x then 2 else 0) + 6 * idxAt x := rfl
          have h_off : (if laneAt x then 2 else 0) ≤ 2 := by cases laneAt x <;> decide
          have hb_lt : b < 8 * sc.numSuperChunks := by omega
          have hdiv_eq : (values x - sc.corrLo) / 3145728 = b / 8 := by omega
          rw [hdiv_eq] at hact_x
          exact hact ⟨hb_lt, hact_x⟩
        rw [hempty, Finset.card_empty]
        exact Nat.zero_le _
    exact ⟨⟨bitAt, values, hlow_eq, hgap, hmono_bit, hbit_bounds, hinj, hact_chunk,
      hprime, hbounds, hwindow, hoct_bound⟩⟩

/-- Plan gluing `K` disjoint-super-chunk `PrefixSubCert`s (`M` chunks of `qSub` pairs per stage)
into a single `GeneralPrefixProfile P qCert corrLo maxHi`. -/
structure MultiSubCertPlan where
  P : ℕ
  M : ℕ
  qSub : ℕ
  qCert : ℕ
  corrLo : ℕ
  maxHi : ℕ
  numOcts : ℕ
  routes : List (List (ℕ × ℕ))
  windowCaps : List PrefixWindowCap
  octWindowCaps : List PrefixWindowCap
  deriving DecidableEq, Repr

def planRoute (plan : MultiSubCertPlan) (j m : ℕ) : ℕ × ℕ :=
  (plan.routes.getD j []).getD m (0, 0)

def planStageSpanWords (subCerts : List PrefixSubCert) (plan : MultiSubCertPlan) (j : ℕ) : ℕ :=
  let gk0 := planRoute plan j 0
  let gkLast := planRoute plan j (plan.M - 1)
  scChunkEndWord (subCerts.getD gkLast.1 default) gkLast.2 -
    scChunkStartWord (subCerts.getD gk0.1 default) gk0.2 + 1

def planTotalSpanWords (subCerts : List PrefixSubCert) (plan : MultiSubCertPlan) : ℕ :=
  ((List.range plan.P).map (planStageSpanWords subCerts plan)).sum

def planCombinedOctList (subCerts : List PrefixSubCert) (plan : MultiSubCertPlan) : List ℕ :=
  let K := subCerts.length
  (List.range plan.numOcts).map fun b =>
    ((List.range K).map fun g => lookupNat b (subCerts.getD g default).octCounts).sum

/-- Fast metadata verifier (`< 5 ms` in `decide +kernel`) for `MultiSubCertPlan`. -/
def checkMultiSubCertPlan (subCerts : List PrefixSubCert) (plan : MultiSubCertPlan) : Bool :=
  let K := subCerts.length
  let combinedOctList := planCombinedOctList subCerts plan
  decide (0 < plan.M) &&
  decide (0 < plan.qSub) &&
  decide (plan.M * plan.qSub = plan.qCert) &&
  decide (plan.routes.length = plan.P) &&
  decide (plan.maxHi < plan.corrLo + 393216 * plan.numOcts) &&
  ((List.range K).all fun g =>
    let sc := subCerts.getD g default
    decide (sc.corrLo = plan.corrLo) &&
    decide (sc.qSub = plan.qSub) &&
    decide (sc.maxHi ≤ plan.maxHi) &&
    decide (sc.windowCaps.length = plan.windowCaps.length)) &&
  ((List.range K).all fun g₁ =>
    (List.range K).all fun g₂ =>
      decide (g₁ = g₂ ∨
        (subCerts.getD g₁ default).activeChunkMask &&&
          (subCerts.getD g₂ default).activeChunkMask = 0)) &&
  ((List.range plan.P).all fun j =>
    decide ((plan.routes.getD j []).length = plan.M) &&
    ((List.range plan.M).all fun m =>
      let gk := planRoute plan j m
      let sc := subCerts.getD gk.1 default
      let gk0 := planRoute plan j 0
      let gkLast := planRoute plan j (plan.M - 1)
      decide (gk.1 < K) &&
      decide (gk.2 < sc.numChunks) &&
      decide (scChunkStage sc gk.2 = j) &&
      decide (scChunkStartWord (subCerts.getD gk0.1 default) gk0.2 ≤ scChunkStartWord sc gk.2) &&
      decide (scChunkEndWord sc gk.2 ≤ scChunkEndWord (subCerts.getD gkLast.1 default) gkLast.2) &&
      ((List.range plan.M).all fun m₂ =>
        decide (m < m₂ →
          scChunkEndWord sc gk.2 <
            scChunkStartWord (subCerts.getD (planRoute plan j m₂).1 default)
              (planRoute plan j m₂).2)))) &&
  ((List.range plan.P).all fun j₁ =>
    (List.range plan.M).all fun m₁ =>
      (List.range plan.P).all fun j₂ =>
        (List.range plan.M).all fun m₂ =>
          decide (planRoute plan j₁ m₁ = planRoute plan j₂ m₂ → j₁ = j₂ ∧ m₁ = m₂)) &&
  ((List.range plan.windowCaps.length).all fun wIdx =>
    let wc := plan.windowCaps.getD wIdx default
    ((List.range K).all fun g =>
      let wcg := (subCerts.getD g default).windowCaps.getD wIdx default
      decide (wcg.minWordIdx = wc.minWordIdx) &&
      decide (wcg.spanWords = wc.spanWords)) &&
    decide (((List.range K).map fun g =>
      ((subCerts.getD g default).windowCaps.getD wIdx default).cap).sum ≤ wc.cap)) &&
  (plan.octWindowCaps.all fun wc =>
    decide (1 ≤ wc.spanWords) &&
    checkMaxWindowSum (combinedOctList.drop wc.minWordIdx) wc.spanWords wc.cap)

private theorem list_getD_eq_getElem {α : Type} (xs : List α) (d : α) (i : ℕ) (hi : i < xs.length) :
    xs.getD i d = xs[i]'hi := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- Assemble `K` verified disjoint-super-chunk `PrefixSubCert`s into a single `GeneralPrefixProfile`
whose `totalSpanWords` and `windowCaps` remain definitionally transparent. -/
noncomputable def assembleGeneralPrefixProfile
    (subCerts : List PrefixSubCert) (plan : MultiSubCertPlan)
    (hplan : checkMultiSubCertPlan subCerts plan = true)
    (profs : ∀ g : Fin subCerts.length, VerifiedSubCertProfile (subCerts[g.val]'g.isLt)) :
    GeneralPrefixProfile plan.P plan.qCert plan.corrLo plan.maxHi :=
  let K := subCerts.length
  have hplan' := hplan
  have hunpack :
      0 < plan.M ∧
      0 < plan.qSub ∧
      plan.M * plan.qSub = plan.qCert ∧
      plan.routes.length = plan.P ∧
      (∀ g (hg : g < K),
        (subCerts[g]'hg).corrLo = plan.corrLo ∧
        (subCerts[g]'hg).qSub = plan.qSub ∧
        (subCerts[g]'hg).maxHi ≤ plan.maxHi ∧
        (subCerts[g]'hg).windowCaps.length = plan.windowCaps.length) ∧
      (∀ g₁ g₂ (hg₁ : g₁ < K) (hg₂ : g₂ < K), g₁ ≠ g₂ →
        (subCerts[g₁]'hg₁).activeChunkMask &&& (subCerts[g₂]'hg₂).activeChunkMask = 0) ∧
      (∀ j < plan.P, ∀ m < plan.M,
        let gk := planRoute plan j m
        let gk0 := planRoute plan j 0
        let gkLast := planRoute plan j (plan.M - 1)
        ∃ hg : gk.1 < K,
          gk.2 < (subCerts[gk.1]'hg).numChunks ∧
          scChunkStage (subCerts[gk.1]'hg) gk.2 = j ∧
          scChunkStartWord (subCerts.getD gk0.1 default) gk0.2 ≤
            scChunkStartWord (subCerts[gk.1]'hg) gk.2 ∧
          scChunkEndWord (subCerts[gk.1]'hg) gk.2 ≤
            scChunkEndWord (subCerts.getD gkLast.1 default) gkLast.2 ∧
          (∀ m₂ < plan.M, m < m₂ →
            scChunkEndWord (subCerts[gk.1]'hg) gk.2 <
              scChunkStartWord (subCerts.getD (planRoute plan j m₂).1 default)
                (planRoute plan j m₂).2)) ∧
      (∀ j₁ < plan.P, ∀ m₁ < plan.M, ∀ j₂ < plan.P, ∀ m₂ < plan.M,
        planRoute plan j₁ m₁ = planRoute plan j₂ m₂ → j₁ = j₂ ∧ m₁ = m₂) ∧
      (∀ wIdx (hw : wIdx < plan.windowCaps.length),
        let wc := plan.windowCaps[wIdx]'hw
        (∀ g (hg : g < K),
          let wcg := (subCerts[g]'hg).windowCaps.getD wIdx default
          wcg.minWordIdx = wc.minWordIdx ∧ wcg.spanWords = wc.spanWords) ∧
        (∑ g : Fin K, ((subCerts[g.val]'g.isLt).windowCaps.getD wIdx default).cap) ≤ wc.cap) ∧
      plan.maxHi < plan.corrLo + 393216 * plan.numOcts ∧
      (∀ wc ∈ plan.octWindowCaps,
        1 ≤ wc.spanWords ∧
        checkMaxWindowSum ((planCombinedOctList subCerts plan).drop wc.minWordIdx)
          wc.spanWords wc.cap = true) := by
    unfold checkMultiSubCertPlan at hplan'
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hplan'
    rcases hplan' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hM, hqSub⟩, hMq⟩, hlenR⟩, hmaxOct⟩, hscAll⟩, hdisjM⟩, hroutes⟩, hinjR⟩, hwinAll⟩, hoctWinAll⟩
    refine ⟨hM, hqSub, hMq, hlenR, ?_, ?_, ?_, ?_, ?_, hmaxOct, hoctWinAll⟩
    · intro g hg
      have h := hscAll g hg
      rw [list_getD_eq_getElem subCerts default g hg] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
    · intro g₁ g₂ hg₁ hg₂ hne
      have h := hdisjM g₁ hg₁ g₂ hg₂
      rw [list_getD_eq_getElem subCerts default g₁ hg₁,
        list_getD_eq_getElem subCerts default g₂ hg₂] at h
      exact h.resolve_left hne
    · intro j hj m hm
      have h := (hroutes j hj).2 m hm
      have hg : (planRoute plan j m).1 < K := h.1.1.1.1.1
      rw [list_getD_eq_getElem subCerts default (planRoute plan j m).1 hg] at h
      exact ⟨hg, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
    · intro j₁ hj₁ m₁ hm₁ j₂ hj₂ m₂ hm₂ heq
      exact hinjR j₁ hj₁ m₁ hm₁ j₂ hj₂ m₂ hm₂ heq
    · intro wIdx hw
      have h := hwinAll wIdx hw
      rw [list_getD_eq_getElem plan.windowCaps default wIdx hw] at h
      refine ⟨?_, ?_⟩
      · intro g hg
        have hg' := h.1 g hg
        rw [list_getD_eq_getElem subCerts default g hg] at hg'
        exact hg'
      · have hsum := h.2
        rw [list_range_map_sum, Finset.sum_range] at hsum
        have heq_sum : (∑ g : Fin K,
            ((subCerts[g.val]'g.isLt).windowCaps.getD wIdx default).cap) =
            ∑ g : Fin K, ((subCerts.getD g.val default).windowCaps.getD wIdx default).cap := by
          apply Finset.sum_congr rfl
          intro g _
          rw [list_getD_eq_getElem subCerts default g.val g.isLt]
        rw [heq_sum]
        exact hsum
  let hM := hunpack.1
  let hqSub := hunpack.2.1
  let hMq := hunpack.2.2.1
  let hscProps := hunpack.2.2.2.2.1
  let hdisjMask := hunpack.2.2.2.2.2.1
  let hrouteProps := hunpack.2.2.2.2.2.2.1
  let hrouteInj := hunpack.2.2.2.2.2.2.2.1
  let hwinProps := hunpack.2.2.2.2.2.2.2.2.1
  let hmaxOct := hunpack.2.2.2.2.2.2.2.2.2.1
  let hoctWinProps := hunpack.2.2.2.2.2.2.2.2.2.2
  let partOf (i : Fin plan.qCert) : Fin plan.M :=
    ⟨i.val / plan.qSub, by
      have hi : i.val < plan.M * plan.qSub := by rw [hMq]; exact i.isLt
      exact (Nat.div_lt_iff_lt_mul hqSub).mpr hi⟩
  let remOf (i : Fin plan.qCert) : Fin plan.qSub :=
    ⟨i.val % plan.qSub, Nat.mod_lt i.val hqSub⟩
  let gIdx (j : Fin plan.P) (m : Fin plan.M) : Fin K :=
    ⟨(planRoute plan j.val m.val).1, (hrouteProps j.val j.isLt m.val m.isLt).1⟩
  let kIdx (j : Fin plan.P) (m : Fin plan.M) :
      Fin (subCerts[(gIdx j m).val]'(gIdx j m).isLt).numChunks :=
    ⟨(planRoute plan j.val m.val).2,
      (hrouteProps j.val j.isLt m.val m.isLt).choose_spec.1⟩
  let rCast (j : Fin plan.P) (m : Fin plan.M) (r : Fin plan.qSub) :
      Fin (subCerts[(gIdx j m).val]'(gIdx j m).isLt).qSub :=
    Fin.cast ((hscProps (gIdx j m).val (gIdx j m).isLt).2.1).symm r
  let subVal (g : Fin K) (k r : ℕ) (side : Bool) : ℕ :=
    if hk : k < (subCerts[g.val]'g.isLt).numChunks then
      if hr : r < (subCerts[g.val]'g.isLt).qSub then
        (profs g).values ((⟨k, hk⟩, ⟨r, hr⟩), side)
      else 0
    else 0
  have hsubVal_eq : ∀ (j : Fin plan.P) (i : Fin plan.qCert) (side : Bool),
      let m := partOf i
      subVal (gIdx j m) (planRoute plan j.val m.val).2 (remOf i).val side =
        (profs (gIdx j m)).values ((kIdx j m, rCast j m (remOf i)), side) := by
    intro j i side
    dsimp [subVal]
    have hk : (planRoute plan j.val (partOf i).val).2 <
        (subCerts[(gIdx j (partOf i)).val]'(gIdx j (partOf i)).isLt).numChunks :=
      (kIdx j (partOf i)).isLt
    have hr : (remOf i).val <
        (subCerts[(gIdx j (partOf i)).val]'(gIdx j (partOf i)).isLt).qSub := by
      rw [(hscProps (gIdx j (partOf i)).val (gIdx j (partOf i)).isLt).2.1]
      exact (remOf i).isLt
    rw [dif_pos hk, dif_pos hr]
    rfl
  let combinedValues : (Fin plan.P × Fin plan.qCert) × Bool → ℕ :=
    fun ⟨⟨j, i⟩, side⟩ =>
      let m := partOf i
      (profs (gIdx j m)).values ((kIdx j m, rCast j m (remOf i)), side)
  { values := combinedValues
    injective := by
      rintro ⟨⟨j₁, i₁⟩, s₁⟩ ⟨⟨j₂, i₂⟩, s₂⟩ heq
      dsimp [combinedValues] at heq
      by_cases hg : gIdx j₁ (partOf i₁) = gIdx j₂ (partOf i₂)
      · have hsv : subVal (gIdx j₁ (partOf i₁)) (planRoute plan j₁.val (partOf i₁).val).2
            (remOf i₁).val s₁ =
            subVal (gIdx j₂ (partOf i₂)) (planRoute plan j₂.val (partOf i₂).val).2
            (remOf i₂).val s₂ := by
          rw [hsubVal_eq j₁ i₁ s₁, hsubVal_eq j₂ i₂ s₂]
          exact heq
        rw [← hg] at hsv
        dsimp [subVal] at hsv
        have hk₁ : (planRoute plan j₁.val (partOf i₁).val).2 <
            (subCerts[(gIdx j₁ (partOf i₁)).val]'(gIdx j₁ (partOf i₁)).isLt).numChunks :=
          (kIdx j₁ (partOf i₁)).isLt
        have hk₂ : (planRoute plan j₂.val (partOf i₂).val).2 <
            (subCerts[(gIdx j₁ (partOf i₁)).val]'(gIdx j₁ (partOf i₁)).isLt).numChunks := by
          rw [hg]; exact (kIdx j₂ (partOf i₂)).isLt
        have hr₁ : (remOf i₁).val <
            (subCerts[(gIdx j₁ (partOf i₁)).val]'(gIdx j₁ (partOf i₁)).isLt).qSub := by
          rw [(hscProps (gIdx j₁ (partOf i₁)).val (gIdx j₁ (partOf i₁)).isLt).2.1]
          exact (remOf i₁).isLt
        have hr₂ : (remOf i₂).val <
            (subCerts[(gIdx j₁ (partOf i₁)).val]'(gIdx j₁ (partOf i₁)).isLt).qSub := by
          rw [(hscProps (gIdx j₁ (partOf i₁)).val (gIdx j₁ (partOf i₁)).isLt).2.1]
          exact (remOf i₂).isLt
        rw [dif_pos hk₁, dif_pos hr₁, dif_pos hk₂, dif_pos hr₂] at hsv
        have hinj_sub := (profs (gIdx j₁ (partOf i₁))).injective hsv
        have hk_eq : (planRoute plan j₁.val (partOf i₁).val).2 =
            (planRoute plan j₂.val (partOf i₂).val).2 :=
          congrArg (fun p => p.1.1.val) hinj_sub
        have hr_eq : (remOf i₁).val = (remOf i₂).val :=
          congrArg (fun p => p.1.2.val) hinj_sub
        have hs_eq : s₁ = s₂ := congrArg Prod.snd hinj_sub
        have hroute_eq : planRoute plan j₁.val (partOf i₁).val =
            planRoute plan j₂.val (partOf i₂).val := by
          ext
          · exact congrArg Fin.val hg
          · exact hk_eq
        obtain ⟨hj_val, hm_val⟩ := hrouteInj j₁.val j₁.isLt (partOf i₁).val (partOf i₁).isLt
          j₂.val j₂.isLt (partOf i₂).val (partOf i₂).isLt hroute_eq
        have hj_eq : j₁ = j₂ := Fin.ext hj_val
        have hi_val : i₁.val = i₂.val := by
          dsimp [partOf] at hm_val
          dsimp [remOf] at hr_eq
          have h1 := Nat.div_add_mod i₁.val plan.qSub
          have h2 := Nat.div_add_mod i₂.val plan.qSub
          rw [← h1, ← h2, hm_val, hr_eq]
        exact Prod.ext (Prod.ext hj_eq (Fin.ext hi_val)) hs_eq
      · exfalso
        set m₁ := partOf i₁
        set m₂ := partOf i₂
        set g₁ := gIdx j₁ m₁
        set g₂ := gIdx j₂ m₂
        have hne_val : g₁.val ≠ g₂.val := fun h => hg (Fin.ext h)
        have hmask0 := hdisjMask g₁.val g₂.val g₁.isLt g₂.isLt hne_val
        set y := (profs g₁).values ((kIdx j₁ m₁, rCast j₁ m₁ (remOf i₁)), s₁)
        have hc₁ : (subCerts[g₁.val]'g₁.isLt).corrLo = plan.corrLo :=
          (hscProps g₁.val g₁.isLt).1
        have hc₂ : (subCerts[g₂.val]'g₂.isLt).corrLo = plan.corrLo :=
          (hscProps g₂.val g₂.isLt).1
        have ht₁ := (profs g₁).active_chunk ((kIdx j₁ m₁, rCast j₁ m₁ (remOf i₁)), s₁)
        have ht₂ := (profs g₂).active_chunk ((kIdx j₂ m₂, rCast j₂ m₂ (remOf i₂)), s₂)
        change (subCerts[g₁.val]'g₁.isLt).activeChunkMask.testBit
          ((y - (subCerts[g₁.val]'g₁.isLt).corrLo) / 3145728) = true at ht₁
        rw [← heq] at ht₂
        change (subCerts[g₂.val]'g₂.isLt).activeChunkMask.testBit
          ((y - (subCerts[g₂.val]'g₂.isLt).corrLo) / 3145728) = true at ht₂
        rw [hc₁] at ht₁
        rw [hc₂] at ht₂
        have hand : ((subCerts[g₁.val]'g₁.isLt).activeChunkMask &&&
            (subCerts[g₂.val]'g₂.isLt).activeChunkMask).testBit
            ((y - plan.corrLo) / 3145728) = true := by
          rw [Nat.testBit_and, ht₁, ht₂]; rfl
        rw [hmask0, Nat.zero_testBit] at hand
        cases hand
    strictMono_low := by
      intro j i₁ i₂ hlt
      dsimp [combinedValues]
      have hm_le : (partOf i₁).val ≤ (partOf i₂).val := Nat.div_le_div_right (le_of_lt hlt)
      by_cases hm_eq : partOf i₁ = partOf i₂
      · rw [← hm_eq]
        have hr_lt : rCast j (partOf i₁) (remOf i₁) < rCast j (partOf i₁) (remOf i₂) := by
          change i₁.val % plan.qSub < i₂.val % plan.qSub
          have hdiv_eq : i₁.val / plan.qSub = i₂.val / plan.qSub := congrArg Fin.val hm_eq
          have h1 := Nat.div_add_mod i₁.val plan.qSub
          have h2 := Nat.div_add_mod i₂.val plan.qSub
          rw [hdiv_eq] at h1
          have hi_lt : i₁.val < i₂.val := hlt
          omega
        have hbit_lt := (profs (gIdx j (partOf i₁))).strictMono_bit (kIdx j (partOf i₁)) hr_lt
        rw [(profs (gIdx j (partOf i₁))).values_low_eq, (profs (gIdx j (partOf i₁))).values_low_eq]
        unfold laneVal
        omega
      · set m₁ := partOf i₁
        set m₂ := partOf i₂
        have hm_lt : m₁.val < m₂.val := lt_of_le_of_ne hm_le (fun h => hm_eq (Fin.ext h))
        have hrp₁ := (hrouteProps j.val j.isLt m₁.val m₁.isLt).choose_spec
        have hrp₂ := (hrouteProps j.val j.isLt m₂.val m₂.isLt).choose_spec
        have hord_w := hrp₁.2.2.2.2 m₂.val m₂.isLt hm_lt
        rw [list_getD_eq_getElem subCerts default (planRoute plan j.val m₂.val).1
          (hrouteProps j.val j.isLt m₂.val m₂.isLt).1] at hord_w
        set bit₁ := (profs (gIdx j m₁)).bitAt (kIdx j m₁) (rCast j m₁ (remOf i₁))
        set bit₂ := (profs (gIdx j m₂)).bitAt (kIdx j m₂) (rCast j m₂ (remOf i₂))
        have hb₁ : bit₁ < 8192 * (scChunkEndWord
            (subCerts[(planRoute plan j.val m₁.val).1]'(hrouteProps j.val j.isLt m₁.val m₁.isLt).1)
            (planRoute plan j.val m₁.val).2 + 1) :=
          ((profs (gIdx j m₁)).bit_bounds (kIdx j m₁) (rCast j m₁ (remOf i₁))).2
        have hb₂ : 8192 * scChunkStartWord
            (subCerts[(planRoute plan j.val m₂.val).1]'(hrouteProps j.val j.isLt m₂.val m₂.isLt).1)
            (planRoute plan j.val m₂.val).2 ≤ bit₂ :=
          ((profs (gIdx j m₂)).bit_bounds (kIdx j m₂) (rCast j m₂ (remOf i₂))).1
        have hbit_lt : bit₁ < bit₂ := by omega
        rw [(profs (gIdx j m₁)).values_low_eq, (profs (gIdx j m₂)).values_low_eq]
        have hc₁ : (subCerts[(gIdx j m₁).val]'(gIdx j m₁).isLt).corrLo = plan.corrLo :=
          (hscProps (gIdx j m₁).val (gIdx j m₁).isLt).1
        have hc₂ : (subCerts[(gIdx j m₂).val]'(gIdx j m₂).isLt).corrLo = plan.corrLo :=
          (hscProps (gIdx j m₂).val (gIdx j m₂).isLt).1
        have hj₁ : scChunkStage (subCerts[(gIdx j m₁).val]'(gIdx j m₁).isLt) (kIdx j m₁).val = j.val :=
          hrp₁.2.1
        have hj₂ : scChunkStage (subCerts[(gIdx j m₂).val]'(gIdx j m₂).isLt) (kIdx j m₂).val = j.val :=
          hrp₂.2.1
        rw [hc₁, hc₂, hj₁, hj₂]
        change laneVal plan.corrLo (stageSrcLane j.val) bit₁ <
          laneVal plan.corrLo (stageSrcLane j.val) bit₂
        unfold laneVal
        omega
    gap := by
      intro j i
      dsimp [combinedValues]
      set m := partOf i
      have hj_eq : scChunkStage (subCerts[(gIdx j m).val]'(gIdx j m).isLt) (kIdx j m).val = j.val :=
        (hrouteProps j.val j.isLt m.val m.isLt).choose_spec.2.1
      rw [(profs (gIdx j m)).gap, hj_eq]
    prime_and_ge_five := by
      rintro ⟨⟨j, i⟩, side⟩
      exact (profs (gIdx j (partOf i))).prime_and_ge_five _
    bounds := by
      rintro ⟨⟨j, i⟩, side⟩
      set g := gIdx j (partOf i)
      have hb := (profs g).bounds ((kIdx j (partOf i), rCast j (partOf i) (remOf i)), side)
      have hcp := hscProps g.val g.isLt
      exact ⟨by rw [← hcp.1]; exact hb.1, le_trans hb.2 hcp.2.2.1⟩
    totalSpanWords := planTotalSpanWords subCerts plan
    stageSpanWords := fun j => planStageSpanWords subCerts plan j.val
    sum_stageSpanWords := by
      rw [planTotalSpanWords, list_range_map_sum, Finset.sum_range]
    stage_span := by
      intro j i₁ i₂
      dsimp [combinedValues]
      set m₁ := partOf i₁
      set m₂ := partOf i₂
      have hrp₁ := (hrouteProps j.val j.isLt m₁.val m₁.isLt).choose_spec
      have hrp₂ := (hrouteProps j.val j.isLt m₂.val m₂.isLt).choose_spec
      set bit₁ := (profs (gIdx j m₁)).bitAt (kIdx j m₁) (rCast j m₁ (remOf i₁))
      set bit₂ := (profs (gIdx j m₂)).bitAt (kIdx j m₂) (rCast j m₂ (remOf i₂))
      have hb₁ : 8192 * scChunkStartWord
          (subCerts[(planRoute plan j.val m₁.val).1]'(hrouteProps j.val j.isLt m₁.val m₁.isLt).1)
          (planRoute plan j.val m₁.val).2 ≤ bit₁ :=
        ((profs (gIdx j m₁)).bit_bounds (kIdx j m₁) (rCast j m₁ (remOf i₁))).1
      have hb₂ : bit₂ < 8192 * (scChunkEndWord
          (subCerts[(planRoute plan j.val m₂.val).1]'(hrouteProps j.val j.isLt m₂.val m₂.isLt).1)
          (planRoute plan j.val m₂.val).2 + 1) :=
        ((profs (gIdx j m₂)).bit_bounds (kIdx j m₂) (rCast j m₂ (remOf i₂))).2
      have hlo_w := hrp₁.2.2.1
      have hhi_w := hrp₂.2.2.2.1
      rw [(profs (gIdx j m₁)).values_low_eq, (profs (gIdx j m₂)).values_low_eq]
      have hc₁ : (subCerts[(gIdx j m₁).val]'(gIdx j m₁).isLt).corrLo = plan.corrLo :=
        (hscProps (gIdx j m₁).val (gIdx j m₁).isLt).1
      have hc₂ : (subCerts[(gIdx j m₂).val]'(gIdx j m₂).isLt).corrLo = plan.corrLo :=
        (hscProps (gIdx j m₂).val (gIdx j m₂).isLt).1
      rw [hc₁, hc₂, hrp₁.2.1, hrp₂.2.1]
      change laneVal plan.corrLo (stageSrcLane j.val) bit₂ -
        laneVal plan.corrLo (stageSrcLane j.val) bit₁ ≤
        planStageSpanWords subCerts plan j.val * 49152
      unfold planStageSpanWords laneVal
      dsimp only
      omega
    windowCaps := plan.windowCaps
    window_cap := by
      intro wc hwc u v hu hvu
      obtain ⟨wIdx, hwIdx, rfl⟩ := List.mem_iff_getElem.mp hwc
      obtain ⟨hw_match, hw_sum⟩ := hwinProps wIdx hwIdx
      have hsub_union :
          (Finset.univ.image combinedValues) ∩ Finset.Ioc u v ⊆
          (Finset.univ : Finset (Fin K)).biUnion (fun g =>
            (Finset.univ.image (profs g).values) ∩ Finset.Ioc u v) := by
        intro y hy
        obtain ⟨himg, hioc⟩ := Finset.mem_inter.mp hy
        obtain ⟨⟨⟨j, i⟩, side⟩, _, rfl⟩ := Finset.mem_image.mp himg
        apply Finset.mem_biUnion.mpr
        refine ⟨gIdx j (partOf i), Finset.mem_univ _, Finset.mem_inter.mpr ⟨?_, hioc⟩⟩
        exact Finset.mem_image.mpr ⟨((kIdx j (partOf i), rCast j (partOf i) (remOf i)), side),
          Finset.mem_univ _, rfl⟩
      have hle_bi : ((Finset.univ.image combinedValues) ∩ Finset.Ioc u v).card ≤
          ∑ g : Fin K, ((Finset.univ.image (profs g).values) ∩ Finset.Ioc u v).card :=
        (Finset.card_le_card hsub_union).trans Finset.card_biUnion_le
      have hterm_le : ∀ g : Fin K,
          ((Finset.univ.image (profs g).values) ∩ Finset.Ioc u v).card ≤
          ((subCerts[g.val]'g.isLt).windowCaps.getD wIdx default).cap := by
        intro g
        have hw_len : wIdx < (subCerts[g.val]'g.isLt).windowCaps.length := by
          rw [(hscProps g.val g.isLt).2.2.2]; exact hwIdx
        set wcg := (subCerts[g.val]'g.isLt).windowCaps[wIdx]'hw_len
        have hgetD_eq : (subCerts[g.val]'g.isLt).windowCaps.getD wIdx default = wcg :=
          list_getD_eq_getElem _ default wIdx hw_len
        rw [hgetD_eq]
        have hm_g := hw_match g.val g.isLt
        rw [hgetD_eq] at hm_g
        have hmem_wcg : wcg ∈ (subCerts[g.val]'g.isLt).windowCaps := List.getElem_mem _
        have hc_g : (subCerts[g.val]'g.isLt).corrLo = plan.corrLo := (hscProps g.val g.isLt).1
        apply (profs g).window_cap wcg hmem_wcg u v
        · rw [hc_g, hm_g.1]; exact hu
        · rw [hm_g.2]; exact hvu
      exact hle_bi.trans ((Finset.sum_le_sum fun g _ => hterm_le g).trans hw_sum)
    octWindowCaps := plan.octWindowCaps
    oct_window_cap := by
      intro wc hwc u v hu hvu
      obtain ⟨hspan1, hmaxWin⟩ := hoctWinProps wc hwc
      set octList := planCombinedOctList subCerts plan
      have hoct_len : octList.length = plan.numOcts := by
        simp [octList, planCombinedOctList]
      set b₀ := (u - plan.corrLo) / 393216
      have hb₀_ge : wc.minWordIdx ≤ b₀ := by omega
      let B_set : Finset ℕ :=
        (Finset.Ico b₀ (b₀ + wc.spanWords)).filter (fun b => b < plan.numOcts)
      have hsub_oct :
          (Finset.univ.image combinedValues) ∩ Finset.Ioc u v ⊆
          B_set.biUnion (fun b =>
            (Finset.univ : Finset (Fin K)).biUnion (fun g =>
              (Finset.univ.image (profs g).values) ∩
                Finset.Ico ((subCerts[g.val]'g.isLt).corrLo + 393216 * b)
                  ((subCerts[g.val]'g.isLt).corrLo + 393216 * (b + 1)))) := by
        intro y hy
        obtain ⟨himg, hioc⟩ := Finset.mem_inter.mp hy
        obtain ⟨⟨⟨j, i⟩, side⟩, _, rfl⟩ := Finset.mem_image.mp himg
        obtain ⟨huy, hyv⟩ := Finset.mem_Ioc.mp hioc
        set g := gIdx j (partOf i)
        set yVal := (profs g).values ((kIdx j (partOf i), rCast j (partOf i) (remOf i)), side)
        have heq_y : combinedValues ((j, i), side) = yVal := rfl
        rw [heq_y] at huy hyv ⊢
        have hby := (profs g).bounds ((kIdx j (partOf i), rCast j (partOf i) (remOf i)), side)
        have hcp := hscProps g.val g.isLt
        have hy_lo : plan.corrLo ≤ yVal := by rw [← hcp.1]; exact hby.1
        have hy_hi : yVal ≤ plan.maxHi := le_trans hby.2 hcp.2.2.1
        set b := (yVal - plan.corrLo) / 393216
        have hb_mem : b ∈ B_set := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_Ico.mpr ⟨by dsimp [b₀, b]; omega, by dsimp [b₀, b]; omega⟩,
            by dsimp [b]; omega⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨b, hb_mem, Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, ?_⟩⟩
        apply Finset.mem_inter.mpr
        refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [hcp.1]
        exact Finset.mem_Ico.mpr ⟨by dsimp [b]; omega, by dsimp [b]; omega⟩
      have hcard_step1 :
          ((Finset.univ.image combinedValues) ∩ Finset.Ioc u v).card ≤
          ∑ b ∈ B_set, ∑ g : Fin K, lookupNat b (subCerts[g.val]'g.isLt).octCounts := by
        calc
          ((Finset.univ.image combinedValues) ∩ Finset.Ioc u v).card
              ≤ ∑ b ∈ B_set, ((Finset.univ : Finset (Fin K)).biUnion (fun g =>
                  (Finset.univ.image (profs g).values) ∩
                    Finset.Ico ((subCerts[g.val]'g.isLt).corrLo + 393216 * b)
                      ((subCerts[g.val]'g.isLt).corrLo + 393216 * (b + 1)))).card :=
            (Finset.card_le_card hsub_oct).trans Finset.card_biUnion_le
          _ ≤ ∑ b ∈ B_set, ∑ g : Fin K,
                ((Finset.univ.image (profs g).values) ∩
                  Finset.Ico ((subCerts[g.val]'g.isLt).corrLo + 393216 * b)
                    ((subCerts[g.val]'g.isLt).corrLo + 393216 * (b + 1))).card :=
            Finset.sum_le_sum fun b _ => Finset.card_biUnion_le
          _ ≤ ∑ b ∈ B_set, ∑ g : Fin K, lookupNat b (subCerts[g.val]'g.isLt).octCounts :=
            Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun g _ => (profs g).oct_used_bound b
      have hsum_le_oct :
          (∑ b ∈ B_set, ∑ g : Fin K, lookupNat b (subCerts[g.val]'g.isLt).octCounts) ≤
          (((octList.drop wc.minWordIdx).drop (b₀ - wc.minWordIdx)).take wc.spanWords).sum := by
        rw [List.drop_drop, Nat.add_sub_of_le hb₀_ge, list_drop_take_sum_eq_Ico_getD,
          ← Finset.sum_filter_add_sum_filter_not (Finset.Ico b₀ (b₀ + wc.spanWords))
            (fun b => b < plan.numOcts)]
        have heq_in : (∑ b ∈ B_set, octList.getD b 0) =
            ∑ b ∈ B_set, ∑ g : Fin K, lookupNat b (subCerts[g.val]'g.isLt).octCounts := by
          apply Finset.sum_congr rfl
          intro b hb
          have hbt : b < plan.numOcts := (Finset.mem_filter.mp hb).2
          have hlt : b < octList.length := by rw [hoct_len]; exact hbt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
          simp only [octList, planCombinedOctList, List.getElem_map, List.getElem_range]
          rw [list_range_map_sum, Finset.sum_range]
          apply Finset.sum_congr rfl
          intro g _
          rw [list_getD_eq_getElem subCerts default g.val g.isLt]
        dsimp [B_set] at heq_in ⊢
        rw [heq_in]
        exact Nat.le_add_right _ _
      have hwin_cap := checkMaxWindowSum_spec (octList.drop wc.minWordIdx)
        wc.spanWords wc.cap (b₀ - wc.minWordIdx) wc.spanWords hmaxWin le_rfl
      omega }

end

end Sude
