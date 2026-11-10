import PASoundness.M236Weakening
import PASoundness.CompactSemantics

/-!
Finite standard-natural definitions in the strict H language. These
metatheoretic finite formulas specialize parameters; the machine itself is
not supplied with a numeral or a preloaded program.
-/
namespace PASoundness.M236Definitions

open PASoundness.M236Game PASoundness.M236Weakening PASoundness.Cantor

def falseCode : Nat := andCode (atomCode 0 0) (notCode (atomCode 0 0))
def orCode (a b : Nat) : Nat := notCode (andCode (notCode a) (notCode b))

theorem false_truth (env : List Nat) : ¬ Truth falseCode env := by
  simp [falseCode, and_truth, not_truth]

theorem or_truth (a b : Nat) (env : List Nat) :
    Truth (orCode a b) env ↔ Truth a env ∨ Truth b env := by
  classical
  simp only [orCode, not_truth, and_truth]
  constructor
  · intro h
    by_cases ha : Truth a env
    · exact Or.inl ha
    · right
      by_contra hb
      exact h ⟨ha, hb⟩
  · rintro (ha | hb) ⟨hna, hnb⟩
    · exact hna ha
    · exact hnb hb

def disj : List Nat → Nat
  | [] => falseCode
  | f :: fs => orCode f (disj fs)

theorem disj_truth (fs : List Nat) (env : List Nat) :
    Truth (disj fs) env ↔ ∃ f ∈ fs, Truth f env := by
  induction fs with
  | nil => simp [disj, false_truth]
  | cons f fs ih => simp [disj, or_truth, ih]

/-- `numeral n i` defines n at positional variable i in the standard
finite-set coding. Its finite recursion visits only bit positions below n. -/
def numeral (n i : Nat) : Nat :=
  allCode (iffCode (atomCode 0 i)
    (disj (List.ofFn fun j : Fin n =>
      if n.testBit j.val then numeral j.val 0 else falseCode)))
termination_by n
decreasing_by exact j.isLt

theorem bit_index_lt (n i : Nat) (h : n.testBit i = true) : i < n := by
  apply PASoundness.CompactSemantics.member_lt n i
  simpa [PASoundness.CompactMatrix.bit_eq_testBit] using h

/-- Every standard natural has a finite strict-H definition with exactly one
relevant positional argument, uniformly under arbitrary surrounding values. -/
theorem numeral_truth (n : Nat) : ∀ (i : Nat) (env : List Nat),
    Truth (numeral n i) env ↔ env.getD i 0 = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i env
    rw [numeral, all_truth]
    simp only [iff_truth, atom_truth, Nat.zero_add, List.getD_cons_zero,
      List.getD_cons_succ]
    have hd (x : Nat) : Truth (disj (List.ofFn fun j : Fin n =>
        if n.testBit j.val then numeral j.val 0 else falseCode)) (x :: env) ↔
        n.testBit x = true := by
      rw [disj_truth]
      simp only [List.mem_ofFn]
      constructor
      · rintro ⟨f, ⟨j, rfl⟩, hf⟩
        by_cases hj : n.testBit j.val = true
        · simp only [hj, if_true] at hf
          have he := (ih j.val j.isLt 0 (x :: env)).mp hf
          simp only [List.getD_cons_zero] at he
          rw [he]
          exact hj
        · have hj0 : n.testBit j.val = false := Bool.eq_false_iff.mpr hj
          simp only [hj0, Bool.false_eq_true, if_false] at hf
          exact False.elim (false_truth _ hf)
      · intro hx
        let j : Fin n := ⟨x, bit_index_lt n x hx⟩
        refine ⟨numeral x 0, ⟨j, ?_⟩, ?_⟩
        · simp [j, hx]
        · exact (ih x j.isLt 0 (x :: env)).mpr rfl
    simp_rw [hd]
    constructor
    · intro hbits
      apply Nat.eq_of_testBit_eq
      intro x
      have hh := hbits x
      cases ha : (env.getD i 0).testBit x <;> cases hb : n.testBit x <;> simp_all
    · intro he x
      rw [he]

def Agree (n : Nat) (left right : List Nat) : Prop :=
  ∀ i, i < n → left.getD i 0 = right.getD i 0

theorem agree_cons {n m : Nat} {left right : List Nat} (h : Agree n left right)
    (v : Nat) (hm : m ≤ n + 1) : Agree m (v :: left) (v :: right) := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => simpa using h i (by omega)

theorem atom_index_bounds (f : Nat) :
    (unpair (payload f)).1 < f + 2 ∧
    (unpair (payload f)).1 + (unpair (payload f)).2 + 1 < f + 2 := by
  have hpair := PASoundness.Cantor.pair_unpair (payload f)
  have htri := PASoundness.Cantor.triangle_ge
    ((unpair (payload f)).1 + (unpair (payload f)).2)
  have hp : payload f ≤ f := PASoundness.Cantor.unpair_snd_le f
  simp only [PASoundness.Cantor.pair] at hpair
  omega

/-- A code f cannot inspect beyond its first f+2 environment positions.
The bound is uniform in all future bound values. -/
theorem truth_agrees (f : Nat) : ∀ left right : List Nat,
    Agree (f+2) left right → (Truth f left ↔ Truth f right) := by
  induction f using Nat.strong_induction_on with
  | h f ih =>
    intro left right ha
    by_cases ht : tag f = 0
    · conv_lhs => rw [Truth, dif_pos ht]
      conv_rhs => rw [Truth, dif_pos ht]
      simp only [atom]
      have hb := atom_index_bounds f
      rw [ha _ hb.1, ha _ hb.2]
    · conv_lhs => rw [Truth, dif_neg ht]
      conv_rhs => rw [Truth, dif_neg ht]
      have hl := (children_lt f ht).1
      have hr := (children_lt f ht).2
      apply or_congr
      · exact not_congr (ih _ hl _ _ (agree_cons ha 0 (by omega)))
      · apply exists_congr
        intro x
        exact not_congr (ih _ hr _ _ (agree_cons ha x (by omega)))

/-- Existentially bind one fixed natural using its finite defining formula. -/
def bindValue (value body : Nat) : Nat :=
  existsCode (andCode (numeral value 0) body)

theorem bindValue_truth (value body : Nat) (env : List Nat) :
    Truth (bindValue value body) env ↔ Truth body (value :: env) := by
  rw [bindValue, exists_truth]
  simp only [and_truth, numeral_truth, List.getD_cons_zero]
  constructor
  · rintro ⟨x, rfl, h⟩
    exact h
  · intro h
    exact ⟨value, rfl, h⟩

/-- Bind a whole finite list in reverse introduction order, producing the
original left-to-right positional environment. -/
def bindValues : List Nat → Nat → Nat
  | [], body => body
  | value :: rest, body => bindValues rest (bindValue value body)

theorem bindValues_truth (values : List Nat) (body : Nat) (env : List Nat) :
    Truth (bindValues values body) env ↔ Truth body (values ++ env) := by
  induction values generalizing body with
  | nil => rfl
  | cons v rest ih =>
    simp only [bindValues, ih, bindValue_truth, List.cons_append]

/-- Copy the old coordinate at offset k to the front using an equality
witness. This handles arbitrary values without a literal object-language term. -/
def copyCoordinate (k body : Nat) : Nat :=
  existsCode (andCode (equalCode 0 (k + 1)) body)

theorem copyCoordinate_truth (k body : Nat) (env : List Nat) :
    Truth (copyCoordinate k body) env ↔ Truth body (env.getD k 0 :: env) := by
  rw [copyCoordinate, exists_truth]
  simp only [and_truth, equal_truth, List.getD_cons_zero, List.getD_cons_succ]
  constructor
  · rintro ⟨x, rfl, h⟩
    exact h
  · intro h
    exact ⟨env.getD k 0, rfl, h⟩

/-- Read a fixed finite prefix of an environment, including implicit zero
entries beyond its explicit tail. -/
def materialize (n : Nat) (env : List Nat) : List Nat :=
  List.ofFn fun i : Fin n => env.getD i.val 0

@[simp] theorem materialize_length (n : Nat) (env : List Nat) :
    (materialize n env).length = n := by simp [materialize]

theorem materialize_getD (n : Nat) (env : List Nat) (i : Nat) (hi : i < n) :
    (materialize n env).getD i 0 = env.getD i 0 := by
  simp [materialize, List.getD_eq_getElem?_getD, hi]

/-- Finite parameter specialization for a unary predicate. All required
parameters are introduced by formulas, then y is copied ahead of them. -/
def specialize (f : Nat) (params : List Nat) : Nat :=
  bindValues (materialize (f+2) params) (copyCoordinate (f+2) f)

theorem specialize_truth (f : Nat) (params : List Nat) (y : Nat) :
    Truth (specialize f params) [y] ↔ Truth f (y :: params) := by
  let values := materialize (f+2) params
  have hlen : values.length = f+2 := by simp [values]
  have hy : (values ++ [y]).getD (f+2) 0 = y := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hlen]
  have ha : Agree (f+2) (y :: (values ++ [y])) (y :: params) := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.getD_cons_succ]
      have hib : i < f+2 := by omega
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact materialize_getD (f+2) params i hib
  change Truth (bindValues values (copyCoordinate (f+2) f)) [y] ↔ _
  rw [bindValues_truth, copyCoordinate_truth, hy]
  exact truth_agrees f _ _ ha

theorem signed_iff_bit (f : Nat) (env : List Nat) (b : Bool) :
    Signed f env (!b) ↔ (b = true ↔ Truth f env) := by
  cases b <;> simp [Signed]

/-- The original finite-support family, including arbitrary finite parameter
environments and the requirement that no bit outside support is set. -/
def ParameterSupportFamily : Prop :=
  ∀ (f : Nat) (params : List Nat) (support : Nat), ∃ code : Nat,
    ∀ y : Nat, code.testBit y = true ↔
      support.testBit y = true ∧ Truth f (y :: params)

/-- Unary initial-segment tables and arbitrary parameterized support tables
are equivalent. This proof constructs a formula for each fixed parameter
list and never exchanges finite witnesses across ranks. -/
theorem finiteTables_iff_parameterSupport : FiniteTableFamily ↔ ParameterSupportFamily := by
  constructor
  · intro h f params support
    obtain ⟨code, hc⟩ := h (specialize f params) support
    refine ⟨code &&& support, ?_⟩
    intro y
    rw [Nat.testBit_land, Bool.and_eq_true]
    constructor
    · rintro ⟨hcode, hsupport⟩
      have hy : y ≤ support := Nat.le_of_lt (bit_index_lt support y hsupport)
      have he := (signed_iff_bit (specialize f params) [y] _).mp (hc y hy)
      exact ⟨hsupport, (specialize_truth f params y).mp (he.mp hcode)⟩
    · rintro ⟨hsupport, htruth⟩
      have hy : y ≤ support := Nat.le_of_lt (bit_index_lt support y hsupport)
      have he := (signed_iff_bit (specialize f params) [y] _).mp (hc y hy)
      exact ⟨he.mpr ((specialize_truth f params y).mpr htruth), hsupport⟩
  · intro h f A
    obtain ⟨code, hc⟩ := h f [] (2^(A+1)-1)
    refine ⟨code, ?_⟩
    intro y hy
    have hsupport : (2^(A+1)-1).testBit y = true := by
      rw [Nat.testBit_two_pow_sub_one]
      simp [show y < A+1 by omega]
    apply (signed_iff_bit f [y] _).mpr
    simpa using (hc y).trans (by simp [hsupport])

/-- All ranks of the selected mathematical source capture arbitrary finite
parameters and support in its strict H language. Physical correspondence and
compact/PA syntax and proof transport remain separate obligations. -/
theorem source_accept_iff_parameterSupport :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      ParameterSupportFamily :=
  selected_source_accept_iff_finite_tables.trans finiteTables_iff_parameterSupport

def ParityParameterSupportFamily : Prop :=
  ∀ (f : Nat) (params : List Nat) (support : Nat), ∃ code : Nat,
    ∀ y : Nat, code.testBit y = true ↔
      support.testBit y = true ∧ parityTruth f (y :: params)

theorem parameterSupport_iff_parity :
    ParameterSupportFamily ↔ ParityParameterSupportFamily := by
  constructor
  · intro h f params support
    obtain ⟨code, hc⟩ := h (toStrict (parityToCantor f)) params support
    refine ⟨code, fun y => ?_⟩
    have ht := (toStrict_truth (parityToCantor f) (y :: params)).trans
      (parityToCantor_truth f (y :: params))
    exact (hc y).trans (and_congr Iff.rfl ht)
  · intro h f params support
    obtain ⟨code, hc⟩ := h (cantorToParity (toUnrestricted f)) params support
    refine ⟨code, fun y => ?_⟩
    have ht := (cantorToParity_truth (toUnrestricted f) (y :: params)).trans
      (toUnrestricted_truth f (y :: params))
    exact (hc y).trans (and_congr Iff.rfl ht)

/-- Full all-rank finite-parameter support equivalence between the selected
mathematical source and the predecessor parity H language. This theorem does
not claim a compact-calculus proof transport or physical implementation. -/
theorem source_accept_iff_parityParameterSupport :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      ParityParameterSupportFamily :=
  source_accept_iff_parameterSupport.trans parameterSupport_iff_parity

/-- A nonzero Cantor-paired environment has a strictly smaller tail. -/
theorem environment_tail_lt (e : Nat) (he : e ≠ 0) : (unpair e).2 < e := by
  have hp := pair_unpair e
  have ht := triangle_ge ((unpair e).1 + (unpair e).2)
  have hb := unpair_snd_le e
  simp only [pair] at hp
  omega

/-- Decode the actual sentinel-zero positional environment representation.
Trailing zero values may be omitted because every absent coordinate defaults
to zero. -/
def unpackEnv (e : Nat) : List Nat :=
  if h : e = 0 then [] else (unpair e).1 :: unpackEnv (unpair e).2
termination_by e
decreasing_by exact environment_tail_lt e h

theorem unpack_represented (e : Nat) : Represents e (unpackEnv e) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · subst e
      simpa [unpackEnv] using represents_empty
    · rw [unpackEnv, dif_neg he]
      have hr := represents_cons (ih (unpair e).2 (environment_tail_lt e he)) (unpair e).1
      rw [pair_unpair] at hr
      exact hr

def packEnv : List Nat → Nat
  | [] => 0
  | x :: xs => pair x (packEnv xs)

theorem pack_represented (env : List Nat) : Represents (packEnv env) env := by
  induction env with
  | nil => exact represents_empty
  | cons x xs ih => exact represents_cons ih x

theorem unpack_pack_agrees (env : List Nat) (i : Nat) :
    (unpackEnv (packEnv env)).getD i 0 = env.getD i 0 := by
  have hu := unpack_represented (packEnv env) i
  have hp := pack_represented env i
  exact hu.symm.trans hp

/-- Even if a zero pair collapses an explicitly stored zero, all formulas are
insensitive to the omitted default-zero tail. -/
theorem parityTruth_unpacked (f y : Nat) (params : List Nat) :
    parityTruth f (y :: unpackEnv (packEnv params)) ↔ parityTruth f (y :: params) := by
  let q := toStrict (parityToCantor f)
  have ht1 : Truth q (y :: unpackEnv (packEnv params)) ↔
      parityTruth f (y :: unpackEnv (packEnv params)) :=
    (toStrict_truth _ _).trans (parityToCantor_truth _ _)
  have ht2 : Truth q (y :: params) ↔ parityTruth f (y :: params) :=
    (toStrict_truth _ _).trans (parityToCantor_truth _ _)
  have ha : Agree (q+2) (y :: unpackEnv (packEnv params)) (y :: params) := by
    intro i _
    cases i with
    | zero => rfl
    | succ i => simpa using unpack_pack_agrees params i
  exact ht1.symm.trans ((truth_agrees q _ _ ha).trans ht2)

/-- The support family with an arbitrary numerical initial environment,
matching the source's actual nested-pair representation. -/
def ParityEncodedSupportFamily : Prop :=
  ∀ (f e support : Nat), ∃ code : Nat, ∀ y : Nat,
    code.testBit y = true ↔ support.testBit y = true ∧ parityTruth f (y :: unpackEnv e)

theorem paritySupport_iff_encoded :
    ParityParameterSupportFamily ↔ ParityEncodedSupportFamily := by
  constructor
  · intro h f e support
    exact h f (unpackEnv e) support
  · intro h f params support
    obtain ⟨code, hc⟩ := h f (packEnv params) support
    refine ⟨code, fun y => ?_⟩
    exact (hc y).trans (and_congr Iff.rfl (parityTruth_unpacked f y params))

theorem source_accept_iff_encodedSupport :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      ParityEncodedSupportFamily :=
  source_accept_iff_parityParameterSupport.trans paritySupport_iff_encoded

/-- Parity-H truth is invariant under environments with identical lookups,
including different representations of the default-zero tail. -/
theorem parityTruth_congr (f : Nat) (left right : List Nat)
    (h : ∀ i, left.getD i 0 = right.getD i 0) :
    parityTruth f left ↔ parityTruth f right := by
  let q := toStrict (parityToCantor f)
  have hl : Truth q left ↔ parityTruth f left :=
    (toStrict_truth _ _).trans (parityToCantor_truth _ _)
  have hr : Truth q right ↔ parityTruth f right :=
    (toStrict_truth _ _).trans (parityToCantor_truth _ _)
  exact hl.symm.trans ((truth_agrees q left right (fun i _ => h i)).trans hr)

/-- The old support convention obtains the support from the first value of
the packed parameter environment. -/
def OldSupportFamily : Prop :=
  ∀ (f e : Nat), ∃ code : Nat, ∀ y : Nat,
    code.testBit y = true ↔
      (lookup e 0).testBit y = true ∧ parityTruth f (y :: unpackEnv e)

/-- Adding a support coordinate is compensated by a capture-aware
weakening behind y. No parameter, value or binder depth is bounded. -/
theorem encodedSupport_iff_old : ParityEncodedSupportFamily ↔ OldSupportFamily := by
  constructor
  · intro h f e
    exact h f e (lookup e 0)
  · intro h f e support
    let q := toStrict (parityToCantor f)
    let q' := cantorToParity (toUnrestricted (weaken q 1))
    obtain ⟨code, hc⟩ := h q' (pair support e)
    refine ⟨code, fun y => ?_⟩
    have henv : ∀ i, (unpackEnv (pair support e)).getD i 0 =
        (support :: unpackEnv e).getD i 0 := by
      intro i
      have h1 := unpack_represented (pair support e) i
      have h2 := represents_cons (unpack_represented e) support i
      exact h1.symm.trans h2
    have henv' : ∀ i, (y :: unpackEnv (pair support e)).getD i 0 =
        (y :: support :: unpackEnv e).getD i 0 := by
      intro i
      cases i with
      | zero => rfl
      | succ i => simpa using henv i
    have hw : Truth (weaken q 1) (y :: support :: unpackEnv e) ↔
        Truth q (y :: unpackEnv e) :=
      weaken_truth q 1 _ _ (compatible_cons (compatible_front support (unpackEnv e)) y)
    have ht : parityTruth q' (y :: unpackEnv (pair support e)) ↔
        parityTruth f (y :: unpackEnv e) := by
      calc
        _ ↔ parityTruth q' (y :: support :: unpackEnv e) := parityTruth_congr _ _ _ henv'
        _ ↔ Truth (weaken q 1) (y :: support :: unpackEnv e) :=
          (cantorToParity_truth _ _).trans (toUnrestricted_truth _ _)
        _ ↔ Truth q (y :: unpackEnv e) := hw
        _ ↔ parityTruth f (y :: unpackEnv e) :=
          (toStrict_truth _ _).trans (parityToCantor_truth _ _)
    have hs : lookup (pair support e) 0 = support := by simp [lookup_pair]
    simpa only [hs] using (hc y).trans (and_congr Iff.rfl ht)

/-- Structural bridge from the selected fair record source to the earlier
parameterized packed-environment support family. -/
theorem source_accept_iff_oldSupport :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      OldSupportFamily :=
  source_accept_iff_encodedSupport.trans encodedSupport_iff_old

/-- The predecessor support-only convention allows extra true bits outside
the support; it requires no bit of C to select a false predicate. -/
def OriginalSupportFamily : Prop :=
  ∀ (f e : Nat), ∃ code : Nat, ∀ y : Nat,
    (code.testBit y = true → parityTruth f (y :: unpackEnv e)) ∧
    ((lookup e 0).testBit y = true → parityTruth f (y :: unpackEnv e) →
      code.testBit y = true)

/-- Masking by the support turns the predecessor's two implications into an
exact intersection, without changing any supported bit. -/
theorem oldSupport_iff_original : OldSupportFamily ↔ OriginalSupportFamily := by
  constructor
  · intro h f e
    obtain ⟨code, hc⟩ := h f e
    refine ⟨code, fun y => ?_⟩
    constructor
    · intro hy
      exact ((hc y).mp hy).2
    · intro hs hp
      exact (hc y).mpr ⟨hs, hp⟩
  · intro h f e
    obtain ⟨code, hc⟩ := h f e
    refine ⟨code &&& lookup e 0, fun y => ?_⟩
    rw [Nat.testBit_land, Bool.and_eq_true]
    constructor
    · rintro ⟨hb, hs⟩
      exact ⟨hs, (hc y).1 hb⟩
    · rintro ⟨hs, hp⟩
      exact ⟨(hc y).2 hs hp, hs⟩

theorem source_accept_iff_originalSupport :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      OriginalSupportFamily :=
  source_accept_iff_oldSupport.trans oldSupport_iff_original

/-- The predecessor pointed support condition includes the additional point
in the second environment position. -/
def PointedSupportFamily : Prop :=
  ∀ (f e : Nat), ∃ code : Nat, ∀ y : Nat,
    (code.testBit y = true → parityTruth f (y :: unpackEnv e)) ∧
    (((lookup e 0).testBit y = true ∨ y = lookup e 1) →
      parityTruth f (y :: unpackEnv e) → code.testBit y = true)

/-- A finite bitwise union installs the distinguished point as support.
The predicate's original environment remains unchanged. -/
theorem originalSupport_iff_pointed : OriginalSupportFamily ↔ PointedSupportFamily := by
  constructor
  · intro h f e
    have hh : ParityEncodedSupportFamily :=
      encodedSupport_iff_old.mpr (oldSupport_iff_original.mpr h)
    let support := lookup e 0 ||| 2^(lookup e 1)
    obtain ⟨code, hc⟩ := hh f e support
    refine ⟨code, fun y => ?_⟩
    have hs : support.testBit y = true ↔
        (lookup e 0).testBit y = true ∨ y = lookup e 1 := by
      simp only [support, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow,
        decide_eq_true_eq]
      exact or_congr Iff.rfl eq_comm
    constructor
    · intro hy
      exact ((hc y).mp hy).2
    · intro hy hp
      exact (hc y).mpr ⟨hs.mpr hy, hp⟩
  · intro h f e
    obtain ⟨code, hc⟩ := h f e
    exact ⟨code, fun y => ⟨(hc y).1,
      fun hs hp => (hc y).2 (Or.inl hs) hp⟩⟩

theorem source_accept_iff_pointedSupport :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      PointedSupportFamily :=
  source_accept_iff_originalSupport.trans originalSupport_iff_pointed

end PASoundness.M236Definitions
