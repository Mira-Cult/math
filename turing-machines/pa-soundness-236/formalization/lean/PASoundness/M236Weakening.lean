import PASoundness.M236Game

/-!
Capture-aware weakening for the strict-ordered atom language. This is a
syntax/truth bridge in the Lean metatheory; no machine implementation or
translation of arbitrary compact formulas is asserted here.
-/
namespace PASoundness.M236Weakening

open PASoundness.Cantor PASoundness.M236Game

def atomCode (j gap : Nat) : Nat := pair 0 (pair j gap)
def hCode (a b : Nat) : Nat := pair (a + 1) b

def shift (cutoff i : Nat) : Nat := if cutoff ≤ i then i + 1 else i

theorem shift_strict (cutoff : Nat) {i j : Nat} (h : i < j) :
    shift cutoff i < shift cutoff j := by
  unfold shift
  split <;> split <;> omega

/-- The new environment agrees after insertion of one value at the cutoff. -/
def Compatible (cutoff : Nat) (new old : List Nat) : Prop :=
  ∀ i, new.getD (shift cutoff i) 0 = old.getD i 0

theorem shift_succ (k i : Nat) : shift (k+1) (i+1) = shift k i + 1 := by
  unfold shift
  split <;> split <;> omega

theorem compatible_cons {k : Nat} {new old : List Nat} (h : Compatible k new old) (v : Nat) :
    Compatible (k+1) (v :: new) (v :: old) := by
  intro i
  cases i with
  | zero => simp [shift]
  | succ i => simpa [shift_succ] using h i

theorem atom_truth (j gap : Nat) (env : List Nat) :
    Truth (atomCode j gap) env ↔
      (env.getD (j + gap + 1) 0).testBit (env.getD j 0) = true := by
  rw [Truth]
  simp [atomCode, tag, payload, atom]

theorem h_truth (a b : Nat) (env : List Nat) :
    Truth (hCode a b) env ↔ ¬ Truth a (0 :: env) ∨ ∃ x, ¬ Truth b (x :: env) := by
  rw [Truth]
  simp [hCode, tag, payload]

/-- Insert a fresh positional coordinate. At both H children the cutoff
increases, since both bind one value. -/
def weaken (f cutoff : Nat) : Nat :=
  if h : tag f = 0 then
    let j := (unpair (payload f)).1
    let gap := (unpair (payload f)).2
    let newJ := shift cutoff j
    let newI := shift cutoff (j + gap + 1)
    atomCode newJ (newI - newJ - 1)
  else
    hCode (weaken (tag f - 1) (cutoff + 1)) (weaken (payload f) (cutoff + 1))
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

/-- Weakening preserves truth under every environment insertion, including
parameters crossing a binder cutoff and arbitrarily deep H formulas. -/
theorem weaken_truth (f : Nat) : ∀ (k : Nat) (new old : List Nat),
    Compatible k new old → (Truth (weaken f k) new ↔ Truth f old) := by
  induction f using Nat.strong_induction_on with
  | h f ih =>
    intro k new old hc
    by_cases ht : tag f = 0
    · rw [weaken, dif_pos ht, atom_truth]
      conv_rhs => rw [Truth, dif_pos ht]
      simp only [atom]
      have hi : shift k (unpair (payload f)).1 <
          shift k ((unpair (payload f)).1 + (unpair (payload f)).2 + 1) :=
        shift_strict k (by omega)
      have heq : shift k (unpair (payload f)).1 +
          (shift k ((unpair (payload f)).1 + (unpair (payload f)).2 + 1) -
            shift k (unpair (payload f)).1 - 1) + 1 =
              shift k ((unpair (payload f)).1 + (unpair (payload f)).2 + 1) := by omega
      rw [heq, hc _, hc _]
    · rw [weaken, dif_neg ht, h_truth]
      conv_rhs => rw [Truth, dif_neg ht]
      apply or_congr
      · exact not_congr (ih (tag f - 1) (children_lt f ht).1 _ _ _ (compatible_cons hc 0))
      · apply exists_congr
        intro x
        exact not_congr (ih (payload f) (children_lt f ht).2 _ _ _ (compatible_cons hc x))

theorem compatible_front (v : Nat) (env : List Nat) : Compatible 0 (v :: env) env := by
  intro i
  simp [shift]

/-- The common outer lift makes a formula independent of the new head value. -/
theorem lift_truth (f : Nat) (v : Nat) (env : List Nat) :
    Truth (weaken f 0) (v :: env) ↔ Truth f env :=
  weaken_truth f 0 (v :: env) env (compatible_front v env)

def nandCode (a b : Nat) : Nat := hCode (weaken a 0) (weaken b 0)
def notCode (a : Nat) : Nat := nandCode a a
def andCode (a b : Nat) : Nat := notCode (nandCode a b)
def allCode (a : Nat) : Nat := notCode (hCode a a)
def existsCode (a : Nat) : Nat := hCode (notCode a) (notCode a)

theorem nand_truth (a b : Nat) (env : List Nat) :
    Truth (nandCode a b) env ↔ ¬ Truth a env ∨ ¬ Truth b env := by
  rw [nandCode, h_truth]
  simp only [lift_truth]
  simp

theorem not_truth (a : Nat) (env : List Nat) :
    Truth (notCode a) env ↔ ¬ Truth a env := by
  simp [notCode, nand_truth]

theorem and_truth (a b : Nat) (env : List Nat) :
    Truth (andCode a b) env ↔ Truth a env ∧ Truth b env := by
  classical
  simp [andCode, not_truth, nand_truth]

theorem all_truth (a : Nat) (env : List Nat) :
    Truth (allCode a) env ↔ ∀ x, Truth a (x :: env) := by
  classical
  simp only [allCode, not_truth, h_truth, not_or, not_not, not_exists]
  constructor
  · exact And.right
  · intro h
    exact ⟨h 0, h⟩

theorem exists_truth (a : Nat) (env : List Nat) :
    Truth (existsCode a) env ↔ ∃ x, Truth a (x :: env) := by
  classical
  simp only [existsCode, h_truth, not_truth, not_not]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact h
  · intro h
    exact Or.inr h

def impCode (a b : Nat) : Nat := nandCode a (notCode b)
def iffCode (a b : Nat) : Nat := andCode (impCode a b) (impCode b a)

theorem imp_truth (a b : Nat) (env : List Nat) :
    Truth (impCode a b) env ↔ (Truth a env → Truth b env) := by
  classical
  rw [impCode, nand_truth, not_truth]
  constructor
  · rintro (ha | hb) h
    · exact False.elim (ha h)
    · exact Classical.byContradiction hb
  · intro h
    by_cases ha : Truth a env
    · exact Or.inr (fun hn => hn (h ha))
    · exact Or.inl ha

theorem iff_truth (a b : Nat) (env : List Nat) :
    Truth (iffCode a b) env ↔ (Truth a env ↔ Truth b env) := by
  simp [iffCode, and_truth, imp_truth, iff_def]

/-- Equality of two old positional variables, expressed solely by strictly
ordered atoms under a fresh universally quantified element. -/
def equalCode (i j : Nat) : Nat :=
  allCode (iffCode (atomCode 0 i) (atomCode 0 j))

theorem equal_truth (i j : Nat) (env : List Nat) :
    Truth (equalCode i j) env ↔ env.getD i 0 = env.getD j 0 := by
  rw [equalCode, all_truth]
  simp only [iff_truth, atom_truth]
  have he : (∀ x, (env.getD i 0).testBit x = true ↔
      (env.getD j 0).testBit x = true) ↔ env.getD i 0 = env.getD j 0 := by
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro x
      have hx := h x
      cases ha : (env.getD i 0).testBit x <;>
        cases hb : (env.getD j 0).testBit x <;> simp_all
    · intro h x
      rw [h]
  simpa using he

/-- An unrestricted membership atom is represented by one fresh variable z,
equality of z with the original element, and a strict atom for the container
and z. This also covers self-membership and older/younger index reversals. -/
def memberCode (i j : Nat) : Nat :=
  existsCode (andCode (equalCode 0 (j + 1)) (atomCode 0 i))

theorem member_truth (i j : Nat) (env : List Nat) :
    Truth (memberCode i j) env ↔ (env.getD i 0).testBit (env.getD j 0) = true := by
  rw [memberCode, exists_truth]
  simp only [and_truth, equal_truth, atom_truth, Nat.zero_add,
    List.getD_cons_zero, List.getD_cons_succ]
  constructor
  · rintro ⟨z, rfl, hb⟩
    exact hb
  · intro hb
    exact ⟨env.getD j 0, rfl, hb⟩

/-- The unrestricted Cantor-tagged H language, with an arbitrary pair of
membership operands at each atom. It shares the selected binding convention. -/
def unrestrictedTruth (f : Nat) (env : List Nat) : Prop :=
  if h : tag f = 0 then
    (env.getD (unpair (payload f)).1 0).testBit
      (env.getD (unpair (payload f)).2 0) = true
  else ¬ unrestrictedTruth (tag f - 1) (0 :: env) ∨
    ∃ x, ¬ unrestrictedTruth (payload f) (x :: env)
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

/-- Translate every unrestricted atom through a fresh equality witness, and
recurse through both binding children. No translation is run by the machine. -/
def toStrict (f : Nat) : Nat :=
  if h : tag f = 0 then
    memberCode (unpair (payload f)).1 (unpair (payload f)).2
  else hCode (toStrict (tag f - 1)) (toStrict (payload f))
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

/-- Truth preservation holds for arbitrary environments and every finite code;
formula size, variable positions, values and traversal depth are unbounded. -/
theorem toStrict_truth (f : Nat) (env : List Nat) :
    Truth (toStrict f) env ↔ unrestrictedTruth f env := by
  induction f using Nat.strong_induction_on generalizing env with
  | h f ih =>
    by_cases ht : tag f = 0
    · rw [toStrict, dif_pos ht, member_truth]
      conv_rhs => rw [unrestrictedTruth, dif_pos ht]
    · rw [toStrict, dif_neg ht, h_truth]
      conv_rhs => rw [unrestrictedTruth, dif_neg ht]
      exact or_congr
        (not_congr (ih _ (children_lt f ht).1 _))
        (exists_congr fun x => not_congr (ih _ (children_lt f ht).2 _))

theorem unrestricted_atom_truth (i j : Nat) (env : List Nat) :
    unrestrictedTruth (pair 0 (pair i j)) env ↔
      (env.getD i 0).testBit (env.getD j 0) = true := by
  rw [unrestrictedTruth]
  simp [tag, payload]

theorem unrestricted_h_truth (a b : Nat) (env : List Nat) :
    unrestrictedTruth (hCode a b) env ↔
      ¬ unrestrictedTruth a (0 :: env) ∨ ∃ x, ¬ unrestrictedTruth b (x :: env) := by
  rw [unrestrictedTruth]
  simp [hCode, tag, payload]

/-- Every selected strict atom has a direct unrestricted origin. -/
def toUnrestricted (f : Nat) : Nat :=
  if h : tag f = 0 then
    let j := (unpair (payload f)).1
    let gap := (unpair (payload f)).2
    pair 0 (pair (j + gap + 1) j)
  else hCode (toUnrestricted (tag f - 1)) (toUnrestricted (payload f))
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

theorem toUnrestricted_truth (f : Nat) (env : List Nat) :
    unrestrictedTruth (toUnrestricted f) env ↔ Truth f env := by
  induction f using Nat.strong_induction_on generalizing env with
  | h f ih =>
    by_cases ht : tag f = 0
    · rw [toUnrestricted, dif_pos ht, unrestricted_atom_truth]
      conv_rhs => rw [Truth, dif_pos ht]
      rfl
    · rw [toUnrestricted, dif_neg ht, unrestricted_h_truth]
      conv_rhs => rw [Truth, dif_neg ht]
      exact or_congr
        (not_congr (ih _ (children_lt f ht).1 _))
        (exists_congr fun x => not_congr (ih _ (children_lt f ht).2 _))

def UnrestrictedSigned (f : Nat) (env : List Nat) (negative : Bool) : Prop :=
  if negative then ¬ unrestrictedTruth f env else unrestrictedTruth f env

theorem signed_toStrict (f : Nat) (env : List Nat) (negative : Bool) :
    Signed (toStrict f) env negative ↔ UnrestrictedSigned f env negative := by
  cases negative <;> simp [Signed, UnrestrictedSigned, toStrict_truth]

theorem signed_toUnrestricted (f : Nat) (env : List Nat) (negative : Bool) :
    UnrestrictedSigned (toUnrestricted f) env negative ↔ Signed f env negative := by
  cases negative <;> simp [Signed, UnrestrictedSigned, toUnrestricted_truth]

def UnrestrictedFiniteTables : Prop :=
  ∀ f A : Nat, ∃ c : Nat, ∀ y : Nat, y ≤ A →
    UnrestrictedSigned f [y] (!(c.testBit y))

/-- Strict and unrestricted Cantor-tagged H syntax have the same full finite
table family. Each translated code and each bound has its own witness. -/
theorem finiteTables_iff_unrestricted : FiniteTableFamily ↔ UnrestrictedFiniteTables := by
  constructor
  · intro h f A
    obtain ⟨c, hc⟩ := h (toStrict f) A
    exact ⟨c, fun y hy => (signed_toStrict f [y] _).mp (hc y hy)⟩
  · intro h f A
    obtain ⟨c, hc⟩ := h (toUnrestricted f) A
    exact ⟨c, fun y hy => (signed_toUnrestricted f [y] _).mp (hc y hy)⟩

/-- The structural all-rank source result extends to the unrestricted H
finite-table family, without using PA or compact-calculus soundness. -/
theorem source_accept_iff_unrestricted_tables :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      UnrestrictedFiniteTables :=
  selected_source_accept_iff_finite_tables.trans finiteTables_iff_unrestricted

/-- The predecessor H syntax used parity tags. Both children of an odd
code are smaller than the parent; zero is an ordinary unrestricted atom. -/
theorem parity_children_lt (f : Nat) (h : f % 2 ≠ 0) :
    (unpair (f / 2)).1 < f ∧ (unpair (f / 2)).2 < f := by
  have hleft := unpair_fst_le (f / 2)
  have hright := unpair_snd_le (f / 2)
  omega

def parityTruth (f : Nat) (env : List Nat) : Prop :=
  if h : f % 2 = 0 then
    (env.getD (unpair (f / 2)).1 0).testBit
      (env.getD (unpair (f / 2)).2 0) = true
  else ¬ parityTruth (unpair (f / 2)).1 (0 :: env) ∨
    ∃ x, ¬ parityTruth (unpair (f / 2)).2 (x :: env)
termination_by f
decreasing_by
  · exact (parity_children_lt f h).1
  · exact (parity_children_lt f h).2

def parityToCantor (f : Nat) : Nat :=
  if h : f % 2 = 0 then pair 0 (f / 2)
  else hCode (parityToCantor (unpair (f / 2)).1)
    (parityToCantor (unpair (f / 2)).2)
termination_by f
decreasing_by
  · exact (parity_children_lt f h).1
  · exact (parity_children_lt f h).2

theorem parityToCantor_truth (f : Nat) (env : List Nat) :
    unrestrictedTruth (parityToCantor f) env ↔ parityTruth f env := by
  induction f using Nat.strong_induction_on generalizing env with
  | h f ih =>
    by_cases hp : f % 2 = 0
    · rw [parityToCantor, dif_pos hp]
      conv_rhs => rw [parityTruth, dif_pos hp]
      rw [unrestrictedTruth]
      simp [tag, payload]
    · rw [parityToCantor, dif_neg hp, unrestricted_h_truth]
      conv_rhs => rw [parityTruth, dif_neg hp]
      exact or_congr
        (not_congr (ih _ (parity_children_lt f hp).1 _))
        (exists_congr fun x => not_congr (ih _ (parity_children_lt f hp).2 _))

theorem parity_atom_truth (i j : Nat) (env : List Nat) :
    parityTruth (2 * pair i j) env ↔
      (env.getD i 0).testBit (env.getD j 0) = true := by
  rw [parityTruth]
  simp

theorem parity_h_truth (a b : Nat) (env : List Nat) :
    parityTruth (2 * pair a b + 1) env ↔
      ¬ parityTruth a (0 :: env) ∨ ∃ x, ¬ parityTruth b (x :: env) := by
  rw [parityTruth]
  have hd : (2 * pair a b + 1) / 2 = pair a b := by omega
  simp [hd]

def cantorToParity (f : Nat) : Nat :=
  if h : tag f = 0 then 2 * payload f
  else 2 * pair (cantorToParity (tag f - 1)) (cantorToParity (payload f)) + 1
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

theorem cantorToParity_truth (f : Nat) (env : List Nat) :
    parityTruth (cantorToParity f) env ↔ unrestrictedTruth f env := by
  induction f using Nat.strong_induction_on generalizing env with
  | h f ih =>
    by_cases ht : tag f = 0
    · rw [cantorToParity, dif_pos ht, parityTruth]
      conv_rhs => rw [unrestrictedTruth, dif_pos ht]
      simp
    · rw [cantorToParity, dif_neg ht, parity_h_truth]
      conv_rhs => rw [unrestrictedTruth, dif_neg ht]
      exact or_congr
        (not_congr (ih _ (children_lt f ht).1 _))
        (exists_congr fun x => not_congr (ih _ (children_lt f ht).2 _))

def ParitySigned (f : Nat) (env : List Nat) (negative : Bool) : Prop :=
  if negative then ¬ parityTruth f env else parityTruth f env

theorem signed_parityToCantor (f : Nat) (env : List Nat) (negative : Bool) :
    UnrestrictedSigned (parityToCantor f) env negative ↔ ParitySigned f env negative := by
  cases negative <;> simp [UnrestrictedSigned, ParitySigned, parityToCantor_truth]

theorem signed_cantorToParity (f : Nat) (env : List Nat) (negative : Bool) :
    ParitySigned (cantorToParity f) env negative ↔ UnrestrictedSigned f env negative := by
  cases negative <;> simp [UnrestrictedSigned, ParitySigned, cantorToParity_truth]

def ParityFiniteTables : Prop :=
  ∀ f A : Nat, ∃ c : Nat, ∀ y : Nat, y ≤ A → ParitySigned f [y] (!(c.testBit y))

theorem unrestrictedTables_iff_parity : UnrestrictedFiniteTables ↔ ParityFiniteTables := by
  constructor
  · intro h f A
    obtain ⟨c, hc⟩ := h (parityToCantor f) A
    exact ⟨c, fun y hy => (signed_parityToCantor f [y] _).mp (hc y hy)⟩
  · intro h f A
    obtain ⟨c, hc⟩ := h (cantorToParity f) A
    exact ⟨c, fun y hy => (signed_cantorToParity f [y] _).mp (hc y hy)⟩

/-- The selected record source has the same all-instance finite-table
condition as the unrestricted parity H syntax. This does not yet transport
compact proofs, parameters, or physical execution. -/
theorem source_accept_iff_parity_tables :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      ParityFiniteTables :=
  source_accept_iff_unrestricted_tables.trans unrestrictedTables_iff_parity

end PASoundness.M236Weakening
