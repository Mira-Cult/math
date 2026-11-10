import PASoundness.M236Definitions

/-!
The predecessor positional four-tag membership/equality language. This
module treats its numerical formula indices as distinct from both the older
parity H and the selected strict Cantor-tagged source.
-/
namespace PASoundness.M236Positional

open PASoundness.Cantor PASoundness.M236Game PASoundness.M236Weakening
open PASoundness.M236Definitions

theorem quarter_lt (f : Nat) (h : f ≠ 0) : f / 4 < f := by omega

theorem quarter_children_lt (f : Nat) (h : f ≠ 0) :
    (unpair (f / 4)).1 < f ∧ (unpair (f / 4)).2 < f := by
  exact ⟨lt_of_le_of_lt (unpair_fst_le _) (quarter_lt f h),
    lt_of_le_of_lt (unpair_snd_le _) (quarter_lt f h)⟩

/-- The literal zero code is truth; positive residues 0,1,2,3 encode
implication, membership, universal quantification, and equality. -/
def Truth4 (f : Nat) (env : List Nat) : Prop :=
  if h0 : f = 0 then True
  else if f % 4 = 0 then
    Truth4 (unpair (f / 4)).1 env → Truth4 (unpair (f / 4)).2 env
  else if f % 4 = 1 then
    (env.getD (unpair (f / 4)).1 0).testBit (env.getD (unpair (f / 4)).2 0) = true
  else if f % 4 = 2 then ∀ x, Truth4 (f / 4) (x :: env)
  else env.getD (unpair (f / 4)).1 0 = env.getD (unpair (f / 4)).2 0
termination_by f
decreasing_by
  · exact (quarter_children_lt f h0).1
  · exact (quarter_children_lt f h0).2
  · exact quarter_lt f h0

def trueCode : Nat := notCode falseCode

theorem trueCode_truth (env : List Nat) : Truth trueCode env := by
  rw [trueCode, not_truth]
  exact false_truth env

/-- Finite metatheoretic translation; it is not a machine input or routine. -/
def toStrict4 (f : Nat) : Nat :=
  if h0 : f = 0 then trueCode
  else if f % 4 = 0 then impCode (toStrict4 (unpair (f / 4)).1)
    (toStrict4 (unpair (f / 4)).2)
  else if f % 4 = 1 then memberCode (unpair (f / 4)).1 (unpair (f / 4)).2
  else if f % 4 = 2 then allCode (toStrict4 (f / 4))
  else equalCode (unpair (f / 4)).1 (unpair (f / 4)).2
termination_by f
decreasing_by
  · exact (quarter_children_lt f h0).1
  · exact (quarter_children_lt f h0).2
  · exact quarter_lt f h0

/-- All four-tag formulas have a finite strict-H translation preserving
truth in every zero-default positional environment. -/
theorem toStrict4_truth (f : Nat) (env : List Nat) :
    Truth (toStrict4 f) env ↔ Truth4 f env := by
  induction f using Nat.strong_induction_on generalizing env with
  | h f ih =>
    by_cases h0 : f = 0
    · subst f
      rw [toStrict4, dif_pos rfl, Truth4, dif_pos rfl]
      exact ⟨fun _ => trivial, fun _ => trueCode_truth env⟩
    · rw [toStrict4, dif_neg h0]
      conv_rhs => rw [Truth4, dif_neg h0]
      by_cases htag0 : f % 4 = 0
      · simp only [htag0, if_true]
        rw [imp_truth]
        exact imp_congr (ih _ (quarter_children_lt f h0).1 _) (ih _ (quarter_children_lt f h0).2 _)
      · simp only [htag0, if_false]
        by_cases htag1 : f % 4 = 1
        · simp only [htag1, if_true]
          exact member_truth _ _ _
        · simp only [htag1, if_false]
          by_cases htag2 : f % 4 = 2
          · simp only [htag2, if_true]
            rw [all_truth]
            exact forall_congr' (fun x => ih _ (quarter_lt f h0) _)
          · simp only [htag2, if_false]
            exact equal_truth _ _ _

def imp4 (a b : Nat) : Nat := 4 * pair a b
def member4 (i j : Nat) : Nat := 4 * pair i j + 1
def all4 (f : Nat) : Nat := 4 * f + 2
def equal4 (i j : Nat) : Nat := 4 * pair i j + 3

@[simp] theorem zero_truth (env : List Nat) : Truth4 0 env := by
  rw [Truth4]
  simp

theorem member4_truth (i j : Nat) (env : List Nat) :
    Truth4 (member4 i j) env ↔
      (env.getD i 0).testBit (env.getD j 0) = true := by
  have hn : member4 i j ≠ 0 := by simp [member4]
  have hm : member4 i j % 4 = 1 := by simp [member4]
  have hd : member4 i j / 4 = pair i j := by simp [member4]; omega
  rw [Truth4, dif_neg hn]
  simp [hm, hd]

theorem all4_truth (f : Nat) (env : List Nat) :
    Truth4 (all4 f) env ↔ ∀ x, Truth4 f (x :: env) := by
  have hn : all4 f ≠ 0 := by simp [all4]
  have hm : all4 f % 4 = 2 := by simp [all4]
  have hd : all4 f / 4 = f := by simp [all4]; omega
  rw [Truth4, dif_neg hn]
  simp [hm, hd]

theorem equal4_truth (i j : Nat) (env : List Nat) :
    Truth4 (equal4 i j) env ↔ env.getD i 0 = env.getD j 0 := by
  have hn : equal4 i j ≠ 0 := by simp [equal4]
  have hm : equal4 i j % 4 = 3 := by simp [equal4]
  have hd : equal4 i j / 4 = pair i j := by simp [equal4]; omega
  rw [Truth4, dif_neg hn]
  simp [hm, hd]

/-- The zero alias for truth is exactly the otherwise special case of
implication from truth to truth. -/
theorem imp4_truth (a b : Nat) (env : List Nat) :
    Truth4 (imp4 a b) env ↔ (Truth4 a env → Truth4 b env) := by
  by_cases hp : pair a b = 0
  · have ha : a = 0 := by have h := left_le_pair a b; omega
    have hb : b = 0 := by have h := right_le_pair a b; omega
    subst a
    subst b
    simp [imp4, pair, triangle]
  · have hn : imp4 a b ≠ 0 := by simp [imp4, hp]
    have hm : imp4 a b % 4 = 0 := by simp [imp4]
    have hd : imp4 a b / 4 = pair a b := by simp [imp4]
    rw [Truth4, dif_neg hn]
    simp [hm, hd]

def bottom4 : Nat := member4 0 0
def not4 (a : Nat) : Nat := imp4 a bottom4
def and4 (a b : Nat) : Nat := not4 (imp4 a (not4 b))
def or4 (a b : Nat) : Nat := imp4 (not4 a) b
def exists4 (a : Nat) : Nat := not4 (all4 (not4 a))

theorem bottom4_false (env : List Nat) : ¬ Truth4 bottom4 env := by
  rw [bottom4, member4_truth]
  have hb : (env.getD 0 0).testBit (env.getD 0 0) = false :=
    Nat.testBit_lt_two_pow Nat.lt_two_pow_self
  rw [hb]
  decide

theorem not4_truth (a : Nat) (env : List Nat) :
    Truth4 (not4 a) env ↔ ¬ Truth4 a env := by
  rw [not4, imp4_truth]
  exact ⟨fun h ha => bottom4_false env (h ha), fun h ha => False.elim (h ha)⟩

theorem and4_truth (a b : Nat) (env : List Nat) :
    Truth4 (and4 a b) env ↔ Truth4 a env ∧ Truth4 b env := by
  classical
  simp [and4, not4_truth, imp4_truth]

theorem or4_truth (a b : Nat) (env : List Nat) :
    Truth4 (or4 a b) env ↔ Truth4 a env ∨ Truth4 b env := by
  classical
  rw [or4, imp4_truth, not4_truth]
  constructor
  · intro h
    by_cases ha : Truth4 a env
    · exact Or.inl ha
    · exact Or.inr (h ha)
  · rintro (ha | hb) hna
    · exact False.elim (hna ha)
    · exact hb

theorem exists4_truth (a : Nat) (env : List Nat) :
    Truth4 (exists4 a) env ↔ ∃ x, Truth4 a (x :: env) := by
  classical
  simp [exists4, not4_truth, all4_truth]

/-- Object zero is characterized by having no members, using a fresh binder. -/
def zero4 : Nat := all4 (not4 (member4 1 0))

theorem zero4_truth (env : List Nat) : Truth4 zero4 env ↔ env.getD 0 0 = 0 := by
  rw [zero4, all4_truth]
  simp only [not4_truth, member4_truth, List.getD_cons_zero, List.getD_cons_succ]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    have hx := h x
    cases hb : (env.getD 0 0).testBit x <;> simp_all
  · intro h x
    rw [h]
    simp

/-- The unrestricted H constructor can be represented by a single fresh
binding, with a zero predicate on its left branch. -/
def strictTo4 (f : Nat) : Nat :=
  if h : tag f = 0 then
    let j := (unpair (payload f)).1
    let gap := (unpair (payload f)).2
    member4 (j + gap + 1) j
  else exists4 (or4 (and4 zero4 (not4 (strictTo4 (tag f - 1))))
    (not4 (strictTo4 (payload f))))
termination_by f
decreasing_by
  · exact (children_lt f h).1
  · exact (children_lt f h).2

theorem strictTo4_truth (f : Nat) (env : List Nat) :
    Truth4 (strictTo4 f) env ↔ Truth f env := by
  induction f using Nat.strong_induction_on generalizing env with
  | h f ih =>
    by_cases ht : tag f = 0
    · rw [strictTo4, dif_pos ht, member4_truth]
      conv_rhs => rw [Truth, dif_pos ht]
      rfl
    · rw [strictTo4, dif_neg ht, exists4_truth]
      simp only [or4_truth, and4_truth, zero4_truth, not4_truth,
        List.getD_cons_zero]
      conv_rhs => rw [Truth, dif_neg ht]
      constructor
      · rintro ⟨x, (⟨rfl, ha⟩ | hb)⟩
        · exact Or.inl (fun hh => ha ((ih _ (children_lt f ht).1 _).mpr hh))
        · exact Or.inr ⟨x, fun hh => hb ((ih _ (children_lt f ht).2 _).mpr hh)⟩
      · rintro (ha | ⟨x, hb⟩)
        · exact ⟨0, Or.inl ⟨rfl, fun hh => ha ((ih _ (children_lt f ht).1 _).mp hh)⟩⟩
        · exact ⟨x, Or.inr (fun hh => hb ((ih _ (children_lt f ht).2 _).mp hh))⟩

/-- The exact pointed support game stated for four-tag positional syntax. -/
def PointedSupport4 : Prop :=
  ∀ (f e : Nat), ∃ code : Nat, ∀ y : Nat,
    (code.testBit y = true → Truth4 f (y :: unpackEnv e)) ∧
    (((lookup e 0).testBit y = true ∨ y = lookup e 1) →
      Truth4 f (y :: unpackEnv e) → code.testBit y = true)

/-- Both directions translate the predicate and keep its entire original
parameter environment and the same support witness. -/
theorem parity_pointed_iff_four : PointedSupportFamily ↔ PointedSupport4 := by
  constructor
  · intro h f e
    let q := cantorToParity (toUnrestricted (toStrict4 f))
    obtain ⟨code, hc⟩ := h q e
    refine ⟨code, fun y => ?_⟩
    have ht : parityTruth q (y :: unpackEnv e) ↔ Truth4 f (y :: unpackEnv e) :=
      (cantorToParity_truth _ _).trans ((toUnrestricted_truth _ _).trans (toStrict4_truth f _))
    exact ⟨fun hb => ht.mp ((hc y).1 hb),
      fun hs hp => (hc y).2 hs (ht.mpr hp)⟩
  · intro h f e
    let q := strictTo4 (toStrict (parityToCantor f))
    obtain ⟨code, hc⟩ := h q e
    refine ⟨code, fun y => ?_⟩
    have ht : Truth4 q (y :: unpackEnv e) ↔ parityTruth f (y :: unpackEnv e) :=
      (strictTo4_truth _ _).trans ((toStrict_truth _ _).trans (parityToCantor_truth f _))
    exact ⟨fun hb => ht.mp ((hc y).1 hb),
      fun hs hp => (hc y).2 hs (ht.mpr hp)⟩

/-- The selected mathematical source captures exactly the old four-tag
pointed family. This is still not a theorem about the literal machine or
about PA: named proof-calculus and physical bridges remain open. -/
theorem source_accept_iff_pointedSupport4 :
    PASoundness.M236Observer.TraceAccept (PASoundness.Source.source selectedValue) ↔
      PointedSupport4 :=
  source_accept_iff_pointedSupport.trans parity_pointed_iff_four

end PASoundness.M236Positional
