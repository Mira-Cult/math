import PASoundness.M236Named
import PASoundness.CompactMatrix
import PASoundness.CompactNamedSemantics

/-! Translation of four-tag positional formulas into named compact syntax.
Even varName names are reserved for binders; odd names are free positions.
-/
namespace PASoundness.M236Reverse

open PASoundness.CompactMatrix PASoundness.M236Positional PASoundness.Cantor

/-- Bound indices count back from the nearest binder; free positions use
distinct odd names. -/
def varName (depth j : Nat) : Nat :=
  if j < depth then 2 * (depth - 1 - j) else 2 * (j - depth) + 1

theorem varName_zero (depth : Nat) : varName (depth + 1) 0 = 2 * depth := by
  simp [varName]

theorem varName_succ (depth j : Nat) :
    varName (depth + 1) (j + 1) = varName depth j := by
  simp only [varName]
  split <;> split <;> omega

theorem varName_ne_binder (depth j : Nat) : varName depth j ≠ 2 * depth := by
  simp only [varName]
  split <;> omega

/-- Relation for all positions, including positions beyond the finite list,
whose stipulated value is zero. -/
def Rel (depth : Nat) (env : List Nat) (ρ : Environment) : Prop :=
  ∀ j, ρ (varName depth j) = env.getD j 0

theorem rel_bind {depth : Nat} {env : List Nat} {ρ : Environment}
    (h : Rel depth env ρ) (value : Nat) :
    Rel (depth + 1) (value :: env) (update ρ (2 * depth) value) := by
  intro j
  cases j with
  | zero => simp [varName_zero, update]
  | succ j =>
    rw [varName_succ]
    simpa [update, varName_ne_binder, List.getD_eq_getElem?_getD] using h j

def toNamed (f depth : Nat) : Formula :=
  if h0 : f = 0 then .truth
  else if f % 4 = 0 then
    .imp (toNamed (unpair (f / 4)).1 depth) (toNamed (unpair (f / 4)).2 depth)
  else if f % 4 = 1 then
    .member (varName depth (unpair (f / 4)).1) (varName depth (unpair (f / 4)).2)
  else if f % 4 = 2 then
    .all (2 * depth) (toNamed (f / 4) (depth + 1))
  else .equal (varName depth (unpair (f / 4)).1) (varName depth (unpair (f / 4)).2)
termination_by f
decreasing_by
  · exact (quarter_children_lt f h0).1
  · exact (quarter_children_lt f h0).2
  · exact quarter_lt f h0

theorem toNamed_truth (f : Nat) : ∀ depth env ρ,
    Rel depth env ρ → ((toNamed f depth).Realize ρ ↔ Truth4 f env) := by
  intro depth env ρ h
  induction f using Nat.strong_induction_on generalizing depth env ρ with
  | h f ih =>
    rw [toNamed, Truth4]
    split
    · simp [Formula.Realize]
    · rename_i h0
      split
      · simp only [Formula.Realize]
        exact imp_congr (ih _ (quarter_children_lt f h0).1 depth env ρ h)
          (ih _ (quarter_children_lt f h0).2 depth env ρ h)
      · split
        · simp only [Formula.Realize, bit_eq_testBit]
          rw [h _, h _]
        · split
          · simp only [Formula.Realize]
            exact forall_congr' fun value => ih _ (quarter_lt f h0) _ _ _ (rel_bind h value)
          · simp only [Formula.Realize]
            rw [h _, h _]

/-- A total named assignment represents every positional environment, with
zero beyond its finite tail. -/
def initialAssignment (env : List Nat) : Environment :=
  fun x => if x % 2 = 1 then env.getD (x / 2) 0 else 0

theorem initial_rel (env : List Nat) : Rel 0 env (initialAssignment env) := by
  intro j
  simp only [varName, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, initialAssignment]
  have hm : (2 * j + 1) % 2 = 1 := by omega
  have hd : (2 * j + 1) / 2 = j := by omega
  simp [hm, hd]

theorem positional_truth_in_named (f : Nat) (env : List Nat) :
    (toNamed f 0).Realize (initialAssignment env) ↔ Truth4 f env :=
  toNamed_truth f 0 env (initialAssignment env) (initial_rel env)

theorem challenge_rel (env : List Nat) (point y : Nat) :
    Rel 0 (y :: env) (update (initialAssignment (point :: env)) 1 y) := by
  intro j
  cases j with
  | zero => simp [varName, update]
  | succ j =>
    have hn : 2 * (j + 1) + 1 ≠ 1 := by omega
    have hj := initial_rel (point :: env) (j + 1)
    simp only [varName, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hj ⊢
    simpa [update, hn, List.getD_eq_getElem?_getD] using hj

theorem challenge_truth (f : Nat) (env : List Nat) (point y : Nat) :
    (toNamed f 0).Realize (update (initialAssignment (point :: env)) 1 y) ↔
      Truth4 f (y :: env) :=
  toNamed_truth f 0 _ _ (challenge_rel env point y)

theorem ofDecoded_truth (f : Formula) (ρ : Environment) :
    (PASoundness.CompactNamed.ofDecoded f).Realize ρ ↔ f.Realize ρ := by
  induction f generalizing ρ with
  | truth | member | equal => rfl
  | imp a b ia ib => exact imp_congr (ia ρ) (ib ρ)
  | all x a ih => exact forall_congr' fun value => ih (update ρ x value)

theorem encode_truth (f : Formula) (ρ : Environment) :
    (decode (PASoundness.RawMatrix.encodeFormula f)).Realize ρ ↔ f.Realize ρ := by
  rw [← PASoundness.CompactNamed.encode_ofDecoded]
  exact (PASoundness.CompactNamed.Formula.encode_realize _ _).trans (ofDecoded_truth f ρ)

/-- Double negation gives a semantically equivalent compact code that is
neither of the two fixed parameter names used by the selector-eight guard. -/
def padded (f : Formula) : Formula := .imp (.imp f falsity) falsity

theorem padded_truth (f : Formula) (ρ : Environment) :
    (padded f).Realize ρ ↔ f.Realize ρ := by
  classical
  simp [padded, Formula.Realize, falsity_false]

theorem padded_code_ge_four (f : Formula) : 4 ≤ PASoundness.RawMatrix.encodeFormula (padded f) := by
  simp only [padded, PASoundness.RawMatrix.encodeFormula, PASoundness.CompactProof.imp,
    PASoundness.RawMatrix.encode_falsity]
  have hp := left_le_pair (4 * pair (PASoundness.RawMatrix.encodeFormula f) 1) 1
  have hp' := right_le_pair (PASoundness.RawMatrix.encodeFormula f) 1
  omega

theorem selector8_implies_pointed
    (h8 : ∀ a b c u ρ, (decode (PASoundness.CompactProof.axiomCode 8 a b c u)).Realize ρ) :
    PointedSupport4 := by
  classical
  open PASoundness.CompactProof PASoundness.CompactSemantics
    PASoundness.M236Game PASoundness.M236Definitions in
  intro f e
  let φ := toNamed f 0
  let c := PASoundness.RawMatrix.encodeFormula (padded φ)
  let ρ := initialAssignment (lookup e 1 :: unpackEnv e)
  have hcge : 4 ≤ c := padded_code_ge_four φ
  have hc3 : c ≠ 3 := by omega
  have hc1 : c ≠ 1 := by omega
  have hρ1 : ρ 1 = lookup e 1 := by simp [ρ, initialAssignment]
  have hρ3 : ρ 3 = lookup e 0 := by
    have hr := unpack_represented e 0
    simpa [ρ, initialAssignment, List.getD_eq_getElem?_getD] using hr.symm
  have hp (σ : Environment) : (decode c).Realize σ ↔ φ.Realize σ :=
    (encode_truth (padded φ) σ).trans (padded_truth φ σ)
  have hpred (y : Nat) :
      (decode c).Realize (update ρ 1 y) ↔ Truth4 f (y :: unpackEnv e) :=
    (hp _).trans (challenge_truth f (unpackEnv e) (lookup e 1) y)
  have hs := h8 3 1 c 0 ρ
  simp only [axiomCode, if_neg (show ¬(c = 3 ∨ c = 1) by simp [hc3, hc1]),
    realize_both, realize_exists, realize_all, realize_imp, realize_member, realize_equal] at hs
  obtain ⟨⟨z, hall, hpoint⟩, _, _⟩ := hs
  have hfresh (y : Nat) :
      (decode c).Realize (update (update ρ c z) 1 y) ↔
        (decode c).Realize (update ρ 1 y) := by
    rw [update_commute ρ c 1 z y hc1]
    exact realize_update_code c (update ρ 1 y) z
  have hlast : (decode c).Realize ρ → bit z (lookup e 1) = true := by
    intro hφ
    have hh := hpoint ((realize_update_code c ρ z).mpr hφ)
    simpa [update, Ne.symm hc1, hρ1] using hh
  refine ⟨z, fun y => ?_⟩
  have hh := hall y
  simp only [hfresh, update_same, update_other (update ρ c z) 1 c y hc1] at hh
  have hsupport : bit (update (update ρ c z) 1 y 3) y = bit (lookup e 0) y := by
    simp [update, Ne.symm hc3, hρ3]
  rw [hsupport] at hh
  constructor
  · intro hz
    apply (hpred y).mp
    exact hh.2 (by simpa [bit_eq_testBit] using hz)
  · intro hguard hφ
    have hp' := (hpred y).mpr hφ
    rw [← bit_eq_testBit]
    rcases hguard with hmem | hpointy
    · exact hh.1 (by simpa [bit_eq_testBit] using hmem) hp'
    · subst y
      apply hlast
      rw [← hρ1, update_self] at hp'
      exact hp'

/-- Soundness of the existing compact derivation system in the standard
finite-set coding on Nat. This does not assert a PA proof translation. -/
def CompactSound : Prop :=
  ∀ (f : Nat), PASoundness.CompactProof.KDerivation f → ∀ ρ, (decode f).Realize ρ

theorem compact_sound_implies_pointed (h : CompactSound) : PointedSupport4 := by
  apply selector8_implies_pointed
  intro a b c u ρ
  exact h _ (.axiom ⟨8, by decide⟩ a b c u) ρ

theorem source_accept_iff_compact_sound :
    PASoundness.M236Observer.TraceAccept
        (PASoundness.Source.source PASoundness.M236Game.selectedValue) ↔ CompactSound := by
  constructor
  · intro h f d ρ
    exact PASoundness.M236Named.source_accept_implies_compact_sound h d ρ
  · intro h
    exact source_accept_iff_pointedSupport4.mpr (compact_sound_implies_pointed h)

end PASoundness.M236Reverse
