import Shared.Beeping.NPcoNP.UnaryBank

/-! The local *tape-level specification* of the producer's unary suffix
shift. It does not assert that any finite transition table implements it.

The input has a designated two-zero gap at integer position `gap`, then an
arbitrary finite encoded suffix and an all-zero right tail. The output leaves
everything left of the gap untouched, moves the entire suffix one cell left,
and writes a fresh `10` zero-register block after it. This generic theorem
applies in particular when the suffix is a finite concatenation of the
producer's `1^(x+1)0` register blocks. Applying this specification to the
concrete four-state scan requires separate proofs of the admissible suffix
shape and head position: a leading one alone does not exclude an internal
double zero. The abstract transformation below imposes neither condition
and does not assert that the physical machine implements it. -/
namespace Shared.Beeping.NPcoNP.UnarySuffixShift

/-- Total value of a finite bit list at a natural offset, with zero padding. -/
def bitAt (xs : List Bool) (i : Nat) : Bool := (xs[i]?).getD false

/-- The old tape: arbitrary protected prefix, a two-zero gap, the finite
suffix, then an infinite zero tail. -/
def before (baseTape : Int → Bool) (gap : Int) (suffix : List Bool) : Int → Bool :=
  fun p => if p < gap then baseTape p else
    if p < gap + 2 then false else bitAt suffix (p - gap - 2).toNat

/-- The specified new tape: the suffix starts one cell earlier and is
followed by a new `10` reserve block and an infinite zero tail. -/
def after (baseTape : Int → Bool) (gap : Int) (suffix : List Bool) : Int → Bool :=
  fun p => if p < gap then baseTape p else
    if p = gap then false else
      if p < gap + 1 + suffix.length then bitAt suffix (p - gap - 1).toNat
      else if p = gap + 1 + suffix.length then true else false

theorem before_prefix (baseTape : Int → Bool) (gap p : Int) (suffix : List Bool)
    (h : p < gap) : before baseTape gap suffix p = baseTape p := by
  simp [before, h]

theorem after_prefix (baseTape : Int → Bool) (gap p : Int) (suffix : List Bool)
    (h : p < gap) : after baseTape gap suffix p = baseTape p := by
  simp [after, h]

theorem preserves_prefix (baseTape : Int → Bool) (gap p : Int) (suffix : List Bool)
    (h : p < gap) : after baseTape gap suffix p = before baseTape gap suffix p := by
  simp [before, after, h]

theorem gap_cells (baseTape : Int → Bool) (gap : Int) (suffix : List Bool) :
    before baseTape gap suffix gap = false ∧
    before baseTape gap suffix (gap + 1) = false ∧
    after baseTape gap suffix gap = false := by
  simp [before, after]

/-- Reading within the old suffix recovers the represented finite data. -/
theorem before_suffix_bit (baseTape : Int → Bool) (gap : Int) (suffix : List Bool)
    (i : Nat) : before baseTape gap suffix (gap + 2 + (i : Int)) = bitAt suffix i := by
  have h0 : (0 : Int) ≤ i := by omega
  have hp : ¬ gap + 2 + (i : Int) < gap := by omega
  have hg : ¬ gap + 2 + (i : Int) < gap + 2 := by omega
  have ho : gap + 2 + (i : Int) - gap - 2 = (i : Int) := by omega
  simp [before, hp, hg, ho]

/-- Reading the shifted suffix recovers the same finite data. -/
theorem after_suffix_bit (baseTape : Int → Bool) (gap : Int) (suffix : List Bool)
    (i : Nat) (hi : i < suffix.length) :
    after baseTape gap suffix (gap + 1 + (i : Int)) = bitAt suffix i := by
  have hi' : (i : Int) < (suffix.length : Int) := by exact_mod_cast hi
  have h0 : (0 : Int) ≤ i := by omega
  have hp : ¬ gap + 1 + (i : Int) < gap := by omega
  have hq : gap + 1 + (i : Int) ≠ gap := by omega
  have hb : gap + 1 + (i : Int) < gap + 1 + (suffix.length : Int) := by omega
  have ho : gap + 1 + (i : Int) - gap - 1 = (i : Int) := by omega
  simp [after, hp, hq, hb, ho]

/-- Every bit of the finite suffix is moved exactly one cell left. -/
theorem shifts_suffix (baseTape : Int → Bool) (gap : Int) (suffix : List Bool)
    (i : Nat) (hi : i < suffix.length) :
    after baseTape gap suffix (gap + 1 + (i : Int)) =
      before baseTape gap suffix (gap + 2 + (i : Int)) := by
  have hi' : (i : Int) < (suffix.length : Int) := by exact_mod_cast hi
  have h0 : (0 : Int) ≤ i := by omega
  have hp : ¬ gap + 1 + (i : Int) < gap := by omega
  have hq : gap + 1 + (i : Int) ≠ gap := by omega
  have hb : gap + 1 + (i : Int) < gap + 1 + (suffix.length : Int) := by omega
  have hp' : ¬ gap + 2 + (i : Int) < gap := by omega
  have hb' : ¬ gap + 2 + (i : Int) < gap + 2 := by omega
  have ho : gap + 1 + (i : Int) - gap - 1 = (i : Int) := by omega
  have ho' : gap + 2 + (i : Int) - gap - 2 = (i : Int) := by omega
  simp only [after, before, hp, hq, hb, hp', hb', if_false, if_true, ho, ho']

/-- The immediately following block encodes the natural zero. -/
theorem appended_zero_block (baseTape : Int → Bool) (gap : Int) (suffix : List Bool) :
    after baseTape gap suffix (gap + 1 + (suffix.length : Int)) = true ∧
    after baseTape gap suffix (gap + 2 + (suffix.length : Int)) = false := by
  have h : (0 : Int) ≤ suffix.length := by omega
  have h1 : ¬ gap + 1 + (suffix.length : Int) < gap := by omega
  have h2 : gap + 1 + (suffix.length : Int) ≠ gap := by omega
  have h3 : ¬ gap + 2 + (suffix.length : Int) < gap := by omega
  have h4 : gap + 2 + (suffix.length : Int) ≠ gap := by omega
  have h5 : ¬ gap + 2 + (suffix.length : Int) < gap + 1 + suffix.length := by omega
  have h6 : gap + 2 + (suffix.length : Int) ≠ gap + 1 + suffix.length := by omega
  constructor
  · simp [after, h1, h2]
  · simp [after, h3, h4, h5, h6]

theorem after_tail_zero (baseTape : Int → Bool) (gap p : Int) (suffix : List Bool)
    (h : gap + 1 + (suffix.length : Int) < p) :
    after baseTape gap suffix p = false := by
  have hn : (0 : Int) ≤ suffix.length := by omega
  simp only [after]
  split <;> rename_i h1
  · omega
  split <;> rename_i h2
  · rfl
  split <;> rename_i h3
  · omega
  split <;> rename_i h4
  · omega
  · rfl

theorem before_tail_zero (baseTape : Int → Bool) (gap p : Int) (suffix : List Bool)
    (h : gap + 2 + (suffix.length : Int) ≤ p) :
    before baseTape gap suffix p = false := by
  have hn : (0 : Int) ≤ suffix.length := by omega
  have hp : ¬ p < gap := by omega
  have hg : ¬ p < gap + 2 := by omega
  have hi : suffix.length ≤ (p - gap - 2).toNat := by omega
  simp [before, hp, hg, bitAt, List.getElem?_eq_none hi]

/-- The same exact one-cell shift for a finite bank in the producer's
`1^(x+1)0` encoding. -/
theorem shifts_unary_bank (baseTape : Int → Bool) (gap : Int) (values : List Nat)
    (i : Nat) (hi : i < (UnaryBank.encode values).length) :
    after baseTape gap (UnaryBank.encode values) (gap + 1 + (i : Int)) =
      before baseTape gap (UnaryBank.encode values) (gap + 2 + (i : Int)) :=
  shifts_suffix baseTape gap (UnaryBank.encode values) i hi

/-- The appended `10` is exactly the standard encoding of one zero-valued
register, with every original encoded bit preserved in its shifted location. -/
theorem unary_reserve (baseTape : Int → Bool) (gap : Int) (values : List Nat) :
    after baseTape gap (UnaryBank.encode values)
        (gap + 1 + ((UnaryBank.encode values).length : Int)) = true ∧
      after baseTape gap (UnaryBank.encode values)
        (gap + 2 + ((UnaryBank.encode values).length : Int)) = false :=
  appended_zero_block baseTape gap (UnaryBank.encode values)

end Shared.Beeping.NPcoNP.UnarySuffixShift
