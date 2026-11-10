import PASoundness.HFCoding
import PASoundness.CompactDerivations
import PASoundness.CompactNamed

/-! Explicit compact zero and successor relation codes over hereditarily
finite sets. Arithmetic naturals are represented by finite ordinal codes. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactZeroSuccessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactMatrix PASoundness.CompactSemantics PASoundness.HFCoding

/-- The names `z` and `w` denote the alleged empty set and its test element. -/
def zeroCode (z w : Nat) : Nat := allCode w (neg (member z w))

/-- Finite-set successor: y has exactly the elements of x together with x.
In the compact syntax `member a b` means that b belongs to a. -/
def successorCode (x y w : Nat) : Nat :=
  allCode w (both
    (imp (member y w) (either (equal w x) (member x w)))
    (imp (either (equal w x) (member x w)) (member y w)))

theorem zeroCode_realize (z w : Nat) (ρ : Environment) (hw : z ≠ w) :
    (decode (zeroCode z w)).Realize ρ ↔ ρ z = 0 := by
  simp only [zeroCode, realize_all, realize_neg, realize_member]
  simp only [update_other ρ w z _ hw, update_same]
  constructor
  · intro h
    have he : (⟨ρ z⟩ : Object) = empty := by
      apply HFCoding.ext
      intro a
      change (bit (ρ z) a.code = true) ↔ a ∈ empty
      simp [h a.code]
    exact congrArg Object.code he
  · intro h v
    simp [h, bit_eq_testBit]

theorem successorCode_realize (x y w : Nat) (ρ : Environment)
    (hx : x ≠ w) (hy : y ≠ w) :
    (decode (successorCode x y w)).Realize ρ ↔
      ρ y = (successor ⟨ρ x⟩).code := by
  simp only [successorCode, realize_all, realize_both, realize_imp, either,
    realize_neg, realize_equal, realize_member]
  simp only [update_other ρ w x _ hx, update_other ρ w y _ hy, update_same]
  constructor
  · intro h
    have he : (⟨ρ y⟩ : Object) = successor ⟨ρ x⟩ := by
      apply HFCoding.ext
      intro a
      cases a with | mk v =>
       change (bit (ρ y) v = true) ↔ (⟨v⟩ : Object) ∈ successor ⟨ρ x⟩
       rw [mem_successor]
       simp only [Object.mk.injEq, Membership.mem, Mem]
       have hh := h v
       classical
       tauto
    exact congrArg Object.code he
  · intro he v
    have hm : (⟨v⟩ : Object) ∈ successor ⟨ρ x⟩ ↔ v = ρ x ∨ bit (ρ x) v = true := by
      rw [mem_successor]
      simp [Membership.mem, Mem]
    have hh : bit (ρ y) v = true ↔ v = ρ x ∨ bit (ρ x) v = true := by
      rw [he]
      exact hm
    classical
    tauto

/-- The exact executable code for successor is bitwise union with the input's
singleton bit; this is an external semantic identification, not a K proof
of totality. -/
theorem successorCode_realize_bits (x y w : Nat) (ρ : Environment)
    (hx : x ≠ w) (hy : y ≠ w) :
    (decode (successorCode x y w)).Realize ρ ↔ ρ y = (ρ x ||| 2^(ρ x)) := by
  rw [successorCode_realize x y w ρ hx hy, HFCoding.successor_code]

/-- Zero is represented by the empty ordinal. -/
theorem ordinal_zero_relation (z w : Nat) (ρ : Environment) (hw : z ≠ w) :
    (decode (zeroCode z w)).Realize ρ ↔ ρ z = (ordinal 0).code := by
  simpa [ordinal, empty] using zeroCode_realize z w ρ hw

/-- On encoded natural ordinals the successor code realizes arithmetic
successor; these ordinal codes are not the ordinary natural numbers. -/
theorem ordinal_successor_relation (x y w n : Nat) (ρ : Environment)
    (hx : x ≠ w) (hy : y ≠ w) (hinput : ρ x = (ordinal n).code) :
    (decode (successorCode x y w)).Realize ρ ↔ ρ y = (ordinal (n+1)).code := by
  rw [successorCode_realize x y w ρ hx hy, hinput]
  rfl

/-- A finite literal K proof of successor-not-zero reasoning from the explicit
membership witnesses: x is in y and x is not in z. -/
def membership_witnesses_distinct (x y z : Nat) :
    KDerivation (imp (neg (member z x)) (imp (member y x) (neg (equal y z)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal y z, member y x, neg (member z x)]
  have he : Context Γ (equal y z) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member y x) := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member z x)) := .hypothesis (by simp [Γ])
  have hz : Context Γ (member z x) := .mp hm (.mp he (.closed (memberLeftEquality y z x)))
  exact .mp hz hn

theorem membership_witnesses_certificate (x y z : Nat) :
    theoremCode (certificate (membership_witnesses_distinct x y z)) =
      imp (neg (member z x)) (imp (member y x) (neg (equal y z))) :=
  certificate_correct (membership_witnesses_distinct x y z)

/-- Named syntax for the disjunction and conjunction used in the graph; both
encode to the literal compact implication-and-bottom forms. -/
def namedEither (a b : CompactNamed.Formula) : CompactNamed.Formula :=
  .imp (.imp a .bottom) b

def namedBoth (a b : CompactNamed.Formula) : CompactNamed.Formula :=
  .imp (.imp a (.imp b .bottom)) .bottom

def namedSuccessorBody (x y w : Nat) : CompactNamed.Formula :=
  namedBoth
    (.imp (.member y w) (namedEither (.equal w x) (.member x w)))
    (.imp (namedEither (.equal w x) (.member x w)) (.member y w))

/-- The empty-set graph directly yields absence of any chosen variable. -/
def zero_excludes (z w x : Nat) (hwx : w ≠ x) (hwz : w ≠ z) :
    KDerivation (imp (zeroCode z w) (neg (member z x))) := by
  have h := CompactNamed.universalInstance w x (.imp (.member z w) .bottom) hwx
    (by simp [CompactNamed.Formula.binders]) (by simp [CompactNamed.Formula.binders])
  simpa [zeroCode, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.neg, hwx, hwz, Ne.symm hwz] using h

/-- The successor graph directly proves that its input belongs to the result. -/
def successor_contains_input (x y w : Nat) (hwx : w ≠ x) (hwy : w ≠ y) :
    KDerivation (imp (successorCode x y w) (member y x)) := by
  let body := namedSuccessorBody x y w
  have hinst := CompactNamed.universalInstance w x body hwx
    (by simp [body, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [body, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders])
  have hstep : KDerivation (imp (successorCode x y w)
      (both (imp (member y x) (either (equal x x) (member x x)))
        (imp (either (equal x x) (member x x)) (member y x)))) := by
    simpa [body, namedSuccessorBody, namedBoth, namedEither, successorCode,
      CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hwx, hwy, Ne.symm hwx, Ne.symm hwy] using hinst
  apply Context.closeEmpty
  apply Context.deduction
  have hb : Context [successorCode x y w]
      (both (imp (member y x) (either (equal x x) (member x x)))
        (imp (either (equal x x) (member x x)) (member y x))) :=
    .mp (Context.head [] (successorCode x y w)) (.closed hstep)
  have hr := Context.conjunctionRight hb
  have heq : Context [successorCode x y w] (equal x x) := .closed (equalityReflexive x)
  exact .mp (Context.disjunctionLeft (b := member x x) heq) hr

/-- Explicit K proof of successor-not-zero from the zero and successor graph
witnesses. Existence of such witnesses inside K is a separate obligation. -/
def successor_ne_zero_from_graphs (x y z w : Nat)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    KDerivation (imp (zeroCode z w) (imp (successorCode x y w) (neg (equal y z)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode x y w, zeroCode z w]
  have hz : Context Γ (zeroCode z w) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hn := Context.mp hz (.closed (zero_excludes z w x hwx hwz))
  have hm := Context.mp hs (.closed (successor_contains_input x y w hwx hwy))
  exact .mp hm (.mp hn (.closed (membership_witnesses_distinct x y z)))

theorem successor_ne_zero_certificate (x y z w : Nat)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    theoremCode (certificate (successor_ne_zero_from_graphs x y z w hwx hwy hwz)) =
      imp (zeroCode z w) (imp (successorCode x y w) (neg (equal y z))) :=
  certificate_correct (successor_ne_zero_from_graphs x y z w hwx hwy hwz)

end PASoundness.PAtoCompactZeroSuccessor
