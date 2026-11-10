import PASoundness.Peano
import PASoundness.PAtoCompactQuotientSuccessor
import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Concrete relational translation of PA terms into the named compact IR.
The allocator below reserves blocks of 64 labels; correctness requires the
caller to put all input/output labels below the initial base. Each relation
instantiation freshens every named binder, rather than using `replace` across
binders. `bottom` remains the distinguished constructor and its encoding is
literal member(0,0), so no raw-K substitution claim is made. This file alone
proves neither the standard-HF truth of the generated graphs nor K totality,
congruence, arithmetic axioms, or an interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTermTranslation

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateExact
attribute [local irreducible] PASoundness.CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle
open PASoundness.CompactMatrix (decode)

/-- Rename every explicit named node, including binder nodes. This is raw IR
construction, not the K `replace` operation or a derivation-level equivalence. -/
def mapNames (f : Nat → Nat) : Formula → Formula
  | .truth => .truth
  | .bottom => .bottom
  | .imp a b => .imp (mapNames f a) (mapNames f b)
  | .member a b => .member (f a) (f b)
  | .equal a b => .equal (f a) (f b)
  | .all x a => .all (f x) (mapNames f a)
  | .ex x a => .ex (f x) (mapNames f a)

/-- Code 1 decodes to `.member 0 0`. Restore the distinguished bottom node
before freshening; its literal encoded value is kept fixed under mapNames. -/
def normalizeBottom : Formula → Formula
  | .truth => .truth
  | .bottom => .bottom
  | .imp a b => .imp (normalizeBottom a) (normalizeBottom b)
  | .member a b => if a = 0 ∧ b = 0 then .bottom else .member a b
  | .equal a b => .equal a b
  | .all x a => .all x (normalizeBottom a)
  | .ex x a => .ex x (normalizeBottom a)

/-- This is literal numeric encoding equality, not a claim that substitution
commutes with formulas containing bottom in arbitrary K structures. -/
theorem normalizeBottom_encode (f : Formula) : (normalizeBottom f).encode = f.encode := by
  induction f with
  | truth | bottom | equal => rfl
  | imp a b ia ib => simp [normalizeBottom, Formula.encode, ia, ib]
  | member a b =>
      by_cases h : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h
        simp [normalizeBottom, Formula.encode, PASoundness.CompactProof.member, PASoundness.Cantor.pair, PASoundness.Cantor.triangle]
      · simp [normalizeBottom, h]
  | all x a ih => simp [normalizeBottom, Formula.encode, ih]
  | ex x a ih => simp [normalizeBottom, Formula.encode, ih]

/-- Full renaming maps every explicit name, including bound labels. -/
theorem mapNames_names (f : Nat → Nat) (a : Formula) :
    (mapNames f a).names = a.names.image f := by
  induction a with
  | truth | bottom | member | equal => simp [mapNames, Formula.names]
  | imp a b ia ib => simp [mapNames, Formula.names, ia, ib, Finset.image_union]
  | all x a ih | ex x a ih => simp [mapNames, Formula.names, ih]

theorem mapNames_binders (f : Nat → Nat) (a : Formula) :
    (mapNames f a).binders = a.binders.image f := by
  induction a with
  | truth | bottom | member | equal => simp [mapNames, Formula.binders]
  | imp a b ia ib => simp [mapNames, Formula.binders, ia, ib, Finset.image_union]
  | all x a ih | ex x a ih => simp [mapNames, Formula.binders, ih]

def andF (a b : Formula) : Formula := (a.imp b.not).not

/-- Template free labels are mapped to the given operands; all other names
are moved to the private block starting at `base + 2`. Operand labels may
denote the same object, though the allocator needs their syntactic names to
lie outside this block. -/
def oneMap (base p x n : Nat) : Nat := if n = p then x else base + 2 + n

def twoMap (base p q x y n : Nat) : Nat :=
  if n = p then x else if n = q then y else base + 2 + n

def threeMap (base p q r x y z n : Nat) : Nat :=
  if n = p then x else if n = q then y else if n = r then z else base + 2 + n

/-- Direct named form of the same candidate used by the quotient successor.
It avoids decoding the enormous numeric code and keeps literal bottom explicit. -/
def domainTemplate (x : Nat) : Formula :=
  andF (andF (namedTransitive x 31 32) (namedMembersTransitive x 30 31 32))
    (andF (.all 33 (namedGreatestSubsetsBody x 33 34 36 37))
      (.all 33 (namedLeastSubsetsBody x 33 34 35 36 37)))

theorem domainTemplate_encode (x : Nat) : (domainTemplate x).encode =
    candidateCode x 30 31 32 33 34 35 36 37 := by rfl

/-- Direct named quotient-successor template, using the same formulas and
fixed binders as `successorFormula` but avoiding numeric decoding. -/
def successorTemplate : Formula := .ex 7
  (andF (domainTemplate 0) (andF (domainTemplate 1) (andF (domainTemplate 7)
    (andF (namedSuccessorBody 0 7 8 |> Formula.all 8)
      (replace 0 7 equivalentFormula)))))

def zeroTemplate : Formula := .all 1 (.imp (.member 0 1) .bottom)

theorem zeroTemplate_encode : zeroTemplate.encode = zeroCode 0 1 := by rfl

/-- Concrete template instances. `base` supplies only private bound labels;
arguments are genuine named-IR labels, not encoded objects. -/
def domainAt (base x : Nat) : Formula := mapNames (oneMap base 0 x) (domainTemplate 0)
def equivAt (base x y : Nat) : Formula := mapNames (twoMap base 0 1 x y) (normalizeBottom equivalentFormula)
def zeroAt (base x : Nat) : Formula :=
  mapNames (oneMap base 0 x) zeroTemplate
def succAt (base x y : Nat) : Formula := mapNames (twoMap base 0 1 x y) successorTemplate
def addAt (base x y z : Nat) : Formula := mapNames (threeMap base 30 31 32 x y z) (normalizeBottom additionFormula)
def mulAt (base x y z : Nat) : Formula := mapNames (threeMap base 0 1 2 x y z) (normalizeBottom productFormula)

/-- Number of fresh labels reserved by the term graph. Private template
binders fit in each 64-label block: the concrete templates use no name above
37. Binary subtrees receive disjoint blocks. -/
def termCost {α : Type} : Peano.language.Term α → Nat
  | .var _ => 64
  | .func .zero _ => 64
  | .func .succ ts => 64 + termCost (ts 0)
  | .func .add ts => 64 + termCost (ts 0) + termCost (ts 1)
  | .func .mul ts => 64 + termCost (ts 0) + termCost (ts 1)

/-- A graph for the term value at output label `out`. `varName` specifies the
labels of free or in-scope de Bruijn variables. All names in the image of
`varName` used by the term, as well as `out`, must be below `base` for the
intended capture-safe reading. The two subterm witnesses are `base` and
`base+1`; nested child graphs occupy disjoint local blocks. Independent
relation templates may reuse binder names in their separate scopes. The
output domain condition is part of every graph; its semantic meaning and the
general recursive free-name invariant are not established in this module. -/
def termGraph {α : Type} (varName : α → Nat) : Peano.language.Term α → Nat → Nat → Formula
  | .var v, out, base => andF (domainAt base out) (equivAt base (varName v) out)
  | .func .zero _, out, base => andF (domainAt base out) (zeroAt base out)
  | .func .succ ts, out, base =>
      andF (domainAt base out) (.ex base
        (andF (termGraph varName (ts 0) base (base + 64)) (succAt base base out)))
  | .func .add ts, out, base =>
      andF (domainAt base out) (.ex base (.ex (base + 1)
        (andF (termGraph varName (ts 0) base (base + 64))
          (andF (termGraph varName (ts 1) (base + 1) (base + 64 + termCost (ts 0)))
            (addAt base base (base + 1) out)))))
  | .func .mul ts, out, base =>
      andF (domainAt base out) (.ex base (.ex (base + 1)
        (andF (termGraph varName (ts 0) base (base + 64))
          (andF (termGraph varName (ts 1) (base + 1) (base + 64 + termCost (ts 0)))
            (mulAt base base (base + 1) out)))))

/-- The reserved 64-name block is large enough for every explicit template.
These are named-IR syntactic checks, independent of semantic correctness. -/
theorem templates_names_bounded :
    (domainTemplate 0).names ⊆ Finset.range 38 ∧
    (normalizeBottom equivalentFormula).names ⊆ Finset.range 38 ∧
    zeroTemplate.names ⊆ Finset.range 38 ∧
    successorTemplate.names ⊆ Finset.range 38 ∧
    (normalizeBottom additionFormula).names ⊆ Finset.range 38 ∧
    (normalizeBottom productFormula).names ⊆ Finset.range 38 := by decide

/-- Input placeholders never occur as local binders in their own template. -/
theorem templates_inputs_unbound :
    0 ∉ (domainTemplate 0).binders ∧
    0 ∉ (normalizeBottom equivalentFormula).binders ∧ 1 ∉ (normalizeBottom equivalentFormula).binders ∧
    0 ∉ zeroTemplate.binders ∧
    0 ∉ successorTemplate.binders ∧ 1 ∉ successorTemplate.binders ∧
    30 ∉ (normalizeBottom additionFormula).binders ∧ 31 ∉ (normalizeBottom additionFormula).binders ∧
    32 ∉ (normalizeBottom additionFormula).binders ∧
    0 ∉ (normalizeBottom productFormula).binders ∧ 1 ∉ (normalizeBottom productFormula).binders ∧
    2 ∉ (normalizeBottom productFormula).binders := by decide

/-- Each literal template has no named free inputs beyond its declared
placeholders. This is a syntactic IR check; literal encoded bottom remains 1. -/
theorem templates_free_names :
    (domainTemplate 0).free ⊆ {0} ∧
    (normalizeBottom equivalentFormula).free ⊆ {0,1} ∧
    zeroTemplate.free ⊆ {0} ∧ successorTemplate.free ⊆ {0,1} ∧
    (normalizeBottom additionFormula).free ⊆ {30,31,32} ∧
    (normalizeBottom productFormula).free ⊆ {0,1,2} := by decide

/-- Every recursive child gets at least one full block, so a second binary
child starts after the first child’s allocated interval. -/
theorem termCost_ge_block {α : Type} (t : Peano.language.Term α) : 64 ≤ termCost t := by
  cases t with
  | var _ => rfl
  | func f ts =>
    cases f <;> simp [termCost] <;> omega

/-- In a binary node, the second child starts no earlier than the end of the
first child's interval. -/
theorem binary_children_disjoint {α : Type} (base i : Nat) (t : Peano.language.Term α)
    (hi : i < termCost t) : base + 64 + i < base + 64 + termCost t := by omega

/-- A checkable allocator condition suffices to bound all binders after the
uniform template renaming, with no assumption that operand values differ. -/
theorem mapNames_binders_in_block (f : Nat → Nat) (a : Formula) (base : Nat)
    (h : ∀ z ∈ a.binders, base + 2 ≤ f z ∧ f z < base + 64) :
    ∀ z ∈ (mapNames f a).binders, base + 2 ≤ z ∧ z < base + 64 := by
  intro z hz
  rw [mapNames_binders] at hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact h w hw

/-- The three-place allocator puts each template binder in its private block
when placeholder labels are not bound and all source names are below 38. -/
theorem threeMap_private (a : Formula) (base p q r x y z : Nat)
    (hp : p ∉ a.binders) (hq : q ∉ a.binders) (hr : r ∉ a.binders)
    (hbound : a.names ⊆ Finset.range 38) :
    ∀ w ∈ (mapNames (threeMap base p q r x y z) a).binders,
      base + 2 ≤ w ∧ w < base + 64 := by
  apply mapNames_binders_in_block
  intro w hw
  have hwp : w ≠ p := by intro e; subst w; exact hp hw
  have hwq : w ≠ q := by intro e; subst w; exact hq hw
  have hwr : w ≠ r := by intro e; subst w; exact hr hw
  have hw38 : w < 38 := Finset.mem_range.mp (hbound (Formula.binders_subset_names a hw))
  simp only [threeMap, if_neg hwp, if_neg hwq, if_neg hwr]
  omega

/-- One-place and two-place templates satisfy the same binder-block bound;
repeated placeholder arguments below are internal to the map, and do not
require distinct operand values. -/
theorem oneMap_private (a : Formula) (base p x : Nat)
    (hp : p ∉ a.binders) (hbound : a.names ⊆ Finset.range 38) :
    ∀ w ∈ (mapNames (oneMap base p x) a).binders,
      base + 2 ≤ w ∧ w < base + 64 := by
  have he : oneMap base p x = threeMap base p p p x x x := by
    funext n
    by_cases h : n = p <;> simp [oneMap, threeMap, h]
  rw [he]
  exact threeMap_private a base p p p x x x hp hp hp hbound

theorem twoMap_private (a : Formula) (base p q x y : Nat)
    (hp : p ∉ a.binders) (hq : q ∉ a.binders)
    (hbound : a.names ⊆ Finset.range 38) :
    ∀ w ∈ (mapNames (twoMap base p q x y) a).binders,
      base + 2 ≤ w ∧ w < base + 64 := by
  have he : twoMap base p q x y = threeMap base p q q x y y := by
    funext n
    by_cases h : n = p <;> by_cases j : n = q <;> simp [twoMap, threeMap, h, j]
  rw [he]
  exact threeMap_private a base p q q x y y hp hq hq hbound

end PASoundness.PAtoCompactTermTranslation

#print axioms PASoundness.PAtoCompactTermTranslation.normalizeBottom_encode
#print axioms PASoundness.PAtoCompactTermTranslation.domainTemplate_encode
#print axioms PASoundness.PAtoCompactTermTranslation.templates_names_bounded
#print axioms PASoundness.PAtoCompactTermTranslation.templates_inputs_unbound
#print axioms PASoundness.PAtoCompactTermTranslation.threeMap_private
