import PASoundness.PAtoCompactSuccessorInjective

/-! A local preimage case split for identifying a graph's maximal image.
The graph-specific functionality and order implications are supplied as
explicit K premises. Negation is implication to literal code 1. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactMaximumPreimage
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If a is in the raw successor X of x, then either a=x or a∈x. The two
displayed pointwise implications turn these cases into the conclusion that
`b≠y` entails `y∈b`. They are intended to be supplied by graph uniqueness
and order preservation respectively, but this theorem does not prove those
graph facts. Freshness concerns variable names, not object values. -/
def proper_image_from_preimage (x X a w b y : Nat)
    (hwx : w ≠ x) (hwX : w ≠ X) (hwa : w ≠ a) :
    KDerivation (imp (successorCode x X w)
      (imp (member X a)
        (imp (imp (equal a x) (equal b y))
          (imp (imp (member x a) (member b y))
            (imp (neg (equal b y)) (member b y)))))) := by
  let S := successorCode x X w
  let U := member X a
  let E := equal a x
  let L := member x a
  let F := equal b y
  let G := member b y
  let H := imp E F
  let J := imp L G
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg F,J,H,U,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hj : Context Γ J := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg F) := .head _ _
  have hcases : Context Γ (either E L) :=
    .mp hu (.mp hs (.closed (successor_inspect x X w a hwx hwX hwa)))
  apply Context.disjunctionElim hcases
  · have he : Context (E :: Γ) E := .head _ _
    have hf : Context (E :: Γ) F := .mp he (Context.under hh E)
    exact Context.explode G (.mp hf (Context.under hn E))
  · have hl : Context (L :: Γ) L := .head _ _
    exact .mp hl (Context.under hj L)

theorem proper_image_from_preimage_certificate (x X a w b y : Nat)
    (hwx : w ≠ x) (hwX : w ≠ X) (hwa : w ≠ a) :
    theoremCode (certificate (proper_image_from_preimage x X a w b y hwx hwX hwa)) =
      imp (successorCode x X w)
        (imp (member X a)
          (imp (imp (equal a x) (equal b y))
            (imp (imp (member x a) (member b y))
              (imp (neg (equal b y)) (member b y))))) :=
  certificate_correct (proper_image_from_preimage x X a w b y hwx hwX hwa)

end PASoundness.PAtoCompactMaximumPreimage

#print axioms PASoundness.PAtoCompactMaximumPreimage.proper_image_from_preimage
#print axioms PASoundness.PAtoCompactMaximumPreimage.proper_image_from_preimage_certificate
