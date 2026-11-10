import PASoundness.PAtoCompactSuccessorMaximum

/-! A conditional local maximum alignment in K. Code 1 is literally
`member 0 0`, so `neg` below means implication to that code. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactMaximumAlignment
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactSuccessorMaximum
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If b is a member of the raw successor of a transitive y, and the supplied
object-level hypothesis says b≠y entails y∈b, then b=y. The displayed name
freshness is syntactic: the denoted objects may be equal. The implication
about b≠y is a premise, not a derived fact about any graph. -/
def maximum_alignment (y Y b w p q : Nat)
    (fresh : [y,Y,b,w,p,q].Nodup) :
    KDerivation (imp (successorCode y Y w)
      (imp (transitiveCode y p q)
        (imp (member Y b)
          (imp (imp (neg (equal b y)) (member b y)) (equal b y))))) := by
  let S := successorCode y Y w
  let T := transitiveCode y p q
  let U := member Y b
  let H := imp (neg (equal b y)) (member b y)
  let E := equal b y
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,U,T,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .head _ _
  have hn : Context Γ (neg (member b y)) :=
    .mp hu (.mp ht (.mp hs (.closed (successor_no_member_above y Y b w p q fresh))))
  apply Context.dne
  apply Context.deduction
  have hne : Context (neg E :: Γ) (neg E) := .head _ _
  have habove : Context (neg E :: Γ) (member b y) :=
    .mp hne (Context.under hh (neg E))
  exact .mp habove (Context.under hn (neg E))

theorem maximum_alignment_certificate (y Y b w p q : Nat)
    (fresh : [y,Y,b,w,p,q].Nodup) :
    theoremCode (certificate (maximum_alignment y Y b w p q fresh)) =
      imp (successorCode y Y w)
        (imp (transitiveCode y p q)
          (imp (member Y b)
            (imp (imp (neg (equal b y)) (member b y)) (equal b y)))) :=
  certificate_correct (maximum_alignment y Y b w p q fresh)

end PASoundness.PAtoCompactMaximumAlignment

#print axioms PASoundness.PAtoCompactMaximumAlignment.maximum_alignment
#print axioms PASoundness.PAtoCompactMaximumAlignment.maximum_alignment_certificate
