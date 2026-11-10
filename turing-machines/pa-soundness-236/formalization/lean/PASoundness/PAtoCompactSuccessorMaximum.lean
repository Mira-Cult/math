import PASoundness.PAtoCompactTransitiveClosure

/-! A local maximality fact for the raw K successor graph. In this calculus
code 1 is literally `member 0 0`; the encoded negation below is implication
to that code, with no semantic irreflexivity assumption. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactSuccessorMaximum
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If `Y` is a raw successor of a transitive `y`, and `b` belongs to `Y`,
then the hypothesis `y ∈ b` entails literal code 1. The six *syntactic
names* must be fresh as displayed; their assigned objects may coincide.
This does not establish an isomorphism, quotient, or PA interpretation. -/
def successor_no_member_above (y Y b w p q : Nat)
    (fresh : [y,Y,b,w,p,q].Nodup) :
    KDerivation (imp (successorCode y Y w)
      (imp (transitiveCode y p q)
        (imp (member Y b) (neg (member b y))))) := by
  have hwy : w ≠ y := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hwY : w ≠ Y := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hwb : w ≠ b := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hpy : p ≠ y := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hpb : p ≠ b := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hpq : p ≠ q := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hqy : q ≠ y := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hqb : q ≠ b := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode y Y w
  let T := transitiveCode y p q
  let U := member Y b
  let V := member b y
  let Γ := [V,U,T,S]
  have hv : Context Γ V := Context.head _ _
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hcases : Context Γ (either (equal b y) (member y b)) :=
    .mp hu (.mp hs (.closed (successor_inspect y Y w b hwy hwY hwb)))
  apply Context.disjunctionElim hcases
  · have he : Context (equal b y :: Γ) (equal b y) := .head _ _
    have hv' : Context (equal b y :: Γ) (member b y) := Context.under hv _
    have hself : Context (equal b y :: Γ) (member y y) :=
      .mp hv' (.mp he (.closed (memberLeftEquality b y y)))
    exact .mp hself (.closed (self_membership_implies_code_one y))
  · have hby : Context (member y b :: Γ) (member y b) := .head _ _
    have hyv : Context (member y b :: Γ) (member b y) := Context.under hv _
    have ht' : Context (member y b :: Γ) T := Context.under ht _
    have hself : Context (member y b :: Γ) (member y y) :=
      .mp hyv (.mp hby (.mp ht' (.closed (transitive_instance y b p q hpy hpb hpq hqy hqb))))
    exact .mp hself (.closed (self_membership_implies_code_one y))

theorem successor_no_member_above_certificate (y Y b w p q : Nat)
    (fresh : [y,Y,b,w,p,q].Nodup) :
    theoremCode (certificate (successor_no_member_above y Y b w p q fresh)) =
      imp (successorCode y Y w)
        (imp (transitiveCode y p q)
          (imp (member Y b) (neg (member b y)))) :=
  certificate_correct (successor_no_member_above y Y b w p q fresh)

end PASoundness.PAtoCompactSuccessorMaximum

#print axioms PASoundness.PAtoCompactSuccessorMaximum.successor_no_member_above
#print axioms PASoundness.PAtoCompactSuccessorMaximum.successor_no_member_above_certificate
