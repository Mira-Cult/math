import PASoundness.PAtoCompactProductOldLexPoint
import PASoundness.PAtoCompactFreeVacuity

/-! The reversed pointwise lexicographic comparison from an old product
matrix, with the same six endpoint guards and two represented triples. This
constructs finite K proof data; no output-cut transport, multiplication
totality, or model-soundness theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldLexSwapped
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanLexTransfer
open PASoundness.PAtoCompactProductOldLexPoint PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact reversed lexicographic comparison at the two displayed triples. -/
def reverseComparison : Formula := namedBoth
  (.imp (.member 5 9) (namedEither (.member 3 7) (namedBoth (.equal 7 3) (.member 4 8))))
  (.imp (namedEither (.member 3 7) (namedBoth (.equal 7 3) (.member 4 8))) (.member 5 9))

/-- Pointwise simultaneous swap through fresh names 40, 41 and 42. -/
def swappedPoint : Formula :=
  replace 42 9 (replace 41 8 (replace 40 7 (replace 9 5 (replace 8 4
    (replace 7 3 (replace 5 42 (replace 4 41 (replace 3 40 (point 10)))))))))

private def contextRename (x y : Nat) (f : Formula)
    (hxy : x ≠ y) (hxb : x ∉ f.binders) (hyb : y ∉ f.binders)
    (hxf : x ∉ oldMatrixAtTen.free)
    (h : Context [oldMatrixAtTen.encode] f.encode) :
    Context [oldMatrixAtTen.encode] (replace x y f).encode := by
  have hv : ∀ z, z ∈ [oldMatrixAtTen.encode] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = oldMatrixAtTen.encode := by simpa using hz
    subst z
    exact free_vacuity x oldMatrixAtTen hxf
  exact .mp (Context.generalize x hv h) (.closed (universalInstance x y f hxy hxb hyb))

private def point_swapped_context : Context [oldMatrixAtTen.encode] swappedPoint.encode := by
  let p := point 10
  let p1 := replace 3 40 p
  let p2 := replace 4 41 p1
  let p3 := replace 5 42 p2
  let p4 := replace 7 3 p3
  let p5 := replace 8 4 p4
  let p6 := replace 9 5 p5
  let p7 := replace 40 7 p6
  let p8 := replace 41 8 p7
  have h0 : Context [oldMatrixAtTen.encode] p.encode :=
    .mp (.head _ _) (.closed matrix_point_at_ten)
  have h1 : Context [oldMatrixAtTen.encode] p1.encode :=
    contextRename 3 40 p (by decide) (by decide) (by decide) (by decide) h0
  have h2 : Context [oldMatrixAtTen.encode] p2.encode :=
    contextRename 4 41 p1 (by decide) (by simp only [p1,replace_binders]; decide)
      (by simp only [p1,replace_binders]; decide) (by decide) h1
  have h3 : Context [oldMatrixAtTen.encode] p3.encode :=
    contextRename 5 42 p2 (by decide) (by simp only [p2,p1,replace_binders]; decide)
      (by simp only [p2,p1,replace_binders]; decide) (by decide) h2
  have h4 : Context [oldMatrixAtTen.encode] p4.encode :=
    contextRename 7 3 p3 (by decide) (by simp only [p3,p2,p1,replace_binders]; decide)
      (by simp only [p3,p2,p1,replace_binders]; decide) (by decide) h3
  have h5 : Context [oldMatrixAtTen.encode] p5.encode :=
    contextRename 8 4 p4 (by decide) (by simp only [p4,p3,p2,p1,replace_binders]; decide)
      (by simp only [p4,p3,p2,p1,replace_binders]; decide) (by decide) h4
  have h6 : Context [oldMatrixAtTen.encode] p6.encode :=
    contextRename 9 5 p5 (by decide) (by simp only [p5,p4,p3,p2,p1,replace_binders]; decide)
      (by simp only [p5,p4,p3,p2,p1,replace_binders]; decide) (by decide) h5
  have h7 : Context [oldMatrixAtTen.encode] p7.encode :=
    contextRename 40 7 p6 (by decide) (by simp only [p6,p5,p4,p3,p2,p1,replace_binders]; decide)
      (by simp only [p6,p5,p4,p3,p2,p1,replace_binders]; decide) (by decide) h6
  have h8 : Context [oldMatrixAtTen.encode] p8.encode :=
    contextRename 41 8 p7 (by decide) (by simp only [p7,p6,p5,p4,p3,p2,p1,replace_binders]; decide)
      (by simp only [p7,p6,p5,p4,p3,p2,p1,replace_binders]; decide) (by decide) h7
  exact contextRename 42 9 p8 (by decide)
    (by simp only [p8,p7,p6,p5,p4,p3,p2,p1,replace_binders]; decide)
    (by simp only [p8,p7,p6,p5,p4,p3,p2,p1,replace_binders]; decide) (by decide) h8

/-- Both directions of the reverse lex comparison, for the same two old
graph triples and all six literal endpoint membership conditions. -/
def matrix_reverse : KDerivation (imp oldMatrixAtTen.encode
    (imp (antecedent 10).encode reverseComparison.encode)) := by
  let swappedAntecedent : Formula := namedBoth (.member 0 7)
    (namedBoth (.member 1 8) (namedBoth (.member 2 9)
      (namedBoth (.member 0 3) (namedBoth (.member 1 4) (namedBoth (.member 2 5)
        (namedBoth (tripleAt 10 7 8 9) (tripleAt 10 3 4 5)))))))
  have hshape : swappedPoint = .imp swappedAntecedent reverseComparison := by decide
  have hs : Context [oldMatrixAtTen.encode] (imp swappedAntecedent.encode reverseComparison.encode) := by
    simpa only [hshape,Formula.encode] using point_swapped_context
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(antecedent 10).encode,oldMatrixAtTen.encode]
  have ha : Context Γ (antecedent 10).encode := .head _ _
  have ha' : Context Γ (both (member 0 3) (both (member 1 4) (both (member 2 5)
      (both (member 0 7) (both (member 1 8) (both (member 2 9)
        (both (tripleAt 10 3 4 5).encode (tripleAt 10 7 8 9).encode))))))) := by
    simpa [antecedent,namedBoth,Formula.encode,CompactProof.both,CompactProof.neg] using ha
  have h1 := Context.conjunctionLeft ha'
  have r1 := Context.conjunctionRight ha'
  have h2 := Context.conjunctionLeft r1
  have r2 := Context.conjunctionRight r1
  have h3 := Context.conjunctionLeft r2
  have r3 := Context.conjunctionRight r2
  have h4 := Context.conjunctionLeft r3
  have r4 := Context.conjunctionRight r3
  have h5 := Context.conjunctionLeft r4
  have r5 := Context.conjunctionRight r4
  have h6 := Context.conjunctionLeft r5
  have ht := Context.conjunctionRight r5
  have hs' : Context Γ swappedAntecedent.encode := by
    simpa [swappedAntecedent,namedBoth,Formula.encode,CompactProof.both,CompactProof.neg] using
      (Context.conjunctionIntro h4 (Context.conjunctionIntro h5 (Context.conjunctionIntro h6
        (Context.conjunctionIntro h1 (Context.conjunctionIntro h2 (Context.conjunctionIntro h3
          (Context.conjunctionIntro (Context.conjunctionRight ht) (Context.conjunctionLeft ht))))))))
  exact .mp hs' (.under hs _)

theorem matrix_reverse_certificate : theoremCode (certificate matrix_reverse) =
    imp oldMatrixAtTen.encode (imp (antecedent 10).encode reverseComparison.encode) :=
  certificate_correct matrix_reverse
end PASoundness.PAtoCompactProductOldLexSwapped
#print axioms PASoundness.PAtoCompactProductOldLexSwapped.matrix_reverse
#print axioms PASoundness.PAtoCompactProductOldLexSwapped.matrix_reverse_certificate
