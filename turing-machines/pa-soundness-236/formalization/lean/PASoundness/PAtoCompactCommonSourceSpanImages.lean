import PASoundness.PAtoCompactCompositionSelectedImages

/-! Joint image selection from two supplied forward-bijection clauses over
one common input. Both selected images retain domain membership, their exact
graph edges and their uniqueness clauses. This does not construct a span
graph or assume that either image object is a candidate. -/
namespace PASoundness.PAtoCompactCommonSourceSpanImages

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactZeroSuccessor

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstTemplate : Formula := namedBoth (.member 0 3)
  (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 2 4)) (.equal 4 3))))

def secondTemplate : Formula := namedBoth (.member 8 3)
  (namedBoth (graphFormula 7 2 3)
    (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 7 2 4)) (.equal 4 3))))

def firstClauseBody : Formula := .imp (.member 1 2) (.ex 3 firstTemplate)
def secondClauseBody : Formula := .imp (.member 1 2) (.ex 3 secondTemplate)
def firstClause : Formula := .all 2 firstClauseBody
def secondClause : Formula := .all 2 secondClauseBody

def firstImageBody : Formula := namedBoth (.member 0 11)
  (namedBoth (graphFormula 6 10 11)
    (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 10 4)) (.equal 4 11))))

def secondImageBody : Formula := namedBoth (.member 8 12)
  (namedBoth (graphFormula 7 10 12)
    (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 7 10 4)) (.equal 4 12))))

def selected : Formula := .ex 11 (.ex 12 (namedBoth firstImageBody secondImageBody))

/-- The first supplied graph clause chooses an image of common input 10. -/
def first_image_exists : KDerivation
    (imp firstClause.encode (imp (member 1 10) (existsCode 11 firstImageBody.encode))) := by
  have hi := universalInstance 2 10 firstClauseBody (by decide) (by decide) (by decide)
  have hs : replace 2 10 firstClauseBody = .imp (.member 1 10)
      (.ex 3 (replace 2 10 firstTemplate)) := by decide
  rw [hs] at hi
  have ha := (existentialAlpha 3 11 (replace 2 10 firstTemplate)
    (by decide) (by decide) (by decide)).1
  have he : replace 3 11 (replace 2 10 firstTemplate) = firstImageBody := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 10,firstClause.encode]
  have hx : Context Γ (member 1 10) := .head _ _
  have hf : Context Γ firstClause.encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (imp (member 1 10)
      (existsCode 3 (replace 2 10 firstTemplate).encode)) := by
    simpa only [firstClause, Formula.encode] using Context.mp hf (.closed hi)
  exact .mp (.mp hx hs') (.closed ha)

/-- The second supplied graph clause independently chooses an image of the
same common input, retaining its own uniqueness statement. -/
def second_image_exists : KDerivation
    (imp secondClause.encode (imp (member 1 10) (existsCode 12 secondImageBody.encode))) := by
  have hi := universalInstance 2 10 secondClauseBody (by decide) (by decide) (by decide)
  have hs : replace 2 10 secondClauseBody = .imp (.member 1 10)
      (.ex 3 (replace 2 10 secondTemplate)) := by decide
  rw [hs] at hi
  have ha := (existentialAlpha 3 12 (replace 2 10 secondTemplate)
    (by decide) (by decide) (by decide)).1
  have he : replace 3 12 (replace 2 10 secondTemplate) = secondImageBody := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 10,secondClause.encode]
  have hx : Context Γ (member 1 10) := .head _ _
  have hf : Context Γ secondClause.encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (imp (member 1 10)
      (existsCode 3 (replace 2 10 secondTemplate).encode)) := by
    simpa only [secondClause, Formula.encode] using Context.mp hf (.closed hi)
  exact .mp (.mp hx hs') (.closed ha)

/-- Both clauses and the one common-source membership produce two nested
image witnesses. Neither image endpoint is assumed candidate. -/
def selected_images_exist : KDerivation
    (imp firstClause.encode (imp secondClause.encode
      (imp (member 1 10) selected.encode))) := by
  let F := firstImageBody.encode
  let T := secondImageBody.encode
  let B := secondClause.encode
  let M := member 1 10
  let P := both F T
  have hlocal : Context [M,B] (imp F (existsCode 12 P)) := by
    apply Context.deduction
    let Γ := [F,M,B]
    have hf : Context Γ F := .head _ _
    have hm : Context Γ M := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have ht : Context Γ (existsCode 12 T) := .mp hm (.mp hb (.closed second_image_exists))
    have hc : Context Γ (imp T P) := by
      apply Context.deduction
      exact Context.conjunctionIntro (.under hf T) (.head Γ T)
    have hv : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 12 f)) := by
      intro f hmem
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hmem
      by_cases hF : f = F
      · subst f; exact firstImageBody.vacuity 12 (by decide)
      · have hmem' := hmem.resolve_left hF
        by_cases hM : f = M
        · subst f; exact (Formula.member 1 10).vacuity 12 (by decide)
        · have hB : f = B := hmem'.resolve_left hM
          subst f; exact secondClause.vacuity 12 (by decide)
    exact exists_map_context (Context.generalize 12 hv hc) ht
  have hv : ∀ f, f ∈ [M,B] → KDerivation (imp f (allCode 11 f)) := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases hM : f = M
    · subst f; exact (Formula.member 1 10).vacuity 11 (by decide)
    · have hB : f = B := hf.resolve_left hM
      subst f; exact secondClause.vacuity 11 (by decide)
  have hall : Context [M,B] (allCode 11 (imp F (existsCode 12 P))) :=
    Context.generalize 11 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [M,B,firstClause.encode]
  have hm : Context Γ M := .head _ _
  have hb : Context Γ firstClause.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (existsCode 11 F) := .mp hm (.mp hb (.closed first_image_exists))
  have hall' : Context Γ (allCode 11 (imp F (existsCode 12 P))) :=
    Context.weaken hall (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with h | h <;> subst a <;> simp [Γ])
  have hout : Context Γ (existsCode 11 (existsCode 12 P)) := exists_map_context hall' hf
  simpa only [selected, namedBoth, Formula.not, Formula.encode, both, neg, P, F, T] using hout

theorem selected_images_exist_certificate :
    theoremCode (certificate selected_images_exist) =
      imp firstClause.encode (imp secondClause.encode (imp (member 1 10) selected.encode)) :=
  certificate_correct selected_images_exist

end PASoundness.PAtoCompactCommonSourceSpanImages

#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.firstTemplate
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.secondTemplate
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.firstClauseBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.secondClauseBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.firstClause
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.secondClause
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.firstImageBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.secondImageBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.selected
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.first_image_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.second_image_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.selected_images_exist
#print axioms PASoundness.PAtoCompactCommonSourceSpanImages.selected_images_exist_certificate
