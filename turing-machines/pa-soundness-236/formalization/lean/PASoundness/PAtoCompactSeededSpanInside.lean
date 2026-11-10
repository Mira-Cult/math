import PASoundness.PAtoCompactSeededSpanStepWitness
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Inside-source successor construction for seeded common-source span collection.
Two supplied forward-bijection clauses choose the selected image witnesses;
the pair and adjoined graph are then constructed in K. The old span graph,
common-source membership and prefix successor remain explicit hypotheses.
This does not yet derive the outside-source case or candidate induction. -/
namespace PASoundness.PAtoCompactSeededSpanInside

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactSeededSpanStepWitness PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def stable : Formula := namedBoth seededSpan
  (namedBoth (.member 1 10) (namedSuccessor 10 13 15))

def imageBundle : Formula := namedBoth firstImageBody secondImageBody

def nextExists : Formula := .ex 9 nextInvariant

theorem selected_syntax : selected.encode =
    existsCode 11 (existsCode 12 imageBundle.encode) := rfl

/-- Selected image witnesses can be eliminated while retaining the old span,
common input membership and prefix successor. -/
def eliminate_selected_images : KDerivation
    (imp stable.encode (imp selected.encode nextExists.encode)) := by
  have hpoint : KDerivation (imp stable.encode (imp imageBundle.encode nextExists.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [imageBundle.encode,stable.encode]
    have hb : Context Γ imageBundle.encode := .head _ _
    have hs : Context Γ stable.encode := .hypothesis (by simp [Γ])
    have hfirst := Context.conjunctionLeft hb
    have hsecond := Context.conjunctionRight hb
    have hi := Context.conjunctionLeft hs
    have hstable := Context.conjunctionRight hs
    have hm := Context.conjunctionLeft hstable
    have hsucc := Context.conjunctionRight hstable
    have hr : Context Γ retained.encode := Context.conjunctionIntro hi
      (Context.conjunctionIntro hfirst (Context.conjunctionIntro hsecond
        (Context.conjunctionIntro hm hsucc)))
    have hn : Context Γ (existsCode 9 nextInvariant.encode) := .mp hr (.closed next_graph_exists)
    simpa only [nextExists, Formula.encode] using hn
  have h12 := guarded_exists_left 12 stable.encode imageBundle.encode nextExists.encode
    (free_vacuity 12 stable (by decide)) (free_vacuity 12 nextExists (by decide)) hpoint
  have h11 := guarded_exists_left 11 stable.encode (existsCode 12 imageBundle.encode) nextExists.encode
    (free_vacuity 11 stable (by decide)) (free_vacuity 11 nextExists (by decide)) h12
  simpa only [selected_syntax] using h11

/-- The two forward clauses choose both image witnesses and construct a new
span graph at the successor prefix. No candidate condition is imposed on the
image objects. -/
def inside_successor : KDerivation
    (imp firstClause.encode (imp secondClause.encode
      (imp stable.encode nextExists.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [stable.encode,secondClause.encode,firstClause.encode]
  have hs : Context Γ stable.encode := .head _ _
  have hg : Context Γ secondClause.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstClause.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 10) :=
    Context.conjunctionLeft (Context.conjunctionRight hs)
  have he : Context Γ selected.encode := .mp hm (.mp hg (.mp hf (.closed selected_images_exist)))
  exact .mp he (.mp hs (.closed eliminate_selected_images))

theorem inside_successor_certificate : theoremCode (certificate inside_successor) =
    imp firstClause.encode (imp secondClause.encode (imp stable.encode nextExists.encode)) :=
  certificate_correct inside_successor

end PASoundness.PAtoCompactSeededSpanInside

#print axioms PASoundness.PAtoCompactSeededSpanInside.stable
#print axioms PASoundness.PAtoCompactSeededSpanInside.imageBundle
#print axioms PASoundness.PAtoCompactSeededSpanInside.nextExists
#print axioms PASoundness.PAtoCompactSeededSpanInside.selected_syntax
#print axioms PASoundness.PAtoCompactSeededSpanInside.eliminate_selected_images
#print axioms PASoundness.PAtoCompactSeededSpanInside.inside_successor
#print axioms PASoundness.PAtoCompactSeededSpanInside.inside_successor_certificate
