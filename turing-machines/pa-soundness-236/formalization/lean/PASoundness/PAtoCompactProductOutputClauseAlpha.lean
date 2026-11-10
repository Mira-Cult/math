import PASoundness.PAtoCompactProductOutputForwardClauseAll
import PASoundness.PAtoCompactProductOutputReverseClauseAll
import PASoundness.PAtoCompactProductOutputLexGraphAll
import PASoundness.PAtoCompactAlphaMapOne

/-! Alpha-rename the explicit transported product clauses to the low binder
names of the standard product matrix. Conjunction reassociation and lex
quantifier-order alignment remain separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputClauseAlpha

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactProductOutputForwardClauseAll PASoundness.PAtoCompactProductOutputReverseClauseAll
open PASoundness.PAtoCompactProductOutputLexGraphAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def forwardMapped : Formula := mapNames (rename 51 9) (mapNames (rename 33 5)
  (mapNames (rename 31 4) (mapNames (rename 30 3) forwardClause)))
def reverseMapped : Formula := mapNames (rename 53 8) (mapNames (rename 51 7)
  (mapNames (rename 31 4) (mapNames (rename 30 3) (mapNames (rename 33 5) reverseClause))))
def orderMapped : Formula := mapNames (rename 55 9) (mapNames (rename 33 5)
  (mapNames (rename 51 8) (mapNames (rename 50 7) (mapNames (rename 31 4)
    (mapNames (rename 30 3) graphOrder)))))

/-- Rename the selected factor/input and unique-output binders. -/
def forward_alpha : ProofEquiv forwardClause forwardMapped := by
  let A := forwardClause
  let B := mapNames (rename 30 3) A
  let C := mapNames (rename 31 4) B
  let D := mapNames (rename 33 5) C
  have h1 := alpha_map_one 30 3 A (by decide) (by decide) (by decide) (by decide)
  have h2 := alpha_map_one 31 4 B (by decide) (by decide) (by decide) (by decide)
  have h3 := alpha_map_one 33 5 C (by decide) (by decide) (by decide) (by decide)
  have h4 := alpha_map_one 51 9 D (by decide) (by decide) (by decide) (by decide)
  simpa [forwardMapped, A, B, C, D] using h1.trans (h2.trans (h3.trans h4))

/-- Rename the target and both selected/competitor factor binders. -/
def reverse_alpha : ProofEquiv reverseClause reverseMapped := by
  let A := reverseClause
  let B := mapNames (rename 33 5) A
  let C := mapNames (rename 30 3) B
  let D := mapNames (rename 31 4) C
  let E := mapNames (rename 51 7) D
  have h1 := alpha_map_one 33 5 A (by decide) (by decide) (by decide) (by decide)
  have h2 := alpha_map_one 30 3 B (by decide) (by decide) (by decide) (by decide)
  have h3 := alpha_map_one 31 4 C (by decide) (by decide) (by decide) (by decide)
  have h4 := alpha_map_one 51 7 D (by decide) (by decide) (by decide) (by decide)
  have h5 := alpha_map_one 53 8 E (by decide) (by decide) (by decide) (by decide)
  simpa [reverseMapped, A, B, C, D, E] using h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Rename all six lex comparison binders, retaining their current order. -/
def order_alpha : ProofEquiv graphOrder orderMapped := by
  let A := graphOrder
  let B := mapNames (rename 30 3) A
  let C := mapNames (rename 31 4) B
  let D := mapNames (rename 50 7) C
  let E := mapNames (rename 51 8) D
  let F := mapNames (rename 33 5) E
  have h1 := alpha_map_one 30 3 A (by decide) (by decide) (by decide) (by decide)
  have h2 := alpha_map_one 31 4 B (by decide) (by decide) (by decide) (by decide)
  have h3 := alpha_map_one 50 7 C (by decide) (by decide) (by decide) (by decide)
  have h4 := alpha_map_one 51 8 D (by decide) (by decide) (by decide) (by decide)
  have h5 := alpha_map_one 33 5 E (by decide) (by decide) (by decide) (by decide)
  have h6 := alpha_map_one 55 9 F (by decide) (by decide) (by decide) (by decide)
  simpa [orderMapped, A, B, C, D, E, F] using h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

theorem forward_alpha_certificate : theoremCode (certificate forward_alpha.forward) =
    imp forwardClause.encode forwardMapped.encode := certificate_correct _
theorem reverse_alpha_certificate : theoremCode (certificate reverse_alpha.forward) =
    imp reverseClause.encode reverseMapped.encode := certificate_correct _
theorem order_alpha_certificate : theoremCode (certificate order_alpha.forward) =
    imp graphOrder.encode orderMapped.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputClauseAlpha

#print axioms PASoundness.PAtoCompactProductOutputClauseAlpha.forward_alpha
#print axioms PASoundness.PAtoCompactProductOutputClauseAlpha.reverse_alpha
#print axioms PASoundness.PAtoCompactProductOutputClauseAlpha.order_alpha
#print axioms PASoundness.PAtoCompactProductOutputClauseAlpha.forward_alpha_certificate
#print axioms PASoundness.PAtoCompactProductOutputClauseAlpha.reverse_alpha_certificate
#print axioms PASoundness.PAtoCompactProductOutputClauseAlpha.order_alpha_certificate
