import PASoundness.PAtoCompactProductOutputSelectedPath

/-! Transport the selected path to a queried triple when all three queried
coordinates equal the selected coordinates. No distinctness of represented
values or graph-collection claim is assumed. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSelectedPathAtQuery

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactProductOutputPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def selected_path_at_query : KDerivation (imp (equal 56 30) (imp (equal 57 31)
    (imp (equal 60 33) (imp partialPath.encode pathAt.encode)))) := by
  have h1 := (equalityReplace 30 56 partialPath (by decide) (by decide)).1
  have h2 := (equalityReplace 31 57 (replace 30 56 partialPath) (by decide) (by decide)).1
  have h3 := (equalityReplace 33 60 (replace 31 57 (replace 30 56 partialPath))
    (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [partialPath.encode,equal 60 33,equal 57 31,equal 56 30]
  have hp : Context Γ partialPath.encode := .head _ _
  have he3 : Context Γ (equal 60 33) := .hypothesis (by simp [Γ])
  have he2 : Context Γ (equal 57 31) := .hypothesis (by simp [Γ])
  have he1 : Context Γ (equal 56 30) := .hypothesis (by simp [Γ])
  have hp1 := Context.mp hp (Context.mp (Context.eqSymm he1) (.closed h1))
  have hp2 := Context.mp hp1 (Context.mp (Context.eqSymm he2) (.closed h2))
  have hp3 := Context.mp hp2 (Context.mp (Context.eqSymm he3) (.closed h3))
  simpa [pathAt] using hp3

theorem selected_path_at_query_certificate : theoremCode (certificate selected_path_at_query) =
    imp (equal 56 30) (imp (equal 57 31) (imp (equal 60 33)
      (imp partialPath.encode pathAt.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSelectedPathAtQuery

#print axioms PASoundness.PAtoCompactProductOutputSelectedPathAtQuery.selected_path_at_query
#print axioms PASoundness.PAtoCompactProductOutputSelectedPathAtQuery.selected_path_at_query_certificate
