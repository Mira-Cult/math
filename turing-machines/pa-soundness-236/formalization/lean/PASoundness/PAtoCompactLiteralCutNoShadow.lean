import PASoundness.PAtoCompactLiteralCutAdditionDefinition
import PASoundness.PAtoCompactEquivNoShadow

/-! Syntactic name inventory and binder non-shadowing for the literal-cut
addition template and its mapped allocator form. This does not assert
addition totality or a compact-calculus equivalence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutNoShadow
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMapNoShadow
open PASoundness.PAtoCompactEquivNoShadow

def literalTemplate : Formula := normalizeBottom literalCut

theorem literal_names : literalTemplate.names =
    ({2,3,4,5,6,19,20,21,22,30,31,32,34,35} : Finset Nat) := by decide

theorem literal_binders : literalTemplate.binders =
    ({2,3,4,5,6,19,20,21,22,34,35} : Finset Nat) := by decide

theorem literal_free : literalTemplate.free = ({30,31,32} : Finset Nat) := by decide

theorem literal_binder_noShadow : ∀ x ∈ literalTemplate.binders, NoShadow x literalTemplate := by
  decide

theorem literal_allNoShadow (x : Nat) : NoShadow x literalTemplate := by
  by_cases hx : x ∈ literalTemplate.binders
  · exact literal_binder_noShadow x hx
  · exact noShadow_of_not_binder literalTemplate x hx

/-- Mapped binders do not shadow even when operand labels coincide. -/
theorem literal_mapped_allNoShadow (base x y z w : Nat) :
    NoShadow w (mapNames (threeMap base 30 31 32 x y z) literalTemplate) := by
  apply allNoShadow_map literalTemplate (threeMap base 30 31 32 x y z) literal_allNoShadow
  intro a ha b hb he
  have ha30 : a ≠ 30 := by intro h; subst a; simp [literal_binders] at ha
  have ha31 : a ≠ 31 := by intro h; subst a; simp [literal_binders] at ha
  have ha32 : a ≠ 32 := by intro h; subst a; simp [literal_binders] at ha
  have hb30 : b ≠ 30 := by intro h; subst b; simp [literal_binders] at hb
  have hb31 : b ≠ 31 := by intro h; subst b; simp [literal_binders] at hb
  have hb32 : b ≠ 32 := by intro h; subst b; simp [literal_binders] at hb
  simp only [threeMap, ha30, ha31, ha32, hb30, hb31, hb32, if_false] at he
  omega
end PASoundness.PAtoCompactLiteralCutNoShadow
#print axioms PASoundness.PAtoCompactLiteralCutNoShadow.literal_names
#print axioms PASoundness.PAtoCompactLiteralCutNoShadow.literal_binders
#print axioms PASoundness.PAtoCompactLiteralCutNoShadow.literal_free
#print axioms PASoundness.PAtoCompactLiteralCutNoShadow.literal_binder_noShadow
#print axioms PASoundness.PAtoCompactLiteralCutNoShadow.literal_allNoShadow
#print axioms PASoundness.PAtoCompactLiteralCutNoShadow.literal_mapped_allNoShadow
