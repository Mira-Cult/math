import PASoundness.PAtoCompactProductCleanProductExists

/-! Capture-safe specialization of the K multiplication graph-cleaning
construction to the actual old-product names.  This retains one graph
witness satisfying both the complete product matrix and the no-garbage
condition.  It does not construct a multiplication successor or establish
multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanRebased303132
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactProductCleanProductExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The actual old product relation at operands 30,31 and result 32. -/
def oldProduct : Formula := replace 2 32 (replace 1 31 (replace 0 30 productFormula))

/-- The full old product matrix at graph 10 and names 30, 31, 32. -/
def oldMatrixActual : Formula :=
  replace 2 32 (replace 1 31 (replace 0 30 (replace 6 10 productMatrix)))

/-- Every member of that same graph is an old-domain nested triple. -/
def oldCleanActual : Formula := replace 2 32 (replace 1 31 (replace 0 30
  (.all 19 (.imp (.member 10 19) (cleanPredicate 19)))))

private def statement : Formula := .imp productFormula cleanWitness
private def moved0 : Formula := replace 0 30 statement
private def moved1 : Formula := replace 1 31 moved0
private def moved2 : Formula := replace 2 32 moved1
private def body : Formula := replace 2 32 (replace 1 31 (replace 0 30
  (namedBoth filteredMatrix (.all 19 (.imp (.member 54 19) (cleanPredicate 19))))))

private noncomputable def proved0 : KDerivation moved0.encode := by
  have h : KDerivation statement.encode := by
    simpa [statement, Formula.encode] using clean_product_exists
  have hi := universalInstance 0 30 statement (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 h) hi
private noncomputable def proved1 : KDerivation moved1.encode := by
  have hi := universalInstance 1 31 moved0 (by decide) (by decide) (by decide)
  exact .mp (.generalize 1 proved0) hi
private noncomputable def proved2 : KDerivation moved2.encode := by
  have hi := universalInstance 2 32 moved1 (by decide) (by decide) (by decide)
  exact .mp (.generalize 2 proved1) hi

private theorem moved_shape : moved2 = .imp oldProduct (.ex 54 body) := by decide
private theorem target_shape : replace 54 10 body = namedBoth oldMatrixActual oldCleanActual := by decide

/-- From the old product relation, K constructs one graph at name 10
satisfying the exact product matrix and the old-domain member-cleanliness
condition used by the multiplication successor construction. -/
noncomputable def clean_old_product_at_names : KDerivation
    (imp oldProduct.encode (existsCode 10 (namedBoth oldMatrixActual oldCleanActual).encode)) := by
  have h := proved2
  rw [moved_shape] at h
  change KDerivation (imp oldProduct.encode (existsCode 54 body.encode)) at h
  have ha := (existentialAlpha 54 10 body (by decide) (by decide) (by decide)).1
  rw [target_shape] at ha
  exact PASoundness.CompactDerivations.compose h ha

theorem clean_old_product_at_names_certificate :
    theoremCode (certificate clean_old_product_at_names) =
      imp oldProduct.encode (existsCode 10 (namedBoth oldMatrixActual oldCleanActual).encode) :=
  certificate_correct clean_old_product_at_names
end PASoundness.PAtoCompactProductCleanRebased303132
#print axioms PASoundness.PAtoCompactProductCleanRebased303132.oldProduct
#print axioms PASoundness.PAtoCompactProductCleanRebased303132.clean_old_product_at_names
#print axioms PASoundness.PAtoCompactProductCleanRebased303132.clean_old_product_at_names_certificate
