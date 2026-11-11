import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Real.Basic

/-! A finite underdetermined homogeneous system has a nonzero direction.
This is the linear-algebra ingredient for one simultaneous rounding step;
it does not establish the rounding count, step size, or discrepancy bound. -/

namespace Sude

/-- If there are fewer equations than variables, a real coefficient matrix
has a nonzero vector in its kernel. The finite index types may be empty. -/
theorem dp_underdetermined_direction {V E : Type*} [Fintype V] [Fintype E]
    (a : Matrix E V ℝ) (h : Fintype.card E < Fintype.card V) :
    ∃ d : V → ℝ, d ≠ 0 ∧ ∀ e : E, ∑ v : V, a e v * d v = 0 := by
  classical
  let f : (V → ℝ) →ₗ[ℝ] (E → ℝ) := a.mulVecLin
  have hk : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa only [Module.finrank_fintype_fun_eq_card] using h
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hfd : f d = 0 := LinearMap.mem_ker.mp hd
  refine ⟨d, hd0, ?_⟩
  intro e
  have he := congrFun hfd e
  simpa [f, Matrix.mulVec, dotProduct] using he

end Sude
