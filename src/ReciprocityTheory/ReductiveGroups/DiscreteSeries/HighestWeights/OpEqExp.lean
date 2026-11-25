module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exists_log (ε : Fin n → Bool) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ toMK k = NormedSpace.exp Y := by
  have hk : toMK k ∈ Formalism.REAL.Kset ε := by
    rw [← Formalism.REAL.range_toMK]; exact ⟨k, rfl⟩
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.kExp n ε (toMK k) hk
  exact ⟨Y, hY, he.symm⟩

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))

variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)

include hder in
theorem pre_op_eq_exp' (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ preOp τ k = NormedSpace.exp (dτ Y) := by
  obtain ⟨Y, hY, he⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ, he]; simp)
  refine ⟨Y, hY, ?_⟩
  simpa [h1] using pre_op_curve τ dτ hder hY γ hγ 1

theorem KType.op_eq_exp {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ T.op k = NormedSpace.exp (T.dτ Y) :=
  pre_op_eq_exp' T.τ T.dτ T.hasDeriv k

end ReciprocityTheory.ChartRestriction.DS.HW
