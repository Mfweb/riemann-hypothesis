module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem KRep.kUnit_units {ε : Fin n → Bool} (R : KRep ε) : Formalism.REAL.KUnit ε R.units :=
  pre_kUnit R.τ R.dτ R.hasDeriv

theorem KRep.kRel_units {ε : Fin n → Bool} (R : KRep ε) : Formalism.REAL.KRel ε R.units :=
  pre_kRel R.τ R.dτ R.hasDeriv

theorem kRepRel : KRepRelStatement := fun _ _ R => ⟨R.kRel_units, R.kUnit_units⟩

end ReciprocityTheory.ChartRestriction.DS.HW
