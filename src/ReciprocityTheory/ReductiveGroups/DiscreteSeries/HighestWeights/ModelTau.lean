module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelFun
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OpEqExp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Formalism.RealPlaceAnalysis.StatementKT
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PiTensorProduct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace, ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner, ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen, ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelFun\npublic import Mathlib.Algebra.MvPolynomial.Monad\npublic import Mathlib.RingTheory.MvPolynomial.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rtr (ε : Fin n → Bool) (k : KG ε) : (KG ε → ℂ) →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rtr_mul (ε : Fin n → Bool) (k₁ k₂ : KG ε) (f : KG ε → ℂ) : rtr ε (k₁ * k₂) f = rtr ε k₁ (rtr ε k₂ f) := by
  funext x
  show f (x * (k₁ * k₂)) = f (x * k₁ * k₂)
  rw [mul_assoc]

theorem rtr_one (ε : Fin n → Bool) (f : KG ε → ℂ) : rtr ε 1 f = f := by
  funext x
  show f (x * 1) = f x
  rw [mul_one]

def Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ (Set.range fun k : KG ε => rtr ε k (f0K ε m))

theorem highest_weight_fn_mem_space (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m ∈ Vsp ε m := by
  have h : rtr ε 1 (f0K ε m) ∈ Vsp ε m := Submodule.subset_span ⟨1, rfl⟩
  rwa [rtr_one] at h

theorem rtr_mem (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    rtr ε k f ∈ Vsp ε m := by
  have h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k', rfl⟩
    show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m
    rw [← rtr_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  exact h hf

def evalK (ε : Fin n → Bool) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] (KG ε → ℂ) :=
  MvPolynomial.aeval fun p : Fin n × Fin n => fun k : KG ε => toMK k p.1 p.2

def polyK (ε : Fin n → Bool) (D : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap

theorem evalK_apply (ε : Fin n → Bool) (Q : MvPolynomial (Fin n × Fin n) ℂ) (x : KG ε) :
    evalK ε Q x = MvPolynomial.aeval (fun p : Fin n × Fin n => toMK x p.1 p.2) Q := by
  induction Q using MvPolynomial.induction_on
  next a => simp [evalK]
  next p q hp hq => rw [map_add (f := _), map_add (f := _), Pi.add_apply, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, Pi.mul_apply, hp]
    simp [evalK]

def rsub (ε : Fin n → Bool) (k : KG ε) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
  fun p => ∑ l, MvPolynomial.X (p.1, l) * MvPolynomial.C (toMK k l p.2)

theorem toMK_mul' (ε : Fin n → Bool) (x k : KG ε) : toMK (x * k) = toMK x * toMK k := rfl

theorem rtr_evalK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) := by
  funext x
  show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x
  rw [evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext p
  simp [rsub, toMK_mul', Matrix.mul_apply]

theorem totalDegree_rsub (ε : Fin n → Bool) (k : KG ε) (p : Fin n × Fin n) :
    (rsub ε k p).totalDegree ≤ 1 := by
  simp only [rsub]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

theorem totalDegree_bind₁_le {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  apply GlobalTheory.PolyEntryMul.totalDegree_bind₁_le_of_le_one <;> assumption

theorem rtr_polyK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) ∈ polyK ε Q.totalDegree := by
  rw [rtr_evalK]
  exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr
    (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))

def f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ a, ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det ^ (mexp ε m a).toNat

theorem evalK_f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : evalK ε (f0P ε m) = f0K ε m := by
  funext k
  rw [evalK_apply]
  show _ = f0 ε m (toMK k)
  simp only [f0P, f0, blkMinor, map_prod, map_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem Vsp_le_polyK (ε : Fin n → Bool) (m : Fin n → ℤ) : ∃ D : ℕ, Vsp ε m ≤ polyK ε D := by
  refine ⟨(f0P ε m).totalDegree, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨k, rfl⟩
  show rtr ε k (f0K ε m) ∈ polyK ε _
  rw [← evalK_f0P]
  exact rtr_polyK ε k (f0P ε m)

theorem finiteDimensional_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (Vsp ε m) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  haveI : FiniteDimensional ℂ (polyK ε D) := by
    unfold polyK
    infer_instance
  exact Submodule.finiteDimensional_of_le hD

theorem differentiable_aeval_entries (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q) := by
  induction Q using MvPolynomial.induction_on
  next a => simp
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    have hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2) := by
      fun_prop
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul hX

theorem Vsp_holo (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, Differentiable ℂ F ∧ ∀ k, f k = F (toMK k) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  have h' : f ∈ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap := hD hf
  obtain ⟨Q, -, rfl⟩ := Submodule.mem_map.mp h'
  exact ⟨fun M => MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q,
    differentiable_aeval_entries Q, fun k => evalK_apply ε Q k⟩

theorem continuous_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    Continuous f := by
  obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m hf
  have hfe : f = fun k => F (toMK k) := funext hfF
  rw [hfe]
  refine hF.continuous.comp ?_
  fun_prop

theorem hasDerivAt_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F) (hfF : ∀ k, f k = F (toMK k))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (x : KG ε) :
    HasDerivAt (fun t : ℝ => f (x * kcurve ε X t)) (fderiv ℂ F (toMK x) (toMK x * X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => toMK (kcurve ε X t)) X 0 := by
    have hk : ∀ t : ℝ, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℝ) • X) := fun t => by
       unfold kcurve
       rw [dite_eq_left hX, Classical.choose_spec (exists_curve ε hX) t, Complex.coe_smul]
    simp only [hk]
    letI iR : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
    haveI : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ)
        (@PseudoMetricSpace.toUniformSpace _ (@MetricSpace.toPseudoMetricSpace _ (@NormedRing.toMetricSpace _ iR))) := by
      exact FiniteDimensional.complete ℂ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (toMK x))
  have hin : HasDerivAt (fun t : ℝ => L (toMK (kcurve ε X t))) (L X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hc
  have h0 : toMK (kcurve ε X 0) = 1 := by
    unfold kcurve
    rw [dite_eq_left hX, Classical.choose_spec (exists_curve ε hX) 0]
    simp
  have hLx : L (toMK (kcurve ε X 0)) = toMK x := by
    rw [h0]
    exact mul_one _
  have hF' := ((hF (toMK x)).hasFDerivAt.restrictScalars ℝ)
  rw [← hLx] at hF'
  have hcomp := hF'.comp_hasDerivAt (0 : ℝ) hin
  have hfun : (fun t : ℝ => f (x * kcurve ε X t)) = fun t => F (L (toMK (kcurve ε X t))) := by
    funext t
    rw [hfF, toMK_mul']
    rfl
  rw [hfun]
  rw [hLx] at hcomp
  exact hcomp

end ReciprocityTheory.ChartRestriction.DS.HW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def MV (ε : Fin n → Bool) (m : Fin n → ℤ) : Type := ↥(Vsp ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : AddCommGroup (MV ε m) := inferInstanceAs (AddCommGroup ↥(Vsp ε m))

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : Module ℂ (MV ε m) := inferInstanceAs (Module ℂ ↥(Vsp ε m))

def MV.fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : KG ε → ℂ := ((show ↥(Vsp ε m) from f) : KG ε → ℂ)

def MV.mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) : MV ε m :=
  (⟨f, hf⟩ : ↥(Vsp ε m))

theorem MV.mem {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : f.fn ∈ Vsp ε m := by
  exact (show ↥(Vsp ε m) from f).2

theorem MV.ext {ε : Fin n → Bool} {m : Fin n → ℤ} {f g : MV ε m} (h : f.fn = g.fn) : f = g := by
  exact Subtype.ext h

@[simp] theorem MV.fn_add {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : (f + g).fn = f.fn + g.fn := rfl

@[simp] theorem MV.fn_smul {ε : Fin n → Bool} {m : Fin n → ℤ} (c : ℂ) (f : MV ε m) : (c • f).fn = c • f.fn := rfl

@[simp] theorem MV.fn_zero {ε : Fin n → Bool} {m : Fin n → ℤ} : (0 : MV ε m).fn = 0 := rfl

def mvInner {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : ℂ :=
  ∫ x, starRingEnd ℂ (f.fn x) * g.fn x ∂(muK ε)

theorem MV.continuous_fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : Continuous f.fn := by
  exact continuous_of_mem_Vsp ε m f.mem

theorem integrable_of_continuous_KG {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    MeasureTheory.Integrable F (muK ε) := by

  have := compactSpace_KG ε
  exact hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

theorem mvInner_integrable {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    MeasureTheory.Integrable (fun x => starRingEnd ℂ (f.fn x) * g.fn x) (muK ε) := by
  exact integrable_of_continuous_KG
    ((Complex.continuous_conj.comp f.continuous_fn).mul g.continuous_fn)

theorem mvInner_self_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) :
    mvInner f f = ((∫ x, Complex.normSq (f.fn x) ∂(muK ε) : ℝ) : ℂ) := by
  unfold mvInner
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  exact integral_ofReal

theorem mvInner_conj {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    starRingEnd ℂ (mvInner g f) = mvInner f g := by
  unfold mvInner
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, starRingEnd_apply, star_star]
  exact mul_comm _ _

theorem mvInner_re_nonneg {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : 0 ≤ (mvInner f f).re := by
  rw [mvInner_self_eq, Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

theorem mvInner_add_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g h : MV ε m) :
    mvInner (f + g) h = mvInner f h + mvInner g h := by
  simp only [mvInner, MV.fn_add, Pi.add_apply, map_add (f := _), add_mul]
  exact integral_add (mvInner_integrable f h) (mvInner_integrable g h)

theorem mvInner_smul_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) (c : ℂ) :
    mvInner (c • f) g = starRingEnd ℂ c * mvInner f g := by
  simp only [mvInner, MV.fn_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact integral_const_mul _ _

theorem mvInner_definite {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) (h : mvInner f f = 0) : f = 0 := by

  have hc : Continuous fun x => Complex.normSq (f.fn x) :=
    Complex.continuous_normSq.comp f.continuous_fn
  rw [mvInner_self_eq, Complex.ofReal_eq_zero] at h
  have hae : (fun x => Complex.normSq (f.fn x)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
      (by
        have := compactSpace_KG ε
        exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)).mp h
  have hz : (fun x => Complex.normSq (f.fn x)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hc continuous_const).mp hae
  apply MV.ext
  funext x
  simpa using congrFun hz x

@[instance_reducible]
def mvCore (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace.Core ℂ (MV ε m) where
  inner := mvInner
  conj_inner_symm := mvInner_conj
  re_inner_nonneg := mvInner_re_nonneg
  add_left := mvInner_add_left
  smul_left := mvInner_smul_left
  definite := mvInner_definite

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : NormedAddCommGroup (MV ε m) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (MV ε m) _ _ _ (mvCore ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace ℂ (MV ε m) :=
  InnerProductSpace.ofCore (mvCore ε m).toCore

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (MV ε m) :=
  finiteDimensional_Vsp ε m

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : CompleteSpace (MV ε m) := FiniteDimensional.complete ℂ _

end ReciprocityTheory.ChartRestriction.DS.HW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen", "h": "module\n\npublic import Formalism.RealPlaceAnalysis.StatementKT\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement\npublic import Formalism.RealPlaceAnalysis.QuotientSettingHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGenA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Pre

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)


theorem pre_dτ_stable_of_kStable (W : Submodule ℂ V) (hW : Formalism.REAL.KStable ε (preUnits dτ) W) :
    ∀ Y, inK ε Y → ∀ v ∈ W, dτ Y v ∈ W := by
  intro Y hY v hv

  rw [Matrix.matrix_eq_sum_single Y, map_sum, _root_.sum_apply]
  refine W.sum_mem fun a _ => ?_

  rw [map_sum, _root_.sum_apply]
  refine W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · have e : Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 := by
      ext i j; simp [Matrix.single_apply]
    rw [e, map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab v hv)
  · have e : Matrix.single a b (Y a b) = 0 := by
      rw [inK_entry_eq_zero hY hab]; ext i j; simp [Matrix.single_apply]
    rw [e, map_zero, _root_.zero_apply]
    exact W.zero_mem


include hcont hder in
theorem pre_kStable_of_stable (W : Submodule ℂ V)
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) :
    Formalism.REAL.KStable ε (preUnits dτ) W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := hder X hX γ hγ
    have hdv : HasDerivAt (fun t : ℝ => preOp τ (γ t) v) (dτ X v) 0 := by
      have := ((ContinuousLinearMap.apply ℂ V v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    rw [hasDerivAt_iff_tendsto_slope] at hdv
    have hcl : IsClosed (W : Set V) := W.closed_of_finiteDimensional
    refine hcl.mem_of_tendsto hdv (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module, SetLike.mem_coe]
    exact Submodule.smul_of_tower_mem W _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  show dτ (Matrix.single a b 1) v ∈ W
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1
  have hA : A * Jm ε = Jm ε * A := single_mul_Jm_comm hab 1
  have hB : B * Jm ε = Jm ε * B := single_mul_Jm_comm hab.symm 1
  have hAB : Aᴴ = B := by
    ext i j
    simp only [A, B, Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]
  have hBA : Bᴴ = A := by rw [← hAB, Matrix.conjTranspose_conjTranspose]
  have h1 : inK ε (A - B) := inK_of_skew_comm (by rw [Matrix.conjTranspose_sub, hAB, hBA, neg_sub])
    (by rw [sub_mul, mul_sub, hA, hB])
  have h2 : inK ε (Complex.I • (A + B)) := inK_of_skew_comm
    (by rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hAB, hBA, Complex.star_def,
      Complex.conj_I, add_comm, neg_smul])
    (by rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hA, hB])
  have e : A = (1 / 2 : ℂ) • (A - B) - (Complex.I / 2) • (Complex.I • (A + B)) := by
    rw [smul_smul, show Complex.I / 2 * Complex.I = -(1 / 2 : ℂ) by
      rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring]
    module
  rw [e, map_sub, map_smul, map_smul, _root_.sub_apply, _root_.smul_apply,
    _root_.smul_apply]
  exact W.sub_mem (W.smul_mem _ (hK _ h1 v hv)) (W.smul_mem _ (hK _ h2 v hv))


include hcont hder in
theorem pre_kSpan_stable (x : V) (k : KG ε) :
    ∀ v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x,
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x := by
  have hS : Formalism.REAL.KStable ε (preUnits dτ) (Formalism.REAL.kSpan ε (preUnits dτ) x) := by
    intro a b hab y hy
    unfold Formalism.REAL.kSpan at hy ⊢
    rw [Submodule.mem_sInf] at hy ⊢
    intro S hS
    exact hS.2 a b hab y (hy S hS)
  obtain ⟨Y, hY, he⟩ := pre_op_eq_exp' τ dτ hder k
  rw [show ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = NormedSpace.exp (dτ Y) from he]
  exact exp_mem_of_stable _ _ (pre_dτ_stable_of_kStable dτ _ hS Y hY)


include hcont hder in
theorem irred_of_gen {Λ : Fin n → ℝ} (w : V)
    (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) :
    ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hx : w ∈ Formalism.REAL.kSpan ε (preUnits dτ) w := by
    unfold Formalism.REAL.kSpan
    rw [Submodule.mem_sInf]
    intro S hS
    exact hS.1
  have htop : Formalism.REAL.kSpan ε (preUnits dτ) w = ⊤ :=
    hgen _ (pre_kSpan_stable τ hcont dτ hder w) hx
  have hhi : Formalism.REAL.KHighest ε (preUnits dτ) Λ w :=
    ⟨fun a => hwt a, fun a b hab he => hhw a b hab he⟩
  have := Formalism.REAL.kIrr V n ε (preUnits dτ) Λ w inferInstance (pre_kRel τ dτ hder)
    (pre_kUnit τ dτ hder) hhi W (htop ▸ le_top) (pre_kStable_of_stable τ hcont dτ hder W hW)
  rwa [htop] at this

end Pre

def kTypeOfGen {ε : Fin n → Bool} {Λ : Fin n → ℝ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
    (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
    (w : V) (hw : ‖w‖ = 1) (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) : KType ε Λ where
  V := V
  τ := τ
  cont := hcont
  irred := irred_of_gen τ hcont dτ hder w hwt hhw hgen
  dτ := dτ
  hasDeriv := hder
  w := w
  w_norm := hw
  w_wt := hwt
  w_hw := hhw

end ReciprocityTheory.ChartRestriction.DS.HW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def tauL (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : MV ε m →ₗ[ℂ] MV ε m where
  toFun f := MV.mk (rtr ε k f.fn) (rtr_mem ε m k f.mem)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tauC (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : MV ε m →L[ℂ] MV ε m :=
  LinearMap.toContinuousLinearMap (tauL ε m k)

@[simp] theorem tauC_fn (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) (f : MV ε m) :
    (tauC ε m k f).fn = rtr ε k f.fn := rfl

theorem tauC_one (ε : Fin n → Bool) (m : Fin n → ℤ) : tauC ε m 1 = 1 := by
  refine ContinuousLinearMap.ext fun f => MV.ext ?_
  rw [tauC_fn, rtr_one]
  rfl

theorem tauC_mul (ε : Fin n → Bool) (m : Fin n → ℤ) (k₁ k₂ : KG ε) :
    tauC ε m (k₁ * k₂) = tauC ε m k₁ * tauC ε m k₂ := by
  refine ContinuousLinearMap.ext fun f => MV.ext ?_
  rw [tauC_fn, rtr_mul, ContinuousLinearMap.mul_apply, tauC_fn, tauC_fn]

theorem tauC_inner (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) (f g : MV ε m) :
    inner ℂ (tauC ε m k f) (tauC ε m k g) = inner ℂ f g := by
  show mvInner _ _ = mvInner _ _
  unfold mvInner
  simp only [tauC_fn]
  haveI := muK_rightInvariant ε
  exact MeasureTheory.integral_mul_right_eq_self (fun x => starRingEnd ℂ (f.fn x) * g.fn x) k

theorem tauC_mem_unitary (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : tauC ε m k ∈ unitary (MV ε m →L[ℂ] MV ε m) := by
  have hinv : ∀ f, tauC ε m k (tauC ε m k⁻¹ f) = f := by
    intro f
    rw [← ContinuousLinearMap.mul_apply, ← tauC_mul, mul_inv_cancel, tauC_one]
    rfl
  have hinv' : ∀ f, tauC ε m k⁻¹ (tauC ε m k f) = f := by
    intro f
    rw [← ContinuousLinearMap.mul_apply, ← tauC_mul, inv_mul_cancel, tauC_one]
    rfl
  have hadj : star (tauC ε m k) = tauC ε m k⁻¹ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← tauC_inner ε m k (tauC ε m k⁻¹ x) y, hinv]
  first
    | rw [Unitary.mem_iff, hadj]
  constructor
  · ext f
    rw [ContinuousLinearMap.mul_apply, hinv', ContinuousLinearMap.one_apply]
  · ext f
    rw [ContinuousLinearMap.mul_apply, hinv, ContinuousLinearMap.one_apply]

def mvFnL (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := f.fn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mvFnL_injective (ε : Fin n → Bool) (m : Fin n → ℤ) : Function.Injective (mvFnL ε m) := fun _ _ h => MV.ext h

theorem continuous_tauC_apply (ε : Fin n → Bool) (m : Fin n → ℤ) (f : MV ε m) :
    Continuous fun k : KG ε => tauC ε m k f := by
  let e := (LinearEquiv.ofInjective (mvFnL ε m) (mvFnL_injective ε m)).toContinuousLinearEquiv
  have h : Continuous fun k : KG ε => e (tauC ε m k f) := by
    refine continuous_induced_rng.2 ?_
    have hfun : (fun k : KG ε => ((e (tauC ε m k f) : LinearMap.range (mvFnL ε m)) : KG ε → ℂ)) =
        fun k x => f.fn (x * k) := rfl
    rw [Function.comp_def, hfun]
    exact continuous_pi fun x => (continuous_of_mem_Vsp ε m f.mem).comp (continuous_const.mul continuous_id)
  have h2 : (fun k : KG ε => tauC ε m k f) = fun k => e.symm (e (tauC ε m k f)) := by
    funext k; simp
  rw [h2]
  exact e.symm.continuous.comp h

theorem continuous_tauC (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (tauC ε m) :=
  continuous_clm_apply.2 (continuous_tauC_apply ε m)

def tauM (ε : Fin n → Bool) (m : Fin n → ℤ) : KG ε →* unitary (MV ε m →L[ℂ] MV ε m) where
  toFun k := ⟨tauC ε m k, tauC_mem_unitary ε m k⟩
  map_one' := Subtype.ext (tauC_one ε m)
  map_mul' k₁ k₂ := Subtype.ext (tauC_mul ε m k₁ k₂)

theorem continuous_tauM (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (tauM ε m) := continuous_induced_rng.2 (continuous_tauC ε m)

private theorem derOp_fn_eq_deriv_kcurve (ε : Fin n → Bool) (m : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (f : MV ε m)
    (x : KG ε) : (derOp ε (tauM ε m) X f).fn x = deriv (fun t : ℝ => f.fn (x * kcurve ε X t)) 0 := by
  by_cases hX : inK ε X
  · have h := derOp_hasDeriv ε (tauM ε m) (continuous_tauM ε m) X hX (kcurve ε X) (kcurve_spec ε hX).2.1
    let evx : MV ε m →ₗ[ℂ] ℂ :=
      { toFun := fun g => g.fn x
        map_add' := fun a b => by simp
        map_smul' := fun c a => by simp }
    let E : (MV ε m →L[ℂ] MV ε m) →L[ℂ] ℂ :=
      (LinearMap.toContinuousLinearMap evx).comp (ContinuousLinearMap.apply ℂ (MV ε m) f)
    have h2 := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    have h3 : HasDerivAt (fun t : ℝ => f.fn (x * kcurve ε X t)) ((derOp ε (tauM ε m) X f).fn x) 0 := h2
    exact h3.deriv.symm
  · have hk : kcurve ε X = fun _ => 1 := by
      unfold kcurve
      rw [dite_eq_right hX]
    simp [derOp, hk]

theorem derOp_fn (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (f : MV ε m)
    (x : KG ε) : (derOp ε (tauM ε m) X f).fn x = deriv (fun t : ℝ => f.fn (x * kcurve ε X t)) 0 := by
  exact derOp_fn_eq_deriv_kcurve ε m X f x

theorem inK_add' (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · unfold inG at h1 h3 ⊢
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem derOp_fn_eq (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (f : MV ε m) (x : KG ε) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F)
    (hfF : ∀ k, f.fn k = F (toMK k)) :
    (derOp ε (tauM ε m) X f).fn x = fderiv ℂ F (toMK x) (toMK x * X) := by
  rw [derOp_fn ε m hX f x]
  exact (hasDerivAt_of_mem_Vsp ε m f.mem hF hfF hX x).deriv

theorem rLinOnK_derOp (ε : Fin n → Bool) (m : Fin n → ℤ) : RLinOnK ε (derOp ε (tauM ε m)) := by
  intro X Y r hX hY
  constructor
  · refine ContinuousLinearMap.ext fun f => MV.ext (funext fun x => ?_)
    obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m f.mem
    rw [_root_.add_apply, MV.fn_add, Pi.add_apply, derOp_fn_eq ε m (inK_add' ε hX hY) f x hF hfF,
      derOp_fn_eq ε m hX f x hF hfF, derOp_fn_eq ε m hY f x hF hfF, Matrix.mul_add, map_add]
  · refine ContinuousLinearMap.ext fun f => MV.ext (funext fun x => ?_)
    obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m f.mem
    rw [_root_.smul_apply, MV.fn_smul, Pi.smul_apply, smul_eq_mul,
      derOp_fn_eq ε m (_root_.ReciprocityTheory.ChartRestriction.DS.HW.inK_ofReal_smul ε hX r) f x hF hfF, derOp_fn_eq ε m hX f x hF hfF, Matrix.mul_smul, map_smul,
      smul_eq_mul]

def dTau (ε : Fin n → Bool) (m : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (MV ε m →L[ℂ] MV ε m) :=
  cextL ε (derOp ε (tauM ε m)) (rLinOnK_derOp ε m)

theorem dTau_fn (ε : Fin n → Bool) (m : Fin n → ℤ) (Z : Matrix (Fin n) (Fin n) ℂ) (f : MV ε m) (x : KG ε) :
    (dTau ε m Z f).fn x = rdc ε Z f.fn x := by
  unfold dTau
  rw [cextL_apply]
  unfold cext
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, MV.fn_add, MV.fn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, derOp_fn_eq_deriv_kcurve]
  rfl

theorem hasDeriv_dTau (ε : Fin n → Bool) (m : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((tauM ε m (γ t) : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m))
      (dTau ε m X) 0 := by
  have h := derOp_hasDeriv ε (tauM ε m) (continuous_tauM ε m) X hX γ hγ
  have he : dTau ε m X = derOp ε (tauM ε m) X := by
    unfold dTau
    rw [cextL_apply, cext_of_inK _ (rLinOnK_derOp ε m) hX]
  simpa [he] using h

def w0 (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m := MV.mk (f0K ε m) (highest_weight_fn_mem_space ε m)

def wN (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m := ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) • w0 ε m

theorem highest_weight_vector_ne_zero (ε : Fin n → Bool) (m : Fin n → ℤ) : w0 ε m ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : MV ε m => f.fn 1) h
  simp only [MV.fn_zero, Pi.zero_apply] at h1
  have h2 : (w0 ε m).fn 1 = 1 := highest_weight_fn_K_one ε m
  rw [h2] at h1
  exact one_ne_zero h1

theorem norm_wN (ε : Fin n → Bool) (m : Fin n → ℤ) : ‖wN ε m‖ = 1 := by
  have h0 : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.mpr (highest_weight_vector_ne_zero ε m)
  unfold wN
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ h0]

theorem derived_action_weight_vector (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (Matrix.single a a 1) (w0 ε m) = (((m a : ℝ)) : ℂ) • w0 ε m := by
  apply MV.ext
  funext x
  rw [dTau_fn, MV.fn_smul, Pi.smul_apply, smul_eq_mul]
  have h := rdc_f0K_wt ε hm a x
  rw [show (w0 ε m).fn = f0K ε m from rfl, h]
  push_cast
  ring

theorem derived_action_highest_vector (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : dTau ε m (Matrix.single a b 1) (w0 ε m) = 0 := by
  apply MV.ext
  funext x
  rw [dTau_fn, MV.fn_zero, Pi.zero_apply]
  exact rdc_f0K_hw ε hm hab he x

theorem dTau_wt (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (Matrix.single a a 1) (wN ε m) = (((m a : ℝ)) : ℂ) • wN ε m := by
  unfold wN
  rw [map_smul, derived_action_weight_vector ε hm a, smul_comm]

theorem dTau_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : dTau ε m (Matrix.single a b 1) (wN ε m) = 0 := by
  unfold wN
  rw [map_smul, derived_action_highest_vector ε hm a b hab he, smul_zero]

theorem gen_wN (ε : Fin n → Bool) (m : Fin n → ℤ) (W : Submodule ℂ (MV ε m))
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((tauM ε m k : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m) v ∈ W)
    (hw : wN ε m ∈ W) : W = ⊤ := by
  have hn : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.mpr (highest_weight_vector_ne_zero ε m)
  have hw0 : w0 ε m ∈ W := by
    have h : w0 ε m = ((‖w0 ε m‖ : ℝ) : ℂ) • wN ε m := by
      unfold wN
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
    rw [h]
    exact W.smul_mem _ hw
  have htr : ∀ k : KG ε, rtr ε k (f0K ε m) ∈ W.map (mvFnL ε m) :=
    fun k => ⟨tauC ε m k (w0 ε m), hW k _ hw0, rfl⟩
  have hle : Vsp ε m ≤ W.map (mvFnL ε m) := by
    rw [Vsp, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact htr k
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.mem
  rw [← mvFnL_injective ε m hyx]
  exact hy

def modelKType (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) : KType ε (fun a => (m a : ℝ)) :=
  kTypeOfGen (MV ε m) (tauM ε m) (continuous_tauM ε m) (dTau ε m) (hasDeriv_dTau ε m) (wN ε m) (norm_wN ε m)
    (dTau_wt ε hm) (dTau_hw ε hm) (gen_wN ε m)

theorem model_exists (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    Nonempty (KType ε (fun a => (m a : ℝ))) := ⟨modelKType ε hm⟩

end ReciprocityTheory.ChartRestriction.DS.HW
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau =====
