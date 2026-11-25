module

public import Formalism.RealPlaceAnalysis.StatementKT
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))

variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)

def preUnits (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)) : Fin n → Fin n → Module.End ℂ V :=
  fun a b => ((dτ (Matrix.single a b 1) : V →L[ℂ] V) : Module.End ℂ V)

def kunits {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : Fin n → Fin n → Module.End ℂ T.V :=
  fun a b => ((T.dτ (Matrix.single a b 1) : T.V →L[ℂ] T.V) : Module.End ℂ T.V)

theorem inK_iff' (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  constructor
  · rintro ⟨hG, hC⟩
    refine ⟨?_, hC⟩
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hC]; exact eq_neg_of_add_eq_zero_left hG
    simpa only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.neg_mul] using
      congrArg (· * Jm ε) h1
  · rintro ⟨hH, hC⟩
    refine ⟨?_, hC⟩
    unfold inG
    rw [hH, Matrix.neg_mul, hC, neg_add_cancel]

theorem toMK_inv' {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = star (toMK k) :=
  Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem k.2.1)

theorem hasDerivAt_real_of_complex' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {g : ℂ → F} {g' : F} {z : ℝ} (h : HasDerivAt g g' (z : ℂ)) :
    HasDerivAt (fun y : ℝ => g (y : ℂ)) g' z := by
  have := h.scomp z Complex.ofRealCLM.hasDerivAt
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at this
  exact this

include hder in
theorem pre_star_dτ {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (dτ X) = -dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  have key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    intro t
    have h1 := pre_op_curve τ dτ hder hX γ hγ t
    have h2 : star (preOp τ (γ t)) * preOp τ (γ t) = 1 := Unitary.coe_star_mul_self _
    rw [h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal] at h2
    exact h2
  have hd0 := (hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul
    (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))
  have hd2 := hasDerivAt_real_of_complex' hd0
  have hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) *
      fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1 := funext fun t => by
    simpa using key t
  rw [hf] at hd2
  have := hd2.unique (hasDerivAt_const _ _)
  simp at this
  exact eq_neg_of_add_eq_zero_left this

theorem inK_conj' {ε : Fin n → Bool} (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    inK ε (toMK k * Y * star (toMK k)) := by
  rw [inK_iff'] at hY ⊢
  have hK := k.2.2
  have hK' : star (toMK k) * Jm ε = Jm ε * star (toMK k) := (Kset_star ε k.2).2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hY.1]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]
  · calc toMK k * Y * star (toMK k) * Jm ε = toMK k * (Y * (star (toMK k) * Jm ε)) := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * (Y * (Jm ε * star (toMK k))) := by rw [hK']
      _ = toMK k * ((Y * Jm ε) * star (toMK k)) := by simp only [Matrix.mul_assoc]
      _ = toMK k * ((Jm ε * Y) * star (toMK k)) := by rw [hY.2]
      _ = (toMK k * Jm ε) * Y * star (toMK k) := by simp only [Matrix.mul_assoc]
      _ = Jm ε * toMK k * Y * star (toMK k) := by rw [hK]
      _ = Jm ε * (toMK k * Y * star (toMK k)) := by simp only [Matrix.mul_assoc]

include hder in
theorem pre_conj_dτ (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    preOp τ k * dτ Y * star (preOp τ k) = dτ (toMK k * Y * star (toMK k)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' k hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK k) :=
    toMK_inv' k
  have hγ' : ∀ t : ℝ, toMK (k * γ t * k⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK k * Y * star (toMK k))) := by
    intro t
    have e1 : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  set B := dτ Y
  set C := dτ (toMK k * Y * star (toMK k))
  have key : ∀ t : ℝ, preOp τ k * NormedSpace.exp ((t : ℂ) • B) * star (preOp τ k) =
      NormedSpace.exp ((t : ℂ) • C) := by
    intro t
    rw [← pre_op_curve τ dτ hder hY γ hγ t, ← pre_op_curve τ dτ hder hY' _ hγ' t, ← preOp_inv,
      preOp_mul, preOp_mul]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (preOp τ k)).mul_const (star (preOp τ k)))
  have h2 := hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))
  have hf : (fun y : ℝ => preOp τ k * NormedSpace.exp ((y : ℂ) • B) * star (preOp τ k)) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • C) := funext key
  simp only [hf] at h1
  have := h1.unique h2
  simpa using this

theorem KType.conj_dτ {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    T.op k * T.dτ Y * star (T.op k) = T.dτ (toMK k * Y * star (toMK k)) :=
  pre_conj_dτ T.τ T.dτ T.hasDeriv k hY

section MatDeriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem mat_conj_hasDerivAt (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun z : ℂ => NormedSpace.exp (z • X) * Y * NormedSpace.exp (z • (-X)))
      (X * Y - Y * X) ((0 : ℝ) : ℂ) := by
  have := ((hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ)).mul_const Y).mul
    (hasDerivAt_exp_smul_const (-X) ((0 : ℝ) : ℂ))
  refine HasDerivAt.congr_deriv this ?_
  simp [sub_eq_add_neg]

theorem pre_dτ_conj_hasDerivAt (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (dτ (X * Y - Y * X)) 0 := by
  have h := ((LinearMap.toContinuousLinearMap dτ).hasFDerivAt).comp_hasDerivAt _
    (mat_conj_hasDerivAt X Y)
  exact hasDerivAt_real_of_complex' (z := 0) h

end MatDeriv

include hder in
theorem pre_dτ_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    dτ X * dτ Y - dτ Y * dτ X = dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  set B := dτ Y
  have hA := pre_star_dτ τ dτ hder hX
  have hXs := ((inK_iff' ε X).1 hX).1
  have key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) =
      dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) := by
    intro s
    have h := pre_conj_dτ τ dτ hder (γ s) hY
    rw [pre_op_curve τ dτ hder hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA,
      Complex.star_def, Complex.conj_ofReal] at h
    rw [h]
    congr 2
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
      Complex.star_def, Complex.conj_ofReal]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul
      (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))
  have h2 := pre_dτ_conj_hasDerivAt dτ X Y
  have h1' := h1.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
    (Filter.Eventually.of_forall fun s => (key s).symm)
  have := h1'.unique h2
  rw [← this]
  simp [sub_eq_add_neg]

theorem single_mul_Jm {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    Matrix.single a b c * Jm ε = Jm ε * Matrix.single a b c := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [h, mul_comm]
  all_goals simp [hi, hj]

def kp1 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - Matrix.single b a 1)

def kp2 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (Matrix.single a b 1 + Matrix.single b a 1)

theorem single_eq_kp (a b : Fin n) :
    Matrix.single a b (1 : ℂ) = kp1 a b + Complex.I • kp2 a b := by
  unfold kp1 kp2
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]
  have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [← mul_assoc, hI]
  split_ifs <;> ring

theorem single_eq_kp' (a b : Fin n) :
    Matrix.single b a (1 : ℂ) = -kp1 a b + Complex.I • kp2 a b := by
  unfold kp1 kp2
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    smul_eq_mul]
  have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [← mul_assoc, hI]
  split_ifs <;> ring

theorem inK_hermitian_unit {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) : inK ε (kp1 a b) := by
  rw [inK_iff']
  unfold kp1
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, ← neg_sub, smul_neg]
    simp
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, single_mul_Jm h,
      single_mul_Jm h.symm]

theorem inK_skew_hermitian_unit {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) : inK ε (kp2 a b) := by
  rw [inK_iff']
  unfold kp2
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, add_comm, ← neg_smul]
    congr 1 <;> simp [Complex.conj_I] <;> ring
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, single_mul_Jm h,
      single_mul_Jm h.symm]

theorem brk_expand {R : Type*} [Ring R] [Algebra ℂ R] (a1 a2 b1 b2 : R) :
    (a1 + Complex.I • a2) * (b1 + Complex.I • b2) - (b1 + Complex.I • b2) * (a1 + Complex.I • a2) =
      (a1 * b1 - b1 * a1) + Complex.I • (a1 * b2 - b2 * a1) + Complex.I • (a2 * b1 - b1 * a2) +
        (Complex.I * Complex.I) • (a2 * b2 - b2 * a2) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, smul_sub]
  abel

include hder in
theorem pre_dτ_bracket_single {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    dτ (Matrix.single a b 1) * dτ (Matrix.single c d 1) -
        dτ (Matrix.single c d 1) * dτ (Matrix.single a b 1) =
      dτ (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
  rw [single_eq_kp a b, single_eq_kp c d, brk_expand, map_add (f := _), map_add (f := _), map_smul, map_smul,
    brk_expand, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    pre_dτ_bracket τ dτ hder (inK_hermitian_unit hab) (inK_hermitian_unit hcd), pre_dτ_bracket τ dτ hder (inK_hermitian_unit hab) (inK_skew_hermitian_unit hcd),
    pre_dτ_bracket τ dτ hder (inK_skew_hermitian_unit hab) (inK_hermitian_unit hcd), pre_dτ_bracket τ dτ hder (inK_skew_hermitian_unit hab) (inK_skew_hermitian_unit hcd)]

include hder in
theorem pre_star_dτ_single {a b : Fin n} (hab : ε a = ε b) :
    star (dτ (Matrix.single a b 1)) = dτ (Matrix.single b a 1) := by
  rw [single_eq_kp a b, single_eq_kp' a b, map_add (f := _), map_smul, map_add (f := _), map_smul, map_neg, star_add,
    star_smul, pre_star_dτ τ dτ hder (inK_hermitian_unit hab), pre_star_dτ τ dτ hder (inK_skew_hermitian_unit hab)]
  simp [Complex.conj_I]

include hder in
theorem pre_kRel : Formalism.REAL.KRel ε (preUnits dτ) := by
  intro a b c d hab hcd
  have hbr := pre_dτ_bracket_single τ dτ hder hab hcd
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1 h2; simp [Matrix.single_mul_single_same]
    · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
    · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
    · simp [Matrix.single_mul_single_of_ne, Matrix.single_mul_single_of_ne, h1, h2]
  rw [hm] at hbr
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun F : V →L[ℂ] V => F x) hbr
  have e : ∀ A B : V →L[ℂ] V, (A * B) x = A (B x) := fun _ _ => rfl
  simp only [_root_.sub_apply, e, map_sub] at hx
  simp only [preUnits, LinearMap.sub_apply, mul_apply_eq_comp, ContinuousLinearMap.coe_coe]
  rw [hx]
  split_ifs <;> simp

include hder in
theorem pre_kUnit : Formalism.REAL.KUnit ε (preUnits dτ) := by
  intro a b hab x y
  show ⟪dτ (Matrix.single a b 1) x, y⟫_ℂ = ⟪x, dτ (Matrix.single b a 1) y⟫_ℂ
  rw [← pre_star_dτ_single τ dτ hder hab, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem KType.kUnit {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KUnit ε (kunits T) :=
  pre_kUnit T.τ T.dτ T.hasDeriv

theorem KType.kRel {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KRel ε (kunits T) :=
  pre_kRel T.τ T.dτ T.hasDeriv

end ReciprocityTheory.ChartRestriction.DS.HW
