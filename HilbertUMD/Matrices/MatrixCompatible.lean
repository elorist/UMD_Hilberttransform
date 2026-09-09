import HilbertUMD.Analysis.CubicLp
import HilbertUMD.Analysis.ScalarLpOperators
import HilbertUMD.Matrices.MatrixCubic

/-! Actual compatible finite-matrix/scalar-operator realizations. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open scoped Classical
namespace HilbertUMD.MatrixCompatible

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] (μ : Measure S)

theorem compLpL_comp_apply {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : F →L[ℝ] G) (B : E →L[ℝ] F) (f : Lp E p μ) :
    A.compLpL p μ (B.compLpL p μ f) = (A.comp B).compLpL p μ f := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (B.compLpL p μ f), B.coeFn_compLpL f,
    (A.comp B).coeFn_compLpL f] with x ha hb hc
  rw [ha, hb, hc]
  rfl

theorem zero_compLpL {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (0 : E →L[ℝ] F).compLpL p μ = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(0 : E →L[ℝ] F).coeFn_compLpL f, Lp.coeFn_zero F p μ] with x h0 hz
  exact h0.trans hz.symm

theorem sum_compLpL {E F κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (s : Finset κ) (A : κ → E →L[ℝ] F) :
    (∑ j ∈ s, A j).compLpL p μ = ∑ j ∈ s, (A j).compLpL p μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_compLpL]
  | @insert j s hj ih => simp [Finset.sum_insert, hj, ContinuousLinearMap.add_compLpL, ih]

theorem functional_eq_sum (A : (ι → ℝ) →L[ℝ] ℝ) :
    A = ∑ j : ι, A (Pi.single j 1) • ScalarLp.coordinate j := by
  classical
  ext x
  have hx : x = ∑ j : ι, x j • (Pi.single j 1 : ι → ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    A x = A (∑ j : ι, x j • (Pi.single j 1 : ι → ℝ)) := congrArg A hx
    _ = ∑ j : ι, A (Pi.single j 1) * x j := by simp [mul_comm]
    _ = _ := by simp [ScalarLp.coordinate]

/-- Every finite scalar functional commutes with scalar amplification. -/
theorem functional_amplification (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (A : (ι → ℝ) →L[ℝ] ℝ) (f : Lp (ι → ℝ) p μ) :
    A.compLpL p μ (ScalarLp.amplification μ p R f) = R (A.compLpL p μ f) := by
  rw [functional_eq_sum A]
  simp only [sum_compLpL, ContinuousLinearMap.smul_compLpL, sum_apply,
    smul_apply, ScalarLp.coordinate_amplification, map_sum, map_smul]

theorem lp_eq_of_coordinates (p : ℝ≥0∞) [Fact (1 ≤ p)] {f g : Lp (ι → ℝ) p μ}
    (h : ∀ j : ι, (ScalarLp.coordinate j).compLpL p μ f = (ScalarLp.coordinate j).compLpL p μ g) :
    f = g := by
  have hj (j : ι) : (fun x => f x j) =ᵐ[μ] (fun x => g x j) := by
    filter_upwards [(ScalarLp.coordinate j).coeFn_compLpL f,
      (ScalarLp.coordinate j).coeFn_compLpL g] with x hf hg
    change ScalarLp.coordinate j (f x) = ScalarLp.coordinate j (g x)
    rw [← hf, h j, hg]
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hj] with x hx
  exact funext hx

/-- Finite matrices commute with coordinatewise scalar operators on actual Lp. -/
theorem matrix_amplification_commute (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (f : Lp (ι → ℝ) p μ) :
    A.compLpL p μ (ScalarLp.amplification μ p R f) =
      ScalarLp.amplification μ p R (A.compLpL p μ f) := by
  apply lp_eq_of_coordinates μ p
  intro j
  rw [compLpL_comp_apply, ScalarLp.coordinate_amplification, compLpL_comp_apply]
  exact functional_amplification μ p R ((ScalarLp.coordinate j).comp A) f

variable (η : ℝ) (c : ℕ → ℝ) (n : ℕ)

def treeCLM : Vec ℝ n →L[ℝ] Vec ℝ n := (treeMatrixLinear η c n).toContinuousLinearMap

@[simp] theorem treeCLM_apply (x : Vec ℝ n) : treeCLM η c n x = treeMatrix η c n x := rfl

def action (p : ℝ≥0∞) [Fact (1 ≤ p)] (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) :
    CubicLp.Space (ι := Leaf n) μ p →L[ℝ] CubicLp.Space (ι := Leaf n) μ p :=
  ((treeCLM η c n).compLpL p μ).comp (ScalarLp.amplification μ p R)

theorem coeFn_action (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (f : CubicLp.Space (ι := Leaf n) μ p) :
    action μ η c n p R f =ᵐ[μ]
      (fun x => treeMatrix η c n (fun i => R ((ScalarLp.coordinate i).compLpL p μ f) x)) := by
  filter_upwards [(treeCLM η c n).coeFn_compLpL (ScalarLp.amplification μ p R f),
    ScalarLp.coeFn_amplification μ p R f] with x ht hr
  change (action μ η c n p R f) x = treeCLM η c n ((ScalarLp.amplification μ p R f) x) at ht
  rw [ht, hr, treeCLM_apply]

theorem energy_action_eq (R : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ)
    (f : CubicLp.Space (ι := Leaf n) μ 3) :
    CubicLp.energy μ (action μ η c n 3 R) f =
      ∫ x, treeEnergy η c n (f x)
        (fun i => R ((ScalarLp.coordinate i).compLpL 3 μ f) x) 0 ∂μ := by
  apply integral_congr_ae
  filter_upwards [coeFn_action μ η c n 3 R f] with x hx
  simp only [treeEnergy, zero_add]
  rw [hx]

theorem action_agree (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (T : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ)
    (hRT : ∀ (f : S → ℝ) (hp : MemLp f 2 μ) (hq : MemLp f 3 μ),
      R (hp.toLp f) =ᵐ[μ] T (hq.toLp f))
    (f : CubicLp.Space (ι := Leaf n) μ 2) (g : CubicLp.Space (ι := Leaf n) μ 3)
    (hfg : f =ᵐ[μ] g) : action μ η c n 2 R f =ᵐ[μ] action μ η c n 3 T g := by
  have h3 : MemLp f 3 μ := (Lp.memLp g).ae_eq hfg.symm
  have hf2 : (Lp.memLp f).toLp f = f := by apply Lp.ext; exact (Lp.memLp f).coeFn_toLp
  have hf3 : h3.toLp f = g := by apply Lp.ext; exact h3.coeFn_toLp.trans hfg
  have ha := ScalarLp.compatible μ 2 3 R T hRT f (Lp.memLp f) h3
  rw [hf2, hf3] at ha
  filter_upwards [(treeCLM η c n).coeFn_compLpL (ScalarLp.amplification μ 2 R f),
    (treeCLM η c n).coeFn_compLpL (ScalarLp.amplification μ 3 T g), ha] with x h2 h3 hx
  exact h2.trans ((congrArg (treeCLM η c n) hx).trans h3.symm)

theorem tree_pair_transpose (hη : η ^ 2 = 1) (x y : Vec ℝ n) :
    treePairing n (treeCLM η c n x) y = η * treePairing n x (treeCLM η c n y) := by
  rw [treePairing_comm n (treeCLM η c n x) y, treeCLM_apply,
    treeMatrix_transpose η c hη n y x, treePairing_comm n (treeMatrix η c n y) x]
  rfl

theorem integral_pair_tree (hη : η ^ 2 = 1)
    (f g : CubicLp.Space (ι := Leaf n) μ 2) :
    (∫ x, ∑ i, (treeCLM η c n).compLpL 2 μ f x i * g x i ∂μ) =
      η * ∫ x, ∑ i, f x i * (treeCLM η c n).compLpL 2 μ g x i ∂μ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(treeCLM η c n).coeFn_compLpL f,
    (treeCLM η c n).coeFn_compLpL g] with x hf hg
  rw [hf, hg]
  exact tree_pair_transpose η c n hη (f x) (g x)

/-- The scalar adjoint factor -η and matrix transpose factor η combine to
give the skew pairing required by the cubic lemma. -/
theorem action_skew (hη : η ^ 2 = 1) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ (f g : Lp ℝ 2 μ), (∫ x, R f x * g x ∂μ) =
      (-η) * ∫ x, f x * R g x ∂μ)
    (f g : CubicLp.Space (ι := Leaf n) μ 2) :
    (∫ x, ∑ i, action μ η c n 2 R f x i * g x i ∂μ) =
      -(∫ x, ∑ i, f x i * action μ η c n 2 R g x i ∂μ) := by
  have ht := integral_pair_tree μ η c n hη (ScalarLp.amplification μ 2 R f) g
  have hs := ScalarLp.integral_pair_amplification μ 2 2 R R (-η) hR f
    ((treeCLM η c n).compLpL 2 μ g)
  rw [hs] at ht
  rw [← matrix_amplification_commute μ 2 R (treeCLM η c n) g] at ht
  change (∫ x, ∑ i, action μ η c n 2 R f x i * g x i ∂μ) =
    η * ((-η) * ∫ x, ∑ i, f x i * action μ η c n 2 R g x i ∂μ) at ht
  rw [ht]
  have hη' : η * (-η) = -1 := by nlinarith [hη]
  rw [← mul_assoc, hη', neg_one_mul]

/-- A fully checked compatible operator for treeMatrix composed with the
coordinatewise action of a compatible scalar pair. -/
def compatible (hη : η ^ 2 = 1)
    (Rtwo : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (Rthree : Lp ℝ 3 μ →L[ℝ] Lp ℝ 3 μ)
    (hAgree : ∀ (f : S → ℝ) (hp : MemLp f 2 μ) (hq : MemLp f 3 μ),
      Rtwo (hp.toLp f) =ᵐ[μ] Rthree (hq.toLp f))
    (hSkew : ∀ (f g : Lp ℝ 2 μ), (∫ x, Rtwo f x * g x ∂μ) =
      (-η) * ∫ x, f x * Rtwo g x ∂μ) : CubicLp.CompatibleRealOperator (ι := Leaf n) μ where
  atTwo := action μ η c n 2 Rtwo
  atThree := action μ η c n 3 Rthree
  agree := action_agree μ η c n Rtwo Rthree hAgree
  skew := action_skew μ η c n hη Rtwo hSkew

end HilbertUMD.MatrixCompatible
