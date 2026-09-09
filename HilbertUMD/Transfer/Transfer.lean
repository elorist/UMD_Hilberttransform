import HilbertUMD.Foundations.Spaces
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Graph norm transfer

This file develops Proposition 2.2. All operator assumptions are explicit
hypotheses. In particular, no Hilbert transform or martingale inequality is
postulated here.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The two matrix estimates needed by the transfer proposition. -/
structure TransferAssumptions (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : Prop where
  l1_bound : ∀ x, ‖T x‖ ≤ l1Norm n x
  hilbert_bound : ∀ x, ‖T x‖ ≤ Real.sqrt ((n : ℝ) + 1) * hilbertNorm n x

theorem one_le_sqrt_level (n : ℕ) : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
  exact Real.le_sqrt_of_sq_le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])

theorem graphNorm_lower (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (x : Vec 𝕜 n) :
    hilbertNorm n x / Real.sqrt ((n : ℝ) + 1) ≤ graphNorm T x :=
  (hilbert_div_sqrt_le_sumNorm n x).trans (le_max_right _ _)

theorem graphNorm_le_l1 {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    (hT : TransferAssumptions T) (x : Vec 𝕜 n) : graphNorm T x ≤ l1Norm n x :=
  max_le (hT.l1_bound x) (sumNorm_le_l1 n x)

theorem graphNorm_le_hilbert {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    (hT : TransferAssumptions T) (x : Vec 𝕜 n) :
    graphNorm T x ≤ Real.sqrt ((n : ℝ) + 1) * hilbertNorm n x := by
  apply max_le (hT.hilbert_bound x)
  exact (sumNorm_le_hilbert n x).trans
    (le_mul_of_one_le_left (apply_nonneg _ _) (one_le_sqrt_level n))

theorem hilbertNorm_le_graphNorm (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (x : Vec 𝕜 n) :
    hilbertNorm n x ≤ Real.sqrt ((n : ℝ) + 1) * graphNorm T x := by
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  simpa [mul_comm] using (div_le_iff₀ hs).mp (graphNorm_lower T x)

theorem summation_transferAssumptions (n : ℕ) :
    TransferAssumptions (summationLinear (𝕜 := 𝕜) n) where
  l1_bound x := (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr (summation_le_l1 n x)
  hilbert_bound := summation_le_hilbert n

theorem signedDyadic_transferAssumptions (n : ℕ) :
    TransferAssumptions (signedDyadicLinear (𝕜 := 𝕜) n) where
  l1_bound x := (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr (signedDyadic_le_l1 n x)
  hilbert_bound := signedDyadic_le_hilbert n

theorem continuous_l1Norm (n : ℕ) : Continuous (l1Norm (𝕜 := 𝕜) n) := by
  change Continuous (fun x : Vec 𝕜 n => ∑ i, ‖x i‖)
  fun_prop

theorem continuous_hilbertNorm (n : ℕ) : Continuous (hilbertNorm (𝕜 := 𝕜) n) :=
  continuous_norm.comp (dyadicMap (𝕜 := 𝕜) n).continuous_of_finiteDimensional

theorem norm_le_l1Norm (n : ℕ) (x : Vec 𝕜 n) : ‖x‖ ≤ l1Norm n x := by
  apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
  intro i
  exact Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)

/-- The infimum defining E is attained, with no measurable-selection assumption. -/
theorem exists_sumNorm_minimizer (n : ℕ) (x : Vec 𝕜 n) :
    ∃ u : Vec 𝕜 n, l1Norm n u + hilbertNorm n (x - u) = sumNorm n x := by
  let f : Vec 𝕜 n → ℝ := fun u => l1Norm n u + hilbertNorm n (x - u)
  have hc : Continuous f := (continuous_l1Norm n).add
    ((continuous_hilbertNorm n).comp (continuous_const.sub continuous_id))
  have hco : Tendsto f (cocompact (Vec 𝕜 n)) atTop := by
    apply tendsto_atTop_mono (fun u => ?_) tendsto_norm_cocompact_atTop
    exact (norm_le_l1Norm n u).trans (le_add_of_nonneg_right (apply_nonneg _ _))
  obtain ⟨u, hu⟩ := hc.exists_forall_le hco
  refine ⟨u, le_antisymm ?_ ?_⟩
  · rw [sumNorm_eq_inf]
    exact le_ciInf hu
  · rw [sumNorm_eq_inf]
    exact ciInf_le ⟨0, by rintro _ ⟨v, rfl⟩; positivity⟩ u

/-- A minimizing decomposition into the l1 and H components. -/
theorem exists_sumNorm_decomposition (n : ℕ) (x : Vec 𝕜 n) :
    ∃ u v : Vec 𝕜 n, x = u + v ∧ l1Norm n u + hilbertNorm n v = sumNorm n x := by
  obtain ⟨u, hu⟩ := exists_sumNorm_minimizer n x
  exact ⟨u, x - u, by abel, hu⟩

section SimpleDecomposition

open MeasureTheory
variable {S : Type*} [MeasurableSpace S]

/-- Pointwise norm-minimizing decompositions can be chosen as simple
functions, preserving the original support. No measurable choice theorem is needed. -/
theorem simpleFunc_sumNorm_decomposition (f : SimpleFunc S (Vec 𝕜 n)) :
    ∃ u v : SimpleFunc S (Vec 𝕜 n), f = u + v ∧
      Function.support u ⊆ Function.support f ∧
      Function.support v ⊆ Function.support f ∧
      ∀ t, l1Norm n (u t) + hilbertNorm n (v t) = sumNorm n (f t) := by
  choose a ha using fun x : Vec 𝕜 n => exists_sumNorm_minimizer n x
  have ha0 : a 0 = 0 := by
    have hz : l1Norm n (a 0) + hilbertNorm n (0 - a 0) = 0 := by
      simpa using ha 0
    have hn := norm_le_l1Norm n (a 0)
    have hp := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (0 - a 0)
    exact norm_eq_zero.mp (by linarith [norm_nonneg (a 0)])
  let b : Vec 𝕜 n → Vec 𝕜 n := fun x => x - a x
  have hb0 : b 0 = 0 := by simp [b, ha0]
  refine ⟨f.map a, f.map b, ?_, ?_, ?_, ?_⟩
  · apply SimpleFunc.ext
    intro t
    change f t = a (f t) + (f t - a (f t))
    abel
  · exact Function.support_comp_subset ha0 f
  · exact Function.support_comp_subset hb0 f
  · exact fun t => ha (f t)

/-- Finite-measure support is also preserved by the minimizing decomposition. -/
theorem simpleFunc_sumNorm_finMeas_decomposition (μ : Measure S)
    (f : SimpleFunc S (Vec 𝕜 n)) (hf : f.FinMeasSupp μ) :
    ∃ u v : SimpleFunc S (Vec 𝕜 n), f = u + v ∧ u.FinMeasSupp μ ∧ v.FinMeasSupp μ ∧
      ∀ t, l1Norm n (u t) + hilbertNorm n (v t) = sumNorm n (f t) := by
  obtain ⟨u, v, huv, hu, hv, he⟩ := simpleFunc_sumNorm_decomposition f
  exact ⟨u, v, huv, (measure_mono hu).trans_lt hf, (measure_mono hv).trans_lt hf, he⟩

theorem simpleFunc_integrable_seminorm_sq (μ : Measure S)
    (f : SimpleFunc S (Vec 𝕜 n)) (hf : f.FinMeasSupp μ) (p : Seminorm 𝕜 (Vec 𝕜 n)) :
    Integrable (fun t => p (f t) ^ 2) μ := by
  have h : (f.map (fun x => p x ^ 2)).FinMeasSupp μ := hf.map (by simp)
  exact h.integrable

/-- The squared integral bound for minimizing simple-function decompositions
on an arbitrary measure space. This is the measure-theoretic decomposition
step in Proposition 2.2, before density is used. -/
theorem simpleFunc_integral_sumNorm_decomposition (μ : Measure S)
    (f : SimpleFunc S (Vec 𝕜 n)) (hf : f.FinMeasSupp μ) :
    ∃ u v : SimpleFunc S (Vec 𝕜 n), f = u + v ∧ u.FinMeasSupp μ ∧ v.FinMeasSupp μ ∧
      (∫ t, l1Norm n (u t) ^ 2 ∂μ) + (∫ t, hilbertNorm n (v t) ^ 2 ∂μ) ≤
        ∫ t, sumNorm n (f t) ^ 2 ∂μ := by
  obtain ⟨u, v, huv, hu, hv, he⟩ := simpleFunc_sumNorm_finMeas_decomposition μ f hf
  refine ⟨u, v, huv, hu, hv, ?_⟩
  have h1 := simpleFunc_integrable_seminorm_sq μ u hu (l1Norm n)
  have h2 := simpleFunc_integrable_seminorm_sq μ v hv (hilbertNorm n)
  have h3 := simpleFunc_integrable_seminorm_sq μ f hf (sumNorm n)
  rw [← integral_add h1 h2]
  apply integral_mono (h1.add h2) h3
  intro t
  change l1Norm n (u t) ^ 2 + hilbertNorm n (v t) ^ 2 ≤ sumNorm n (f t) ^ 2
  rw [← he t]
  have ha := apply_nonneg (l1Norm (𝕜 := 𝕜) n) (u t)
  have hb := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (v t)
  nlinarith only [mul_nonneg ha hb]

end SimpleDecomposition

section FiniteL2

variable {ι : Type*} [Fintype ι]

/-- The Euclidean norm of a real function on a finite sample space. -/
def sampleL2 (f : ι → ℝ) : ℝ := ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖

theorem sampleL2_nonneg (f : ι → ℝ) : 0 ≤ sampleL2 f := norm_nonneg _

theorem sampleL2_sq (f : ι → ℝ) : sampleL2 f ^ 2 = ∑ i, f i ^ 2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 f)

theorem sampleL2_mono {f g : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ g i) :
    sampleL2 f ≤ sampleL2 g := by
  apply (sq_le_sq₀ (sampleL2_nonneg f) (sampleL2_nonneg g)).mp
  simp only [sampleL2_sq]
  exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hf i) (h i) 2)

theorem sampleL2_add_le (f g : ι → ℝ) :
    sampleL2 (fun i => f i + g i) ≤ sampleL2 f + sampleL2 g := by
  exact norm_add_le (WithLp.toLp 2 f : EuclideanSpace ℝ ι) (WithLp.toLp 2 g)

theorem sampleL2_mul (c : ℝ) (hc : 0 ≤ c) (f : ι → ℝ) :
    sampleL2 (fun i => c * f i) = c * sampleL2 f := by
  change ‖c • (WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ = _
  rw [norm_smul, Real.norm_of_nonneg hc]
  rfl

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- The L2 seminorm over finite counting measure, with a specified fibre seminorm. -/
def finiteL2 (p : Seminorm 𝕜 E) (f : ι → E) : ℝ := sampleL2 (fun i => p (f i))

theorem finiteL2_nonneg (p : Seminorm 𝕜 E) (f : ι → E) : 0 ≤ finiteL2 p f :=
  sampleL2_nonneg _

theorem finiteL2_sq (p : Seminorm 𝕜 E) (f : ι → E) :
    finiteL2 p f ^ 2 = ∑ i, p (f i) ^ 2 := sampleL2_sq _

theorem finiteL2_add_le (p : Seminorm 𝕜 E) (f g : ι → E) :
    finiteL2 p (f + g) ≤ finiteL2 p f + finiteL2 p g := by
  calc
    finiteL2 p (f + g) ≤ sampleL2 (fun i => p (f i) + p (g i)) :=
      sampleL2_mono (fun i => apply_nonneg _ _) (fun i => map_add_le_add p _ _)
    _ ≤ finiteL2 p f + finiteL2 p g := sampleL2_add_le _ _

theorem finiteL2_bound (p q : Seminorm 𝕜 E) {c : ℝ} (hc : 0 ≤ c)
    (f g : ι → E) (h : ∀ i, p (f i) ≤ c * q (g i)) :
    finiteL2 p f ≤ c * finiteL2 q g := by
  calc
    finiteL2 p f ≤ sampleL2 (fun i => c * q (g i)) :=
      sampleL2_mono (fun i => apply_nonneg _ _) h
    _ = c * finiteL2 q g := sampleL2_mul c hc _

/-- Choosing pointwise minimizers yields precisely the squared decomposition
bound used in the transfer argument, on every finite sample space. -/
theorem finiteL2_sumNorm_decomposition (f : ι → Vec 𝕜 n) :
    ∃ u v : ι → Vec 𝕜 n, f = u + v ∧
      finiteL2 (l1Norm n) u ^ 2 + finiteL2 (hilbertNorm n) v ^ 2 ≤
        finiteL2 (sumNorm n) f ^ 2 := by
  choose u v hv he using fun i => exists_sumNorm_decomposition n (f i)
  refine ⟨u, v, funext hv, ?_⟩
  simp only [finiteL2_sq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← he i]
  have ha := apply_nonneg (l1Norm (𝕜 := 𝕜) n) (u i)
  have hb := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (v i)
  nlinarith [mul_nonneg ha hb]

/-- Coordinatewise amplification of a scalar linear operator on a finite
sample space. It acts on the sample variable, not the vector-coordinate variable. -/
def coordinateAction (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜)) :
    (ι → Vec 𝕜 n) →ₗ[𝕜] (ι → Vec 𝕜 n) where
  toFun f := fun i j => U (fun k => f k j) i
  map_add' f g := by
    ext i j
    exact congrFun (U.map_add (fun k => f k j) (fun k => g k j)) i
  map_smul' c f := by
    ext i j
    exact congrFun (U.map_smul c (fun k => f k j)) i

omit [Fintype ι] in
theorem blockSum_coordinateAction (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))
    (f : ι → Vec 𝕜 n) (i : ι) (a : Node n) :
    blockSum n (coordinateAction U f i) a =
      U (fun k => blockSum n (f k) a) i := by
  classical
  simp only [blockSum_eq_sum_nodeLeaves]
  have heq : (fun k => ∑ j ∈ nodeLeaves n a, f k j) =
      ∑ j ∈ nodeLeaves n a, (fun k => f k j) := by
    ext k
    simp
  rw [heq, map_sum]
  simp [coordinateAction]

/-- Scalar L2 contractions are contractions for the dyadic Hilbert norm.
This is proved by exchanging the finite sums over samples and dyadic blocks. -/
theorem finiteL2_hilbert_contraction (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))
    (hU : ∀ g : ι → 𝕜, (∑ i, ‖U g i‖ ^ 2) ≤ ∑ i, ‖g i‖ ^ 2)
    (f : ι → Vec 𝕜 n) :
    finiteL2 (hilbertNorm n) (coordinateAction U f) ≤ finiteL2 (hilbertNorm n) f := by
  apply (sq_le_sq₀ (finiteL2_nonneg _ _) (finiteL2_nonneg _ _)).mp
  simp only [finiteL2_sq, hilbertNorm_sq, blockSum_coordinateAction]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i a => ‖blockSum n (f i) a‖ ^ 2)]
  exact Finset.sum_le_sum (fun a _ => hU (fun k => blockSum n (f k) a))

/-- Squaring the maximum norm and summing is bounded by the sum of the
squared L2 norms of its two defining components. -/
theorem finiteL2_graph_sq_le (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (f : ι → Vec 𝕜 n) :
    finiteL2 (graphNorm T) f ^ 2 ≤
      finiteL2 ((normSeminorm 𝕜 (Vec 𝕜 n)).comp T) f ^ 2 +
        finiteL2 (sumNorm n) f ^ 2 := by
  simp only [finiteL2_sq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (max ‖T (f i)‖ (sumNorm n (f i))) ^ 2 ≤ ‖T (f i)‖ ^ 2 + _
  rcases le_total ‖T (f i)‖ (sumNorm n (f i)) with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖T (f i)‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (sumNorm n (f i))]

/-- The scalar-contraction estimate in Proposition 2.2 on every finite
counting-measure space. The assumptions on U and M are respectively its
scalar L2 contraction bound and the L2(l1)-to-L2(linfinity) bound of TU.
The sharp squared factor M² + 2(n+1) is derived, not assumed. -/
theorem finiteL2_scalar_transfer {T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n}
    (hT : TransferAssumptions T) (U : (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜))
    (hU : ∀ g : ι → 𝕜, (∑ i, ‖U g i‖ ^ 2) ≤ ∑ i, ‖g i‖ ^ 2)
    (M : ℝ) (_hM_nonneg : 0 ≤ M)
    (hM : ∀ g : ι → Vec 𝕜 n,
      finiteL2 ((normSeminorm 𝕜 (Vec 𝕜 n)).comp T) (coordinateAction U g) ≤
        M * finiteL2 (l1Norm n) g)
    (f : ι → Vec 𝕜 n) :
    finiteL2 (graphNorm T) (coordinateAction U f) ^ 2 ≤
      (M ^ 2 + 2 * ((n : ℝ) + 1)) * finiteL2 (graphNorm T) f ^ 2 := by
  let pT := (normSeminorm 𝕜 (Vec 𝕜 n)).comp T
  let s := Real.sqrt ((n : ℝ) + 1)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hH (g : ι → Vec 𝕜 n) :
      finiteL2 (hilbertNorm n) (coordinateAction U g) ≤ finiteL2 (hilbertNorm n) g :=
    finiteL2_hilbert_contraction U hU g
  have hHE (g : ι → Vec 𝕜 n) :
      finiteL2 (sumNorm n) g ≤ finiteL2 (hilbertNorm n) g := by
    simpa using finiteL2_bound (sumNorm n) (hilbertNorm n) (by norm_num : (0 : ℝ) ≤ 1)
      g g (fun i => by simpa using sumNorm_le_hilbert n (g i))
  have hEF : finiteL2 (sumNorm n) f ≤ finiteL2 (graphNorm T) f := by
    simpa using finiteL2_bound (sumNorm n) (graphNorm T) (by norm_num : (0 : ℝ) ≤ 1)
      f f (fun i => by
        simpa only [one_mul] using (show sumNorm n (f i) ≤ graphNorm T (f i) from
          le_max_right _ _))
  have hHF : finiteL2 (hilbertNorm n) f ≤ s * finiteL2 (graphNorm T) f := by
    apply finiteL2_bound (hilbertNorm n) (graphNorm T) hs f f
    intro i
    change hilbertNorm n (f i) ≤ Real.sqrt ((n : ℝ) + 1) * graphNorm T (f i)
    exact hilbertNorm_le_graphNorm (𝕜 := 𝕜) (n := n) T (f i)
  have hE : finiteL2 (sumNorm n) (coordinateAction U f) ≤ s * finiteL2 (graphNorm T) f :=
    (hHE _).trans ((hH f).trans hHF)
  have hE2 : finiteL2 (sumNorm n) (coordinateAction U f) ^ 2 ≤
      (s * finiteL2 (graphNorm T) f) ^ 2 := by
    apply pow_le_pow_left₀ _ hE 2
    exact finiteL2_nonneg _ _
  rw [mul_pow, hs2] at hE2
  obtain ⟨u, v, huv, hdec⟩ := finiteL2_sumNorm_decomposition (𝕜 := 𝕜) (n := n) f
  have hEF2 : finiteL2 (sumNorm n) f ^ 2 ≤ finiteL2 (graphNorm T) f ^ 2 := by
    apply pow_le_pow_left₀ _ hEF 2
    exact finiteL2_nonneg _ _
  have hdecF : finiteL2 (l1Norm n) u ^ 2 + finiteL2 (hilbertNorm n) v ^ 2 ≤
      finiteL2 (graphNorm T) f ^ 2 :=
    hdec.trans hEF2
  have hTv : finiteL2 pT (coordinateAction U v) ≤ s * finiteL2 (hilbertNorm n) v :=
    (finiteL2_bound pT (hilbertNorm n) hs (coordinateAction U v)
      (coordinateAction U v) (fun i => hT.hilbert_bound _)).trans
      (mul_le_mul_of_nonneg_left (hH v) hs)
  have hTf : finiteL2 pT (coordinateAction U f) ≤
      M * finiteL2 (l1Norm n) u + s * finiteL2 (hilbertNorm n) v := by
    rw [huv, map_add]
    exact (finiteL2_add_le pT _ _).trans (add_le_add (hM u) hTv)
  have hTf2 : finiteL2 pT (coordinateAction U f) ^ 2 ≤
      (M * finiteL2 (l1Norm n) u + s * finiteL2 (hilbertNorm n) v) ^ 2 := by
    apply pow_le_pow_left₀ _ hTf 2
    exact finiteL2_nonneg _ _
  have hCS : (M * finiteL2 (l1Norm n) u + s * finiteL2 (hilbertNorm n) v) ^ 2 ≤
      (M ^ 2 + s ^ 2) * (finiteL2 (l1Norm n) u ^ 2 + finiteL2 (hilbertNorm n) v ^ 2) := by
    nlinarith only [sq_nonneg (M * finiteL2 (hilbertNorm n) v - s * finiteL2 (l1Norm n) u)]
  have hTfFinal : finiteL2 pT (coordinateAction U f) ^ 2 ≤
      (M ^ 2 + s ^ 2) * finiteL2 (graphNorm T) f ^ 2 := hTf2.trans (hCS.trans
    (mul_le_mul_of_nonneg_left hdecF (by positivity : 0 ≤ M ^ 2 + s ^ 2)))
  rw [hs2] at hTfFinal
  dsimp only [pT] at hTfFinal
  calc
    finiteL2 (graphNorm T) (coordinateAction U f) ^ 2 ≤
        finiteL2 ((normSeminorm 𝕜 (Vec 𝕜 n)).comp T) (coordinateAction U f) ^ 2 +
          finiteL2 (sumNorm n) (coordinateAction U f) ^ 2 := finiteL2_graph_sq_le T _
    _ ≤ (M ^ 2 + ((n : ℝ) + 1)) * finiteL2 (graphNorm T) f ^ 2 +
        ((n : ℝ) + 1) * finiteL2 (graphNorm T) f ^ 2 := add_le_add hTfFinal hE2
    _ = _ := by ring

end FiniteL2
end HilbertUMD
