import HilbertUMD.UMD.UMD
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-!
# Hilbert-valued L2 martingale orthogonality

The locally integrable martingale definition is connected directly to
mathlib's L2 orthogonal projections. Global L1 membership is not required.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace HilbertUMD

section Projections

variable {Ω ι E 𝕜 : Type*} [MeasurableSpace Ω] [Preorder ι] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {ℱ : Filtration ι ‹MeasurableSpace Ω›} {f : ι → Ω → E}

/-- Bundle each member of an L2 martingale as an element of the Hilbert L2 space. -/
def IsLpMartingale.toL2 (hf : IsLpMartingale f ℱ 2 μ) (i : ι) : Lp E 2 μ :=
  (hf.memLp i).toLp (f i)

omit [CompleteSpace E] in
theorem IsLpMartingale.toL2_coe (hf : IsLpMartingale f ℱ 2 μ) (i : ι) :
    hf.toL2 i =ᵐ[μ] f i := (hf.memLp i).coeFn_toLp

omit [CompleteSpace E] in
theorem IsLpMartingale.toL2_measurable (hf : IsLpMartingale f ℱ 2 μ) (i : ι) :
    AEStronglyMeasurable[ℱ i] (hf.toL2 i) μ :=
  (hf.stronglyAdapted i).aestronglyMeasurable.congr (hf.toL2_coe i).symm

/-- The martingale relation is exactly the corresponding L2 projection identity. -/
theorem IsLpMartingale.condExpL2_toL2 (hf : IsLpMartingale f ℱ 2 μ)
    {i j : ι} (hij : i ≤ j) :
    (condExpL2 E 𝕜 (ℱ.le i) (hf.toL2 j) : Lp E 2 μ) = hf.toL2 i := by
  apply Lp.ext
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 (ℱ.le i) _ _
    (by norm_num) (by norm_num)
    (fun s _ hs => integrableOn_condExpL2_of_measure_ne_top (ℱ.le i) hs.ne _)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne) ?_
    (aestronglyMeasurable_condExpL2 _ _) (hf.toL2_measurable i)
  intro s hs hμs
  rw [integral_condExpL2_eq (ℱ.le i) _ hs hμs.ne,
    integral_congr_ae (ae_restrict_of_ae (hf.toL2_coe j)),
    integral_congr_ae (ae_restrict_of_ae (hf.toL2_coe i))]
  exact (hf.setIntegral_eq i j hij s hs hμs).symm

theorem IsLpMartingale.inner_toL2_eq (hf : IsLpMartingale f ℱ 2 μ)
    {i j : ι} (hij : i ≤ j) :
    inner 𝕜 (hf.toL2 j) (hf.toL2 i) = inner 𝕜 (hf.toL2 i) (hf.toL2 i) := by
  rw [← inner_condExpL2_eq_inner_fun (ℱ.le i) (hf.toL2 j) (hf.toL2 i)
    (hf.toL2_measurable i), hf.condExpL2_toL2 hij]

theorem IsLpMartingale.inner_sub_toL2_eq_zero (hf : IsLpMartingale f ℱ 2 μ)
    {i j k : ι} (hki : k ≤ i) (hij : i ≤ j) :
    inner 𝕜 (hf.toL2 j - hf.toL2 i) (hf.toL2 k) = 0 := by
  rw [inner_sub_left, hf.inner_toL2_eq (hki.trans hij), hf.inner_toL2_eq hki, sub_self]

end Projections

section OrthogonalSums

variable {ι E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Pythagoras for a finite family whose distinct members are orthogonal. -/
theorem norm_sum_sq_of_pairwise_orthogonal (d : ι → E)
    (hd : Pairwise fun i j => inner 𝕜 (d i) (d j) = 0) (s : Finset ι) :
    ‖∑ i ∈ s, d i‖ ^ 2 = ∑ i ∈ s, ‖d i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hz : inner 𝕜 (d i) (∑ j ∈ s, d j) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun j hj => hd (by intro h; subst j; exact hi hj)
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hz
    simp only [← sq] at hpy
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hpy, ih]

/-- Unimodular scalar coefficients preserve the norm of an orthogonal sum. -/
theorem norm_unimodular_sum_eq [Fintype ι] (d : ι → E)
    (hd : Pairwise fun i j => inner 𝕜 (d i) (d j) = 0)
    (ε : ι → 𝕜) (hε : ∀ i, ‖ε i‖ = 1) :
    ‖∑ i, ε i • d i‖ = ‖∑ i, d i‖ := by
  have hεd : Pairwise fun i j => inner 𝕜 (ε i • d i) (ε j • d j) = 0 := by
    intro i j hij
    simp [inner_smul_left, inner_smul_right, hd hij]
  have hsq := norm_sum_sq_of_pairwise_orthogonal (fun i => ε i • d i) hεd Finset.univ
  have hdq := norm_sum_sq_of_pairwise_orthogonal d hd Finset.univ
  simp only [norm_smul, hε, one_mul] at hsq
  nlinarith [norm_nonneg (∑ i, ε i • d i), norm_nonneg (∑ i, d i)]

end OrthogonalSums

section MartingaleTransforms

variable {Ω E 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {m : ℕ} {ℱ : Filtration (Fin (m + 1)) ‹MeasurableSpace Ω›}
  {f : Fin (m + 1) → Ω → E}

def IsLpMartingale.l2Difference (hf : IsLpMartingale f ℱ 2 μ) (k : Fin m) : Lp E 2 μ :=
  hf.toL2 k.succ - hf.toL2 k.castSucc

omit [CompleteSpace E] in
theorem IsLpMartingale.l2Difference_coe (hf : IsLpMartingale f ℱ 2 μ) (k : Fin m) :
    hf.l2Difference k =ᵐ[μ] fun x => f k.succ x - f k.castSucc x := by
  exact (Lp.coeFn_sub _ _).trans ((hf.toL2_coe k.succ).sub (hf.toL2_coe k.castSucc))

theorem IsLpMartingale.inner_l2Difference_eq_zero_of_lt (hf : IsLpMartingale f ℱ 2 μ)
    {k l : Fin m} (hkl : k < l) : inner 𝕜 (hf.l2Difference l) (hf.l2Difference k) = 0 := by
  have hks : k.succ ≤ l.castSucc := by simpa using hkl
  have hkc : k.castSucc ≤ l.castSucc := by simpa using hkl.le
  have hls : l.castSucc ≤ l.succ := by change l.val ≤ l.val + 1; omega
  rw [IsLpMartingale.l2Difference, IsLpMartingale.l2Difference, inner_sub_right,
    hf.inner_sub_toL2_eq_zero hks hls, hf.inner_sub_toL2_eq_zero hkc hls, sub_self]

theorem IsLpMartingale.l2Difference_orthogonal (hf : IsLpMartingale f ℱ 2 μ) :
    Pairwise fun k l => inner 𝕜 (hf.l2Difference k) (hf.l2Difference l) = 0 := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact inner_eq_zero_symm.mp (hf.inner_l2Difference_eq_zero_of_lt h)
  · exact hf.inner_l2Difference_eq_zero_of_lt h

omit [CompleteSpace E] in
theorem IsLpMartingale.sum_l2Difference_coe (hf : IsLpMartingale f ℱ 2 μ) :
    ⇑(∑ k, hf.l2Difference k) =ᵐ[μ] differenceSum f := by
  refine (Lp.coeFn_fun_finsetSum Finset.univ hf.l2Difference).trans ?_
  filter_upwards [ae_all_iff.mpr (fun k => hf.l2Difference_coe k)] with x hx
  exact Finset.sum_congr rfl fun k _ => hx k

omit [CompleteSpace E] in
theorem IsLpMartingale.transform_l2Difference_coe (hf : IsLpMartingale f ℱ 2 μ)
    (ε : Fin m → 𝕜) :
    ⇑(∑ k, ε k • hf.l2Difference k) =ᵐ[μ]
      martingaleTransform (ContinuousLinearMap.id 𝕜 E) ε f := by
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun k => ε k • hf.l2Difference k)).trans ?_
  have hεd : ∀ k, ⇑(ε k • hf.l2Difference k) =ᵐ[μ]
      fun x => ε k • (f k.succ x - f k.castSucc x) := fun k =>
    (Lp.coeFn_smul _ _).trans ((hf.l2Difference_coe k).const_smul (ε k))
  filter_upwards [ae_all_iff.mpr hεd] with x hx
  exact Finset.sum_congr rfl fun k _ => hx k

/-- Every deterministic unimodular transform of a Hilbert-valued L2 martingale
preserves the L2 norm of the sum of its differences. -/
theorem IsLpMartingale.eLpNorm_transform_eq (hf : IsLpMartingale f ℱ 2 μ)
    (ε : Fin m → 𝕜) (hε : ∀ k, ‖ε k‖ = 1) :
    eLpNorm (martingaleTransform (ContinuousLinearMap.id 𝕜 E) ε f) 2 μ =
      eLpNorm (differenceSum f) 2 μ := by
  rw [← eLpNorm_congr_ae (hf.transform_l2Difference_coe ε),
    ← eLpNorm_congr_ae hf.sum_l2Difference_coe, ← Lp.enorm_def, ← Lp.enorm_def]
  have hn := norm_unimodular_sum_eq (hf.l2Difference) hf.l2Difference_orthogonal ε hε
  simp only [enorm, nnnorm, hn]

end MartingaleTransforms

universe uΩ

/-- The Hilbert-valued L2 UMD bound one, over either scalar field and all
sigma-finite sample spaces in the chosen universe. -/
theorem umdBound_two_hilbert {E 𝕜 : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E] :
    UMDBound.{uΩ} 2 (ContinuousLinearMap.id 𝕜 E) 1 := by
  intro Ω mΩ μ hμ m hm ℱ hℱ f hf ε hε
  rw [hf.eLpNorm_transform_eq ε hε]
  simp

end HilbertUMD
