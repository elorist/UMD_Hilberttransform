import HilbertUMD.UMD.WeightedBinaryEncoding

/-! Approximation of all branching probabilities with a common binary block length. -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace HilbertUMD.WeightedTree

def roundProbability (L : ℕ) (p : ℝ) : ℝ :=
  (⌊(2 : ℝ) ^ L * p⌋₊ : ℝ) / (2 : ℝ) ^ L

theorem roundProbability_bounds (L : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ roundProbability L p ∧ roundProbability L p ≤ p ∧
      p - roundProbability L p ≤ ((2 : ℝ) ^ L)⁻¹ := by
  have hD : 0 < (2 : ℝ) ^ L := by positivity
  have hlo := Nat.floor_le (mul_nonneg hD.le hp)
  have hhi := Nat.lt_floor_add_one ((2 : ℝ) ^ L * p)
  have he : roundProbability L p * (2 : ℝ) ^ L = (⌊(2 : ℝ) ^ L * p⌋₊ : ℝ) :=
    div_mul_cancel₀ _ hD.ne'
  have hinv : ((2 : ℝ) ^ L)⁻¹ * (2 : ℝ) ^ L = 1 := inv_mul_cancel₀ hD.ne'
  refine ⟨by unfold roundProbability; positivity, ?_, ?_⟩
  · apply (mul_le_mul_iff_left₀ hD).mp
    nlinarith
  · apply (mul_le_mul_iff_left₀ hD).mp
    nlinarith

theorem tendsto_roundProbability {p : ℝ} (hp : 0 ≤ p) :
    Tendsto (fun L => roundProbability L p) atTop (𝓝 p) := by
  have hz : Tendsto (fun L => p - roundProbability L p) atTop (𝓝 0) :=
    squeeze_zero (fun L => sub_nonneg.mpr (roundProbability_bounds L hp).2.1)
      (fun L => (roundProbability_bounds L hp).2.2)
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).inv_tendsto_atTop
  simpa only [sub_sub_cancel, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)).sub hz

def threshold (L t : ℕ) (i : Leaf L) : Bool := decide ((leafEquivFin L i).val < t)

theorem branchProbability_threshold (L t : ℕ) (ht : t ≤ 2 ^ L) :
    branchProbability L (threshold L t) = (t : ℝ) / (2 : ℝ) ^ L := by
  have hsum : (∑ i : Leaf L, if threshold L t i then (1 : ℝ) else 0) = t := by
    calc
      _ = ∑ i : Fin (2 ^ L), if i.val < t then (1 : ℝ) else 0 := by
        simpa [threshold] using
          (leafEquivFin L).sum_comp (fun i => if i.val < t then (1 : ℝ) else 0)
      _ = ∑ i ∈ Finset.range (2 ^ L), if i < t then (1 : ℝ) else 0 :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < t then (1 : ℝ) else 0) (2 ^ L)
      _ = ∑ i ∈ Finset.range t, (1 : ℝ) := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      _ = t := by simp
  change ((2 : ℝ) ^ L)⁻¹ * (∑ i, if threshold L t i then (1 : ℝ) else 0) = _
  rw [hsum]
  ring

def approximatingCode {n : ℕ} (L : ℕ) (b : Bias n) : Code L n :=
  fun a => threshold L ⌊(2 : ℝ) ^ L * b a⌋₊

theorem bias_approximatingCode {n : ℕ} (L : ℕ) (b : Bias n) (hb : Valid b) (a : Node n) :
    bias (approximatingCode L b) a = roundProbability L (b a) := by
  change branchProbability L (threshold L ⌊(2 : ℝ) ^ L * b a⌋₊) = _
  apply branchProbability_threshold
  have h := Nat.floor_le_floor (mul_le_of_le_one_right (by positivity : 0 ≤ (2 : ℝ) ^ L) (hb a).2)
  have hN : (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by norm_cast
  rw [hN, Nat.floor_natCast] at h
  simpa only [← hN] using h

theorem tendsto_bias_approximatingCode {n : ℕ} (b : Bias n) (hb : Valid b) :
    Tendsto (fun L => bias (approximatingCode L b)) atTop (𝓝 b) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have he : (fun L => bias (approximatingCode L b) a) =
      (fun L => roundProbability L (b a)) := funext (fun L => bias_approximatingCode L b hb a)
  rw [he]
  exact tendsto_roundProbability (hb a).1

end HilbertUMD.WeightedTree
