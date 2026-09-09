import HilbertUMD.Interfaces.HilbertThreeHalves
import HilbertUMD.Hilbert.Cotlar
import HilbertUMD.Interfaces.HilbertPV
import HilbertUMD.Hilbert.HilbertLpDuality

/-!
Scalar real-line Hilbert-transform facts, used to prove the
compatibility of the existing Fourier L2 transform with the L3 realizations.

Reference: L. Grafakos, *Classical Fourier Analysis*, 3rd ed. (2014).
Theorem 5.1.7, p. 320, gives Cp ≤ 2p/(p-1) for 1<p≤2, hence 6 at p=3/2.
Theorem 5.1.12, p. 323, identifies the bounded Lp extension with a.e.
principal-value truncation limits. The proof of Theorem 5.1.7, p. 322,
uses the scalar duality identity H*=-H. Here that pairing identity is deduced
from the bounded Lp PV realizations and the smooth-test PV/Fourier bridge:
L2 skew duality extends by smooth density and the continuous Holder pairing.
It has no separate admission and does not use general L2/Lp compatibility.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace HilbertUMD.Interfaces

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num⟩

local instance : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]⟩

/-- Scalar H*=-H at conjugate exponents, for the actual real-line PV maps.
Checked deduction from the cited Lp realizations and smooth-test PV/Fourier
identification; compare Grafakos, proof of Theorem 5.1.7, p. 322. -/
theorem real_hilbert_duality {f g Hf Hg : ℝ → ℝ}
    (hf : MemLp f 3 volume) (hg : MemLp g (3 / 2) volume)
    (hpf : IsHilbertPVAe f Hf) (hpg : IsHilbertPVAe g Hg) :
    (∫ t, Hf t * g t) = -(∫ t, f t * Hg t) := by
  obtain ⟨R, _, hR⟩ := exists_real_hilbert_three
  obtain ⟨T, _, hT⟩ := exists_real_hilbert_three_halves
  apply real_hilbert_duality_of_realizations (by norm_num) (by finiteness)
    R T hR hT ?_ hf hg hpf hpg
  intro φ hφ hc
  obtain ⟨u, hu, hpv, heq⟩ := real_scalar_pv_fourier φ hφ hc
  have hae := hu.coeFn_toLp
  rw [heq] at hae
  filter_upwards [hpv.ae, hae] with t ht hut
  simpa only [hut] using ht

end HilbertUMD.Interfaces
