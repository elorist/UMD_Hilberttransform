import HilbertUMD.Foundations.Dyadic

noncomputable section
open scoped BigOperators
namespace HilbertUMD
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Lower triangular summation, with the left half preceding the right half. -/
def summation : (n : ℕ) → Vec 𝕜 n → Vec 𝕜 n
  | 0, x => x
  | n + 1, x => Sum.elim (summation n (left x))
      (fun i => total (left x) + summation n (right x) i)

/-- Signed dyadic matrix from the manuscript, including D_0 = [1]. -/
def signedDyadic : (n : ℕ) → Vec 𝕜 n → Vec 𝕜 n
  | 0, x => x
  | n + 1, x => Sum.elim
      (fun i => signedDyadic n (left x) i + (-1 : 𝕜) ^ (n + 1) * total (right x))
      (fun i => (-1 : 𝕜) ^ (n + 1) * total (left x) + signedDyadic n (right x) i)

theorem summation_add (n : ℕ) (x y : Vec 𝕜 n) :
    summation n (x + y) = summation n x + summation n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with i | i
    · exact congrFun (ih (left x) (left y)) i
    · change total (left x + left y) + summation n (right x + right y) i = _
      rw [total_add (left x) (left y), ih]
      change _ = (total (left x) + summation n (right x) i) +
        (total (left y) + summation n (right y) i)
      simp only [Pi.add_apply]; ring

theorem summation_smul (n : ℕ) (c : 𝕜) (x : Vec 𝕜 n) :
    summation n (c • x) = c • summation n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with i | i
    · exact congrFun (ih (left x)) i
    · change total (c • left x) + summation n (c • right x) i = _
      rw [total_smul c (left x), ih]
      change c * total (left x) + c * summation n (right x) i =
        c * (total (left x) + summation n (right x) i)
      ring

theorem signedDyadic_add (n : ℕ) (x y : Vec 𝕜 n) :
    signedDyadic n (x + y) = signedDyadic n x + signedDyadic n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with i | i
    · change signedDyadic n (left x + left y) i +
        (-1 : 𝕜) ^ (n + 1) * total (right x + right y) = _
      rw [ih, total_add (right x) (right y)]
      change (signedDyadic n (left x) i + signedDyadic n (left y) i) +
        (-1 : 𝕜) ^ (n + 1) * (total (right x) + total (right y)) =
        (signedDyadic n (left x) i + (-1 : 𝕜) ^ (n + 1) * total (right x)) +
        (signedDyadic n (left y) i + (-1 : 𝕜) ^ (n + 1) * total (right y))
      ring
    · change (-1 : 𝕜) ^ (n + 1) * total (left x + left y) +
        signedDyadic n (right x + right y) i = _
      rw [ih, total_add (left x) (left y)]
      change (-1 : 𝕜) ^ (n + 1) * (total (left x) + total (left y)) +
        (signedDyadic n (right x) i + signedDyadic n (right y) i) =
        ((-1 : 𝕜) ^ (n + 1) * total (left x) + signedDyadic n (right x) i) +
        ((-1 : 𝕜) ^ (n + 1) * total (left y) + signedDyadic n (right y) i)
      ring

theorem signedDyadic_smul (n : ℕ) (c : 𝕜) (x : Vec 𝕜 n) :
    signedDyadic n (c • x) = c • signedDyadic n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with i | i
    · change signedDyadic n (c • left x) i +
        (-1 : 𝕜) ^ (n + 1) * total (c • right x) = _
      rw [ih, total_smul c (right x)]
      change c * signedDyadic n (left x) i + (-1 : 𝕜) ^ (n + 1) * (c * total (right x)) =
        c * (signedDyadic n (left x) i + (-1 : 𝕜) ^ (n + 1) * total (right x))
      ring
    · change (-1 : 𝕜) ^ (n + 1) * total (c • left x) +
        signedDyadic n (c • right x) i = _
      rw [ih, total_smul c (left x)]
      change (-1 : 𝕜) ^ (n + 1) * (c * total (left x)) + c * signedDyadic n (right x) i =
        c * ((-1 : 𝕜) ^ (n + 1) * total (left x) + signedDyadic n (right x) i)
      ring

def summationLinear (n : ℕ) : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n where
  toFun := summation n
  map_add' := summation_add n
  map_smul' := summation_smul n

def signedDyadicLinear (n : ℕ) : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n where
  toFun := signedDyadic n
  map_add' := signedDyadic_add n
  map_smul' := signedDyadic_smul n

theorem summation_le_l1 (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    ‖summation n x i‖ ≤ l1Norm n x := by
  induction n with
  | zero =>
    rw [l1Norm_eq]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simp [summation, hi]
  | succ n ih =>
    rw [l1Norm_succ]
    rcases i with i | i
    · exact (ih (left x) i).trans (le_add_of_nonneg_right (apply_nonneg (l1Norm (𝕜 := 𝕜) n) _))
    · exact (norm_add_le _ _).trans (add_le_add (norm_total_le n (left x)) (ih (right x) i))

theorem signedDyadic_le_l1 (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    ‖signedDyadic n x i‖ ≤ l1Norm n x := by
  induction n with
  | zero =>
    rw [l1Norm_eq]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simp [signedDyadic, hi]
  | succ n ih =>
    rw [l1Norm_succ]
    rcases i with i | i
    · change ‖signedDyadic n (left x) i + (-1 : 𝕜) ^ (n + 1) * total (right x)‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
        add_le_add (ih (left x) i) (norm_total_le n (right x))
    · change ‖(-1 : 𝕜) ^ (n + 1) * total (left x) + signedDyadic n (right x) i‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
        add_le_add (norm_total_le n (left x)) (ih (right x) i)

/-- A two-term Cauchy--Schwarz estimate used in each binary-tree step. -/
private theorem two_term_sq_bound (a b : 𝕜) (A B k : ℝ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hk : 0 ≤ k)
    (ha : ‖a‖ ^ 2 ≤ k * A ^ 2) (hb : ‖b‖ ≤ B) :
    ‖a + b‖ ^ 2 ≤ (k + 1) * (A ^ 2 + B ^ 2) := by
  have hs := Real.sq_sqrt hk
  have hsA : (Real.sqrt k * A) ^ 2 = k * A ^ 2 := by rw [mul_pow, hs]
  have hsB : (Real.sqrt k * B) ^ 2 = k * B ^ 2 := by rw [mul_pow, hs]
  have ha' : ‖a‖ ≤ Real.sqrt k * A := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
    rwa [hsA]
  have hab := (norm_add_le a b).trans (add_le_add ha' hb)
  have hab2 := pow_le_pow_left₀ (norm_nonneg (a + b)) hab 2
  nlinarith only [hab2, hsA, hsB, sq_nonneg (A - Real.sqrt k * B)]

theorem summation_le_hilbert_sq (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    ‖summation n x i‖ ^ 2 ≤ ((n : ℝ) + 1) * hilbertNorm n x ^ 2 := by
  induction n with
  | zero =>
    rw [hilbertNorm_zero_level x]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simp [summation, hi]
  | succ n ih =>
    have hL := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (left x)
    have hR := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (right x)
    have ht := hilbertNorm_succ_sq n x
    rcases i with i | i
    · have hi := ih (left x) i
      change ‖summation n (left x) i‖ ^ 2 ≤ _
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity)
        (sq_nonneg ‖total x‖), mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity)
        (sq_nonneg (hilbertNorm n (right x))), sq_nonneg (hilbertNorm n (left x))]
    · have hi := two_term_sq_bound (summation n (right x) i) (total (left x))
        (hilbertNorm n (right x)) (hilbertNorm n (left x)) ((n : ℝ) + 1)
        hR hL (by positivity) (ih (right x) i) (norm_total_le_hilbert n (left x))
      change ‖total (left x) + summation n (right x) i‖ ^ 2 ≤ _
      rw [add_comm (total (left x))]
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity) (sq_nonneg ‖total x‖)]

theorem signedDyadic_le_hilbert_sq (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    ‖signedDyadic n x i‖ ^ 2 ≤ ((n : ℝ) + 1) * hilbertNorm n x ^ 2 := by
  induction n with
  | zero =>
    rw [hilbertNorm_zero_level x]
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simp [signedDyadic, hi]
  | succ n ih =>
    have hL := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (left x)
    have hR := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (right x)
    have ht := hilbertNorm_succ_sq n x
    rcases i with i | i
    · have hb : ‖(-1 : 𝕜) ^ (n + 1) * total (right x)‖ ≤ hilbertNorm n (right x) := by
        simpa using norm_total_le_hilbert n (right x)
      have hi := two_term_sq_bound (signedDyadic n (left x) i)
        ((-1 : 𝕜) ^ (n + 1) * total (right x))
        (hilbertNorm n (left x)) (hilbertNorm n (right x)) ((n : ℝ) + 1)
        hL hR (by positivity) (ih (left x) i) hb
      change ‖signedDyadic n (left x) i + (-1 : 𝕜) ^ (n + 1) * total (right x)‖ ^ 2 ≤ _
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity) (sq_nonneg ‖total x‖)]
    · have hb : ‖(-1 : 𝕜) ^ (n + 1) * total (left x)‖ ≤ hilbertNorm n (left x) := by
        simpa using norm_total_le_hilbert n (left x)
      have hi := two_term_sq_bound (signedDyadic n (right x) i)
        ((-1 : 𝕜) ^ (n + 1) * total (left x))
        (hilbertNorm n (right x)) (hilbertNorm n (left x)) ((n : ℝ) + 1)
        hR hL (by positivity) (ih (right x) i) hb
      change ‖(-1 : 𝕜) ^ (n + 1) * total (left x) + signedDyadic n (right x) i‖ ^ 2 ≤ _
      rw [add_comm ((-1 : 𝕜) ^ (n + 1) * total (left x))]
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity) (sq_nonneg ‖total x‖)]

private theorem sqrt_bound_of_sq {a b : ℝ} (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ ((n : ℝ) + 1) * b ^ 2) : a ≤ Real.sqrt ((n : ℝ) + 1) * b := by
  apply (sq_le_sq₀ ha (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  rwa [mul_pow, Real.sq_sqrt (by positivity)]

theorem summation_le_hilbert (n : ℕ) (x : Vec 𝕜 n) :
    ‖summation n x‖ ≤ Real.sqrt ((n : ℝ) + 1) * hilbertNorm n x := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) x))).mpr
  intro i
  exact sqrt_bound_of_sq n (norm_nonneg _) (apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) x)
    (summation_le_hilbert_sq n x i)

theorem signedDyadic_le_hilbert (n : ℕ) (x : Vec 𝕜 n) :
    ‖signedDyadic n x‖ ≤ Real.sqrt ((n : ℝ) + 1) * hilbertNorm n x := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) x))).mpr
  intro i
  exact sqrt_bound_of_sq n (norm_nonneg _) (apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) x)
    (signedDyadic_le_hilbert_sq n x i)

@[simp] theorem summation_zero (n : ℕ) : summation n (0 : Vec 𝕜 n) = 0 :=
  (summationLinear (𝕜 := 𝕜) n).map_zero

@[simp] theorem signedDyadic_zero (n : ℕ) : signedDyadic n (0 : Vec 𝕜 n) = 0 :=
  (signedDyadicLinear (𝕜 := 𝕜) n).map_zero

abbrev L1Vec (𝕜 : Type*) (n : ℕ) := PiLp 1 (fun _ : Leaf n => 𝕜)

private theorem l1_operator_bound (n : ℕ) (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) (x : L1Vec 𝕜 n) :
    ‖T (WithLp.ofLp x)‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [PiLp.norm_eq_of_L1]
  exact h (WithLp.ofLp x) i

/-- A genuine continuous linear map from counting-measure l1 to linfinity. -/
def asL1Operator (n : ℕ) (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n)
    (h : ∀ x i, ‖T x i‖ ≤ l1Norm n x) : L1Vec 𝕜 n →L[𝕜] Vec 𝕜 n :=
  (T.comp (WithLp.linearEquiv 1 𝕜 (Vec 𝕜 n)).toLinearMap).mkContinuous 1
    (l1_operator_bound n T h)

def summationOperator (n : ℕ) : L1Vec 𝕜 n →L[𝕜] Vec 𝕜 n :=
  asL1Operator n (summationLinear n) (summation_le_l1 n)

def signedDyadicOperator (n : ℕ) : L1Vec 𝕜 n →L[𝕜] Vec 𝕜 n :=
  asL1Operator n (signedDyadicLinear n) (signedDyadic_le_l1 n)

end HilbertUMD
