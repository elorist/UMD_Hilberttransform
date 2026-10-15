module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

/-!
# Theorem 1.1: sharp Hilbert-transform and UMD comparisons

This independent statement imports only Mathlib. It includes the concrete
spaces from the paper, the principal-value Hilbert constant, and the full
sigma-finite martingale UMD constant. The sole deliberate proof hole is the
final theorem. All elementary proofs above it merely construct the norms.

A depth-n binary tree has 2^n leaves. Its H norm is the Euclidean norm of all
dyadic block sums; E has the infimum norm l1 + H. The X and Y norms are the
maximum of the E norm and the sup norm after, respectively, the summation
matrix and the signed dyadic matrix. Both spaces are complete.

The final statement quantifies one pair of positive real constants before
the depth and both scalar fields. It asserts the dimensions and all eight
inequalities at p=2, with n and sqrt(n) exactly as in the paper. The UMD
sample-space universe is arbitrary. Remark 1.2 and Corollary 1.3 are not
claims of this submission.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal NNReal

namespace HilbertUMD
universe uΩ

section DyadicGeometry

/-- Leaves of the full binary tree, ordered by putting the left half first. -/
abbrev Leaf : ℕ → Type
  | 0 => Fin 1
  | n + 1 => Leaf n ⊕ Leaf n

instance leafFintype : (n : ℕ) → Fintype (Leaf n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | n + 1 => by
    letI := leafFintype n
    exact inferInstanceAs (Fintype (Leaf n ⊕ Leaf n))

instance leafDecidableEq : (n : ℕ) → DecidableEq (Leaf n)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | n + 1 => by
    letI := leafDecidableEq n
    exact inferInstanceAs (DecidableEq (Leaf n ⊕ Leaf n))

instance leafNonempty : (n : ℕ) → Nonempty (Leaf n)
  | 0 => inferInstanceAs (Nonempty (Fin 1))
  | n + 1 => by
    let := leafNonempty n
    exact inferInstanceAs (Nonempty (Leaf n ⊕ Leaf n))

/-- Nodes include the root and every node of each child tree, including leaves. -/
abbrev Node : ℕ → Type
  | 0 => Fin 1
  | n + 1 => Unit ⊕ (Node n ⊕ Node n)

instance nodeFintype : (n : ℕ) → Fintype (Node n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | n + 1 => by
    letI := nodeFintype n
    exact inferInstanceAs (Fintype (Unit ⊕ (Node n ⊕ Node n)))

theorem card_leaf (n : ℕ) : Fintype.card (Leaf n) = 2 ^ n := by
  induction n with
  | zero => simp [Leaf]
  | succ n ih => simp [Leaf, Fintype.card_sum, ih, pow_succ]; omega

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Vec (𝕜 : Type*) (n : ℕ) := Leaf n → 𝕜

def left {n : ℕ} (x : Vec 𝕜 (n + 1)) : Vec 𝕜 n := fun i => x (Sum.inl i)
def right {n : ℕ} (x : Vec 𝕜 (n + 1)) : Vec 𝕜 n := fun i => x (Sum.inr i)

def total {n : ℕ} (x : Vec 𝕜 n) : 𝕜 := ∑ i, x i

@[simp] theorem total_zero {n : ℕ} : total (0 : Vec 𝕜 n) = 0 := by simp [total]
@[simp] theorem total_add {n : ℕ} (x y : Vec 𝕜 n) :
    total (x + y) = total x + total y := by simp [total, Finset.sum_add_distrib]
@[simp] theorem total_smul {n : ℕ} (c : 𝕜) (x : Vec 𝕜 n) :
    total (c • x) = c • total x := by simp [total, Finset.mul_sum]

theorem total_succ {n : ℕ} (x : Vec 𝕜 (n + 1)) :
    total x = total (left x) + total (right x) := by
  exact Fintype.sum_sum_type x

/-- The sum of coordinates below each dyadic node. -/
def blockSum : (n : ℕ) → Vec 𝕜 n → Node n → 𝕜
  | 0, x, i => x i
  | _n + 1, x, Sum.inl _ => total x
  | n + 1, x, Sum.inr (Sum.inl i) => blockSum n (left x) i
  | n + 1, x, Sum.inr (Sum.inr i) => blockSum n (right x) i

theorem blockSum_add (n : ℕ) (x y : Vec 𝕜 n) :
    blockSum n (x + y) = blockSum n x + blockSum n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with u | (i | i)
    · exact total_add x y
    · exact congrFun (ih (left x) (left y)) i
    · exact congrFun (ih (right x) (right y)) i

theorem blockSum_smul (n : ℕ) (c : 𝕜) (x : Vec 𝕜 n) :
    blockSum n (c • x) = c • blockSum n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    rcases i with u | (i | i)
    · exact total_smul c x
    · exact congrFun (ih (left x)) i
    · exact congrFun (ih (right x)) i

/-- The dyadic sum map into a genuine finite-dimensional Hilbert space. -/
def dyadicMap (n : ℕ) : Vec 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 (Node n) where
  toFun x := WithLp.toLp 2 (blockSum n x)
  map_add' x y := by apply PiLp.ext; exact congrFun (blockSum_add n x y)
  map_smul' c x := by apply PiLp.ext; exact congrFun (blockSum_smul n c x)

/-- The manuscript's Hilbert norm, as a seminorm pulled back along the dyadic sum map. -/
def hilbertNorm (n : ℕ) : Seminorm 𝕜 (Vec 𝕜 n) :=
  (normSeminorm 𝕜 (EuclideanSpace 𝕜 (Node n))).comp (dyadicMap n)

theorem hilbertNorm_sq (n : ℕ) (x : Vec 𝕜 n) :
    hilbertNorm n x ^ 2 = ∑ i, ‖blockSum n x i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq (dyadicMap n x)

theorem hilbertNorm_zero_level (x : Vec 𝕜 0) : hilbertNorm 0 x = ‖x 0‖ := by
  change ‖dyadicMap 0 x‖ = ‖x 0‖
  rw [EuclideanSpace.norm_eq]
  simp [dyadicMap, blockSum, Node]

theorem hilbertNorm_succ_sq (n : ℕ) (x : Vec 𝕜 (n + 1)) :
    hilbertNorm (n + 1) x ^ 2 =
      ‖total x‖ ^ 2 + hilbertNorm n (left x) ^ 2 + hilbertNorm n (right x) ^ 2 := by
  rw [hilbertNorm_sq (n + 1) x, hilbertNorm_sq n (left x), hilbertNorm_sq n (right x)]
  rw [Fintype.sum_sum_type]
  simp only [blockSum, Fintype.sum_unique, Fintype.sum_sum_type]
  ring

/-- Counting-measure l1 norm. -/
def l1Norm (n : ℕ) : Seminorm 𝕜 (Vec 𝕜 n) :=
  Seminorm.of (fun x => ∑ i, ‖x i‖)
    (fun x y => by simpa [Finset.sum_add_distrib] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => norm_add_le (x i) (y i)))
    (fun c x => by simp [Finset.mul_sum])

theorem l1Norm_eq (n : ℕ) (x : Vec 𝕜 n) : l1Norm n x = ∑ i, ‖x i‖ := rfl

theorem l1Norm_succ (n : ℕ) (x : Vec 𝕜 (n + 1)) :
    l1Norm (n + 1) x = l1Norm n (left x) + l1Norm n (right x) :=
  Fintype.sum_sum_type _

theorem norm_total_le (n : ℕ) (x : Vec 𝕜 n) : ‖total x‖ ≤ l1Norm n x :=
  norm_sum_le _ _

/-- The infimum norm l1 + H, using mathlib's infimum of seminorms. -/
def sumNorm (n : ℕ) : Seminorm 𝕜 (Vec 𝕜 n) := l1Norm n ⊓ hilbertNorm n

theorem sumNorm_eq_inf (n : ℕ) (x : Vec 𝕜 n) :
    sumNorm n x = ⨅ u : Vec 𝕜 n, l1Norm n u + hilbertNorm n (x - u) := rfl

theorem sumNorm_le_l1 (n : ℕ) (x : Vec 𝕜 n) : sumNorm n x ≤ l1Norm n x :=
  (inf_le_left : sumNorm n ≤ l1Norm n) x

theorem sumNorm_le_hilbert (n : ℕ) (x : Vec 𝕜 n) : sumNorm n x ≤ hilbertNorm n x :=
  (inf_le_right : sumNorm n ≤ hilbertNorm n) x

theorem norm_total_le_hilbert (n : ℕ) (x : Vec 𝕜 n) : ‖total x‖ ≤ hilbertNorm n x := by
  cases n with
  | zero => rw [hilbertNorm_zero_level x]; simp [total]
  | succ n =>
    have h := hilbertNorm_succ_sq n x
    have hp := apply_nonneg (hilbertNorm (𝕜 := 𝕜) (n + 1)) x
    nlinarith [sq_nonneg (hilbertNorm n (left x)), sq_nonneg (hilbertNorm n (right x))]

theorem norm_coordinate_le_hilbert (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    ‖x i‖ ≤ hilbertNorm n x := by
  induction n with
  | zero =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simpa [hi] using (le_of_eq (hilbertNorm_zero_level x).symm)
  | succ n ih =>
    have h := hilbertNorm_succ_sq n x
    have hp := apply_nonneg (hilbertNorm (𝕜 := 𝕜) (n + 1)) x
    rcases i with i | i
    · have hi := ih (left x) i
      have hq := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (left x)
      change ‖left x i‖ ≤ _
      nlinarith [sq_nonneg ‖total x‖, sq_nonneg (hilbertNorm n (right x))]
    · have hi := ih (right x) i
      have hq := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (right x)
      change ‖right x i‖ ≤ _
      nlinarith [sq_nonneg ‖total x‖, sq_nonneg (hilbertNorm n (left x))]

theorem hilbertNorm_eq_zero_iff (n : ℕ) (x : Vec 𝕜 n) : hilbertNorm n x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    exact norm_eq_zero.mp (le_antisymm (h ▸ norm_coordinate_le_hilbert n x i) (norm_nonneg _))
  · rintro rfl; exact map_zero _

theorem dyadicMap_injective (n : ℕ) : Function.Injective (dyadicMap (𝕜 := 𝕜) n) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (hilbertNorm_eq_zero_iff n _).mp
  change ‖dyadicMap n (x - y)‖ = 0
  simp [map_sub, h]

theorem hilbertNorm_le_l1_sq (n : ℕ) (x : Vec 𝕜 n) :
    hilbertNorm n x ^ 2 ≤ ((n : ℝ) + 1) * l1Norm n x ^ 2 := by
  induction n with
  | zero =>
    rw [hilbertNorm_zero_level x, l1Norm_eq 0 x]
    simp
  | succ n ih =>
    have hl := ih (left x)
    have hr := ih (right x)
    have ht := norm_total_le (n + 1) x
    have ha := apply_nonneg (l1Norm (𝕜 := 𝕜) n) (left x)
    have hb := apply_nonneg (l1Norm (𝕜 := 𝕜) n) (right x)
    rw [l1Norm_succ] at ht ⊢
    rw [hilbertNorm_succ_sq]
    push_cast
    have ht2 : ‖total x‖ ^ 2 ≤ (l1Norm n (left x) + l1Norm n (right x)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    have hab := mul_nonneg (mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) ha) hb
    nlinarith

theorem hilbertNorm_le_l1 (n : ℕ) (x : Vec 𝕜 n) :
    hilbertNorm n x ≤ Real.sqrt ((n : ℝ) + 1) * l1Norm n x := by
  have h := hilbertNorm_le_l1_sq n x
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hp := apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) x
  have hq := apply_nonneg (l1Norm (𝕜 := 𝕜) n) x
  have hr := Real.sqrt_nonneg ((n : ℝ) + 1)
  apply (sq_le_sq₀ hp (mul_nonneg hr hq)).mp
  rw [mul_pow, hs]
  exact h

theorem hilbert_div_sqrt_le_sumNorm (n : ℕ) (x : Vec 𝕜 n) :
    hilbertNorm n x / Real.sqrt ((n : ℝ) + 1) ≤ sumNorm n x := by
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    have h := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [sumNorm_eq_inf]
  apply le_ciInf
  intro u
  apply (div_le_iff₀ hs).mpr
  have h := le_map_add_map_sub (hilbertNorm n) x u
  have hu := hilbertNorm_le_l1 n u
  have hv := mul_le_mul_of_nonneg_right h1 (apply_nonneg (hilbertNorm (𝕜 := 𝕜) n) (x - u))
  nlinarith

theorem sumNorm_eq_zero_iff (n : ℕ) (x : Vec 𝕜 n) : sumNorm n x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (hilbertNorm_eq_zero_iff n x).mp
    have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hx := hilbert_div_sqrt_le_sumNorm n x
    rw [h] at hx
    have := (div_le_iff₀ hs).mp hx
    exact le_antisymm (by simpa using this) (apply_nonneg _ _)
  · rintro rfl; exact map_zero _

end DyadicGeometry

-- Match source-module boundaries for Lean's local auxiliary-proof naming cache.
-- This clears no declarations and changes neither the statements nor kernel checking.
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section Matrices
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


end Matrices

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section Spaces
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The norm max(norm(Tx)_infinity, norm(x)_E). -/
def graphNorm (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : Seminorm 𝕜 (Vec 𝕜 n) :=
  (normSeminorm 𝕜 (Vec 𝕜 n)).comp T ⊔ sumNorm n

theorem graphNorm_eq_zero_iff (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) (x : Vec 𝕜 n) :
    graphNorm T x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (sumNorm_eq_zero_iff n x).mp
    apply le_antisymm _ (apply_nonneg (sumNorm (𝕜 := 𝕜) n) x)
    have hx : sumNorm n x ≤ graphNorm T x := le_max_right _ _
    simpa [h] using hx
  · rintro rfl; exact map_zero _

/-- A general graph-norm space used for X_n and Y_n. -/
def GraphSpace (_T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) := Vec 𝕜 n

instance (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : AddCommGroup (GraphSpace T) :=
  inferInstanceAs (AddCommGroup (Vec 𝕜 n))
instance (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : Module 𝕜 (GraphSpace T) :=
  inferInstanceAs (Module 𝕜 (Vec 𝕜 n))

def graphGroupNorm (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : AddGroupNorm (GraphSpace T) where
  toAddGroupSeminorm := (graphNorm T).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' x := (graphNorm_eq_zero_iff T x).mp

instance (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : NormedAddCommGroup (GraphSpace T) :=
  (graphGroupNorm T).toNormedAddCommGroup

instance (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : NormedSpace 𝕜 (GraphSpace T) where
  norm_smul_le c x := le_of_eq (map_smul_eq_mul (graphNorm T) c x)

instance (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : FiniteDimensional 𝕜 (GraphSpace T) :=
  inferInstanceAs (FiniteDimensional 𝕜 (Vec 𝕜 n))

instance (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : CompleteSpace (GraphSpace T) :=
  FiniteDimensional.complete 𝕜 (GraphSpace T)

abbrev XSpace (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := GraphSpace (summationLinear (𝕜 := 𝕜) n)
abbrev YSpace (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := GraphSpace (signedDyadicLinear (𝕜 := 𝕜) n)

end Spaces

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section PrincipalValue
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The symmetrically truncated kernel, with the manuscript's `1/π` normalization. -/
def hilbertTrunc (ε : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  (Real.pi)⁻¹ • ∫ y in {y : ℝ | ε < |x - y|}, (x - y)⁻¹ • f y

/-- The principal value exists at every point and is equal to `g`. -/
def IsHilbertPV (f g : ℝ → E) : Prop :=
  ∀ x : ℝ, Tendsto (fun ε : ℝ => hilbertTrunc ε f x) (𝓝[>] 0) (𝓝 (g x))


end PrincipalValue

section HilbertConstant
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- A finite operator Hilbert-transform bound on all `C¹` compactly supported tests. -/
def HilbertBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ f : ℝ → E, ContDiff ℝ 1 f → HasCompactSupport f →
    ∃ g : ℝ → F, IsHilbertPV (fun x => T (f x)) g ∧ MemLp g p volume ∧
      eLpNorm g p volume ≤ (C : ℝ≥0∞) * eLpNorm f p volume

/-- Least finite principal-value Hilbert-transform bound, or infinity if none exists. -/
def hilbertConstant (p : ℝ≥0∞) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : HilbertBound p T C), (C : ℝ≥0∞)


end HilbertConstant

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section Martingales
variable {Ω ι E : Type*} [MeasurableSpace Ω] [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The locally integrable characterization of an Lp martingale. -/
structure IsLpMartingale (f : ι → Ω → E)
    (ℱ : Filtration ι ‹MeasurableSpace Ω›) (p : ℝ≥0∞) (μ : Measure Ω) : Prop where
  stronglyAdapted : StronglyAdapted ℱ f
  memLp : ∀ i, MemLp (f i) p μ
  setIntegral_eq : ∀ i j, i ≤ j → ∀ s, MeasurableSet[ℱ i] s → μ s < ∞ →
    ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ


end Martingales

section Transforms
variable {Ω E F 𝕜 : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {m : ℕ}

/-- The sum of the chronological differences, indexed from zero in Lean. -/
def differenceSum (f : Fin (m + 1) → Ω → E) (x : Ω) : E :=
  ∑ k : Fin m, (f k.succ x - f k.castSucc x)

/-- A deterministic martingale transform followed by the coefficient operator. -/
def martingaleTransform (T : E →L[𝕜] F) (ε : Fin m → 𝕜)
    (f : Fin (m + 1) → Ω → E) (x : Ω) : F :=
  ∑ k : Fin m, ε k • T (f k.succ x - f k.castSucc x)


end Transforms

section UMDConstant
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The manuscript's operator UMD inequality on all sigma-finite sample spaces
in universe `uΩ`, with all unimodular scalars of the chosen field. -/
def UMDBound (p : ℝ≥0∞) (T : E →L[𝕜] F) (C : ℝ≥0) : Prop :=
  ∀ (Ω : Type uΩ) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), SigmaFinite μ →
  ∀ (m : ℕ), 1 ≤ m →
  ∀ (ℱ : Filtration (Fin (m + 1)) mΩ), SigmaFiniteFiltration μ ℱ →
  ∀ (f : Fin (m + 1) → Ω → E), IsLpMartingale f ℱ p μ →
  ∀ (ε : Fin m → 𝕜), (∀ k, ‖ε k‖ = 1) →
    eLpNorm (martingaleTransform T ε f) p μ ≤ (C : ℝ≥0∞) * eLpNorm (differenceSum f) p μ

/-- Least finite UMD bound, or infinity if no finite bound exists. -/
def umdConstant (p : ℝ≥0∞) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : UMDBound.{uΩ} p T C), (C : ℝ≥0∞)


end UMDConstant

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace Paper

/-- The paper's first family, indexed by the same depth n. -/
abbrev X (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := XSpace 𝕜 n

/-- The paper's second family, indexed by the same depth n. -/
abbrev Y (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) := YSpace 𝕜 n

/-- The paper's Hilbert constant hbar_{p,E}, over the displayed scalar field. -/
abbrev hbar (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] : ℝ≥0∞ :=
  hilbertConstant p (ContinuousLinearMap.id 𝕜 E)

/-- The paper's UMD constant beta_{p,E}, with sample spaces in universe uΩ.
At p=2, its value is independent of that universe. -/
abbrev beta (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] : ℝ≥0∞ :=
  umdConstant.{uΩ} p (ContinuousLinearMap.id 𝕜 E)

/-- The dimensions and all eight inequalities of Theorem 1.1, using n and
sqrt(n) exactly as in the paper. The spaces are Banach spaces by their existing
normed-space and completeness instances. Constants c and C are universal in
the public theorem; this statement does not prescribe Remark 1.2's numbers. -/
structure Theorem11Bounds (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)
    [NormedSpace ℝ (X 𝕜 n)] [NormedSpace ℝ (Y 𝕜 n)] (c C : ℝ) : Prop where
  x_dimension : Module.finrank 𝕜 (X 𝕜 n) = 2 ^ n
  y_dimension : Module.finrank 𝕜 (Y 𝕜 n) = 2 ^ n
  x_hilbert_lower : ENNReal.ofReal (c * (n : ℝ)) ≤ hbar 𝕜 2 (X 𝕜 n)
  x_hilbert_upper : hbar 𝕜 2 (X 𝕜 n) ≤ ENNReal.ofReal (C * (n : ℝ))
  x_umd_lower : ENNReal.ofReal (c * Real.sqrt (n : ℝ)) ≤ beta.{uΩ} 𝕜 2 (X 𝕜 n)
  x_umd_upper : beta.{uΩ} 𝕜 2 (X 𝕜 n) ≤ ENNReal.ofReal (C * Real.sqrt (n : ℝ))
  y_umd_lower : ENNReal.ofReal (c * (n : ℝ)) ≤ beta.{uΩ} 𝕜 2 (Y 𝕜 n)
  y_umd_upper : beta.{uΩ} 𝕜 2 (Y 𝕜 n) ≤ ENNReal.ofReal (C * (n : ℝ))
  y_hilbert_lower : ENNReal.ofReal (c * Real.sqrt (n : ℝ)) ≤ hbar 𝕜 2 (Y 𝕜 n)
  y_hilbert_upper : hbar 𝕜 2 (Y 𝕜 n) ≤ ENNReal.ofReal (C * Real.sqrt (n : ℝ))


end Paper

/-- Theorem 1.1, simultaneously over the real and complex fields, with the
full UMD constant over sample spaces in any chosen universe. -/
theorem Comparison.theorem_1_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Paper.Theorem11Bounds.{uΩ} ℝ n c C ∧ Paper.Theorem11Bounds.{uΩ} ℂ n c C := by
  sorry

end HilbertUMD
