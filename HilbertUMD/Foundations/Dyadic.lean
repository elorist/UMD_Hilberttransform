import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic

/-! Finite dyadic geometry for Hilbert transform and UMD constants. -/

namespace HilbertUMD

noncomputable section
open scoped BigOperators

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

/-- The j-th unit coordinate vector. -/
def basisVec {n : ℕ} (j : Leaf n) : Vec 𝕜 n := fun i => if i = j then 1 else 0

@[simp] theorem basisVec_self {n : ℕ} (j : Leaf n) : (basisVec j : Vec 𝕜 n) j = 1 := by
  simp [basisVec]

@[simp] theorem total_basisVec {n : ℕ} (j : Leaf n) : total (basisVec j : Vec 𝕜 n) = 1 := by
  simp [total, basisVec]

@[simp] theorem l1Norm_basisVec {n : ℕ} (j : Leaf n) : l1Norm n (basisVec j : Vec 𝕜 n) = 1 := by
  simp [l1Norm_eq, basisVec, apply_ite norm]

@[simp] theorem left_basisVec_inl {n : ℕ} (j : Leaf n) :
    left (basisVec (Sum.inl j) : Vec 𝕜 (n + 1)) = basisVec j := by
  funext i; simp [left, basisVec, Sum.inl.injEq]

@[simp] theorem right_basisVec_inl {n : ℕ} (j : Leaf n) :
    right (basisVec (Sum.inl j) : Vec 𝕜 (n + 1)) = 0 := by
  funext i; simp [right, basisVec]

@[simp] theorem left_basisVec_inr {n : ℕ} (j : Leaf n) :
    left (basisVec (Sum.inr j) : Vec 𝕜 (n + 1)) = 0 := by
  funext i; simp [left, basisVec]

@[simp] theorem right_basisVec_inr {n : ℕ} (j : Leaf n) :
    right (basisVec (Sum.inr j) : Vec 𝕜 (n + 1)) = basisVec j := by
  funext i; simp [right, basisVec, Sum.inr.injEq]

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

end
end HilbertUMD
