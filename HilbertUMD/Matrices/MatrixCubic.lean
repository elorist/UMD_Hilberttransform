import HilbertUMD.Foundations.Matrices
import HilbertUMD.Analysis.Cubic

/-!
# The tree matrices in the cubic upper-bound argument

The common recursion includes the antisymmetric sign matrix and the
zero-diagonal part of the signed dyadic matrix. Algebraic energy increments
are proved here; analytic estimates on their integrals are separate inputs.
-/

noncomputable section
open scoped BigOperators
namespace HilbertUMD

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Off-diagonal tree matrix, with sibling coefficient indexed by height. -/
def treeMatrix (η : 𝕜) (c : ℕ → 𝕜) : (n : ℕ) → Vec 𝕜 n → Vec 𝕜 n
  | 0, _ => 0
  | n + 1, x => Sum.elim
      (fun i => treeMatrix η c n (left x) i + c (n + 1) * total (right x))
      (fun i => treeMatrix η c n (right x) i + η * c (n + 1) * total (left x))

theorem treeMatrix_add (η : 𝕜) (c : ℕ → 𝕜) (n : ℕ) (x y : Vec 𝕜 n) :
    treeMatrix η c n (x + y) = treeMatrix η c n x + treeMatrix η c n y := by
  induction n with
  | zero => simp [treeMatrix]
  | succ n ih =>
    funext i
    rcases i with i | i
    · change treeMatrix η c n (left x + left y) i + c (n+1) * total (right x + right y) = _
      rw [ih, total_add]
      change (treeMatrix η c n (left x) i + treeMatrix η c n (left y) i) +
        c (n+1) * (total (right x) + total (right y)) = _
      simp only [Pi.add_apply, treeMatrix, Sum.elim_inl]
      ring
    · change treeMatrix η c n (right x + right y) i + η * c (n+1) * total (left x + left y) = _
      rw [ih, total_add]
      change (treeMatrix η c n (right x) i + treeMatrix η c n (right y) i) +
        η * c (n+1) * (total (left x) + total (left y)) = _
      simp only [Pi.add_apply, treeMatrix, Sum.elim_inr]
      ring

theorem treeMatrix_smul (η : 𝕜) (c : ℕ → 𝕜) (n : ℕ) (a : 𝕜) (x : Vec 𝕜 n) :
    treeMatrix η c n (a • x) = a • treeMatrix η c n x := by
  induction n with
  | zero => simp [treeMatrix]
  | succ n ih =>
    funext i
    rcases i with i | i
    · change treeMatrix η c n (a • left x) i + c (n+1) * total (a • right x) = _
      rw [ih, total_smul]
      change a * treeMatrix η c n (left x) i + c (n+1) * (a * total (right x)) =
        a * (treeMatrix η c n (left x) i + c (n+1) * total (right x))
      ring
    · change treeMatrix η c n (a • right x) i + η * c (n+1) * total (a • left x) = _
      rw [ih, total_smul]
      change a * treeMatrix η c n (right x) i + η * c (n+1) * (a * total (left x)) =
        a * (treeMatrix η c n (right x) i + η * c (n+1) * total (left x))
      ring

def treeMatrixLinear (η : 𝕜) (c : ℕ → 𝕜) (n : ℕ) : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n where
  toFun := treeMatrix η c n
  map_add' := treeMatrix_add η c n
  map_smul' := treeMatrix_smul η c n

theorem treeMatrix_signedDyadic (n : ℕ) (x : Vec 𝕜 n) :
    treeMatrix 1 (fun k => (-1 : 𝕜)^k) n x = signedDyadic n x - x := by
  induction n with
  | zero => simp [treeMatrix, signedDyadic]
  | succ n ih =>
    funext i
    rcases i with i | i
    · change treeMatrix 1 (fun k => (-1 : 𝕜)^k) n (left x) i + (-1 : 𝕜)^(n+1) * total (right x) = _
      rw [ih]
      change (signedDyadic n (left x) i - left x i) + (-1 : 𝕜)^(n+1) * total (right x) =
        (signedDyadic n (left x) i + (-1 : 𝕜)^(n+1) * total (right x)) - left x i
      ring
    · change treeMatrix 1 (fun k => (-1 : 𝕜)^k) n (right x) i + 1 * (-1 : 𝕜)^(n+1) * total (left x) = _
      rw [ih]
      change (signedDyadic n (right x) i - right x i) + 1 * (-1 : 𝕜)^(n+1) * total (left x) =
        ((-1 : 𝕜)^(n+1) * total (left x) + signedDyadic n (right x) i) - right x i
      ring

/-- The antisymmetric tree matrix is 2Σ−J−I, with the manuscript's ordering. -/
theorem treeMatrix_sign (n : ℕ) (x : Vec 𝕜 n) (i : Leaf n) :
    treeMatrix (-1) (fun _ => (-1 : 𝕜)) n x i =
      2 * summation n x i - total x - x i := by
  induction n with
  | zero =>
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    simp [treeMatrix, summation, total, hi]
    ring
  | succ n ih =>
    rw [total_succ]
    rcases i with i | i
    · change treeMatrix (-1) (fun _ => (-1 : 𝕜)) n (left x) i + (-1) * total (right x) = _
      rw [ih]
      change (2 * summation n (left x) i - total (left x) - left x i) + (-1) * total (right x) =
        2 * summation n (left x) i - (total (left x) + total (right x)) - left x i
      ring
    · change treeMatrix (-1) (fun _ => (-1 : 𝕜)) n (right x) i + (-1) * (-1) * total (left x) = _
      rw [ih]
      change (2 * summation n (right x) i - total (right x) - right x i) + (-1) * (-1) * total (left x) =
        2 * (total (left x) + summation n (right x) i) - (total (left x) + total (right x)) - right x i
      ring

def treePairing (n : ℕ) (x y : Vec 𝕜 n) : 𝕜 := ∑ i, x i * y i

theorem treePairing_comm (n : ℕ) (x y : Vec 𝕜 n) :
    treePairing n x y = treePairing n y x := by
  simp only [treePairing, mul_comm]

theorem treePairing_matrix_succ (η : 𝕜) (c : ℕ → 𝕜) (n : ℕ)
    (x y : Vec 𝕜 (n+1)) :
    treePairing (n+1) x (treeMatrix η c (n+1) y) =
      treePairing n (left x) (treeMatrix η c n (left y)) +
      treePairing n (right x) (treeMatrix η c n (right y)) +
      c (n+1) * total (left x) * total (right y) +
      η * c (n+1) * total (right x) * total (left y) := by
  change (∑ i : Leaf n ⊕ Leaf n, x i * treeMatrix η c (n+1) y i) = _
  rw [Fintype.sum_sum_type]
  simp only [treeMatrix, Sum.elim_inl, Sum.elim_inr, mul_add, Finset.sum_add_distrib]
  simp only [treePairing, total, left, right, ← Finset.sum_mul]
  ring

/-- The precise transpose relation, valid over either scalar field. -/
theorem treeMatrix_transpose (η : 𝕜) (c : ℕ → 𝕜) (hη : η ^ 2 = 1)
    (n : ℕ) (x y : Vec 𝕜 n) :
    treePairing n x (treeMatrix η c n y) =
      η * treePairing n (treeMatrix η c n x) y := by
  induction n with
  | zero => simp [treeMatrix, treePairing]
  | succ n ih =>
    rw [treePairing_comm (n+1) (treeMatrix η c (n+1) x) y]
    rw [treePairing_matrix_succ, treePairing_matrix_succ]
    rw [ih (left x) (left y), ih (right x) (right y)]
    rw [treePairing_comm n (treeMatrix η c n (left x)) (left y),
      treePairing_comm n (treeMatrix η c n (right x)) (right y)]
    calc
      _ = η * (treePairing n (left y) (treeMatrix η c n (left x)) +
        treePairing n (right y) (treeMatrix η c n (right x))) +
        c (n+1) * total (left x) * total (right y) +
        η * c (n+1) * total (right x) * total (left y) := by ring
      _ = η * (treePairing n (left y) (treeMatrix η c n (left x)) +
        treePairing n (right y) (treeMatrix η c n (right x))) +
        η^2 * c (n+1) * total (left x) * total (right y) +
        η * c (n+1) * total (right x) * total (left y) := by rw [hη, one_mul]
      _ = _ := by ring

/-- One parent block's exact contribution to equation (3.9). -/
theorem tree_energy_increment (η c u v a b r : ℝ) (hη : η ^ 2 = 1) (hc : c ^ 2 = 1) :
    u * (r + c * b)^2 + v * (r + η * c * a)^2 - (u + v) * r^2 =
      u * b^2 + v * a^2 + 2 * c * r * (u * b + η * v * a) := by
  calc
    _ = u * c^2 * b^2 + v * η^2 * c^2 * a^2 + 2 * c * r * (u * b + η * v * a) := by ring
    _ = _ := by rw [hη, hc]; ring

/-- Full energy with an external common row value. -/
def treeEnergy (η : ℝ) (c : ℕ → ℝ) (n : ℕ) (x y : Vec ℝ n) (b : ℝ) : ℝ :=
  ∑ i, x i * (b + treeMatrix η c n y i)^2

def treeRootJump (η c u v a b r : ℝ) : ℝ :=
  u * b^2 + v * a^2 + 2 * c * r * (u * b + η * v * a)

/-- Sum of the energy increments at one depth; the background is updated
along the path to each parent block. -/
def treeLevelJump (η : ℝ) (c : ℕ → ℝ) :
    (n k : ℕ) → Vec ℝ n → Vec ℝ n → ℝ → ℝ
  | 0, _, _, _, _ => 0
  | n+1, 0, x, y, b => treeRootJump η (c (n+1))
      (total (left x)) (total (right x)) (total (left y)) (total (right y)) b
  | n+1, k+1, x, y, b =>
      treeLevelJump η c n k (left x) (left y) (b + c (n+1) * total (right y)) +
      treeLevelJump η c n k (right x) (right y) (b + η * c (n+1) * total (left y))

theorem treeEnergy_succ (η : ℝ) (c : ℕ → ℝ) (n : ℕ)
    (x y : Vec ℝ (n+1)) (b : ℝ) :
    treeEnergy η c (n+1) x y b =
      treeEnergy η c n (left x) (left y) (b + c (n+1) * total (right y)) +
      treeEnergy η c n (right x) (right y) (b + η * c (n+1) * total (left y)) := by
  change (∑ i : Leaf n ⊕ Leaf n, x i * (b + treeMatrix η c (n+1) y i)^2) = _
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · simp only [treeMatrix, Sum.elim_inl, left]
    ring
  · simp only [treeMatrix, Sum.elim_inr, right]
    ring

/-- Exact finite energy telescoping, before any analytic estimates are used. -/
theorem treeEnergy_eq_sum_jumps (η : ℝ) (c : ℕ → ℝ)
    (hη : η^2 = 1) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ)
    (x y : Vec ℝ n) (b : ℝ) :
    treeEnergy η c n x y b = total x * b^2 +
      ∑ k ∈ Finset.range n, treeLevelJump η c n k x y b := by
  induction n generalizing b with
  | zero => simp [treeEnergy, treeMatrix, total]
  | succ n ih =>
    rw [treeEnergy_succ, ih, ih, total_succ, Finset.sum_range_succ']
    simp only [treeLevelJump, Finset.sum_add_distrib]
    have h := tree_energy_increment η (c (n+1)) (total (left x))
      (total (right x)) (total (left y)) (total (right y)) b hη (hc (n+1))
    unfold treeRootJump
    linarith

/-- In the actual application there is no external row at the root. -/
theorem tree_cubic_energy_eq (η : ℝ) (c : ℕ → ℝ)
    (hη : η^2 = 1) (hc : ∀ k, c k ^ 2 = 1) (n : ℕ) (x y : Vec ℝ n) :
    (∑ i, x i * (treeMatrix η c n y i)^2) =
      ∑ k ∈ Finset.range n, treeLevelJump η c n k x y 0 := by
  simpa only [treeEnergy, zero_add, zero_pow (by decide : 2 ≠ 0), mul_zero]
    using treeEnergy_eq_sum_jumps η c hη hc n x y 0

/-- Internal blocks at a given depth. Empty depths need no special hypotheses
when summing; the levels 0,...,n−1 are the nonempty ones. -/
abbrev TreeParents : ℕ → ℕ → Type
  | 0, _ => PEmpty
  | _+1, 0 => Unit
  | n+1, k+1 => TreeParents n k ⊕ TreeParents n k

instance treeParentsFintype : (n k : ℕ) → Fintype (TreeParents n k)
  | 0, _ => inferInstanceAs (Fintype PEmpty)
  | _+1, 0 => inferInstanceAs (Fintype Unit)
  | n+1, k+1 => by
      letI := treeParentsFintype n k
      exact inferInstanceAs (Fintype (TreeParents n k ⊕ TreeParents n k))

structure TreeBlockValues where
  u : ℝ
  v : ℝ
  b : ℝ

/-- Child sums and common external row value at a parent block. -/
def treeBlockValues (η : ℝ) (c : ℕ → ℝ) :
    (n k : ℕ) → Vec ℝ n → ℝ → TreeParents n k → TreeBlockValues
  | 0, _, _, _, i => nomatch i
  | _n+1, 0, x, b, _ => ⟨total (left x), total (right x), b⟩
  | n+1, k+1, x, b, Sum.inl i =>
      treeBlockValues η c n k (left x) (b + c (n+1) * total (right x)) i
  | n+1, k+1, x, b, Sum.inr i =>
      treeBlockValues η c n k (right x) (b + η * c (n+1) * total (left x)) i

/-- The children at any internal depth partition all the input coordinates. -/
theorem treeBlockValues_sum (η : ℝ) (c : ℕ → ℝ) (n k : ℕ) (hk : k < n)
    (x : Vec ℝ n) (b : ℝ) :
    (∑ i, ((treeBlockValues η c n k x b i).u + (treeBlockValues η c n k x b i).v)) =
      total x := by
  induction n generalizing k b with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp only [treeBlockValues, Fintype.sum_unique, total_succ]
    | succ k =>
      change (∑ i : TreeParents n k ⊕ TreeParents n k, _) = _
      rw [Fintype.sum_sum_type]
      simp only [treeBlockValues]
      rw [ih k (by omega), ih k (by omega), total_succ]

theorem treeBlockValues_nonneg (η : ℝ) (c : ℕ → ℝ) (n k : ℕ)
    (x : Vec ℝ n) (hx : ∀ i, 0 ≤ x i) (b : ℝ) (i : TreeParents n k) :
    0 ≤ (treeBlockValues η c n k x b i).u ∧
      0 ≤ (treeBlockValues η c n k x b i).v := by
  induction n generalizing k b with
  | zero => exact PEmpty.elim i
  | succ n ih =>
    cases k with
    | zero =>
      constructor
      · exact Finset.sum_nonneg (fun j _ => hx (Sum.inl j))
      · exact Finset.sum_nonneg (fun j _ => hx (Sum.inr j))
    | succ k =>
      rcases i with i | i
      · exact ih k (left x) (fun j => hx (Sum.inl j)) _ i
      · exact ih k (right x) (fun j => hx (Sum.inr j)) _ i

/-- The external row is bounded by the mass outside the current block,
plus the original background. This proves the manuscript's |b_I|≤g. -/
theorem treeBlockValues_mass_bound (η : ℝ) (c : ℕ → ℝ)
    (hη : |η| ≤ 1) (hc : ∀ k, |c k| ≤ 1) (n k : ℕ)
    (x : Vec ℝ n) (hx : ∀ i, 0 ≤ x i) (b : ℝ) (i : TreeParents n k) :
    |(treeBlockValues η c n k x b i).b| +
      (treeBlockValues η c n k x b i).u + (treeBlockValues η c n k x b i).v ≤
      total x + |b| := by
  induction n generalizing k b with
  | zero => exact PEmpty.elim i
  | succ n ih =>
    have hl : 0 ≤ total (left x) := Finset.sum_nonneg (fun j _ => hx (Sum.inl j))
    have hr : 0 ≤ total (right x) := Finset.sum_nonneg (fun j _ => hx (Sum.inr j))
    cases k with
    | zero =>
      simp only [treeBlockValues, total_succ]
      linarith
    | succ k =>
      rcases i with i | i
      · have h := ih k (left x) (fun j => hx (Sum.inl j))
          (b + c (n+1) * total (right x)) i
        have hab : |b + c (n+1) * total (right x)| ≤ |b| + total (right x) := by
          calc
            _ ≤ |b| + |c (n+1) * total (right x)| := abs_add_le _ _
            _ = |b| + |c (n+1)| * total (right x) := by rw [abs_mul, abs_of_nonneg hr]
            _ ≤ _ := by nlinarith [hc (n+1)]
        change _ ≤ total x + |b|
        rw [total_succ]
        exact h.trans (by linarith)
      · have h := ih k (right x) (fun j => hx (Sum.inr j))
          (b + η * c (n+1) * total (left x)) i
        have he : |η * c (n+1)| ≤ 1 := by
          rw [abs_mul]
          simpa using mul_le_mul hη (hc (n+1)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
        have hab : |b + η * c (n+1) * total (left x)| ≤ |b| + total (left x) := by
          calc
            _ ≤ |b| + |η * c (n+1) * total (left x)| := abs_add_le _ _
            _ = |b| + |η * c (n+1)| * total (left x) := by rw [abs_mul, abs_of_nonneg hl]
            _ ≤ _ := by nlinarith
        rw [total_succ]
        exact h.trans (by linarith)

/-- The recursive level sum is exactly the finite parent-block sum used in
the analytic product estimates. The auxiliary background `a` drops out. -/
theorem treeLevelJump_eq_sum_blocks (η : ℝ) (c : ℕ → ℝ) (n k : ℕ)
    (x y : Vec ℝ n) (a b : ℝ) :
    treeLevelJump η c n k x y b =
      ∑ i, treeRootJump η (c (n-k))
        (treeBlockValues η c n k x a i).u (treeBlockValues η c n k x a i).v
        (treeBlockValues η c n k y b i).u (treeBlockValues η c n k y b i).v
        (treeBlockValues η c n k y b i).b := by
  induction n generalizing k a b with
  | zero => simp [treeLevelJump]
  | succ n ih =>
    cases k with
    | zero => simp [treeLevelJump, treeBlockValues]
    | succ k =>
      change _ = ∑ i : TreeParents n k ⊕ TreeParents n k, _
      rw [Fintype.sum_sum_type]
      simp only [treeLevelJump, treeBlockValues, Nat.add_sub_add_right]
      rw [ih k (left x) (left y) (a + c (n+1) * total (right x)),
        ih k (right x) (right y) (a + η * c (n+1) * total (left x))]

section LinearCommutation

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]

/-- The same block data over a real vector space, in particular a Bochner
Lp space. This avoids choosing pointwise-linear representatives of Lp maps. -/
structure TreeBlockVector (E : Type*) where
  u : E
  v : E
  b : E

def treeBlockVector (η : ℝ) (c : ℕ → ℝ) :
    (n k : ℕ) → (Leaf n → E) → E → TreeParents n k → TreeBlockVector E
  | 0, _, _, _, i => nomatch i
  | _n+1, 0, x, b, _ => ⟨∑ j, x (Sum.inl j), ∑ j, x (Sum.inr j), b⟩
  | n+1, k+1, x, b, Sum.inl i =>
      treeBlockVector η c n k (fun j => x (Sum.inl j))
        (b + c (n+1) • ∑ j, x (Sum.inr j)) i
  | n+1, k+1, x, b, Sum.inr i =>
      treeBlockVector η c n k (fun j => x (Sum.inr j))
        (b + (η * c (n+1)) • ∑ j, x (Sum.inl j)) i

/-- Every scalar linear realization commutes with the child sums and the
common row background. This applies directly to bundled Lp operators. -/
theorem treeBlockVector_map (R : E →ₗ[ℝ] F) (η : ℝ) (c : ℕ → ℝ) (n k : ℕ)
    (x : Leaf n → E) (b : E) (i : TreeParents n k) :
    (treeBlockVector η c n k (fun j => R (x j)) (R b) i).u =
      R (treeBlockVector η c n k x b i).u ∧
    (treeBlockVector η c n k (fun j => R (x j)) (R b) i).v =
      R (treeBlockVector η c n k x b i).v ∧
    (treeBlockVector η c n k (fun j => R (x j)) (R b) i).b =
      R (treeBlockVector η c n k x b i).b := by
  induction n generalizing k b with
  | zero => exact PEmpty.elim i
  | succ n ih =>
    cases k with
    | zero => simp [treeBlockVector, map_sum]
    | succ k =>
      rcases i with i | i
      · simpa only [treeBlockVector, map_add, map_smul, map_sum] using
          ih k (fun j => x (Sum.inl j)) (b + c (n+1) • ∑ j, x (Sum.inr j)) i
      · simpa only [treeBlockVector, map_add, map_smul, map_sum] using
          ih k (fun j => x (Sum.inr j)) (b + (η * c (n+1)) • ∑ j, x (Sum.inl j)) i

end LinearCommutation

end HilbertUMD
