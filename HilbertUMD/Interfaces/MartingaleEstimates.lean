import HilbertUMD.UMD.MartingaleMaximal

/-!
# Classical estimates used in the martingale product argument

Source: Hytönen, van Neerven, Veraar, Weis, Analysis in Banach Spaces I (2016),
DOI https://doi.org/10.1007/978-3-319-48520-1.

The first two statements specialize Corollary 4.5.15, printed pp. 346--347,
the Hilbert-to-Hilbert predictable martingale-transform bound p* - 1.
For p=3 this is 2. The first takes the kth coefficient to be ε_k times
the identity. The second takes that coefficient to be the isometric embedding
of the coordinate Hilbert space into the kth orthogonal time coordinate of
its finite Hilbert direct sum. Its terminal norm is exactly the l2 norm of
the coordinate square functions. The initial coefficient is zero in both
specializations. Arbitrary dimension and depth occur after the fixed constant.

The third specializes the vector-valued Doob inequality, Theorem 3.2.7,
printed p. 178, to p=3, q=2 and the nonnegative submartingales |E_k f_j|.
The project's actual finite conditional averages and maximal functions are
used directly in the local proof, with the explicit constant (65 / 4).

The transform bound is proved in `MartingaleThree` using the cubic
Burkholder function and the actual finite conditional averages.
`MartingaleSquare` supplies the orthogonal time-coordinate identification
and proves the square-function bound. `MartingaleMaximal` proves the vector
Doob bound by a quadratic pathwise maximal inequality and scalar square-function
duality. All three cited names below are proved compatibility wrappers.
-/

noncomputable section
open scoped ENNReal NNReal
namespace HilbertUMD.Interfaces

/-- HNVW I, Corollary 4.5.15, at p=3, finite Hilbert target and deterministic
real scalar contractions. -/
theorem dyadic_hilbert_transform_three {ι : Type*} [Fintype ι]
    (n : ℕ) (ε : Fin n → ℝ) (hε : ∀ k, |ε k| ≤ 1) (f : Leaf n → ι → ℝ) :
    mixedNorm 3 2 (leafUniform n) (fun x j => dyadicScalar n ε (fun y => f y j) x) ≤
      2 * mixedNorm 3 2 (leafUniform n) f := by
  exact HilbertUMD.dyadic_hilbert_transform_three n ε hε f

/-- HNVW I, Corollary 4.5.15, with orthogonal coordinate embeddings of the
successive martingale differences. -/
theorem dyadic_hilbert_square_three {ι : Type*} [Fintype ι]
    (n : ℕ) (f : Leaf n → ι → ℝ) :
    mixedNorm 3 2 (leafUniform n) (fun x j => dyadicSquareFunction n (fun y => f y j) x) ≤
      2 * mixedNorm 3 2 (leafUniform n) f := by
  exact HilbertUMD.dyadic_hilbert_square_three n f

/-- HNVW I, Theorem 3.2.7, specialized to the actual finite dyadic averages.
The constant is quantified before both depth and coordinate space. -/
theorem exists_dyadic_vector_doob_three_two :
    ∃ D : ℝ≥0, ∀ (n : ℕ) (ι : Type) [Fintype ι] (f : Leaf n → ι → ℝ),
      mixedNorm 3 2 (leafUniform n) (fun x j => dyadicMaximal n (fun y => f y j) x) ≤
        (D : ℝ≥0∞) * mixedNorm 3 2 (leafUniform n) f := by
  refine ⟨(65 / 4), ?_⟩
  intro n ι _ f
  simpa only [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat]
    using HilbertUMD.dyadic_vector_doob_three_two n f

end HilbertUMD.Interfaces
