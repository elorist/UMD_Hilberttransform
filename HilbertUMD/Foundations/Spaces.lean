import HilbertUMD.Foundations.Matrices
import HilbertUMD.Foundations.Geometry

noncomputable section
namespace HilbertUMD
variable (𝕜 : Type*) [RCLike 𝕜] (n : ℕ)

/-- H_n as a separate type, to avoid confusing its norm with the coordinate sup norm. -/
def HSpace := Vec 𝕜 n

instance : AddCommGroup (HSpace 𝕜 n) := inferInstanceAs (AddCommGroup (Vec 𝕜 n))
instance : Module 𝕜 (HSpace 𝕜 n) := inferInstanceAs (Module 𝕜 (Vec 𝕜 n))

def hSpaceMap : HSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 (Node n) := dyadicMap n

instance : NormedAddCommGroup (HSpace 𝕜 n) :=
  NormedAddCommGroup.induced _ _ (hSpaceMap 𝕜 n) (dyadicMap_injective n)

instance : InnerProductSpace 𝕜 (HSpace 𝕜 n) := InnerProductSpace.induced (hSpaceMap 𝕜 n)

instance : FiniteDimensional 𝕜 (HSpace 𝕜 n) :=
  inferInstanceAs (FiniteDimensional 𝕜 (Vec 𝕜 n))

instance : CompleteSpace (HSpace 𝕜 n) := FiniteDimensional.complete 𝕜 (HSpace 𝕜 n)

/-- E_n with the infimum norm from the manuscript. -/
def ESpace := Vec 𝕜 n

instance : AddCommGroup (ESpace 𝕜 n) := inferInstanceAs (AddCommGroup (Vec 𝕜 n))
instance : Module 𝕜 (ESpace 𝕜 n) := inferInstanceAs (Module 𝕜 (Vec 𝕜 n))

private def eGroupNorm : AddGroupNorm (ESpace 𝕜 n) where
  toAddGroupSeminorm := (sumNorm (𝕜 := 𝕜) n).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' x := (sumNorm_eq_zero_iff n x).mp

instance : NormedAddCommGroup (ESpace 𝕜 n) := (eGroupNorm 𝕜 n).toNormedAddCommGroup

instance : NormedSpace 𝕜 (ESpace 𝕜 n) where
  norm_smul_le c x := le_of_eq (map_smul_eq_mul (sumNorm (𝕜 := 𝕜) n) c x)

instance : FiniteDimensional 𝕜 (ESpace 𝕜 n) :=
  inferInstanceAs (FiniteDimensional 𝕜 (Vec 𝕜 n))

instance : CompleteSpace (ESpace 𝕜 n) := FiniteDimensional.complete 𝕜 (ESpace 𝕜 n)

variable {𝕜 n}

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

private def graphGroupNorm (T : Vec 𝕜 n →ₗ[𝕜] Vec 𝕜 n) : AddGroupNorm (GraphSpace T) where
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

end HilbertUMD
