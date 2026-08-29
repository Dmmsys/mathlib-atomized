/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Whitney embedding theorem

In this file we prove a version of the Whitney embedding theorem: for any compact real manifold `M`,
for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.

## TODO

* Prove the weak Whitney embedding theorem: any `σ`-compact smooth `m`-dimensional manifold can be
  embedded into `ℝ^(2m+1)`. This requires a version of Sard's theorem: for a locally Lipschitz
  continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`, hence it
  has measure zero.

## Tags

partition of unity, smooth bump function, whitney theorem
-/

universe uι uE uH uM

open Function Filter Module Set Topology
open scoped Manifold ContDiff

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

namespace SmoothBumpCovering

/-!
### Whitney embedding theorem

In this section we prove a version of the Whitney embedding theorem: for any compact real manifold
`M`, for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.
-/

variable [T2Space M] [Fintype ι] {s : Set M} (f : SmoothBumpCovering ι I M s)

/--
Definition of `embeddingPiTangent` / `embeddingPiTangent` 的定义

English:
definition embeddingPiTangent
  signature: : C^∞⟮I, M; 𝓘(Real, ι -> E × Real), ι -> E × Real⟯ where
  body: (f i x • extChartAt I (f.c i) x, f i x)
  property :=
    contMDiff_pi_space.2 fun i =>
      ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

@[local simp]

中文:
定义 embeddingPiTangent
  签名: : C^∞⟮I, M; 𝓘(实数, ι -> E × 实数), ι -> E × 实数⟯ where
  定义体: (f i x • extChartAt I (f.c i) x, f i x)
  property :=
    contMDiff_pi_space.2 fun i =>
      ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

@[local simp]

Depends on / 依赖: extChartAt
-/
def embeddingPiTangent : C^∞⟮I, M; 𝓘(Real, ι -> E × Real), ι -> E × Real⟯ where
  val x i := (f i x • extChartAt I (f.c i) x, f i x)
  property :=
    contMDiff_pi_space.2 fun i =>
      ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

@[local simp]
/--
theorem `embeddingPiTangent_coe` / 定理 `embeddingPiTangent_coe`

English:
theorem embeddingPiTangent_coe
  proof: (rfl)

中文:
定理 embeddingPiTangent_coe
  证明: (rfl)
-/
theorem embeddingPiTangent_coe :
    ⇑f.embeddingPiTangent = fun x i => (f i x • extChartAt I (f.c i) x, f i x) :=
  (rfl)

/--
theorem `embeddingPiTangent_injOn` / 定理 `embeddingPiTangent_injOn`

English:
theorem embeddingPiTangent_injOn
  statement: InjOn f.embeddingPiTangent s
  proof: by
  intro x hx y _ h
  simp only [embeddingPiTangent_coe, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂]; rw [f.apply_ind x hx]; rw [one_smul]; rw [one_smul] at h₁
  have := f.mem_extChartAt_source_of_eq_one h₂.symm
  exact (extChartAt

中文:
定理 embeddingPiTangent_injOn
  结论: InjOn f.embeddingPiTangent s
  证明: by
  intro x hx y _ h
  simp only [embeddingPiTangent_coe, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂]; rw [f.apply_ind x hx]; rw [one_smul]; rw [one_smul] at h₁
  have := f.mem_extChartAt_source_of_eq_one h₂.symm
  exact (extChartAt

Depends on / 依赖: Prod.mk_inj, apply_ind, embeddingPiTangent_coe, extChartAt, f.apply_ind, f.ind, f.mem_extChartAt_ind_source, f.mem_extChartAt_source_of_eq_one, funext_iff, mem_extChartAt_ind_source, mem_extChartAt_source_of_eq_one, mk_inj, one_smul
-/
theorem embeddingPiTangent_injOn : InjOn f.embeddingPiTangent s := by
  intro x hx y _ h
  simp only [embeddingPiTangent_coe, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂]; rw [f.apply_ind x hx]; rw [one_smul]; rw [one_smul] at h₁
  have := f.mem_extChartAt_source_of_eq_one h₂.symm
  exact (extChartAt I (f.c _)).injOn (f.mem_extChartAt_ind_source x hx) this h₁

/--
theorem `embeddingPiTangent_injective` / 定理 `embeddingPiTangent_injective`

English:
theorem embeddingPiTangent_injective
  given: (f : SmoothBumpCovering ι I M)
  proof: injOn_univ.1 f.embeddingPiTangent_injOn

中文:
定理 embeddingPiTangent_injective
  条件: (f : SmoothBumpCovering ι I M)
  证明: injOn_univ.1 f.embeddingPiTangent_injOn

Depends on / 依赖: embeddingPiTangent_injOn, f.embeddingPiTangent_injOn, injOn_univ
-/
theorem embeddingPiTangent_injective (f : SmoothBumpCovering ι I M) :
    Injective f.embeddingPiTangent :=
  injOn_univ.1 f.embeddingPiTangent_injOn

/--
theorem `comp_embeddingPiTangent_mfderiv` / 定理 `comp_embeddingPiTangent_mfderiv`

English:
theorem comp_embeddingPiTangent_mfderiv
  given: (x : M) (hx : x in s)
  proof: by
  set L :=
    (ContinuousLinearMap.fst Real E Real).comp
      (@ContinuousLinearMap.proj Real _ ι (fun _ => E × Real) _ _ (fun _ => inferInstance) (f.ind x hx))
  have := L.hasMFDerivAt.comp x
    (f.embeddingPiTangent.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  convert! hasMFDerivAt_

中文:
定理 comp_embeddingPiTangent_mfderiv
  条件: (x : M) (hx : x in s)
  证明: by
  set L :=
    (ContinuousLinearMap.fst Real E Real).comp
      (@ContinuousLinearMap.proj Real _ ι (fun _ => E × Real) _ _ (fun _ => inferInstance) (f.ind x hx))
  have := L.hasMFDerivAt.comp x
    (f.embeddingPiTangent.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  convert! hasMFDerivAt_

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_c, ContinuousLinearMap.fst, ContinuousLinearMap.proj, L.hasMFDerivAt.comp, coe_c, congr_of_eventuallyEq, contMDiff, convert, embeddingPiTangent, embeddingPiTangent_coe, eventuallyEq_one, f.embeddingPiTangent.contMDiff.mdifferentiableAt, f.eventuallyEq_one, f.ind, f.mem_chartAt_ind_source, hasMFDerivAt, hasMFDerivAt_extChartAt, hasMFDerivAt_unique, mdifferentiableAt
-/
theorem comp_embeddingPiTangent_mfderiv (x : M) (hx : x in s) :
    ((ContinuousLinearMap.fst Real E Real).comp
            (@ContinuousLinearMap.proj Real _ ι (fun _ => E × Real) _ _ (fun _ => inferInstance)
              (f.ind x hx))).comp
        (mfderiv I 𝓘(Real, ι -> E × Real) f.embeddingPiTangent x) =
      mfderiv% (chartAt H (f.c (f.ind x hx))) x := by
  set L :=
    (ContinuousLinearMap.fst Real E Real).comp
      (@ContinuousLinearMap.proj Real _ ι (fun _ => E × Real) _ _ (fun _ => inferInstance) (f.ind x hx))
  have := L.hasMFDerivAt.comp x
    (f.embeddingPiTangent.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  convert! hasMFDerivAt_unique this _
  refine (hasMFDerivAt_extChartAt (f.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq ?_
  refine (f.eventuallyEq_one x hx).mono fun y hy => ?_
  simp only [L, embeddingPiTangent_coe, ContinuousLinearMap.coe_comp, (· ∘ ·),
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]
  rw [hy]; rw [Pi.one_apply]; rw [one_smul]

/--
theorem `embeddingPiTangent_ker_mfderiv` / 定理 `embeddingPiTangent_ker_mfderiv`

English:
theorem embeddingPiTangent_ker_mfderiv
  given: (x : M) (hx : x in s)
  proof: by
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
      (f.mem_chartAt_ind_source x hx)]; rw [← comp_embeddingPiTangent_mfderiv]
  exact LinearMap.ker_le_ker_comp _ _

中文:
定理 embeddingPiTangent_ker_mfderiv
  条件: (x : M) (hx : x in s)
  证明: by
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
      (f.mem_chartAt_ind_source x hx)]; rw [← comp_embeddingPiTangent_mfderiv]
  exact LinearMap.ker_le_ker_comp _ _

Depends on / 依赖: LinearMap, LinearMap.ker_le_ker_comp, bot_unique, comp_embeddingPiTangent_mfderiv, f.ind, f.mem_chartAt_ind_source, ker_le_ker_comp, ker_mfderiv_eq_bot, mdifferentiable_chart, mem_chartAt_ind_source
-/
theorem embeddingPiTangent_ker_mfderiv (x : M) (hx : x in s) :
    (mfderiv I 𝓘(Real, ι -> E × Real) f.embeddingPiTangent x).ker = ⊥ := by
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
      (f.mem_chartAt_ind_source x hx)]; rw [← comp_embeddingPiTangent_mfderiv]
  exact LinearMap.ker_le_ker_comp _ _

/--
theorem `embeddingPiTangent_injective_mfderiv` / 定理 `embeddingPiTangent_injective_mfderiv`

English:
theorem embeddingPiTangent_injective_mfderiv
  given: (x : M) (hx : x in s)
  proof: LinearMap.ker_eq_bot.1 (f.embeddingPiTangent_ker_mfderiv x hx)

中文:
定理 embeddingPiTangent_injective_mfderiv
  条件: (x : M) (hx : x in s)
  证明: LinearMap.ker_eq_bot.1 (f.embeddingPiTangent_ker_mfderiv x hx)

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, embeddingPiTangent_ker_mfderiv, f.embeddingPiTangent_ker_mfderiv, ker_eq_bot
-/
theorem embeddingPiTangent_injective_mfderiv (x : M) (hx : x in s) :
    Injective (mfderiv I 𝓘(Real, ι -> E × Real) f.embeddingPiTangent x) :=
  LinearMap.ker_eq_bot.1 (f.embeddingPiTangent_ker_mfderiv x hx)

/-- Baby version of the **Whitney weak embedding theorem**: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be immersed into the `n`-dimensional
Euclidean space. -/
public theorem exists_immersion_euclidean {ι : Type*} [Finite ι] (f : SmoothBumpCovering ι I M) :
    exists (n : Nat) (e : M -> EuclideanSpace Real (Fin n)),
      CMDiff ∞ e ∧ Injective e ∧ forall x : M, Injective (mfderiv% e x) := by
  cases nonempty_fintype ι
  set F := EuclideanSpace Real (Fin <| finrank Real (ι -> E × Real))
  let : IsNoetherian Real (E × Real) := IsNoetherian.iff_fg.2 inferInstance
  let : FiniteDimensional Real (ι -> E × Real) := IsNoetherian.iff_fg.1 inferInstance
  set eEF : (ι -> E × Real) ≃L[Real] F :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  refine ⟨_, eEF ∘ f.embeddingPiTangent,
    eEF.toDiffeomorph.contMDiff.comp f.embeddingPiTangent.contMDiff,
    eEF.injective.comp f.embeddingPiTangent_injective, fun x => ?_⟩
  rw [mfderiv_comp _ eEF.differentiableAt.mdifferentiableAt
      (f.embeddingPiTangent.contMDiff.mdifferentiableAt (by simp))]; rw [eEF.mfderiv_eq]
  exact eEF.injective.comp (f.embeddingPiTangent_injective_mfderiv _ trivial)

end SmoothBumpCovering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
public theorem exists_embedding_euclidean_of_compact [T2Space M] [CompactSpace M] :
    exists (n : Nat) (e : M -> EuclideanSpace Real (Fin n)),
      CMDiff ∞ e ∧ IsClosedEmbedding e ∧ forall x : M, Injective (mfderiv% e x) := by
  rcases SmoothBumpCovering.exists_isSubordinate I isClosed_univ fun (x : M) _ => univ_mem with
    ⟨ι, f, -⟩
  have := f.fintype
  rcases f.exists_immersion_euclidean with ⟨n, e, hsmooth, hinj, hinj_mfderiv⟩
  exact ⟨n, e, hsmooth, hsmooth.continuous.isClosedEmbedding hinj, hinj_mfderiv⟩
