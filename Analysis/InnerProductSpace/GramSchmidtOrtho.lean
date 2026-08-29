/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gramSchmidt`: the Gram-Schmidt process
- `gramSchmidt_orthogonal`: `gramSchmidt` produces an orthogonal system of vectors.
- `span_gramSchmidt`: `gramSchmidt` preserves span of vectors.
- `gramSchmidt_linearIndependent`: if the input vectors of `gramSchmidt` are linearly independent,
  then so are the output vectors.
- `gramSchmidt_ne_zero`: if the input vectors of `gramSchmidt` are linearly independent,
  then the output vectors are non-zero.
- `gramSchmidtBasis`: the basis produced by the Gram-Schmidt process when given a basis as input
- `gramSchmidtNormed`:
  the normalized `gramSchmidt` process, i.e each vector in `gramSchmidtNormed` has unit length
- `gramSchmidt_orthonormal`: `gramSchmidtNormed` produces an orthonormal system of vectors.
- `gramSchmidtOrthonormalBasis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/

@[expose] public section


open Finset Submodule Module

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace InnerProductSpace

/--
Definition of `gramSchmidt` / `gramSchmidt` 的定义

English:
definition gramSchmidt
  signature: [WellFoundedLT ι] (f : ι -> E) (n : ι)
  body: f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2

中文:
定义 gramSchmidt
  签名: [WellFoundedLT ι] (f : ι -> E) (n : ι)
  定义体: f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2

Depends on / 依赖: decreasing_by, gramSchmidt, mem_Iio, starProjection, termination_by
-/
noncomputable def gramSchmidt [WellFoundedLT ι] (f : ι -> E) (n : ι) : E :=
  f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2

variable [WellFoundedLT ι]

/--
theorem `gramSchmidt_def` / 定理 `gramSchmidt_def`

English:
theorem gramSchmidt_def
  given: (f : ι -> E) (n : ι)
  proof: by
  rw [← sum_attach]; rw [attach_eq_univ]; rw [gramSchmidt]

中文:
定理 gramSchmidt_def
  条件: (f : ι -> E) (n : ι)
  证明: by
  rw [← sum_attach]; rw [attach_eq_univ]; rw [gramSchmidt]

Depends on / 依赖: attach_eq_univ, gramSchmidt, sum_attach
-/
theorem gramSchmidt_def (f : ι -> E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [← sum_attach]; rw [attach_eq_univ]; rw [gramSchmidt]

/--
theorem `gramSchmidt_def'` / 定理 `gramSchmidt_def'`

English:
theorem gramSchmidt_def'
  given: (f : ι -> E) (n : ι)
  proof: by
  rw [gramSchmidt_def]; rw [sub_add_cancel]

中文:
定理 gramSchmidt_def'
  条件: (f : ι -> E) (n : ι)
  证明: by
  rw [gramSchmidt_def]; rw [sub_add_cancel]

Depends on / 依赖: gramSchmidt_def, sub_add_cancel
-/
theorem gramSchmidt_def' (f : ι -> E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [gramSchmidt_def]; rw [sub_add_cancel]

/--
theorem `gramSchmidt_def''` / 定理 `gramSchmidt_def''`

English:
theorem gramSchmidt_def''
  given: (f : ι -> E) (n : ι)
  proof: by
  simp only [← map_pow, ← starProjection_singleton, ← gramSchmidt_def' 𝕜 f n]

@[simp]

中文:
定理 gramSchmidt_def''
  条件: (f : ι -> E) (n : ι)
  证明: by
  simp only [← map_pow, ← starProjection_singleton, ← gramSchmidt_def' 𝕜 f n]

@[simp]

Depends on / 依赖: gramSchmidt_def, map_pow, starProjection_singleton
-/
theorem gramSchmidt_def'' (f : ι -> E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in Iio n,
      (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i := by
  simp only [← map_pow, ← starProjection_singleton, ← gramSchmidt_def' 𝕜 f n]

@[simp]
/--
theorem `gramSchmidt_bot` / 定理 `gramSchmidt_bot`

English:
theorem gramSchmidt_bot
  statement: {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
  proof: by
  rw [gramSchmidt_def]; rw [Iio_eq_Ico]; rw [Finset.Ico_self]; rw [Finset.sum_empty]; rw [sub_zero]

@[simp]

中文:
定理 gramSchmidt_bot
  结论: {ι : 类型} [线性序 ι] [局部有限序 ι] [有底序 ι]
  证明: by
  rw [gramSchmidt_def]; rw [Iio_eq_Ico]; rw [Finset.Ico_self]; rw [Finset.sum_empty]; rw [sub_zero]

@[simp]

Depends on / 依赖: Finset, Finset.Ico_self, Finset.sum_empty, Ico_self, Iio_eq_Ico, gramSchmidt_def, sub_zero, sum_empty
-/
theorem gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [WellFoundedLT ι] (f : ι -> E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gramSchmidt_def]; rw [Iio_eq_Ico]; rw [Finset.Ico_self]; rw [Finset.sum_empty]; rw [sub_zero]

@[simp]
/--
theorem `gramSchmidt_zero` / 定理 `gramSchmidt_zero`

English:
theorem gramSchmidt_zero
  given: (n : ι)
  statement: gramSchmidt 𝕜 (0 : ι -> E) n = 0
  proof: by rw [gramSchmidt_def]; simp

中文:
定理 gramSchmidt_zero
  条件: (n : ι)
  结论: gramSchmidt 𝕜 (0 : ι -> E) n = 0
  证明: by rw [gramSchmidt_def]; simp

Depends on / 依赖: NormedAlgebra, SubalgebraClass, SubalgebraClass.toNormedAlgebra, gramSchmidt_def, toNormedAlgebra
-/
theorem gramSchmidt_zero (n : ι) : gramSchmidt 𝕜 (0 : ι -> E) n = 0 := by rw [gramSchmidt_def]; simp

/--
theorem `gramSchmidt_orthogonal` / 定理 `gramSchmidt_orthogonal`

English:
theorem gramSchmidt_orthogonal
  given: (f : ι -> E) {a b : ι} (h₀ : a != b)
  proof: by
  suffices forall a b : ι, a < b -> ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    rcases h₀.lt_or_gt with ha | hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  intro a b h₀
  revert a
  apply wellFounded_lt.induction b
  intro b ih a h₀
  simp 

中文:
定理 gramSchmidt_orthogonal
  条件: (f : ι -> E) {a b : ι} (h₀ : a != b)
  证明: by
  suffices forall a b : ι, a < b -> ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    rcases h₀.lt_or_gt with ha | hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  intro a b h₀
  revert a
  apply wellFounded_lt.induction b
  intro b ih a h₀
  simp 

Depends on / 依赖: Finset, Finset.mem_Iio.mpr, Finset.sum_eq_single_of_mem, gramSchmidt, gramSchmidt_def, inner_eq_zero_symm, inner_smul_right, inner_sub_right, inner_sum, inner_zero_left, lt_or_gt, mem_Iio, revert, starProjection_singleton, sum_eq_single_of_mem, wellFounded_lt, wellFounded_lt.induction
-/
theorem gramSchmidt_orthogonal (f : ι -> E) {a b : ι} (h₀ : a != b) :
    ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices forall a b : ι, a < b -> ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    rcases h₀.lt_or_gt with ha | hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  intro a b h₀
  revert a
  apply wellFounded_lt.induction b
  intro b ih a h₀
  simp only [gramSchmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    starProjection_singleton, inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h₀)]
  · by_cases h : gramSchmidt 𝕜 f a = 0
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
    · rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K, div_mul_cancel₀, sub_self]
      rwa [inner_self_ne_zero]
  intro i hi hia
  simp only [mul_eq_zero, div_eq_zero_iff]
  right
  rcases hia.lt_or_gt with hia₁ | hia₂
  · rw [inner_eq_zero_symm]
    exact ih a h₀ i hia₁
  · exact ih i (mem_Iio.1 hi) a hia₂

/--
theorem `gramSchmidt_pairwise_orthogonal` / 定理 `gramSchmidt_pairwise_orthogonal`

English:
theorem gramSchmidt_pairwise_orthogonal
  given: (f : ι -> E)
  proof: fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f

中文:
定理 gramSchmidt_pairwise_orthogonal
  条件: (f : ι -> E)
  证明: fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f
-/
theorem gramSchmidt_pairwise_orthogonal (f : ι -> E) :
    Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f

/--
theorem `gramSchmidt_inv_triangular` / 定理 `gramSchmidt_inv_triangular`

English:
theorem gramSchmidt_inv_triangular
  given: (v : ι -> E) {i j : ι} (hij : i < j)
  proof: by
  rw [gramSchmidt_def'' 𝕜 v]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  set b : ι -> E := gramSchmidt 𝕜 v
  convert! zero_add (0 : 𝕜)
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, 

中文:
定理 gramSchmidt_inv_triangular
  条件: (v : ι -> E) {i j : ι} (hij : i < j)
  证明: by
  rw [gramSchmidt_def'' 𝕜 v]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  set b : ι -> E := gramSchmidt 𝕜 v
  convert! zero_add (0 : 𝕜)
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, 

Depends on / 依赖: Finset, Finset.sum_eq_zero, convert, gramSchmidt, gramSchmidt_def, gramSchmidt_orthogonal, hij.ne, hki.trans, inner_add_right, inner_smul_right, inner_sum, sum_eq_zero, zero_add
-/
theorem gramSchmidt_inv_triangular (v : ι -> E) {i j : ι} (hij : i < j) :
    ⟪gramSchmidt 𝕜 v j, v i⟫ = 0 := by
  rw [gramSchmidt_def'' 𝕜 v]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  set b : ι -> E := gramSchmidt 𝕜 v
  convert! zero_add (0 : 𝕜)
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, b k⟫ = 0 := gramSchmidt_orthogonal 𝕜 v (hki.trans hij).ne'
  simp [this]

open Submodule Set Order

/--
theorem `mem_span_gramSchmidt` / 定理 `mem_span_gramSchmidt`

English:
theorem mem_span_gramSchmidt
  given: (f : ι -> E) {i j : ι} (hij : i <= j)
  proof: by
  rw [gramSchmidt_def' 𝕜 f i]
  simp_rw [starProjection_singleton]
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk => smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)) _ <|
subset_span mem_image_of_mem (gramSchmidt 𝕜 f) (Finset.mem_Iio.1 hk).le

中文:
定理 mem_span_gramSchmidt
  条件: (f : ι -> E) {i j : ι} (hij : i <= j)
  证明: by
  rw [gramSchmidt_def' 𝕜 f i]
  simp_rw [starProjection_singleton]
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk => smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)) _ <|
subset_span mem_image_of_mem (gramSchmidt 𝕜 f) (Finset.mem_Iio.1 hk).le

Depends on / 依赖: Finset, Finset.mem_Iio, Set.Iic, Submodule, Submodule.add_mem, Submodule.sum_mem, add_mem, gramSchmidt, gramSchmidt_def, le.trans, mem_Iio, mem_image_of_mem, simp_rw, smul_mem, starProjection_singleton, subset_span, sum_mem
-/
theorem mem_span_gramSchmidt (f : ι -> E) {i j : ι} (hij : i <= j) :
    f i in span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) := by
  rw [gramSchmidt_def' 𝕜 f i]
  simp_rw [starProjection_singleton]
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk => smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)) _ <|
subset_span mem_image_of_mem (gramSchmidt 𝕜 f) (Finset.mem_Iio.1 hk).le.trans hij)

/--
theorem `gramSchmidt_mem_span` / 定理 `gramSchmidt_mem_span`

English:
theorem gramSchmidt_mem_span
  given: (f : ι -> E)
  proof: by
  intro j i hij
  rw [gramSchmidt_def 𝕜 f i]
  simp_rw [starProjection_singleton]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact smul_mem _ _
    (span_mono (image_mono <|

中文:
定理 gramSchmidt_mem_span
  条件: (f : ι -> E)
  证明: by
  intro j i hij
  rw [gramSchmidt_def 𝕜 f i]
  simp_rw [starProjection_singleton]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact smul_mem _ _
    (span_mono (image_mono <|

Depends on / 依赖: Finset, Finset.mem_Iio, Iic_subset_Iic, Set.Iic_subset_Iic, Submodule, Submodule.sub_mem, Submodule.sum_mem, gramSchmidt_def, gramSchmidt_mem_span, hkj.le, image_mono, le_rfl, mem_Iio, mem_image_of_mem, simp_rw, smul_mem, span_mono, starProjection_singleton, sub_mem, subset_span
-/
theorem gramSchmidt_mem_span (f : ι -> E) :
    forall {j i}, i <= j -> gramSchmidt 𝕜 f i in span 𝕜 (f '' Set.Iic j) := by
  intro j i hij
  rw [gramSchmidt_def 𝕜 f i]
  simp_rw [starProjection_singleton]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact smul_mem _ _
    (span_mono (image_mono <| Set.Iic_subset_Iic.2 hkj.le) <| gramSchmidt_mem_span _ le_rfl)
termination_by j => j

/--
theorem `span_gramSchmidt_Iic` / 定理 `span_gramSchmidt_Iic`

English:
theorem span_gramSchmidt_Iic
  given: (f : ι -> E) (c : ι)
  proof: span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _)
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _

中文:
定理 span_gramSchmidt_Iic
  条件: (f : ι -> E) (c : ι)
  证明: span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _)
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _

Depends on / 依赖: Set.image_subset_iff, gramSchmidt_mem_span, image_subset_iff, mem_span_gramSchmidt, span_eq_span
-/
theorem span_gramSchmidt_Iic (f : ι -> E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic c) = span 𝕜 (f '' Set.Iic c) :=
span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _)
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _

/--
theorem `span_gramSchmidt_Iio` / 定理 `span_gramSchmidt_Iio`

English:
theorem span_gramSchmidt_Iio
  given: (f : ι -> E) (c : ι)
  proof: span_eq_span (Set.image_subset_iff.2 fun _ hi =>
span_mono (image_mono <| Iic_subset_Iio.2 hi) gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
span_mono (image_mono <| Iic_subset_Iio.2 hi) mem_span_gramSchmidt _ _ le_rfl

中文:
定理 span_gramSchmidt_Iio
  条件: (f : ι -> E) (c : ι)
  证明: span_eq_span (Set.image_subset_iff.2 fun _ hi =>
span_mono (image_mono <| Iic_subset_Iio.2 hi) gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
span_mono (image_mono <| Iic_subset_Iio.2 hi) mem_span_gramSchmidt _ _ le_rfl

Depends on / 依赖: Iic_subset_Iio, Set.image_subset_iff, gramSchmidt_mem_span, image_mono, image_subset_iff, le_rfl, mem_span_gramSchmidt, span_eq_span, span_mono
-/
theorem span_gramSchmidt_Iio (f : ι -> E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ hi =>
span_mono (image_mono <| Iic_subset_Iio.2 hi) gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
span_mono (image_mono <| Iic_subset_Iio.2 hi) mem_span_gramSchmidt _ _ le_rfl

/--
theorem `span_gramSchmidt` / 定理 `span_gramSchmidt`

English:
theorem span_gramSchmidt
  given: (f : ι -> E)
  statement: span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f)
  proof: span_eq_span (range_subset_iff.2 fun _ =>
span_mono (image_subset_range _ _) gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
span_mono (image_subset_range _ _) mem_span_gramSchmidt _ _ le_rfl

中文:
定理 span_gramSchmidt
  条件: (f : ι -> E)
  结论: span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f)
  证明: span_eq_span (range_subset_iff.2 fun _ =>
span_mono (image_subset_range _ _) gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
span_mono (image_subset_range _ _) mem_span_gramSchmidt _ _ le_rfl

Depends on / 依赖: gramSchmidt_mem_span, image_subset_range, le_rfl, mem_span_gramSchmidt, range_subset_iff, span_eq_span, span_mono
-/
theorem span_gramSchmidt (f : ι -> E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f) :=
  span_eq_span (range_subset_iff.2 fun _ =>
span_mono (image_subset_range _ _) gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
span_mono (image_subset_range _ _) mem_span_gramSchmidt _ _ le_rfl

/--
theorem `gramSchmidt_of_orthogonal` / 定理 `gramSchmidt_of_orthogonal`

English:
theorem gramSchmidt_of_orthogonal
  given: {f : ι -> E} (hf : Pairwise (⟪f ·, f ·⟫ = 0))
  proof: by
  ext i
  rw [gramSchmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_apply]; rw [Submodule.coe_eq_zero]
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjectionOnto_apply_of_mem_orthogonal
      rw [mem_ort

中文:
定理 gramSchmidt_of_orthogonal
  条件: {f : ι -> E} (hf : 两两 (⟪f ·, f ·⟫ = 0))
  证明: by
  ext i
  rw [gramSchmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_apply]; rw [Submodule.coe_eq_zero]
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjectionOnto_apply_of_mem_orthogonal
      rw [mem_ort

Depends on / 依赖: Finset, Finset.mem, Finset.sum_eq_zero, Set.Iic, Submodule, Submodule.coe_eq_zero, Submodule.starProjection_apply, coe_eq_zero, gramSchmidt_def, gramSchmidt_mem_span, isOrtho_span, le_refl, lt_of_le_of_lt, mem_orthogonal_singleton_iff_inner_left, mem_orthogonal_singleton_iff_inner_right, orthogonalProjectionOnto_apply_of_mem_orthogonal, starProjection_apply, sum_eq_zero
-/
theorem gramSchmidt_of_orthogonal {f : ι -> E} (hf : Pairwise (⟪f ·, f ·⟫ = 0)) :
    gramSchmidt 𝕜 f = f := by
  ext i
  rw [gramSchmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_apply]; rw [Submodule.coe_eq_zero]
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjectionOnto_apply_of_mem_orthogonal
      rw [mem_orthogonal_singleton_iff_inner_left]; rw [← mem_orthogonal_singleton_iff_inner_right]
      exact this (gramSchmidt_mem_span 𝕜 f (le_refl j))
    rw [isOrtho_span]
    rintro u ⟨k, hk, rfl⟩ v (rfl : v = f i)
    apply hf
    exact (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj)).ne
  · simp

variable {𝕜}

/--
theorem `gramSchmidt_ne_zero_coe` / 定理 `gramSchmidt_ne_zero_coe`

English:
theorem gramSchmidt_ne_zero_coe
  statement: {f : ι -> E} (n : ι)
  proof: by
  by_contra h
  have h₁ : f n in span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n]; rw [gramSchmidt_def' 𝕜 f]; rw [h]; rw [zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    simp only [starProjection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio]

中文:
定理 gramSchmidt_ne_zero_coe
  结论: {f : ι -> E} (n : ι)
  证明: by
  by_contra h
  have h₁ : f n in span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n]; rw [gramSchmidt_def' 𝕜 f]; rw [h]; rw [zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    simp only [starProjection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio]

Depends on / 依赖: Finset, Finset.mem_Iio, LinearIndependent, LinearIndependent.notMem_, Set.Iic, Set.Iio, Submodule, Submodule.smul_mem, Submodule.sum_mem, gramSchmidt_def, image_comp, le_refl, mem_Iio, notMem_, smul_mem, span_gramSchmidt_Iio, starProjection_singleton, subset_span, sum_mem, zero_add
-/
theorem gramSchmidt_ne_zero_coe {f : ι -> E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))) : gramSchmidt 𝕜 f n != 0 := by
  by_contra h
  have h₁ : f n in span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n]; rw [gramSchmidt_def' 𝕜 f]; rw [h]; rw [zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    simp only [starProjection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    exact subset_span ⟨a, ha, by rfl⟩
  have h₂ : (f ∘ ((↑) : Set.Iic n -> ι)) ⟨n, le_refl n⟩ in
      span 𝕜 (f ∘ ((↑) : Set.Iic n -> ι) '' Set.Iio ⟨n, le_refl n⟩) := by
    rw [image_comp]
    simpa using h₁
  apply LinearIndependent.notMem_span_image h₀ _ h₂
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]

/--
theorem `gramSchmidt_ne_zero` / 定理 `gramSchmidt_ne_zero`

English:
theorem gramSchmidt_ne_zero
  given: {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f)
  proof: gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

中文:
定理 gramSchmidt_ne_zero
  条件: {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f)
  证明: gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

Depends on / 依赖: LinearIndependent, LinearIndependent.comp, Subtype, Subtype.coe_injective, coe_injective, gramSchmidt_ne_zero_coe
-/
theorem gramSchmidt_ne_zero {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    gramSchmidt 𝕜 f n != 0 :=
  gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/--
theorem `gramSchmidt_triangular` / 定理 `gramSchmidt_triangular`

English:
theorem gramSchmidt_triangular
  given: {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E)
  proof: by
  have : gramSchmidt 𝕜 b i in span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i in span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support subseteq Set.Iio j :=
    Ba

中文:
定理 gramSchmidt_triangular
  条件: {i j : ι} (hij : i < j) (b : 基 ι 𝕜 E)
  证明: by
  have : gramSchmidt 𝕜 b i in span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i in span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support subseteq Set.Iio j :=
    Ba

Depends on / 依赖: Basis.repr_support_subset_of_mem_span, Finsupp, Finsupp.mem_supported, Set.Iio, Set.mem_image, Set.self_notMem_Iio, b.repr, gramSchmidt, mem_image, mem_supported, repr_support_subset_of_mem_span, self_notMem_Iio, span_gramSchmidt_Iio, subset_span, subseteq, support
-/
theorem gramSchmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) :
    b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i in span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i in span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support subseteq Set.Iio j :=
    Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j Set.self_notMem_Iio

/--
theorem `gramSchmidt_linearIndependent` / 定理 `gramSchmidt_linearIndependent`

English:
theorem gramSchmidt_linearIndependent
  given: {f : ι -> E} (h₀ : LinearIndependent 𝕜 f)
  proof: linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f

中文:
定理 gramSchmidt_linearIndependent
  条件: {f : ι -> E} (h₀ : LinearIndependent 𝕜 f)
  证明: linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f

Depends on / 依赖: gramSchmidt_ne_zero, gramSchmidt_orthogonal, linearIndependent_of_ne_zero_of_inner_eq_zero
-/
theorem gramSchmidt_linearIndependent {f : ι -> E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f

/--
Definition of `gramSchmidtBasis` / `gramSchmidtBasis` 的定义

English:
definition gramSchmidtBasis
  signature: (b : Basis ι 𝕜 E)
  body: Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge

中文:
定义 gramSchmidtBasis
  签名: (b : 基 ι 𝕜 E)
  定义体: Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge

Depends on / 依赖: Basis.mk, b.linearIndependent, b.span_eq, gramSchmidt_linearIndependent, linearIndependent, span_eq, span_gramSchmidt
-/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge

/--
theorem `coe_gramSchmidtBasis` / 定理 `coe_gramSchmidtBasis`

English:
theorem coe_gramSchmidtBasis
  given: (b : Basis ι 𝕜 E)
  statement: (gramSchmidtBasis b : ι -> E) = gramSchmidt 𝕜 b
  proof: Basis.coe_mk _ _

中文:
定理 coe_gramSchmidtBasis
  条件: (b : 基 ι 𝕜 E)
  结论: (gramSchmidtBasis b : ι -> E) = gramSchmidt 𝕜 b
  证明: Basis.coe_mk _ _

Depends on / 依赖: Basis.coe_mk, coe_mk
-/
theorem coe_gramSchmidtBasis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι -> E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _

variable (𝕜) in
/--
Definition of `gramSchmidtNormed` / `gramSchmidtNormed` 的定义

English:
definition gramSchmidtNormed
  signature: (f : ι -> E) (n : ι)
  body: (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

中文:
定义 gramSchmidtNormed
  签名: (f : ι -> E) (n : ι)
  定义体: (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

Depends on / 依赖: gramSchmidt
-/
noncomputable def gramSchmidtNormed (f : ι -> E) (n : ι) : E :=
  (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

/--
theorem `gramSchmidtNormed_unit_length_coe` / 定理 `gramSchmidtNormed_unit_length_coe`

English:
theorem gramSchmidtNormed_unit_length_coe
  statement: {f : ι -> E} (n : ι)
  proof: by
  simp only [gramSchmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne,
    not_false_iff]

中文:
定理 gramSchmidtNormed_unit_length_coe
  结论: {f : ι -> E} (n : ι)
  证明: by
  simp only [gramSchmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne,
    not_false_iff]

Depends on / 依赖: gramSchmidtNormed, gramSchmidt_ne_zero_coe, norm_smul_inv_norm, not_false_iff
-/
theorem gramSchmidtNormed_unit_length_coe {f : ι -> E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))) : ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  simp only [gramSchmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne,
    not_false_iff]

/--
theorem `gramSchmidtNormed_unit_length` / 定理 `gramSchmidtNormed_unit_length`

English:
theorem gramSchmidtNormed_unit_length
  given: {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f)
  proof: gramSchmidtNormed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

中文:
定理 gramSchmidtNormed_unit_length
  条件: {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f)
  证明: gramSchmidtNormed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

Depends on / 依赖: LinearIndependent, LinearIndependent.comp, Subtype, Subtype.coe_injective, coe_injective, gramSchmidtNormed_unit_length_coe
-/
theorem gramSchmidtNormed_unit_length {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 :=
  gramSchmidtNormed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/--
theorem `gramSchmidtNormed_unit_length'` / 定理 `gramSchmidtNormed_unit_length'`

English:
theorem gramSchmidtNormed_unit_length'
  given: {f : ι -> E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n != 0)
  proof: by
  rw [gramSchmidtNormed] at *
  rw [norm_smul_inv_norm]
  simpa using hn

中文:
定理 gramSchmidtNormed_unit_length'
  条件: {f : ι -> E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n != 0)
  证明: by
  rw [gramSchmidtNormed] at *
  rw [norm_smul_inv_norm]
  simpa using hn

Depends on / 依赖: gramSchmidtNormed, norm_smul_inv_norm
-/
theorem gramSchmidtNormed_unit_length' {f : ι -> E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n != 0) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  rw [gramSchmidtNormed] at *
  rw [norm_smul_inv_norm]
  simpa using hn

/--
theorem `gramSchmidtNormed_orthonormal` / 定理 `gramSchmidtNormed_orthonormal`

English:
theorem gramSchmidtNormed_orthonormal
  given: {f : ι -> E} (h₀ : LinearIndependent 𝕜 f)
  proof: by
  unfold Orthonormal
  constructor
  · simp only [gramSchmidtNormed_unit_length, h₀, imp_true_iff]
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, RCLike.conj_inv,
      RCLike.conj_ofReal, mul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero]
    r

中文:
定理 gramSchmidtNormed_orthonormal
  条件: {f : ι -> E} (h₀ : LinearIndependent 𝕜 f)
  证明: by
  unfold Orthonormal
  constructor
  · simp only [gramSchmidtNormed_unit_length, h₀, imp_true_iff]
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, RCLike.conj_inv,
      RCLike.conj_ofReal, mul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero]
    r

Depends on / 依赖: Orthonormal, RCLike, RCLike.conj_inv, RCLike.conj_ofReal, RCLike.ofReal_eq_zero, conj_inv, conj_ofReal, gramSchmidtNormed, gramSchmidtNormed_unit_length, gramSchmidt_orthogonal, imp_true_iff, inner_smul_left, inner_smul_right, inv_eq_zero, mul_eq_zero, norm_eq_zero, ofReal_eq_zero, repeat
-/
theorem gramSchmidtNormed_orthonormal {f : ι -> E} (h₀ : LinearIndependent 𝕜 f) :
    Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [gramSchmidtNormed_unit_length, h₀, imp_true_iff]
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, RCLike.conj_inv,
      RCLike.conj_ofReal, mul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero]
    repeat' right
    exact gramSchmidt_orthogonal 𝕜 f hij

/--
theorem `gramSchmidtNormed_orthonormal'` / 定理 `gramSchmidtNormed_orthonormal'`

English:
theorem gramSchmidtNormed_orthonormal'
  given: (f : ι -> E)
  proof: by
  refine ⟨fun i => gramSchmidtNormed_unit_length' i.prop, ?_⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]

中文:
定理 gramSchmidtNormed_orthonormal'
  条件: (f : ι -> E)
  证明: by
  refine ⟨fun i => gramSchmidtNormed_unit_length' i.prop, ?_⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, gramSchmidtNormed, gramSchmidtNormed_unit_length, gramSchmidt_orthogonal, i.prop, inner_smul_left, inner_smul_right
-/
theorem gramSchmidtNormed_orthonormal' (f : ι -> E) :
    Orthonormal 𝕜 fun i : { i | gramSchmidtNormed 𝕜 f i != 0 } => gramSchmidtNormed 𝕜 f i := by
  refine ⟨fun i => gramSchmidtNormed_unit_length' i.prop, ?_⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]

open Submodule Set Order

/--
theorem `span_gramSchmidtNormed` / 定理 `span_gramSchmidtNormed`

English:
theorem span_gramSchmidtNormed
  given: (f : ι -> E) (s : Set ι)
  proof: by
  refine span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi =>
      span_mono (image_mono <| singleton_subset_set_iff.2 hi) ?_)
  simp only [coe_singleton, Set.image_singleton]
  by_cases h : gramSchmidt

中文:
定理 span_gramSchmidtNormed
  条件: (f : ι -> E) (s : 集合 ι)
  证明: by
  refine span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi =>
      span_mono (image_mono <| singleton_subset_set_iff.2 hi) ?_)
  simp only [coe_singleton, Set.image_singleton]
  by_cases h : gramSchmidt

Depends on / 依赖: Set.image_singleton, Set.image_subset_iff, coe_singleton, gramSchmidt, image_mono, image_singleton, image_subset_iff, mem_image_of_mem, mem_span_singleton, mod_cast, norm_ne_zero_iff, singleton_subset_set_iff, smul_mem, span_eq_span, span_mono, subset_span
-/
theorem span_gramSchmidtNormed (f : ι -> E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi =>
      span_mono (image_mono <| singleton_subset_set_iff.2 hi) ?_)
  simp only [coe_singleton, Set.image_singleton]
  by_cases h : gramSchmidt 𝕜 f i = 0
  · simp [h]
  · refine mem_span_singleton.2 ⟨‖gramSchmidt 𝕜 f i‖, smul_inv_smul₀ ?_ _⟩
    exact mod_cast norm_ne_zero_iff.2 h

/--
theorem `span_gramSchmidtNormed_range` / 定理 `span_gramSchmidtNormed_range`

English:
theorem span_gramSchmidtNormed_range
  given: (f : ι -> E)
  proof: by
  simpa only [image_univ.symm] using span_gramSchmidtNormed f univ

中文:
定理 span_gramSchmidtNormed_range
  条件: (f : ι -> E)
  证明: by
  simpa only [image_univ.symm] using span_gramSchmidtNormed f univ

Depends on / 依赖: image_univ, image_univ.symm, span_gramSchmidtNormed
-/
theorem span_gramSchmidtNormed_range (f : ι -> E) :
    span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f)) := by
  simpa only [image_univ.symm] using span_gramSchmidtNormed f univ

/--
theorem `gramSchmidtNormed_linearIndependent` / 定理 `gramSchmidtNormed_linearIndependent`

English:
theorem gramSchmidtNormed_linearIndependent
  given: {f : ι -> E} (h₀ : LinearIndependent 𝕜 f)
  proof: by
  unfold gramSchmidtNormed
  have (i : ι) : IsUnit (‖gramSchmidt 𝕜 f i‖⁻¹ : 𝕜) :=
    isUnit_iff_ne_zero.mpr (by simp [gramSchmidt_ne_zero i h₀])
  let w : ι -> 𝕜ˣ := fun i => (this i).unit
  apply (gramSchmidt_linearIndependent h₀).units_smul (w := fun i => (this i).unit)

中文:
定理 gramSchmidtNormed_linearIndependent
  条件: {f : ι -> E} (h₀ : LinearIndependent 𝕜 f)
  证明: by
  unfold gramSchmidtNormed
  have (i : ι) : IsUnit (‖gramSchmidt 𝕜 f i‖⁻¹ : 𝕜) :=
    isUnit_iff_ne_zero.mpr (by simp [gramSchmidt_ne_zero i h₀])
  let w : ι -> 𝕜ˣ := fun i => (this i).unit
  apply (gramSchmidt_linearIndependent h₀).units_smul (w := fun i => (this i).unit)

Depends on / 依赖: IsUnit, gramSchmidt, gramSchmidtNormed, gramSchmidt_linearIndependent, gramSchmidt_ne_zero, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, units_smul
-/
theorem gramSchmidtNormed_linearIndependent {f : ι -> E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold gramSchmidtNormed
  have (i : ι) : IsUnit (‖gramSchmidt 𝕜 f i‖⁻¹ : 𝕜) :=
    isUnit_iff_ne_zero.mpr (by simp [gramSchmidt_ne_zero i h₀])
  let w : ι -> 𝕜ˣ := fun i => (this i).unit
  apply (gramSchmidt_linearIndependent h₀).units_smul (w := fun i => (this i).unit)

section OrthonormalBasis

variable [Fintype ι] [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = Fintype.card ι) (f : ι -> E)

/--
Definition of `gramSchmidtOrthonormalBasis` / `gramSchmidtOrthonormalBasis` 的定义

English:
definition gramSchmidtOrthonormalBasis
  signature: : OrthonormalBasis ι 𝕜 E
  body: ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose

中文:
定义 gramSchmidtOrthonormalBasis
  签名: : 正交标准基 ι 𝕜 E
  定义体: ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose

Depends on / 依赖: exists_orthonormalBasis_extension_of_card_eq, gramSchmidtNormed, gramSchmidtNormed_orthonormal
-/
noncomputable def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose

/--
theorem `gramSchmidtOrthonormalBasis_apply` / 定理 `gramSchmidtOrthonormalBasis_apply`

English:
theorem gramSchmidtOrthonormalBasis_apply
  given: {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i != 0)
  proof: ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose_spec i hi

中文:
定理 gramSchmidtOrthonormalBasis_apply
  条件: {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i != 0)
  证明: ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose_spec i hi

Depends on / 依赖: choose_spec, exists_orthonormalBasis_extension_of_card_eq, gramSchmidtNormed, gramSchmidtNormed_orthonormal
-/
theorem gramSchmidtOrthonormalBasis_apply {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i != 0) :
    gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f i :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose_spec i hi

/--
theorem `gramSchmidtOrthonormalBasis_apply_of_orthogonal` / 定理 `gramSchmidtOrthonormalBasis_apply_of_orthogonal`

English:
theorem gramSchmidtOrthonormalBasis_apply_of_orthogonal
  statement: {f : ι -> E}
  proof: by
  have H : gramSchmidtNormed 𝕜 f i = (‖f i‖⁻¹ : 𝕜) • f i := by
    rw [gramSchmidtNormed]; rw [gramSchmidt_of_orthogonal 𝕜 hf]
  rw [gramSchmidtOrthonormalBasis_apply h]; rw [H]
  simpa [H] using hi

中文:
定理 gramSchmidtOrthonormalBasis_apply_of_orthogonal
  结论: {f : ι -> E}
  证明: by
  have H : gramSchmidtNormed 𝕜 f i = (‖f i‖⁻¹ : 𝕜) • f i := by
    rw [gramSchmidtNormed]; rw [gramSchmidt_of_orthogonal 𝕜 hf]
  rw [gramSchmidtOrthonormalBasis_apply h]; rw [H]
  simpa [H] using hi

Depends on / 依赖: gramSchmidtNormed, gramSchmidtOrthonormalBasis_apply, gramSchmidt_of_orthogonal
-/
theorem gramSchmidtOrthonormalBasis_apply_of_orthogonal {f : ι -> E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) {i : ι} (hi : f i != 0) :
    gramSchmidtOrthonormalBasis h f i = (‖f i‖⁻¹ : 𝕜) • f i := by
  have H : gramSchmidtNormed 𝕜 f i = (‖f i‖⁻¹ : 𝕜) • f i := by
    rw [gramSchmidtNormed]; rw [gramSchmidt_of_orthogonal 𝕜 hf]
  rw [gramSchmidtOrthonormalBasis_apply h]; rw [H]
  simpa [H] using hi

/--
theorem `inner_gramSchmidtOrthonormalBasis_eq_zero` / 定理 `inner_gramSchmidtOrthonormalBasis_eq_zero`

English:
theorem inner_gramSchmidtOrthonormalBasis_eq_zero
  statement: {f : ι -> E} {i : ι}
  proof: by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i by
    apply this
    rw [span_gramSchmidtNormed]
    exact mem_span_gramSchmidt 𝕜 f le_rfl
  rw [isOrtho_span]
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
 

中文:
定理 inner_gramSchmidtOrthonormalBasis_eq_zero
  结论: {f : ι -> E} {i : ι}
  证明: by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i by
    apply this
    rw [span_gramSchmidtNormed]
    exact mem_span_gramSchmidt 𝕜 f le_rfl
  rw [isOrtho_span]
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
 

Depends on / 依赖: Set.Iic, gramSchmidtNormed, gramSchmidtOrthonormalBasis, gramSchmidtOrthonormalBasis_apply, inner_zero_left, isOrtho_span, le_rfl, mem_orthogonal_singleton_iff_inner_right, mem_span_gramSchmidt, orthonormal, span_gramSchmidtNormed
-/
theorem inner_gramSchmidtOrthonormalBasis_eq_zero {f : ι -> E} {i : ι}
    (hi : gramSchmidtNormed 𝕜 f i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0 := by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i by
    apply this
    rw [span_gramSchmidtNormed]
    exact mem_span_gramSchmidt 𝕜 f le_rfl
  rw [isOrtho_span]
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
  by_cases hk : gramSchmidtNormed 𝕜 f k = 0
  · rw [hk, inner_zero_left]
  rw [← gramSchmidtOrthonormalBasis_apply h hk]
  have : k != i := by
    rintro rfl
    exact hk hi
  exact (gramSchmidtOrthonormalBasis h f).orthonormal.2 this

/--
theorem `gramSchmidtOrthonormalBasis_inv_triangular` / 定理 `gramSchmidtOrthonormalBasis_inv_triangular`

English:
theorem gramSchmidtOrthonormalBasis_inv_triangular
  given: {i j : ι} (hij : i < j)
  proof: by
  by_cases hi : gramSchmidtNormed 𝕜 f j = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]

中文:
定理 gramSchmidtOrthonormalBasis_inv_triangular
  条件: {i j : ι} (hij : i < j)
  证明: by
  by_cases hi : gramSchmidtNormed 𝕜 f j = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]

Depends on / 依赖: gramSchmidtNormed, gramSchmidtOrthonormalBasis_apply, gramSchmidt_inv_triangular, inner_gramSchmidtOrthonormalBasis_eq_zero, inner_smul_left
-/
theorem gramSchmidtOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) :
    ⟪gramSchmidtOrthonormalBasis h f j, f i⟫ = 0 := by
  by_cases hi : gramSchmidtNormed 𝕜 f j = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]

/--
theorem `gramSchmidtOrthonormalBasis_inv_triangular'` / 定理 `gramSchmidtOrthonormalBasis_inv_triangular'`

English:
theorem gramSchmidtOrthonormalBasis_inv_triangular'
  given: {i j : ι} (hij : i < j)
  proof: by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij

中文:
定理 gramSchmidtOrthonormalBasis_inv_triangular'
  条件: {i j : ι} (hij : i < j)
  证明: by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.repr_apply_apply, gramSchmidtOrthonormalBasis_inv_triangular, repr_apply_apply
-/
theorem gramSchmidtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) :
    (gramSchmidtOrthonormalBasis h f).repr (f i) j = 0 := by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij

/--
theorem `gramSchmidtOrthonormalBasis_inv_isUpperTriangular` / 定理 `gramSchmidtOrthonormalBasis_inv_isUpperTriangular`

English:
theorem gramSchmidtOrthonormalBasis_inv_isUpperTriangular
  proof: fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f

@[deprecated (since := "2026-07-30")]
alias gramSchmidtOrthonormalBasis_inv_blockTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular

中文:
定理 gramSchmidtOrthonormalBasis_inv_isUpperTriangular
  证明: fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f

@[deprecated (since := "2026-07-30")]
alias gramSchmidtOrthonormalBasis_inv_blockTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular
-/
theorem gramSchmidtOrthonormalBasis_inv_isUpperTriangular :
    ((gramSchmidtOrthonormalBasis h f).toBasis.toMatrix f).IsUpperTriangular := fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f

@[deprecated (since := "2026-07-30")]
alias gramSchmidtOrthonormalBasis_inv_blockTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular

/--
theorem `gramSchmidtOrthonormalBasis_det` / 定理 `gramSchmidtOrthonormalBasis_det`

English:
theorem gramSchmidtOrthonormalBasis_det
  given: [DecidableEq ι]
  proof: by
  convert! Matrix.det_of_isUpperTriangular (gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f)
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm

中文:
定理 gramSchmidtOrthonormalBasis_det
  条件: [DecidableEq ι]
  证明: by
  convert! Matrix.det_of_isUpperTriangular (gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f)
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm

Depends on / 依赖: Matrix, Matrix.det_of_isUpperTriangular, convert, det_of_isUpperTriangular, gramSchmidtOrthonormalBasis, gramSchmidtOrthonormalBasis_inv_isUpperTriangular, repr_apply_apply
-/
theorem gramSchmidtOrthonormalBasis_det [DecidableEq ι] :
    (gramSchmidtOrthonormalBasis h f).toBasis.det f =
      ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫ := by
  convert! Matrix.det_of_isUpperTriangular (gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f)
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm

end OrthonormalBasis

end InnerProductSpace
