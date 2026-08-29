/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuity of inner product

We show that the inner product is continuous, `continuous_inner`.

## Tags

inner product space, Hilbert space, norm

-/

public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap renaming BilinForm -> BilinForm

variable {𝕜 E F : Type*} [RCLike 𝕜]


section Continuous

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-!
### Continuity of the inner product
-/

/--
theorem `_root_.isBoundedBilinearMap_inner` / 定理 `_root_.isBoundedBilinearMap_inner`

English:
theorem _root_.isBoundedBilinearMap_inner
  given: [NormedSpace Real E] [IsScalarTower Real 𝕜 E]
  proof: { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebraMap_eq_ofReal, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebraMap_eq_ofReal, inner_smul_real_right

中文:
定理 _root_.isBoundedBilinearMap_inner
  条件: [赋范空间 实数 E] [标量塔 实数 𝕜 E]
  证明: { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebraMap_eq_ofReal, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebraMap_eq_ofReal, inner_smul_real_right

Depends on / 依赖: add_left, add_right, algebraMap_eq_ofReal, algebraMap_smul, inner_add_left, inner_add_right, inner_smul_real_left, inner_smul_real_right, norm_inner_le_norm, one_mul, smul_left, smul_right, zero_lt_one
-/
theorem _root_.isBoundedBilinearMap_inner [NormedSpace Real E] [IsScalarTower Real 𝕜 E] :
    IsBoundedBilinearMap Real fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebraMap_eq_ofReal, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebraMap_eq_ofReal, inner_smul_real_right]
    bound :=
      ⟨1, zero_lt_one, fun x y => by
        rw [one_mul]
        exact norm_inner_le_norm x y⟩ }

/--
theorem `continuous_inner` / 定理 `continuous_inner`

English:
theorem continuous_inner
  statement: Continuous fun p : E × E => ⟪p.1, p.2⟫
  proof: letI : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  haveI := IsScalarTower.restrictScalars Real 𝕜 E
  isBoundedBilinearMap_inner.continuous

中文:
定理 continuous_inner
  结论: 连续 fun p : E × E => ⟪p.1, p.2⟫
  证明: letI : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  haveI := IsScalarTower.restrictScalars Real 𝕜 E
  isBoundedBilinearMap_inner.continuous

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, IsScalarTower, IsScalarTower.restrictScalars, continuous, isBoundedBilinearMap_inner, isBoundedBilinearMap_inner.continuous, rclikeToReal, restrictScalars
-/
theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  letI : InnerProductSpace Real E := InnerProductSpace.rclikeToReal 𝕜 E
  haveI := IsScalarTower.restrictScalars Real 𝕜 E
  isBoundedBilinearMap_inner.continuous

variable {α : Type*}

/--
theorem `Filter.Tendsto.inner` / 定理 `Filter.Tendsto.inner`

English:
theorem Filter.Tendsto.inner
  statement: {f g : α -> E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
  proof: (continuous_inner.tendsto _).comp (hf.prodMk_nhds hg)

中文:
定理 滤子.收敛.inner
  结论: {f g : α -> E} {l : 滤子 α} {x y : E} (hf : 收敛 f l (𝓝 x))
  证明: (continuous_inner.tendsto _).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_inner, continuous_inner.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
theorem Filter.Tendsto.inner {f g : α -> E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.tendsto _).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α] {f g : α -> E} {x : α} {s : Set α}

/--
theorem `ContinuousWithinAt.inner` / 定理 `ContinuousWithinAt.inner`

English:
theorem ContinuousWithinAt.inner
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: Filter.Tendsto.inner hf hg

@[fun_prop]

中文:
定理 ContinuousWithinAt.inner
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: Filter.Tendsto.inner hf hg

@[fun_prop]

Depends on / 依赖: Filter, Filter.Tendsto.inner, Tendsto
-/
theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  Filter.Tendsto.inner hf hg

@[fun_prop]
/--
theorem `ContinuousAt.inner` / 定理 `ContinuousAt.inner`

English:
theorem ContinuousAt.inner
  given: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  proof: Filter.Tendsto.inner hf hg

@[fun_prop]

中文:
定理 ContinuousAt.inner
  条件: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  证明: Filter.Tendsto.inner hf hg

@[fun_prop]

Depends on / 依赖: Filter, Filter.Tendsto.inner, Tendsto
-/
theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  Filter.Tendsto.inner hf hg

@[fun_prop]
/--
theorem `ContinuousOn.inner` / 定理 `ContinuousOn.inner`

English:
theorem ContinuousOn.inner
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun x hx => (hf x hx).inner (hg x hx)

@[continuity, fun_prop]

中文:
定理 ContinuousOn.inner
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun x hx => (hf x hx).inner (hg x hx)

@[continuity, fun_prop]
-/
theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => ⟪f t, g t⟫) s := fun x hx => (hf x hx).inner (hg x hx)

@[continuity, fun_prop]
/--
theorem `Continuous.inner` / 定理 `Continuous.inner`

English:
theorem Continuous.inner
  given: (hf : Continuous f) (hg : Continuous g)
  statement: Continuous fun t => ⟪f t, g t⟫
  proof: continuous_iff_continuousAt.2 fun _x => by fun_prop

中文:
定理 连续.inner
  条件: (hf : 连续 f) (hg : 连续 g)
  结论: 连续 fun t => ⟪f t, g t⟫
  证明: continuous_iff_continuousAt.2 fun _x => by fun_prop

Depends on / 依赖: continuous_iff_continuousAt, fun_prop
-/
theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuousAt.2 fun _x => by fun_prop

end Continuous

open Submodule

variable {E F ι : Type*}
variable (𝕜 : Type*) [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace Real F]
variable {x y : E} {S : Set E} {f : ι -> E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `Dense.eq_zero_of_inner_left` / 定理 `Dense.eq_zero_of_inner_left`

English:
theorem Dense.eq_zero_of_inner_left
  given: (hS : Dense S) (h : forall v in S, ⟪x, v⟫ = 0)
  statement: x = 0
  proof: by
  let K := span 𝕜 S
  have hK : Dense (K : Set E) := hS.mono subset_span
  have : (⟪x, ·⟫) = 0 := (continuous_const.inner continuous_id).ext_on
    hK continuous_const fun v => Submodule.span_induction h (by simp)
      (by simp +contextual [inner_add_right]) (by simp +contextual [inner_smul_righ

中文:
定理 稠密.eq_zero_of_inner_left
  条件: (hS : 稠密 S) (h : 对任意 v in S, ⟪x, v⟫ = 0)
  结论: x = 0
  证明: by
  let K := span 𝕜 S
  have hK : Dense (K : Set E) := hS.mono subset_span
  have : (⟪x, ·⟫) = 0 := (continuous_const.inner continuous_id).ext_on
    hK continuous_const fun v => Submodule.span_induction h (by simp)
      (by simp +contextual [inner_add_right]) (by simp +contextual [inner_smul_righ

Depends on / 依赖: Submodule, Submodule.span_induction, congr_fun, contextual, continuous_const, continuous_const.inner, continuous_id, ext_on, hS.mono, inner_add_right, inner_smul_right, span_induction, subset_span
-/
theorem Dense.eq_zero_of_inner_left (hS : Dense S) (h : forall v in S, ⟪x, v⟫ = 0) : x = 0 := by
  let K := span 𝕜 S
  have hK : Dense (K : Set E) := hS.mono subset_span
  have : (⟪x, ·⟫) = 0 := (continuous_const.inner continuous_id).ext_on
    hK continuous_const fun v => Submodule.span_induction h (by simp)
      (by simp +contextual [inner_add_right]) (by simp +contextual [inner_smul_right])
  simpa using congr_fun this x

/--
theorem `Dense.eq_zero_of_inner_right` / 定理 `Dense.eq_zero_of_inner_right`

English:
theorem Dense.eq_zero_of_inner_right
  given: (hS : Dense S) (h : forall v in S, ⟪v, x⟫ = 0)
  statement: x = 0
  proof: hS.eq_zero_of_inner_left 𝕜 fun v hv => by rw! [← inner_conj_symm]; simp [-inner_conj_symm, h, hv]

中文:
定理 稠密.eq_zero_of_inner_right
  条件: (hS : 稠密 S) (h : 对任意 v in S, ⟪v, x⟫ = 0)
  结论: x = 0
  证明: hS.eq_zero_of_inner_left 𝕜 fun v hv => by rw! [← inner_conj_symm]; simp [-inner_conj_symm, h, hv]

Depends on / 依赖: eq_zero_of_inner_left, hS.eq_zero_of_inner_left, inner_conj_symm
-/
theorem Dense.eq_zero_of_inner_right (hS : Dense S) (h : forall v in S, ⟪v, x⟫ = 0) : x = 0 :=
  hS.eq_zero_of_inner_left 𝕜 fun v hv => by rw! [← inner_conj_symm]; simp [-inner_conj_symm, h, hv]

/--
theorem `Dense.eq_of_inner_left` / 定理 `Dense.eq_of_inner_left`

English:
theorem Dense.eq_of_inner_left
  given: (hS : Dense S) (h : forall v in S, ⟪x, v⟫ = ⟪y, v⟫)
  statement: x = y
  proof: by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_left 𝕜 (by simpa [inner_sub_left, sub_eq_zero])

中文:
定理 稠密.eq_of_inner_left
  条件: (hS : 稠密 S) (h : 对任意 v in S, ⟪x, v⟫ = ⟪y, v⟫)
  结论: x = y
  证明: by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_left 𝕜 (by simpa [inner_sub_left, sub_eq_zero])

Depends on / 依赖: eq_zero_of_inner_left, hS.eq_zero_of_inner_left, inner_sub_left, sub_eq_zero
-/
theorem Dense.eq_of_inner_left (hS : Dense S) (h : forall v in S, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_left 𝕜 (by simpa [inner_sub_left, sub_eq_zero])

/--
theorem `Dense.eq_of_inner_right` / 定理 `Dense.eq_of_inner_right`

English:
theorem Dense.eq_of_inner_right
  given: (hS : Dense S) (h : forall v in S, ⟪v, x⟫ = ⟪v, y⟫)
  statement: x = y
  proof: by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_right 𝕜 (by simpa [inner_sub_right, sub_eq_zero])

nonrec theorem DenseRange.eq_of_inner_left (hf : DenseRange f) (h : forall i, ⟪x, f i⟫ = ⟪y, f i⟫) :
    x = y := hf.eq_of_inner_left 𝕜 (by simpa)

nonrec theorem DenseRange.eq_of_inner_right (hf : 

中文:
定理 稠密.eq_of_inner_right
  条件: (hS : 稠密 S) (h : 对任意 v in S, ⟪v, x⟫ = ⟪v, y⟫)
  结论: x = y
  证明: by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_right 𝕜 (by simpa [inner_sub_right, sub_eq_zero])

nonrec theorem DenseRange.eq_of_inner_left (hf : DenseRange f) (h : forall i, ⟪x, f i⟫ = ⟪y, f i⟫) :
    x = y := hf.eq_of_inner_left 𝕜 (by simpa)

nonrec theorem DenseRange.eq_of_inner_right (hf : 

Depends on / 依赖: eq_zero_of_inner_right, hS.eq_zero_of_inner_right, inner_sub_right, sub_eq_zero
-/
theorem Dense.eq_of_inner_right (hS : Dense S) (h : forall v in S, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_right 𝕜 (by simpa [inner_sub_right, sub_eq_zero])

nonrec theorem DenseRange.eq_of_inner_left (hf : DenseRange f) (h : forall i, ⟪x, f i⟫ = ⟪y, f i⟫) :
    x = y := hf.eq_of_inner_left 𝕜 (by simpa)

nonrec theorem DenseRange.eq_of_inner_right (hf : DenseRange f) (h : forall i, ⟪f i, x⟫ = ⟪f i, y⟫) :
    x = y := hf.eq_of_inner_right 𝕜 (by simpa)

nonrec theorem DenseRange.eq_zero_of_inner_left (hf : DenseRange f) (h : forall i, ⟪x, f i⟫ = 0) :
    x = 0 := hf.eq_zero_of_inner_left 𝕜 (by simpa)

nonrec theorem DenseRange.eq_zero_of_inner_right (hf : DenseRange f) (h : forall i, ⟪f i, x⟫ = 0) :
    x = 0 := hf.eq_zero_of_inner_right 𝕜 (by simpa)
