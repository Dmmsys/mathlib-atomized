/-
Copyright (c) 2026 Hampus Nyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hampus Nyberg, Yaël Dillies
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Reproducing Kernel Hilbert Spaces

This file defines vector-valued reproducing Kernel Hilbert spaces, which are Hilbert spaces of
functions, as well as characterizing these spaces in terms of infinite-dimensional
positive semidefinite matrices.

## Main results

- `RKHS`: the class of reproducing kernel Hilbert spaces
- `RKHS.kernel`: the kernel of a RKHS as a matrix.
- `RKHS.kerFun`: the kernel functions of a RKHS.
- `RKHS.kerFun_dense`: the kernel functions are dense in the Hilbert space.
- `RKHS.posSemidef_kernel`: The kernel is positive semidefinite.
- `RKHS.OfKernel`: RKHS constructed from a positive semidefinite matrix.
- `RKHS.kernel_ofKernel`: The kernel of the constructed RKHS is equal to the matrix, this is
    essentially Moore's theorem.

## TODO

- Privatize `RKHS.H₀`

## References
* [Paulsen, Vern I. and Raghupathi, Mrinal,
  *An introduction to the theory of reproducing kernel Hilbert spaces*][MR3526117]
-/

public noncomputable section

open ContinuousLinearMap InnerProductSpace Submodule ComplexConjugate Filter
open scoped Topology

/--
Definition of `RKHS` / `RKHS` 的定义

English:
class RKHS
  parameters: (𝕜 : outParam Type*) (H : Type*) (X V : outParam Type*) [RCLike 𝕜]
  axioms and operations (2):
    - coeCLM((𝕜)) : H ->L[𝕜] X -> V
    - coeCLM_injective : Function.Injective (coeCLM : H -> X -> V)

中文:
类 RKHS
  参数: (𝕜 : outParam 类型) (H : 类型) (X V : outParam 类型) [RCLike 𝕜]
  公理与运算 (2 个):
    - coeCLM((𝕜)) : H ->L[𝕜] X -> V
    - coeCLM_injective : 函数.单射 (coeCLM : H -> X -> V)
-/
class RKHS (𝕜 : outParam Type*) (H : Type*) (X V : outParam Type*) [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  /-- Continuous injection to functions from the reproducing kernel Hilbert space `H` to functions
  from the domain `X` to the Hilbert space `V` -/
  coeCLM (𝕜) : H ->L[𝕜] X -> V
  coeCLM_injective : Function.Injective (coeCLM : H -> X -> V)

namespace RKHS

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [RKHS 𝕜 H X V]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike H X V where
  body: coeCLM 𝕜 f
  coe_injective := coeCLM_injective

@[ext]

中文:
实例 instFunLike
  签名: : 函数状 H X V where
  定义体: coeCLM 𝕜 f
  coe_injective := coeCLM_injective

@[ext]

Depends on / 依赖: coeCLM
-/
instance instFunLike : FunLike H X V where
  coe f := coeCLM 𝕜 f
  coe_injective := coeCLM_injective

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : H} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

@[simp]

中文:
引理 ext
  条件: {f g : H} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma ext {f g : H} (h : forall x, f x = g x) : f = g := DFunLike.ext _ _ h

@[simp]
/--
lemma `coeCLM_apply` / 引理 `coeCLM_apply`

English:
lemma coeCLM_apply
  given: (f : H)
  statement: coeCLM 𝕜 f = f
  proof: rfl

@[simp]

中文:
引理 coeCLM_apply
  条件: (f : H)
  结论: coeCLM 𝕜 f = f
  证明: rfl

@[simp]
-/
lemma coeCLM_apply (f : H) : coeCLM 𝕜 f = f := rfl

@[simp]
/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ⇑(0 : H) = 0
  proof: (coeCLM 𝕜).map_zero ..

@[simp]

中文:
引理 coe_zero
  结论: ⇑(0 : H) = 0
  证明: (coeCLM 𝕜).map_zero ..

@[simp]

Depends on / 依赖: coeCLM, map_zero
-/
lemma coe_zero : ⇑(0 : H) = 0 := (coeCLM 𝕜).map_zero ..

@[simp]
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (f g : H)
  statement: ⇑(f + g) = f + g
  proof: (coeCLM 𝕜).map_add ..

@[simp]

中文:
引理 coe_add
  条件: (f g : H)
  结论: ⇑(f + g) = f + g
  证明: (coeCLM 𝕜).map_add ..

@[simp]

Depends on / 依赖: coeCLM, map_add
-/
lemma coe_add (f g : H) : ⇑(f + g) = f + g := (coeCLM 𝕜).map_add ..

@[simp]
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (f g : H)
  statement: ⇑(f - g) = f - g
  proof: (coeCLM 𝕜).map_sub (M₂ := X -> V) ..

@[simp]

中文:
引理 coe_sub
  条件: (f g : H)
  结论: ⇑(f - g) = f - g
  证明: (coeCLM 𝕜).map_sub (M₂ := X -> V) ..

@[simp]

Depends on / 依赖: coeCLM, map_sub
-/
lemma coe_sub (f g : H) : ⇑(f - g) = f - g := (coeCLM 𝕜).map_sub (M₂ := X -> V) ..

@[simp]
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (f : H)
  statement: ⇑(-f) = -f
  proof: (coeCLM 𝕜).map_neg (M₂ := X -> V) ..

@[simp]

中文:
引理 coe_neg
  条件: (f : H)
  结论: ⇑(-f) = -f
  证明: (coeCLM 𝕜).map_neg (M₂ := X -> V) ..

@[simp]

Depends on / 依赖: coeCLM, map_neg
-/
lemma coe_neg (f : H) : ⇑(-f) = -f := (coeCLM 𝕜).map_neg (M₂ := X -> V) ..

@[simp]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (f : H) (c : 𝕜)
  statement: ⇑(c • f) = c • f
  proof: (coeCLM 𝕜).map_smul ..

@[simp]

中文:
引理 coe_smul
  条件: (f : H) (c : 𝕜)
  结论: ⇑(c • f) = c • f
  证明: (coeCLM 𝕜).map_smul ..

@[simp]

Depends on / 依赖: coeCLM, map_smul
-/
lemma coe_smul (f : H) (c : 𝕜) : ⇑(c • f) = c • f := (coeCLM 𝕜).map_smul ..

@[simp]
/--
lemma `continuous_eval` / 引理 `continuous_eval`

English:
lemma continuous_eval
  given: (x : X)
  statement: Continuous (fun (f : H) => f x)
  proof: by
  simp_rw [← coeCLM_apply]
  fun_prop

中文:
引理 continuous_eval
  条件: (x : X)
  结论: 连续 (fun (f : H) => f x)
  证明: by
  simp_rw [← coeCLM_apply]
  fun_prop

Depends on / 依赖: coeCLM_apply, fun_prop, simp_rw
-/
lemma continuous_eval (x : X) : Continuous (fun (f : H) => f x) := by
  simp_rw [← coeCLM_apply]
  fun_prop

variable (H) [CompleteSpace H] [CompleteSpace V]

/--
Definition of `kerFun` / `kerFun` 的定义

English:
definition kerFun
  signature: (x : X)
  body: (.proj x ∘L coeCLM 𝕜).adjoint

中文:
定义 kerFun
  签名: (x : X)
  定义体: (.proj x ∘L coeCLM 𝕜).adjoint

Depends on / 依赖: adjoint, coeCLM
-/
def kerFun (x : X) : V ->L[𝕜] H := (.proj x ∘L coeCLM 𝕜).adjoint

/--
Definition of `kernel` / `kernel` 的定义

English:
definition kernel
  signature: : Matrix X X (V ->L[𝕜] V)
  body: .of fun x y => (kerFun H x).adjoint ∘L kerFun H y

中文:
定义 kernel
  签名: : 矩阵 X X (V ->L[𝕜] V)
  定义体: .of fun x y => (kerFun H x).adjoint ∘L kerFun H y

Depends on / 依赖: adjoint, kerFun
-/
def kernel : Matrix X X (V ->L[𝕜] V) := .of fun x y => (kerFun H x).adjoint ∘L kerFun H y

/--
lemma `kerFun_apply` / 引理 `kerFun_apply`

English:
lemma kerFun_apply
  given: (y : X) (v : V) (x : X)
  statement: kerFun H y v x = kernel H x y v
  proof: by
  simp [kernel, kerFun]

中文:
引理 kerFun_apply
  条件: (y : X) (v : V) (x : X)
  结论: kerFun H y v x = kernel H x y v
  证明: by
  simp [kernel, kerFun]

Depends on / 依赖: kerFun, kernel
-/
lemma kerFun_apply (y : X) (v : V) (x : X) : kerFun H y v x = kernel H x y v := by
  simp [kernel, kerFun]

/--
lemma `kernel_apply` / 引理 `kernel_apply`

English:
lemma kernel_apply
  given: (x y : X)
  statement: kernel H x y = (kerFun H x).adjoint ∘L kerFun H y
  proof: by
  simp [kerFun, kernel]

中文:
引理 kernel_apply
  条件: (x y : X)
  结论: kernel H x y = (kerFun H x).adjoint ∘L kerFun H y
  证明: by
  simp [kerFun, kernel]

Depends on / 依赖: kerFun, kernel
-/
lemma kernel_apply (x y : X) : kernel H x y = (kerFun H x).adjoint ∘L kerFun H y := by
  simp [kerFun, kernel]

variable {H} in
/-- Point evaluation `f ↦ f x` is the adjoint of the kernel function `kerFun H x`. -/
@[simp]
/--
lemma `adjoint_kerFun` / 引理 `adjoint_kerFun`

English:
lemma adjoint_kerFun
  given: (x : X) (f : H)
  statement: (kerFun H x).adjoint f = f x
  proof: by
  simp [kerFun]

中文:
引理 adjoint_kerFun
  条件: (x : X) (f : H)
  结论: (kerFun H x).adjoint f = f x
  证明: by
  simp [kerFun]

Depends on / 依赖: kerFun
-/
lemma adjoint_kerFun (x : X) (f : H) : (kerFun H x).adjoint f = f x := by
  simp [kerFun]

variable {H} in
/-- The "reproducing" property of the kernel functions, left version. -/
@[simp]
/--
lemma `kerFun_inner` / 引理 `kerFun_inner`

English:
lemma kerFun_inner
  given: (x : X) (v : V) (f : H)
  statement: ⟪kerFun H x v, f⟫_𝕜 = ⟪v, f x⟫_𝕜
  proof: by
  simp [kerFun, ← adjoint_inner_right]

中文:
引理 kerFun_inner
  条件: (x : X) (v : V) (f : H)
  结论: ⟪kerFun H x v, f⟫_𝕜 = ⟪v, f x⟫_𝕜
  证明: by
  simp [kerFun, ← adjoint_inner_right]

Depends on / 依赖: adjoint_inner_right, kerFun
-/
lemma kerFun_inner (x : X) (v : V) (f : H) : ⟪kerFun H x v, f⟫_𝕜 = ⟪v, f x⟫_𝕜 := by
  simp [kerFun, ← adjoint_inner_right]

variable {H} in
/-- The "reproducing" property of the kernel functions, right version. -/
@[simp]
/--
lemma `inner_kerFun` / 引理 `inner_kerFun`

English:
lemma inner_kerFun
  given: (x : X) (v : V) (f : H)
  statement: ⟪f, kerFun H x v⟫_𝕜 = ⟪f x, v⟫_𝕜
  proof: by
  simp [kerFun, ← adjoint_inner_left]

中文:
引理 inner_kerFun
  条件: (x : X) (v : V) (f : H)
  结论: ⟪f, kerFun H x v⟫_𝕜 = ⟪f x, v⟫_𝕜
  证明: by
  simp [kerFun, ← adjoint_inner_left]

Depends on / 依赖: adjoint_inner_left, kerFun
-/
lemma inner_kerFun (x : X) (v : V) (f : H) : ⟪f, kerFun H x v⟫_𝕜 = ⟪f x, v⟫_𝕜 := by
  simp [kerFun, ← adjoint_inner_left]

/--
lemma `kernel_inner` / 引理 `kernel_inner`

English:
lemma kernel_inner
  given: (x y : X) (v w : V)
  proof: by
  simp [← adjoint_inner_left, kernel]

中文:
引理 kernel_inner
  条件: (x y : X) (v w : V)
  证明: by
  simp [← adjoint_inner_left, kernel]

Depends on / 依赖: adjoint_inner_left, kernel
-/
lemma kernel_inner (x y : X) (v w : V) :
    ⟪kernel H x y v, w⟫_𝕜 = ⟪kerFun H y v, kerFun H x w⟫_𝕜 := by
  simp [← adjoint_inner_left, kernel]

/--
lemma `norm_kernel_eq_norm_kerFun_sq` / 引理 `norm_kernel_eq_norm_kerFun_sq`

English:
lemma norm_kernel_eq_norm_kerFun_sq
  given: (x)
  statement: ‖kernel H x x‖ = ‖kerFun H x‖ ^ 2
  proof: by
  rw [sq]; rw [← ContinuousLinearMap.norm_adjoint_comp_self]; rw [kernel_apply]

中文:
引理 norm_kernel_eq_norm_kerFun_sq
  条件: (x)
  结论: ‖kernel H x x‖ = ‖kerFun H x‖ ^ 2
  证明: by
  rw [sq]; rw [← ContinuousLinearMap.norm_adjoint_comp_self]; rw [kernel_apply]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_adjoint_comp_self, kernel_apply, norm_adjoint_comp_self
-/
lemma norm_kernel_eq_norm_kerFun_sq (x) : ‖kernel H x x‖ = ‖kerFun H x‖ ^ 2 := by
  rw [sq]; rw [← ContinuousLinearMap.norm_adjoint_comp_self]; rw [kernel_apply]

/--
lemma `norm_kerFun_eq_sqrt_norm_kernel` / 引理 `norm_kerFun_eq_sqrt_norm_kernel`

English:
lemma norm_kerFun_eq_sqrt_norm_kernel
  given: (x)
  statement: ‖kerFun H x‖ = √‖kernel H x x‖
  proof: by
  rw [norm_kernel_eq_norm_kerFun_sq]; rw [Real.sqrt_sq (norm_nonneg _)]

中文:
引理 norm_kerFun_eq_sqrt_norm_kernel
  条件: (x)
  结论: ‖kerFun H x‖ = √‖kernel H x x‖
  证明: by
  rw [norm_kernel_eq_norm_kerFun_sq]; rw [Real.sqrt_sq (norm_nonneg _)]

Depends on / 依赖: Real.sqrt_sq, norm_kernel_eq_norm_kerFun_sq, norm_nonneg, sqrt_sq
-/
lemma norm_kerFun_eq_sqrt_norm_kernel (x) : ‖kerFun H x‖ = √‖kernel H x x‖ := by
  rw [norm_kernel_eq_norm_kerFun_sq]; rw [Real.sqrt_sq (norm_nonneg _)]

/--
lemma `norm_kernel_le` / 引理 `norm_kernel_le`

English:
lemma norm_kernel_le
  given: (x y)
  statement: ‖kernel H x y‖ <= √‖kernel H x x‖ * √‖kernel H y y‖
  proof: by
  grw [kernel_apply, opNorm_comp_le]
  simp [norm_kerFun_eq_sqrt_norm_kernel]

中文:
引理 norm_kernel_le
  条件: (x y)
  结论: ‖kernel H x y‖ <= √‖kernel H x x‖ * √‖kernel H y y‖
  证明: by
  grw [kernel_apply, opNorm_comp_le]
  simp [norm_kerFun_eq_sqrt_norm_kernel]

Depends on / 依赖: kernel_apply, norm_kerFun_eq_sqrt_norm_kernel, opNorm_comp_le
-/
lemma norm_kernel_le (x y) : ‖kernel H x y‖ <= √‖kernel H x x‖ * √‖kernel H y y‖ := by
  grw [kernel_apply, opNorm_comp_le]
  simp [norm_kerFun_eq_sqrt_norm_kernel]

/--
lemma `norm_kernel_sq_le` / 引理 `norm_kernel_sq_le`

English:
lemma norm_kernel_sq_le
  given: (x y)
  statement: ‖kernel H x y‖ ^ 2 <= ‖kernel H x x‖ * ‖kernel H y y‖
  proof: by
  grw [norm_kernel_le]; simp [mul_pow]

中文:
引理 norm_kernel_sq_le
  条件: (x y)
  结论: ‖kernel H x y‖ ^ 2 <= ‖kernel H x x‖ * ‖kernel H y y‖
  证明: by
  grw [norm_kernel_le]; simp [mul_pow]

Depends on / 依赖: mul_pow, norm_kernel_le
-/
lemma norm_kernel_sq_le (x y) : ‖kernel H x y‖ ^ 2 <= ‖kernel H x x‖ * ‖kernel H y y‖ := by
  grw [norm_kernel_le]; simp [mul_pow]

variable {H} in
/--
lemma `norm_apply_le` / 引理 `norm_apply_le`

English:
lemma norm_apply_le
  given: (f : H) (x : X)
  statement: ‖f x‖ <= ‖f‖ * √‖kernel H x x‖
  proof: by
  grw [← adjoint_kerFun, le_opNorm, norm_map, norm_kerFun_eq_sqrt_norm_kernel, mul_comm]

中文:
引理 norm_apply_le
  条件: (f : H) (x : X)
  结论: ‖f x‖ <= ‖f‖ * √‖kernel H x x‖
  证明: by
  grw [← adjoint_kerFun, le_opNorm, norm_map, norm_kerFun_eq_sqrt_norm_kernel, mul_comm]

Depends on / 依赖: adjoint_kerFun, le_opNorm, mul_comm, norm_kerFun_eq_sqrt_norm_kernel, norm_map
-/
lemma norm_apply_le (f : H) (x : X) : ‖f x‖ <= ‖f‖ * √‖kernel H x x‖ := by
  grw [← adjoint_kerFun, le_opNorm, norm_map, norm_kerFun_eq_sqrt_norm_kernel, mul_comm]

variable {H} in
/--
theorem `tendstoUniformlyOn_of_norm_kerFun_le` / 定理 `tendstoUniformlyOn_of_norm_kerFun_le`

English:
theorem tendstoUniformlyOn_of_norm_kerFun_le
  statement: {C : Real} {s : Set X}
  proof: by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp h).mul_const C
  rw [zero_mul] at hnorm
  filter_upwards [hnorm.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [dist_eq_norm']; rw [← Pi.sub_apply]; rw [← coe_sub]
  grw [norm_apply_le, ← nor

中文:
定理 tendstoUniformlyOn_of_norm_kerFun_le
  结论: {C : 实数} {s : 集合 X}
  证明: by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp h).mul_const C
  rw [zero_mul] at hnorm
  filter_upwards [hnorm.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [dist_eq_norm']; rw [← Pi.sub_apply]; rw [← coe_sub]
  grw [norm_apply_le, ← nor

Depends on / 依赖: Metric, Metric.tendstoUniformlyOn_iff, Pi.sub_apply, coe_sub, dist_eq_norm, eventually, filter_upwards, gt_mem_nhds, hnorm.eventually, mul_const, norm_apply_le, norm_kerFun_eq_sqrt_norm_kernel, sub_apply, tendstoUniformlyOn_iff, tendsto_iff_norm_sub_tendsto_zero, tendsto_iff_norm_sub_tendsto_zero.mp, zero_mul
-/
theorem tendstoUniformlyOn_of_norm_kerFun_le {C : Real} {s : Set X}
    (hC : forall x in s, ‖kerFun H x‖ <= C)
    {ι : Type*} {l : Filter ι} {F : ι -> H} {f : H} (h : Tendsto F l (𝓝 f)) :
    TendstoUniformlyOn (fun n => ⇑(F n)) (⇑f) l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp h).mul_const C
  rw [zero_mul] at hnorm
  filter_upwards [hnorm.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [dist_eq_norm']; rw [← Pi.sub_apply]; rw [← coe_sub]
  grw [norm_apply_le, ← norm_kerFun_eq_sqrt_norm_kernel, hC x hx, hn]

variable {H} in
/--
theorem `tendstoUniformly_of_norm_kerFun_le` / 定理 `tendstoUniformly_of_norm_kerFun_le`

English:
theorem tendstoUniformly_of_norm_kerFun_le
  statement: {C : Real} (hC : forall x, ‖kerFun H x‖ <= C)
  proof: by
  rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_of_norm_kerFun_le (fun x _ => hC x) h

中文:
定理 tendstoUniformly_of_norm_kerFun_le
  结论: {C : 实数} (hC : 对任意 x, ‖kerFun H x‖ <= C)
  证明: by
  rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_of_norm_kerFun_le (fun x _ => hC x) h

Depends on / 依赖: tendstoUniformlyOn_of_norm_kerFun_le, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_of_norm_kerFun_le {C : Real} (hC : forall x, ‖kerFun H x‖ <= C)
    {ι : Type*} {l : Filter ι} {F : ι -> H} {f : H} (h : Tendsto F l (𝓝 f)) :
    TendstoUniformly (fun n => ⇑(F n)) (⇑f) l := by
  rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_of_norm_kerFun_le (fun x _ => hC x) h

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `kerFun_dense` / 定理 `kerFun_dense`

English:
theorem kerFun_dense
  statement: topologicalClosure (span 𝕜 {kerFun H x v | (x) (v)}) = ⊤
  proof: by
  refine (orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr fun f fin => DFunLike.ext f 0 ?_))
  refine fun x => ext_inner_left 𝕜 fun v => ?_
  simp only [← kerFun_inner, coe_zero, Pi.zero_apply, inner_zero_right]
  refine inner_right_of_mem_orthogonal (subset_closure ?_) fin
  simp [mem_spa

中文:
定理 kerFun_dense
  结论: topologicalClosure (span 𝕜 {kerFun H x v | (x) (v)}) = ⊤
  证明: by
  refine (orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr fun f fin => DFunLike.ext f 0 ?_))
  refine fun x => ext_inner_left 𝕜 fun v => ?_
  simp only [← kerFun_inner, coe_zero, Pi.zero_apply, inner_zero_right]
  refine inner_right_of_mem_orthogonal (subset_closure ?_) fin
  simp [mem_spa

Depends on / 依赖: DFunLike, DFunLike.ext, Pi.zero_apply, Submodule, Submodule.eq_bot_iff, coe_zero, eq_bot_iff, ext_inner_left, inner_right_of_mem_orthogonal, inner_zero_right, kerFun_inner, mem_span_of_mem, orthogonal_eq_bot_iff, orthogonal_eq_bot_iff.mp, subset_closure, zero_apply
-/
theorem kerFun_dense : topologicalClosure (span 𝕜 {kerFun H x v | (x) (v)}) = ⊤ := by
  refine (orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr fun f fin => DFunLike.ext f 0 ?_))
  refine fun x => ext_inner_left 𝕜 fun v => ?_
  simp only [← kerFun_inner, coe_zero, Pi.zero_apply, inner_zero_right]
  refine inner_right_of_mem_orthogonal (subset_closure ?_) fin
  simp [mem_span_of_mem]

/--
lemma `isHermitian_kernel` / 引理 `isHermitian_kernel`

English:
lemma isHermitian_kernel
  statement: (kernel H).IsHermitian
  proof: by
  ext
  refine ext_inner_right 𝕜 fun w => ?_
  simp only [Matrix.conjTranspose_apply, star, adjoint_inner_left,
    ← inner_conj_symm _ (kernel H _ _ _), kernel_inner, inner_conj_symm]

中文:
引理 isHermitian_kernel
  结论: (kernel H).IsHermitian
  证明: by
  ext
  refine ext_inner_right 𝕜 fun w => ?_
  simp only [Matrix.conjTranspose_apply, star, adjoint_inner_left,
    ← inner_conj_symm _ (kernel H _ _ _), kernel_inner, inner_conj_symm]

Depends on / 依赖: Matrix, Matrix.conjTranspose_apply, adjoint_inner_left, conjTranspose_apply, ext_inner_right, inner_conj_symm, kernel, kernel_inner
-/
lemma isHermitian_kernel : (kernel H).IsHermitian := by
  ext
  refine ext_inner_right 𝕜 fun w => ?_
  simp only [Matrix.conjTranspose_apply, star, adjoint_inner_left,
    ← inner_conj_symm _ (kernel H _ _ _), kernel_inner, inner_conj_symm]

open scoped ComplexOrder in
/--
theorem `posSemidef_kernel` / 定理 `posSemidef_kernel`

English:
theorem posSemidef_kernel
  statement: (kernel H).PosSemidef
  proof: by
  refine ⟨isHermitian_kernel H, fun s => (ContinuousLinearMap.isPositive_iff' _).2 ⟨?_, fun v => ?_⟩⟩
  · rw [IsSelfAdjoint, sub_zero, star_finsuppSum, Finsupp.sum_comm]
    simp [← mul_assoc, (isHermitian_kernel H).apply]
  · simp [Finsupp.sum_apply'', Finsupp.sum_inner, star, adjoint_inner_left

中文:
定理 posSemidef_kernel
  结论: (kernel H).PosSemidef
  证明: by
  refine ⟨isHermitian_kernel H, fun s => (ContinuousLinearMap.isPositive_iff' _).2 ⟨?_, fun v => ?_⟩⟩
  · rw [IsSelfAdjoint, sub_zero, star_finsuppSum, Finsupp.sum_comm]
    simp [← mul_assoc, (isHermitian_kernel H).apply]
  · simp [Finsupp.sum_apply'', Finsupp.sum_inner, star, adjoint_inner_left

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.isPositive_iff, Finsupp, Finsupp.inner_sum, Finsupp.sum_apply, Finsupp.sum_comm, Finsupp.sum_inner, IsSelfAdjoint, adjoint_inner_left, inner_kerFun, inner_sum, isHermitian_kernel, isPositive_iff, kerFun_inner, kernel_inner, mul_assoc, star_finsuppSum, sub_zero, sum_apply, sum_comm
-/
theorem posSemidef_kernel : (kernel H).PosSemidef := by
  refine ⟨isHermitian_kernel H, fun s => (ContinuousLinearMap.isPositive_iff' _).2 ⟨?_, fun v => ?_⟩⟩
  · rw [IsSelfAdjoint, sub_zero, star_finsuppSum, Finsupp.sum_comm]
    simp [← mul_assoc, (isHermitian_kernel H).apply]
  · simp [Finsupp.sum_apply'', Finsupp.sum_inner, star, adjoint_inner_left,
      kernel_inner, -inner_kerFun, -kerFun_inner]
    simp [← Finsupp.sum_inner, ← Finsupp.inner_sum, -kerFun_inner, -inner_kerFun]

/-!
## Construction of RKHS from kernel
-/

variable {H} {K : Matrix X X (V ->L[𝕜] V)}

/--
lemma `isSelfAdjoint_finsuppSum` / 引理 `isSelfAdjoint_finsuppSum`

English:
lemma isSelfAdjoint_finsuppSum
  given: (h : K.IsHermitian) (f : X ->₀ V ->L[𝕜] V)
  proof: by
  simp only [mul_assoc, isSelfAdjoint_iff, star_finsuppSum, Pi.star_apply, star_mul, h.apply,
    star_star]
  rw [Finsupp.sum_comm]

中文:
引理 isSelfAdjoint_finsuppSum
  条件: (h : K.IsHermitian) (f : X ->₀ V ->L[𝕜] V)
  证明: by
  simp only [mul_assoc, isSelfAdjoint_iff, star_finsuppSum, Pi.star_apply, star_mul, h.apply,
    star_star]
  rw [Finsupp.sum_comm]
-/
private lemma isSelfAdjoint_finsuppSum (h : K.IsHermitian) (f : X ->₀ V ->L[𝕜] V) :
    IsSelfAdjoint (f.sum fun i xi => f.sum fun j xj => star xi * K i j * xj) := by
  simp only [mul_assoc, isSelfAdjoint_iff, star_finsuppSum, Pi.star_apply, star_mul, h.apply,
    star_star]
  rw [Finsupp.sum_comm]

/--
theorem `posSemidef_tfae` / 定理 `posSemidef_tfae`

English:
theorem posSemidef_tfae
  statement: List.TFAE [K.PosSemidef, K.IsHermitian ∧ forall (f : X × V ->₀ 𝕜),
  proof: by
  have {h p1 p2 p3 : Prop} (htfae : h -> List.TFAE [p1, p2, p3]) :
      List.TFAE [h ∧ p1, h ∧ p2, h ∧ p3] := by
    tfae_have 1 -> 2 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 0 1).mp t⟩
    tfae_have 2 -> 3 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 1 2).mp t⟩
    tfae_have 3 -> 1 := fun ⟨h, t⟩ => ⟨h, ((htf

中文:
定理 posSemidef_tfae
  结论: 列表.TFAE [K.PosSemidef, K.IsHermitian ∧ 对任意 (f : X × V ->₀ 𝕜),
  证明: by
  have {h p1 p2 p3 : Prop} (htfae : h -> List.TFAE [p1, p2, p3]) :
      List.TFAE [h ∧ p1, h ∧ p2, h ∧ p3] := by
    tfae_have 1 -> 2 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 0 1).mp t⟩
    tfae_have 2 -> 3 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 1 2).mp t⟩
    tfae_have 3 -> 1 := fun ⟨h, t⟩ => ⟨h, ((htf

Depends on / 依赖: List.TFAE, isPositive_def, isSelfAdjoint_finsuppSum, nonneg_iff_isPositive, reApplyInnerSelf_apply, star_eq_adjoint, tfae_finish, tfae_have, true_and, zero_apply
-/
theorem posSemidef_tfae : List.TFAE [K.PosSemidef, K.IsHermitian ∧ forall (f : X × V ->₀ 𝕜),
    0 <= RCLike.re (f.sum fun xv z => f.sum fun xv' w => conj z * w * ⟪K xv'.1 xv.1 xv.2, xv'.2⟫_𝕜),
    K.IsHermitian ∧ forall (vv : X ->₀ V),
    0 <= RCLike.re (vv.sum fun x w => vv.sum fun x' w' => ⟪K x' x w, w'⟫_𝕜),
    ] := by
  have {h p1 p2 p3 : Prop} (htfae : h -> List.TFAE [p1, p2, p3]) :
      List.TFAE [h ∧ p1, h ∧ p2, h ∧ p3] := by
    tfae_have 1 -> 2 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 0 1).mp t⟩
    tfae_have 2 -> 3 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 1 2).mp t⟩
    tfae_have 3 -> 1 := fun ⟨h, t⟩ => ⟨h, ((htfae h).out 2 0).mp t⟩
    tfae_finish
  refine this fun hHerm => ?_
  simp only [nonneg_iff_isPositive, isPositive_def', isSelfAdjoint_finsuppSum hHerm,
    reApplyInnerSelf_apply, true_and]
  simp only [star_eq_adjoint, zero_apply, add_apply, implies_true, Finsupp.sum_apply'',
    FunLike.coe_mul_eq_comp, Function.comp_apply, Finsupp.sum_inner, adjoint_inner_left]
  -- FIXME: nontriviality should work here
  refine (subsingleton_or_nontrivial V).elim (fun h => ?_) fun _ => ?_
  · have : forall v : V, v = 0 := fun v => Subsingleton.elim v 0
    simp [this]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  tfae_have 1 -> 2 := fun h ff => by
    rw [Finsupp.sum_comm]
    convert! h (ff.sum fun xv z => .single xv.1 ((z / ‖v‖ ^ 2) • (innerSL 𝕜 v).smulRight xv.2)) v
    simp [Finsupp.sum_sum_index, inner_add_right, inner_add_left, ← smul_assoc, hv]
    simp [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm]
  tfae_have 2 -> 3 := fun h vv => by
    simpa [add_mul, Finsupp.sum_sum_index] using (h (vv.sum fun x v => .single ⟨x, v⟩ 1))
  tfae_have 3 -> 1 := fun h ff v => by
    rw [Finsupp.sum_comm]
    simpa [Finsupp.sum_sum_index, inner_add_right, inner_add_left] using
      h (ff.sum fun x T => .single x (T v))
  tfae_finish

set_option linter.unusedVariables false in
/-- Auxiliary construction for `OfKernel`. TODO: Privatize -/
@[nolint unusedArguments]
/--
Definition of `H₀` / `H₀` 的定义

English:
abbreviation H₀
  signature: (K : Matrix X X (V ->L[𝕜] V))
  body: X × V ->₀ 𝕜

中文:
缩写 H₀
  签名: (K : 矩阵 X X (V ->L[𝕜] V))
  定义体: X × V ->₀ 𝕜
-/
abbrev H₀ (K : Matrix X X (V ->L[𝕜] V)) := X × V ->₀ 𝕜

variable [Fact K.PosSemidef]

/--
Instance `instPreInnerProductSpaceCoreH₀` / 实例 `instPreInnerProductSpaceCoreH₀`

English:
instance instPreInnerProductSpaceCoreH₀
  signature: : PreInnerProductSpace.Core 𝕜 (H₀ K) where
  body: f.sum fun ⟨y, u⟩ z => g.sum fun ⟨x, v⟩ w => star z * w * ⟪K x y u, v⟫_𝕜
  conj_inner_symm f g := by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← (Fact.out : K.PosSemidef).isHermitian.apply]
    simp [star, adjoint_inner_right, mul_comm]
  add_left _ _ _ := by
    r

中文:
实例 instPreInnerProductSpaceCoreH₀
  签名: : PreInnerProduct空间.核 𝕜 (H₀ K) where
  定义体: f.sum fun ⟨y, u⟩ z => g.sum fun ⟨x, v⟩ w => star z * w * ⟪K x y u, v⟫_𝕜
  conj_inner_symm f g := by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← (Fact.out : K.PosSemidef).isHermitian.apply]
    simp [star, adjoint_inner_right, mul_comm]
  add_left _ _ _ := by
    r

Depends on / 依赖: f.sum, g.sum
-/
instance instPreInnerProductSpaceCoreH₀ : PreInnerProductSpace.Core 𝕜 (H₀ K) where
  inner f g := f.sum fun ⟨y, u⟩ z => g.sum fun ⟨x, v⟩ w => star z * w * ⟪K x y u, v⟫_𝕜
  conj_inner_symm f g := by
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum]
    congr! 6
    rw [← (Fact.out : K.PosSemidef).isHermitian.apply]
    simp [star, adjoint_inner_right, mul_comm]
  add_left _ _ _ := by
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  smul_left _ _ _ := by
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
  re_inner_nonneg := by
    have := (posSemidef_tfae.out 0 1).mp (Fact.out : K.PosSemidef)
    exact this.2

/--
Instance `instSeminormedAddCommGroupH₀` / 实例 `instSeminormedAddCommGroupH₀`

English:
instance instSeminormedAddCommGroupH₀
  signature: : SeminormedAddCommGroup (H₀ K)
  body: InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := 𝕜)

中文:
实例 instSeminormedAddCommGroupH₀
  签名: : SeminormedAddComm群 (H₀ K)
  定义体: InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := 𝕜)

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toSeminormedAddCommGroup, toSeminormedAddCommGroup
-/
instance instSeminormedAddCommGroupH₀ : SeminormedAddCommGroup (H₀ K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := 𝕜)

/--
Instance `instInnerProductSpaceH₀` / 实例 `instInnerProductSpaceH₀`

English:
instance instInnerProductSpaceH₀
  signature: : InnerProductSpace 𝕜 (H₀ K)
  body: .ofCore _

中文:
实例 instInnerProductSpaceH₀
  签名: : 内积空间 𝕜 (H₀ K)
  定义体: .ofCore _

Depends on / 依赖: ofCore
-/
instance instInnerProductSpaceH₀ : InnerProductSpace 𝕜 (H₀ K) := .ofCore _

/--
lemma `inner_H₀_def` / 引理 `inner_H₀_def`

English:
lemma inner_H₀_def
  given: (f g : H₀ K)
  proof: rfl

中文:
引理 inner_H₀_def
  条件: (f g : H₀ K)
  证明: rfl
-/
private lemma inner_H₀_def (f g : H₀ K) :
    ⟪f, g⟫_𝕜 = f.sum fun ⟨y, u⟩ z => g.sum fun ⟨x, v⟩ w => star z * w * ⟪K x y u, v⟫_𝕜 := rfl

variable (K) in
/--
Definition of `OfKernel` / `OfKernel` 的定义

English:
abbreviation OfKernel
  body: UniformSpace.Completion (H₀ K)

中文:
缩写 OfKernel
  定义体: UniformSpace.Completion (H₀ K)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion
-/
abbrev OfKernel := UniformSpace.Completion (H₀ K)
--deriving SeminormedAddCommGroup, InnerProductSpace 𝕜, CompleteSpace

namespace OfKernel

/--
Definition of `kerFunAux` / `kerFunAux` 的定义

English:
abbreviation kerFunAux
  signature: (x : X)
  body: .coe' (.single ⟨x, v⟩ 1)
  map_add' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f => ?_
    simp [inner_add_left, inner_H₀_def, ← Finsupp.sum_add, ← mul_add]
  map_smul' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f => ?_


中文:
缩写 kerFunAux
  签名: (x : X)
  定义体: .coe' (.single ⟨x, v⟩ 1)
  map_add' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f => ?_
    simp [inner_add_left, inner_H₀_def, ← Finsupp.sum_add, ← mul_add]
  map_smul' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f => ?_

-/
private abbrev kerFunAux (x : X) : V ->ₗ[𝕜] UniformSpace.Completion (H₀ K) where
  toFun v := .coe' (.single ⟨x, v⟩ 1)
  map_add' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f => ?_
    simp [inner_add_left, inner_H₀_def, ← Finsupp.sum_add, ← mul_add]
  map_smul' _ _ := by
    refine UniformSpace.Completion.denseRange_coe.eq_of_inner_left 𝕜 fun f => ?_
    simp [inner_smul_left, inner_H₀_def, Finsupp.mul_sum, ← mul_assoc, mul_comm]

variable (K) in
/--
Definition of `kerFun` / `kerFun` 的定义

English:
abbreviation kerFun
  signature: (x : X)
  body: (kerFunAux x).mkContinuous √‖K x x‖ fun v => by
  refine (sq_le_sq₀ (by simp) (by simp [mul_nonneg])).mp ?_
  simp only [LinearMap.coe_mk, AddHom.coe_mk, UniformSpace.Completion.norm_coe,
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_re_eq_norm]
  simp only [inner_H₀_def, RCLike.star_def, mul_zer

中文:
缩写 kerFun
  签名: (x : X)
  定义体: (kerFunAux x).mkContinuous √‖K x x‖ fun v => by
  refine (sq_le_sq₀ (by simp) (by simp [mul_nonneg])).mp ?_
  simp only [LinearMap.coe_mk, AddHom.coe_mk, UniformSpace.Completion.norm_coe,
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_re_eq_norm]
  simp only [inner_H₀_def, RCLike.star_def, mul_zer
-/
private abbrev kerFun (x : X) :
    V ->L[𝕜] UniformSpace.Completion (H₀ K) := (kerFunAux x).mkContinuous √‖K x x‖ fun v => by
  refine (sq_le_sq₀ (by simp) (by simp [mul_nonneg])).mp ?_
  simp only [LinearMap.coe_mk, AddHom.coe_mk, UniformSpace.Completion.norm_coe,
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_self_re_eq_norm]
  simp only [inner_H₀_def, RCLike.star_def, mul_zero, zero_mul,
    Finsupp.sum_single_index, mul_one, map_zero, map_one, one_mul]
  calc
    _ <= ‖K x x v‖ * ‖v‖ := by simp [norm_inner_le_norm]
    _ <= ‖K x x‖ * ‖v‖ * ‖v‖ := by simp [mul_le_mul_of_nonneg_right, le_opNorm]
    _ <= _ := by simp [mul_pow, mul_assoc, ← sq]

@[no_expose]
/--
Instance `instRKHS` / 实例 `instRKHS`

English:
instance instRKHS
  signature: : RKHS 𝕜 (OfKernel K) X V where
  body: .pi fun x => (OfKernel.kerFun K x).adjoint
  coeCLM_injective := by
    refine (injective_iff_map_eq_zero _).mpr fun f h => ?_
    refine UniformSpace.Completion.denseRange_coe.eq_zero_of_inner_right 𝕜 fun ff => ?_
    induction ff using Finsupp.induction with
    | zero =>
      have : @UniformSpac

中文:
实例 instRKHS
  签名: : RKHS 𝕜 (OfKernel K) X V where
  定义体: .pi fun x => (OfKernel.kerFun K x).adjoint
  coeCLM_injective := by
    refine (injective_iff_map_eq_zero _).mpr fun f h => ?_
    refine UniformSpace.Completion.denseRange_coe.eq_zero_of_inner_right 𝕜 fun ff => ?_
    induction ff using Finsupp.induction with
    | zero =>
      have : @UniformSpac

Depends on / 依赖: OfKernel, OfKernel.kerFun, adjoint, kerFun
-/
instance instRKHS : RKHS 𝕜 (OfKernel K) X V where
  coeCLM := .pi fun x => (OfKernel.kerFun K x).adjoint
  coeCLM_injective := by
    refine (injective_iff_map_eq_zero _).mpr fun f h => ?_
    refine UniformSpace.Completion.denseRange_coe.eq_zero_of_inner_right 𝕜 fun ff => ?_
    induction ff using Finsupp.induction with
    | zero =>
      have : @UniformSpace.Completion.coe' (H₀ K) PseudoMetricSpace.toUniformSpace 0 = 0 := rfl
      simp [this]
    | single_add i a =>
    simp only [UniformSpace.Completion.coe_add, inner_add_left, *, add_zero]
    rw [← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜)]
    have := (ext_iff_inner_left 𝕜).mp (congrFun h i.1) i.2
    have := by simpa [OfKernel.kerFun, adjoint_inner_right] using this
    rw [← mul_zero (conj a)]; rw [← this]; rw [← inner_smul_left]
    refine (ext_iff_inner_right 𝕜).mp ?_ f
    simp [← UniformSpace.Completion.coe_toComplL (𝕜 := 𝕜),
      ← map_smul, -SeparationQuotient.mkCLM_apply, -UniformSpace.Completion.coe_toComplL]

/-- The kernel of the reproducing kernel Hilbert space
generated by a positive semidefinite matrix is the original positive semidefinite matrix.
-/
@[simp]
/--
theorem `kernel_ofKernel` / 定理 `kernel_ofKernel`

English:
theorem kernel_ofKernel
  statement: kernel (OfKernel K) = K
  proof: by
  ext x y v
  refine ext_inner_right 𝕜 fun w => ?_
  simp [kernel, adjoint_inner_left, -inner_kerFun, -kerFun_inner,
    coeCLM, OfKernel.kerFun, inner_H₀_def, RKHS.kerFun]

中文:
定理 kernel_ofKernel
  结论: kernel (OfKernel K) = K
  证明: by
  ext x y v
  refine ext_inner_right 𝕜 fun w => ?_
  simp [kernel, adjoint_inner_left, -inner_kerFun, -kerFun_inner,
    coeCLM, OfKernel.kerFun, inner_H₀_def, RKHS.kerFun]

Depends on / 依赖: OfKernel, OfKernel.kerFun, RKHS.kerFun, adjoint_inner_left, coeCLM, ext_inner_right, inner_kerFun, kerFun, kerFun_inner, kernel
-/
theorem kernel_ofKernel : kernel (OfKernel K) = K := by
  ext x y v
  refine ext_inner_right 𝕜 fun w => ?_
  simp [kernel, adjoint_inner_left, -inner_kerFun, -kerFun_inner,
    coeCLM, OfKernel.kerFun, inner_H₀_def, RKHS.kerFun]

end RKHS.OfKernel
