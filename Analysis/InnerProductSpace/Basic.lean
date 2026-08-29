/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Properties of inner product spaces

This file proves many basic properties of inner product spaces (real or complex).

## Main results

- `inner_mul_inner_self_le`: the Cauchy-Schwarz inequality (one of many variants).
- `norm_inner_eq_norm_iff`: the equality criterion in the Cauchy-Schwarz inequality (also in many
  variants).
- `inner_eq_sum_norm_sq_div_four`: the polarization identity.

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_re_inner)

@[simp]
/--
theorem `inner_conj_symm` / 定理 `inner_conj_symm`

English:
theorem inner_conj_symm
  given: (x y : E)
  statement: ⟪y, x⟫† = ⟪x, y⟫
  proof: InnerProductSpace.conj_inner_symm _ _

中文:
定理 inner_conj_symm
  条件: (x y : E)
  结论: ⟪y, x⟫† = ⟪x, y⟫
  证明: InnerProductSpace.conj_inner_symm _ _

Depends on / 依赖: InnerProductSpace, InnerProductSpace.conj_inner_symm, conj_inner_symm
-/
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_inner_symm _ _

/--
theorem `real_inner_comm` / 定理 `real_inner_comm`

English:
theorem real_inner_comm
  given: (x y : F)
  statement: ⟪y, x⟫_Real = ⟪x, y⟫_Real
  proof: @inner_conj_symm Real _ _ _ _ x y

中文:
定理 real_inner_comm
  条件: (x y : F)
  结论: ⟪y, x⟫_实数 = ⟪x, y⟫_实数
  证明: @inner_conj_symm Real _ _ _ _ x y

Depends on / 依赖: inner_conj_symm
-/
theorem real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real :=
  @inner_conj_symm Real _ _ _ _ x y

/--
theorem `inner_eq_zero_symm` / 定理 `inner_eq_zero_symm`

English:
theorem inner_eq_zero_symm
  given: {x y : E}
  statement: ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0
  proof: by
  rw [← inner_conj_symm]
  exact star_eq_zero

中文:
定理 inner_eq_zero_symm
  条件: {x y : E}
  结论: ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0
  证明: by
  rw [← inner_conj_symm]
  exact star_eq_zero

Depends on / 依赖: inner_conj_symm, star_eq_zero
-/
theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

instance {ι : Sort*} (v : ι -> E) : Std.Symm fun i j => ⟪v i, v j⟫ = 0 where
  symm _ _ := inner_eq_zero_symm.1

/--
theorem `inner_self_im` / 定理 `inner_self_im`

English:
theorem inner_self_im
  given: (x : E)
  statement: im ⟪x, x⟫ = 0
  proof: by
  rw [← @ofReal_inj 𝕜]; rw [im_eq_conj_sub]; simp

中文:
定理 inner_self_im
  条件: (x : E)
  结论: im ⟪x, x⟫ = 0
  证明: by
  rw [← @ofReal_inj 𝕜]; rw [im_eq_conj_sub]; simp

Depends on / 依赖: im_eq_conj_sub, ofReal_inj
-/
theorem inner_self_im (x : E) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜]; rw [im_eq_conj_sub]; simp

/--
theorem `inner_add_left` / 定理 `inner_add_left`

English:
theorem inner_add_left
  given: (x y z : E)
  statement: ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  proof: InnerProductSpace.add_left _ _ _

中文:
定理 inner_add_left
  条件: (x y z : E)
  结论: ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  证明: InnerProductSpace.add_left _ _ _

Depends on / 依赖: InnerProductSpace, InnerProductSpace.add_left, add_left
-/
theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _

/--
theorem `inner_add_right` / 定理 `inner_add_right`

English:
theorem inner_add_right
  given: (x y z : E)
  statement: ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
  proof: by
  rw [← inner_conj_symm]; rw [inner_add_left]; rw [map_add]
  simp only [inner_conj_symm]

中文:
定理 inner_add_right
  条件: (x y z : E)
  结论: ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫
  证明: by
  rw [← inner_conj_symm]; rw [inner_add_left]; rw [map_add]
  simp only [inner_conj_symm]

Depends on / 依赖: inner_add_left, inner_conj_symm, map_add
-/
theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm]; rw [inner_add_left]; rw [map_add]
  simp only [inner_conj_symm]

/--
theorem `inner_re_symm` / 定理 `inner_re_symm`

English:
theorem inner_re_symm
  given: (x y : E)
  statement: re ⟪x, y⟫ = re ⟪y, x⟫
  proof: by rw [← inner_conj_symm, conj_re]

中文:
定理 inner_re_symm
  条件: (x y : E)
  结论: re ⟪x, y⟫ = re ⟪y, x⟫
  证明: by rw [← inner_conj_symm, conj_re]

Depends on / 依赖: conj_re, inner_conj_symm
-/
theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

/--
theorem `inner_im_symm` / 定理 `inner_im_symm`

English:
theorem inner_im_symm
  given: (x y : E)
  statement: im ⟪x, y⟫ = -im ⟪y, x⟫
  proof: by rw [← inner_conj_symm, conj_im]

中文:
定理 inner_im_symm
  条件: (x y : E)
  结论: im ⟪x, y⟫ = -im ⟪y, x⟫
  证明: by rw [← inner_conj_symm, conj_im]

Depends on / 依赖: conj_im, inner_conj_symm
-/
theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

section Algebra
variable {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [Module 𝕝 E]
  [IsScalarTower 𝕝 𝕜 E] [StarModule 𝕝 𝕜]

/--
lemma `inner_smul_left_eq_star_smul` / 引理 `inner_smul_left_eq_star_smul`

English:
lemma inner_smul_left_eq_star_smul
  given: (x y : E) (r : 𝕝)
  statement: ⟪r • x, y⟫ = r† • ⟪x, y⟫
  proof: by
  rw [← algebraMap_smul 𝕜 r]; rw [InnerProductSpace.smul_left]; rw [starRingEnd_apply]; rw [starRingEnd_apply]; rw [← algebraMap_star_comm]; rw [← smul_eq_mul]; rw [algebraMap_smul]

中文:
引理 inner_smul_left_eq_star_smul
  条件: (x y : E) (r : 𝕝)
  结论: ⟪r • x, y⟫ = r† • ⟪x, y⟫
  证明: by
  rw [← algebraMap_smul 𝕜 r]; rw [InnerProductSpace.smul_left]; rw [starRingEnd_apply]; rw [starRingEnd_apply]; rw [← algebraMap_star_comm]; rw [← smul_eq_mul]; rw [algebraMap_smul]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.smul_left, algebraMap_smul, algebraMap_star_comm, smul_eq_mul, smul_left, starRingEnd_apply
-/
lemma inner_smul_left_eq_star_smul (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫ := by
  rw [← algebraMap_smul 𝕜 r]; rw [InnerProductSpace.smul_left]; rw [starRingEnd_apply]; rw [starRingEnd_apply]; rw [← algebraMap_star_comm]; rw [← smul_eq_mul]; rw [algebraMap_smul]

/--
lemma `inner_smul_left_eq_smul` / 引理 `inner_smul_left_eq_smul`

English:
lemma inner_smul_left_eq_smul
  given: [TrivialStar 𝕝] (x y : E) (r : 𝕝)
  statement: ⟪r • x, y⟫ = r • ⟪x, y⟫
  proof: by
  rw [inner_smul_left_eq_star_smul]; rw [starRingEnd_apply]; rw [star_trivial]

中文:
引理 inner_smul_left_eq_smul
  条件: [TrivialStar 𝕝] (x y : E) (r : 𝕝)
  结论: ⟪r • x, y⟫ = r • ⟪x, y⟫
  证明: by
  rw [inner_smul_left_eq_star_smul]; rw [starRingEnd_apply]; rw [star_trivial]

Depends on / 依赖: inner_smul_left_eq_star_smul, starRingEnd_apply, star_trivial
-/
lemma inner_smul_left_eq_smul [TrivialStar 𝕝] (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left_eq_star_smul]; rw [starRingEnd_apply]; rw [star_trivial]

/--
lemma `inner_smul_right_eq_smul` / 引理 `inner_smul_right_eq_smul`

English:
lemma inner_smul_right_eq_smul
  given: (x y : E) (r : 𝕝)
  statement: ⟪x, r • y⟫ = r • ⟪x, y⟫
  proof: by
  rw [← inner_conj_symm]; rw [inner_smul_left_eq_star_smul]; rw [starRingEnd_apply]; rw [starRingEnd_apply]; rw [star_smul]; rw [star_star]; rw [← starRingEnd_apply]; rw [inner_conj_symm]

中文:
引理 inner_smul_right_eq_smul
  条件: (x y : E) (r : 𝕝)
  结论: ⟪x, r • y⟫ = r • ⟪x, y⟫
  证明: by
  rw [← inner_conj_symm]; rw [inner_smul_left_eq_star_smul]; rw [starRingEnd_apply]; rw [starRingEnd_apply]; rw [star_smul]; rw [star_star]; rw [← starRingEnd_apply]; rw [inner_conj_symm]

Depends on / 依赖: inner_conj_symm, inner_smul_left_eq_star_smul, starRingEnd_apply, star_smul, star_star
-/
lemma inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪x, r • y⟫ = r • ⟪x, y⟫ := by
  rw [← inner_conj_symm]; rw [inner_smul_left_eq_star_smul]; rw [starRingEnd_apply]; rw [starRingEnd_apply]; rw [star_smul]; rw [star_star]; rw [← starRingEnd_apply]; rw [inner_conj_symm]

end Algebra

/--
theorem `inner_smul_left` / 定理 `inner_smul_left`

English:
theorem inner_smul_left
  given: (x y : E) (r : 𝕜)
  statement: ⟪r • x, y⟫ = r† * ⟪x, y⟫
  proof: inner_smul_left_eq_star_smul ..

中文:
定理 inner_smul_left
  条件: (x y : E) (r : 𝕜)
  结论: ⟪r • x, y⟫ = r† * ⟪x, y⟫
  证明: inner_smul_left_eq_star_smul ..

Depends on / 依赖: inner_smul_left_eq_star_smul
-/
theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left_eq_star_smul ..

/--
theorem `real_inner_smul_left` / 定理 `real_inner_smul_left`

English:
theorem real_inner_smul_left
  given: (x y : F) (r : Real)
  statement: ⟪r • x, y⟫_Real = r * ⟪x, y⟫_Real
  proof: inner_smul_left _ _ _

中文:
定理 real_inner_smul_left
  条件: (x y : F) (r : 实数)
  结论: ⟪r • x, y⟫_实数 = r * ⟪x, y⟫_实数
  证明: inner_smul_left _ _ _

Depends on / 依赖: inner_smul_left
-/
theorem real_inner_smul_left (x y : F) (r : Real) : ⟪r • x, y⟫_Real = r * ⟪x, y⟫_Real :=
  inner_smul_left _ _ _

/--
theorem `inner_smul_real_left` / 定理 `inner_smul_real_left`

English:
theorem inner_smul_real_left
  given: (x y : E) (r : Real)
  statement: ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫
  proof: by
  rw [inner_smul_left]; rw [conj_ofReal]; rw [Algebra.smul_def]

中文:
定理 inner_smul_real_left
  条件: (x y : E) (r : 实数)
  结论: ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫
  证明: by
  rw [inner_smul_left]; rw [conj_ofReal]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, conj_ofReal, inner_smul_left, smul_def
-/
theorem inner_smul_real_left (x y : E) (r : Real) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left]; rw [conj_ofReal]; rw [Algebra.smul_def]

/--
theorem `inner_smul_right` / 定理 `inner_smul_right`

English:
theorem inner_smul_right
  given: (x y : E) (r : 𝕜)
  statement: ⟪x, r • y⟫ = r * ⟪x, y⟫
  proof: inner_smul_right_eq_smul ..

中文:
定理 inner_smul_right
  条件: (x y : E) (r : 𝕜)
  结论: ⟪x, r • y⟫ = r * ⟪x, y⟫
  证明: inner_smul_right_eq_smul ..

Depends on / 依赖: inner_smul_right_eq_smul
-/
theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right_eq_smul ..

/--
theorem `real_inner_smul_right` / 定理 `real_inner_smul_right`

English:
theorem real_inner_smul_right
  given: (x y : F) (r : Real)
  statement: ⟪x, r • y⟫_Real = r * ⟪x, y⟫_Real
  proof: inner_smul_right _ _ _

中文:
定理 real_inner_smul_right
  条件: (x y : F) (r : 实数)
  结论: ⟪x, r • y⟫_实数 = r * ⟪x, y⟫_实数
  证明: inner_smul_right _ _ _

Depends on / 依赖: inner_smul_right
-/
theorem real_inner_smul_right (x y : F) (r : Real) : ⟪x, r • y⟫_Real = r * ⟪x, y⟫_Real :=
  inner_smul_right _ _ _

/--
theorem `inner_smul_real_right` / 定理 `inner_smul_real_right`

English:
theorem inner_smul_real_right
  given: (x y : E) (r : Real)
  statement: ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫
  proof: by
  rw [inner_smul_right]; rw [Algebra.smul_def]

中文:
定理 inner_smul_real_right
  条件: (x y : E) (r : 实数)
  结论: ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫
  证明: by
  rw [inner_smul_right]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, inner_smul_right, smul_def
-/
theorem inner_smul_real_right (x y : E) (r : Real) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right]; rw [Algebra.smul_def]


variable (𝕜)

/--
Definition of `innerₛₗ` / `innerₛₗ` 的定义

English:
definition innerₛₗ
  signature: : E ->ₗ⋆[𝕜] E ->ₗ[𝕜] 𝕜
  body: LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]

中文:
定义 innerₛₗ
  签名: : E ->ₗ⋆[𝕜] E ->ₗ[𝕜] 𝕜
  定义体: LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mk, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right
-/
def innerₛₗ : E ->ₗ⋆[𝕜] E ->ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]
/--
theorem `coe_innerₛₗ_apply` / 定理 `coe_innerₛₗ_apply`

English:
theorem coe_innerₛₗ_apply
  given: (v : E)
  statement: ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫
  proof: rfl

@[simp]

中文:
定理 coe_innerₛₗ_apply
  条件: (v : E)
  结论: ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫
  证明: rfl

@[simp]
-/
theorem coe_innerₛₗ_apply (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
/--
theorem `innerₛₗ_apply_apply` / 定理 `innerₛₗ_apply_apply`

English:
theorem innerₛₗ_apply_apply
  given: (v w : E)
  statement: innerₛₗ 𝕜 v w = ⟪v, w⟫
  proof: rfl

中文:
定理 innerₛₗ_apply_apply
  条件: (v w : E)
  结论: innerₛₗ 𝕜 v w = ⟪v, w⟫
  证明: rfl
-/
theorem innerₛₗ_apply_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl

variable (F)
/--
Definition of `innerₗ` / `innerₗ` 的定义

English:
definition innerₗ
  signature: : F ->ₗ[Real] F ->ₗ[Real] Real
  body: innerₛₗ Real

中文:
定义 innerₗ
  签名: : F ->ₗ[实数] F ->ₗ[实数] 实数
  定义体: innerₛₗ Real
-/
def innerₗ : F ->ₗ[Real] F ->ₗ[Real] Real := innerₛₗ Real

/--
lemma `flip_innerₗ` / 引理 `flip_innerₗ`

English:
lemma flip_innerₗ
  statement: (innerₗ F).flip = innerₗ F
  proof: by
  ext v w
  exact real_inner_comm v w

中文:
引理 flip_innerₗ
  结论: (innerₗ F).flip = innerₗ F
  证明: by
  ext v w
  exact real_inner_comm v w
-/
@[simp] lemma flip_innerₗ : (innerₗ F).flip = innerₗ F := by
  ext v w
  exact real_inner_comm v w

variable {F}

/--
lemma `innerₗ_apply_apply` / 引理 `innerₗ_apply_apply`

English:
lemma innerₗ_apply_apply
  given: (v w : F)
  statement: innerₗ F v w = ⟪v, w⟫_Real
  proof: rfl

中文:
引理 innerₗ_apply_apply
  条件: (v w : F)
  结论: innerₗ F v w = ⟪v, w⟫_实数
  证明: rfl
-/
@[simp] lemma innerₗ_apply_apply (v w : F) : innerₗ F v w = ⟪v, w⟫_Real := rfl

variable {𝕜}

/--
theorem `sum_inner` / 定理 `sum_inner`

English:
theorem sum_inner
  given: {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E)
  proof: map_sum ((innerₛₗ 𝕜).flip x) _ _

中文:
定理 sum_inner
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> E) (x : E)
  证明: map_sum ((innerₛₗ 𝕜).flip x) _ _

Depends on / 依赖: map_sum
-/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) :
    ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
  map_sum ((innerₛₗ 𝕜).flip x) _ _

/--
theorem `inner_sum` / 定理 `inner_sum`

English:
theorem inner_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E)
  proof: map_sum (innerₛₗ 𝕜 x) _ _

中文:
定理 inner_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> E) (x : E)
  证明: map_sum (innerₛₗ 𝕜 x) _ _

Depends on / 依赖: map_sum
-/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) :
    ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
  map_sum (innerₛₗ 𝕜 x) _ _

/--
theorem `Finsupp.sum_inner` / 定理 `Finsupp.sum_inner`

English:
theorem Finsupp.sum_inner
  statement: {ι : Type*} {M : Type*} [Zero M] (l : ι ->₀ M)
  proof: by
  simp [sum, sum_inner]

中文:
定理 有限支撑.sum_inner
  结论: {ι : 类型} {M : 类型} [零 M] (l : ι ->₀ M)
  证明: by
  simp [sum, sum_inner]
-/
protected theorem Finsupp.sum_inner {ι : Type*} {M : Type*} [Zero M] (l : ι ->₀ M)
    (v : ι -> M -> E) (x : E) : ⟪l.sum v, x⟫ = l.sum fun (i : ι) (a : M) => ⟪v i a, x⟫ := by
  simp [sum, sum_inner]

/--
theorem `Finsupp.inner_sum` / 定理 `Finsupp.inner_sum`

English:
theorem Finsupp.inner_sum
  statement: {ι : Type*} {M : Type*} [Zero M] (l : ι ->₀ M)
  proof: by
  simp [sum, inner_sum]

中文:
定理 有限支撑.inner_sum
  结论: {ι : 类型} {M : 类型} [零 M] (l : ι ->₀ M)
  证明: by
  simp [sum, inner_sum]
-/
protected theorem Finsupp.inner_sum {ι : Type*} {M : Type*} [Zero M] (l : ι ->₀ M)
    (v : ι -> M -> E) (x : E) : ⟪x, l.sum v⟫ = l.sum fun (i : ι) (a : M) => ⟪x, v i a⟫ := by
  simp [sum, inner_sum]

/--
theorem `DFinsupp.sum_inner` / 定理 `DFinsupp.sum_inner`

English:
theorem DFinsupp.sum_inner
  statement: {ι : Type*} [DecidableEq ι] {α : ι -> Type*}
  proof: by
  simp +contextual only [DFinsupp.sum, sum_inner]

中文:
定理 直和有限支撑.sum_inner
  结论: {ι : 类型} [DecidableEq ι] {α : ι -> 类型}
  证明: by
  simp +contextual only [DFinsupp.sum, sum_inner]
-/
protected theorem DFinsupp.sum_inner {ι : Type*} [DecidableEq ι] {α : ι -> Type*}
    [forall i, AddZeroClass (α i)] [forall (i) (x : α i), Decidable (x != 0)] (f : forall i, α i -> E)
    (l : Π₀ i, α i) (x : E) : ⟪l.sum f, x⟫ = l.sum fun i a => ⟪f i a, x⟫ := by
  simp +contextual only [DFinsupp.sum, sum_inner]

/--
theorem `DFinsupp.inner_sum` / 定理 `DFinsupp.inner_sum`

English:
theorem DFinsupp.inner_sum
  statement: {ι : Type*} [DecidableEq ι] {α : ι -> Type*}
  proof: by
  simp +contextual only [DFinsupp.sum, inner_sum]

@[simp]

中文:
定理 直和有限支撑.inner_sum
  结论: {ι : 类型} [DecidableEq ι] {α : ι -> 类型}
  证明: by
  simp +contextual only [DFinsupp.sum, inner_sum]

@[simp]
-/
protected theorem DFinsupp.inner_sum {ι : Type*} [DecidableEq ι] {α : ι -> Type*}
    [forall i, AddZeroClass (α i)] [forall (i) (x : α i), Decidable (x != 0)] (f : forall i, α i -> E)
    (l : Π₀ i, α i) (x : E) : ⟪x, l.sum f⟫ = l.sum fun i a => ⟪x, f i a⟫ := by
  simp +contextual only [DFinsupp.sum, inner_sum]

@[simp]
/--
theorem `inner_zero_left` / 定理 `inner_zero_left`

English:
theorem inner_zero_left
  given: (x : E)
  statement: ⟪0, x⟫ = 0
  proof: by
  rw [← zero_smul 𝕜 (0 : E)]; rw [inner_smul_left]; rw [map_zero]; rw [zero_mul]

中文:
定理 inner_zero_left
  条件: (x : E)
  结论: ⟪0, x⟫ = 0
  证明: by
  rw [← zero_smul 𝕜 (0 : E)]; rw [inner_smul_left]; rw [map_zero]; rw [zero_mul]

Depends on / 依赖: inner_smul_left, map_zero, zero_mul, zero_smul
-/
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E)]; rw [inner_smul_left]; rw [map_zero]; rw [zero_mul]

/--
theorem `inner_re_zero_left` / 定理 `inner_re_zero_left`

English:
theorem inner_re_zero_left
  given: (x : E)
  statement: re ⟪0, x⟫ = 0
  proof: by
  simp only [inner_zero_left, map_zero]

@[simp]

中文:
定理 inner_re_zero_left
  条件: (x : E)
  结论: re ⟪0, x⟫ = 0
  证明: by
  simp only [inner_zero_left, map_zero]

@[simp]

Depends on / 依赖: inner_zero_left, map_zero
-/
theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, map_zero]

@[simp]
/--
theorem `inner_zero_right` / 定理 `inner_zero_right`

English:
theorem inner_zero_right
  given: (x : E)
  statement: ⟪x, 0⟫ = 0
  proof: by
  rw [← inner_conj_symm]; rw [inner_zero_left]; rw [map_zero]

中文:
定理 inner_zero_right
  条件: (x : E)
  结论: ⟪x, 0⟫ = 0
  证明: by
  rw [← inner_conj_symm]; rw [inner_zero_left]; rw [map_zero]

Depends on / 依赖: inner_conj_symm, inner_zero_left, map_zero
-/
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm]; rw [inner_zero_left]; rw [map_zero]

/--
theorem `inner_re_zero_right` / 定理 `inner_re_zero_right`

English:
theorem inner_re_zero_right
  given: (x : E)
  statement: re ⟪x, 0⟫ = 0
  proof: by
  simp only [inner_zero_right, map_zero]

中文:
定理 inner_re_zero_right
  条件: (x : E)
  结论: re ⟪x, 0⟫ = 0
  证明: by
  simp only [inner_zero_right, map_zero]

Depends on / 依赖: inner_zero_right, map_zero
-/
theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, map_zero]

/--
theorem `inner_self_nonneg` / 定理 `inner_self_nonneg`

English:
theorem inner_self_nonneg
  given: {x : E}
  statement: 0 <= re ⟪x, x⟫
  proof: PreInnerProductSpace.toCore.re_inner_nonneg x

中文:
定理 inner_self_nonneg
  条件: {x : E}
  结论: 0 <= re ⟪x, x⟫
  证明: PreInnerProductSpace.toCore.re_inner_nonneg x

Depends on / 依赖: PreInnerProductSpace, PreInnerProductSpace.toCore.re_inner_nonneg, re_inner_nonneg, toCore
-/
theorem inner_self_nonneg {x : E} : 0 <= re ⟪x, x⟫ :=
  PreInnerProductSpace.toCore.re_inner_nonneg x

/--
theorem `real_inner_self_nonneg` / 定理 `real_inner_self_nonneg`

English:
theorem real_inner_self_nonneg
  given: {x : F}
  statement: 0 <= ⟪x, x⟫_Real
  proof: @inner_self_nonneg Real F _ _ _ x

中文:
定理 real_inner_self_nonneg
  条件: {x : F}
  结论: 0 <= ⟪x, x⟫_实数
  证明: @inner_self_nonneg Real F _ _ _ x

Depends on / 依赖: inner_self_nonneg
-/
theorem real_inner_self_nonneg {x : F} : 0 <= ⟪x, x⟫_Real :=
  @inner_self_nonneg Real F _ _ _ x

/--
theorem `inner_self_ofReal_re` / 定理 `inner_self_ofReal_re`

English:
theorem inner_self_ofReal_re
  given: (x : E)
  statement: (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫
  proof: ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im (𝕜 := 𝕜) x)

@[simp]

中文:
定理 inner_self_of实数_re
  条件: (x : E)
  结论: (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫
  证明: ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im (𝕜 := 𝕜) x)

@[simp]

Depends on / 依赖: RCLike, RCLike.is_real_TFAE, inner_self_im, is_real_TFAE
-/
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im (𝕜 := 𝕜) x)

@[simp]
/--
theorem `inner_self_eq_norm_sq_to_K` / 定理 `inner_self_eq_norm_sq_to_K`

English:
theorem inner_self_eq_norm_sq_to_K
  given: (x : E)
  statement: ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2
  proof: by
  rw [← inner_self_ofReal_re]; rw [← norm_sq_eq_re_inner]; rw [ofReal_pow]

中文:
定理 inner_self_eq_norm_sq_to_K
  条件: (x : E)
  结论: ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2
  证明: by
  rw [← inner_self_ofReal_re]; rw [← norm_sq_eq_re_inner]; rw [ofReal_pow]

Depends on / 依赖: inner_self_ofReal_re, norm_sq_eq_re_inner, ofReal_pow
-/
theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2 := by
  rw [← inner_self_ofReal_re]; rw [← norm_sq_eq_re_inner]; rw [ofReal_pow]

/--
theorem `inner_self_re_eq_norm` / 定理 `inner_self_re_eq_norm`

English:
theorem inner_self_re_eq_norm
  given: (x : E)
  statement: re ⟪x, x⟫ = ‖⟪x, x⟫‖
  proof: by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg

中文:
定理 inner_self_re_eq_norm
  条件: (x : E)
  结论: re ⟪x, x⟫ = ‖⟪x, x⟫‖
  证明: by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg

Depends on / 依赖: conv_rhs, inner_self_nonneg, inner_self_ofReal_re, norm_of_nonneg
-/
theorem inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖ := by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg

/--
theorem `inner_self_ofReal_norm` / 定理 `inner_self_ofReal_norm`

English:
theorem inner_self_ofReal_norm
  given: (x : E)
  statement: (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫
  proof: by
  rw [← inner_self_re_eq_norm]
  exact inner_self_ofReal_re _

中文:
定理 inner_self_of实数_norm
  条件: (x : E)
  结论: (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫
  证明: by
  rw [← inner_self_re_eq_norm]
  exact inner_self_ofReal_re _

Depends on / 依赖: inner_self_ofReal_re, inner_self_re_eq_norm
-/
theorem inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫ := by
  rw [← inner_self_re_eq_norm]
  exact inner_self_ofReal_re _

/--
theorem `real_inner_self_abs` / 定理 `real_inner_self_abs`

English:
theorem real_inner_self_abs
  given: (x : F)
  statement: |⟪x, x⟫_Real| = ⟪x, x⟫_Real
  proof: @inner_self_ofReal_norm Real F _ _ _ x

中文:
定理 real_inner_self_abs
  条件: (x : F)
  结论: |⟪x, x⟫_实数| = ⟪x, x⟫_实数
  证明: @inner_self_ofReal_norm Real F _ _ _ x

Depends on / 依赖: inner_self_ofReal_norm
-/
theorem real_inner_self_abs (x : F) : |⟪x, x⟫_Real| = ⟪x, x⟫_Real :=
  @inner_self_ofReal_norm Real F _ _ _ x

/--
theorem `norm_inner_symm` / 定理 `norm_inner_symm`

English:
theorem norm_inner_symm
  given: (x y : E)
  statement: ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖
  proof: by rw [← inner_conj_symm, norm_conj]

@[simp]

中文:
定理 norm_inner_symm
  条件: (x y : E)
  结论: ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖
  证明: by rw [← inner_conj_symm, norm_conj]

@[simp]

Depends on / 依赖: inner_conj_symm, norm_conj
-/
theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

@[simp]
/--
theorem `inner_neg_left` / 定理 `inner_neg_left`

English:
theorem inner_neg_left
  given: (x y : E)
  statement: ⟪-x, y⟫ = -⟪x, y⟫
  proof: by
  rw [← neg_one_smul 𝕜 x]; rw [inner_smul_left]
  simp

@[simp]

中文:
定理 inner_neg_left
  条件: (x y : E)
  结论: ⟪-x, y⟫ = -⟪x, y⟫
  证明: by
  rw [← neg_one_smul 𝕜 x]; rw [inner_smul_left]
  simp

@[simp]

Depends on / 依赖: inner_smul_left, neg_one_smul
-/
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x]; rw [inner_smul_left]
  simp

@[simp]
/--
theorem `inner_neg_right` / 定理 `inner_neg_right`

English:
theorem inner_neg_right
  given: (x y : E)
  statement: ⟪x, -y⟫ = -⟪x, y⟫
  proof: by
  rw [← inner_conj_symm]; rw [inner_neg_left]; simp only [map_neg, inner_conj_symm]

中文:
定理 inner_neg_right
  条件: (x y : E)
  结论: ⟪x, -y⟫ = -⟪x, y⟫
  证明: by
  rw [← inner_conj_symm]; rw [inner_neg_left]; simp only [map_neg, inner_conj_symm]

Depends on / 依赖: inner_conj_symm, inner_neg_left, map_neg
-/
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm]; rw [inner_neg_left]; simp only [map_neg, inner_conj_symm]

/--
theorem `inner_neg_neg` / 定理 `inner_neg_neg`

English:
theorem inner_neg_neg
  given: (x y : E)
  statement: ⟪-x, -y⟫ = ⟪x, y⟫
  proof: by simp

中文:
定理 inner_neg_neg
  条件: (x y : E)
  结论: ⟪-x, -y⟫ = ⟪x, y⟫
  证明: by simp
-/
theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

/--
theorem `inner_self_conj` / 定理 `inner_self_conj`

English:
theorem inner_self_conj
  given: (x : E)
  statement: ⟪x, x⟫† = ⟪x, x⟫
  proof: inner_conj_symm _ _

中文:
定理 inner_self_conj
  条件: (x : E)
  结论: ⟪x, x⟫† = ⟪x, x⟫
  证明: inner_conj_symm _ _

Depends on / 依赖: inner_conj_symm
-/
theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _

/--
theorem `inner_sub_left` / 定理 `inner_sub_left`

English:
theorem inner_sub_left
  given: (x y z : E)
  statement: ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
  proof: by
  simp [sub_eq_add_neg, inner_add_left]

中文:
定理 inner_sub_left
  条件: (x y z : E)
  结论: ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫
  证明: by
  simp [sub_eq_add_neg, inner_add_left]

Depends on / 依赖: inner_add_left, sub_eq_add_neg
-/
theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

/--
theorem `inner_sub_right` / 定理 `inner_sub_right`

English:
theorem inner_sub_right
  given: (x y z : E)
  statement: ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
  proof: by
  simp [sub_eq_add_neg, inner_add_right]

中文:
定理 inner_sub_right
  条件: (x y z : E)
  结论: ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫
  证明: by
  simp [sub_eq_add_neg, inner_add_right]

Depends on / 依赖: inner_add_right, sub_eq_add_neg
-/
theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

/--
theorem `inner_mul_symm_re_eq_norm` / 定理 `inner_mul_symm_re_eq_norm`

English:
theorem inner_mul_symm_re_eq_norm
  given: (x y : E)
  statement: re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖
  proof: by
  rw [← inner_conj_symm]; rw [mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

中文:
定理 inner_mul_symm_re_eq_norm
  条件: (x y : E)
  结论: re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖
  证明: by
  rw [← inner_conj_symm]; rw [mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

Depends on / 依赖: inner_conj_symm, mul_comm, re_eq_norm_of_mul_conj
-/
theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm]; rw [mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

/--
theorem `inner_add_add_self` / 定理 `inner_add_add_self`

English:
theorem inner_add_add_self
  given: (x y : E)
  statement: ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
  proof: by
  simp only [inner_add_left, inner_add_right]; ring

中文:
定理 inner_add_add_self
  条件: (x y : E)
  结论: ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫
  证明: by
  simp only [inner_add_left, inner_add_right]; ring

Depends on / 依赖: inner_add_left, inner_add_right
-/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

/--
theorem `real_inner_add_add_self` / 定理 `real_inner_add_add_self`

English:
theorem real_inner_add_add_self
  given: (x y : F)
  proof: by
  have : ⟪y, x⟫_Real = ⟪x, y⟫_Real := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

中文:
定理 real_inner_add_add_self
  条件: (x y : F)
  证明: by
  have : ⟪y, x⟫_Real = ⟪x, y⟫_Real := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

Depends on / 依赖: _Real, add_left_inj, inner_add_add_self, inner_conj_symm
-/
theorem real_inner_add_add_self (x y : F) :
    ⟪x + y, x + y⟫_Real = ⟪x, x⟫_Real + 2 * ⟪x, y⟫_Real + ⟪y, y⟫_Real := by
  have : ⟪y, x⟫_Real = ⟪x, y⟫_Real := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

-- Expand `⟪x - y, x - y⟫`
/--
theorem `inner_sub_sub_self` / 定理 `inner_sub_sub_self`

English:
theorem inner_sub_sub_self
  given: (x y : E)
  statement: ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
  proof: by
  simp only [inner_sub_left, inner_sub_right]; ring

中文:
定理 inner_sub_sub_self
  条件: (x y : E)
  结论: ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫
  证明: by
  simp only [inner_sub_left, inner_sub_right]; ring

Depends on / 依赖: inner_sub_left, inner_sub_right
-/
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/--
theorem `real_inner_sub_sub_self` / 定理 `real_inner_sub_sub_self`

English:
theorem real_inner_sub_sub_self
  given: (x y : F)
  proof: by
  have : ⟪y, x⟫_Real = ⟪x, y⟫_Real := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

中文:
定理 real_inner_sub_sub_self
  条件: (x y : F)
  证明: by
  have : ⟪y, x⟫_Real = ⟪x, y⟫_Real := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

Depends on / 依赖: _Real, add_left_inj, inner_conj_symm, inner_sub_sub_self
-/
theorem real_inner_sub_sub_self (x y : F) :
    ⟪x - y, x - y⟫_Real = ⟪x, x⟫_Real - 2 * ⟪x, y⟫_Real + ⟪y, y⟫_Real := by
  have : ⟪y, x⟫_Real = ⟪x, y⟫_Real := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

/--
theorem `parallelogram_law` / 定理 `parallelogram_law`

English:
theorem parallelogram_law
  given: {x y : E}
  statement: ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫)
  proof: by
  simp only [inner_add_add_self, inner_sub_sub_self]
  ring

中文:
定理 parallelogram_law
  条件: {x y : E}
  结论: ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫)
  证明: by
  simp only [inner_add_add_self, inner_sub_sub_self]
  ring

Depends on / 依赖: inner_add_add_self, inner_sub_sub_self
-/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp only [inner_add_add_self, inner_sub_sub_self]
  ring

/-- **Cauchy–Schwarz inequality**. -/
@[wikidata Q190546]
/--
theorem `inner_mul_inner_self_le` / 定理 `inner_mul_inner_self_le`

English:
theorem inner_mul_inner_self_le
  given: (x y : E)
  statement: ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫
  proof: letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

中文:
定理 inner_mul_inner_self_le
  条件: (x y : E)
  结论: ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫
  证明: letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.inner_mul_inner_self_le, PreInnerProductSpace, PreInnerProductSpace.Core, PreInnerProductSpace.toCore, inner_mul_inner_self_le, toCore
-/
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ <= re ⟪x, x⟫ * re ⟪y, y⟫ :=
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

/--
theorem `real_inner_mul_inner_self_le` / 定理 `real_inner_mul_inner_self_le`

English:
theorem real_inner_mul_inner_self_le
  given: (x y : F)
  statement: ⟪x, y⟫_Real * ⟪x, y⟫_Real <= ⟪x, x⟫_Real * ⟪y, y⟫_Real
  proof: calc
    ⟪x, y⟫_Real * ⟪x, y⟫_Real <= ‖⟪x, y⟫_Real‖ * ‖⟪y, x⟫_Real‖ := by
      rw [real_inner_comm y]; rw [← norm_mul]
      exact le_abs_self _
    _ <= ⟪x, x⟫_Real * ⟪y, y⟫_Real := @inner_mul_inner_self_le Real _ _ _ _ x y

中文:
定理 real_inner_mul_inner_self_le
  条件: (x y : F)
  结论: ⟪x, y⟫_实数 * ⟪x, y⟫_实数 <= ⟪x, x⟫_实数 * ⟪y, y⟫_实数
  证明: calc
    ⟪x, y⟫_Real * ⟪x, y⟫_Real <= ‖⟪x, y⟫_Real‖ * ‖⟪y, x⟫_Real‖ := by
      rw [real_inner_comm y]; rw [← norm_mul]
      exact le_abs_self _
    _ <= ⟪x, x⟫_Real * ⟪y, y⟫_Real := @inner_mul_inner_self_le Real _ _ _ _ x y

Depends on / 依赖: _Real, inner_mul_inner_self_le, le_abs_self, norm_mul, real_inner_comm
-/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_Real * ⟪x, y⟫_Real <= ⟪x, x⟫_Real * ⟪y, y⟫_Real :=
  calc
    ⟪x, y⟫_Real * ⟪x, y⟫_Real <= ‖⟪x, y⟫_Real‖ * ‖⟪y, x⟫_Real‖ := by
      rw [real_inner_comm y]; rw [← norm_mul]
      exact le_abs_self _
    _ <= ⟪x, x⟫_Real * ⟪y, y⟫_Real := @inner_mul_inner_self_le Real _ _ _ _ x y

/--
theorem `inner_eq_ofReal_norm_sq_left_iff` / 定理 `inner_eq_ofReal_norm_sq_left_iff`

English:
theorem inner_eq_ofReal_norm_sq_left_iff
  given: {v w : E}
  statement: ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0
  proof: by
  rw [inner_sub_right]; rw [sub_eq_zero]; rw [inner_self_eq_norm_sq_to_K]; rw [eq_comm]

中文:
定理 inner_eq_of实数_norm_sq_left_iff
  条件: {v w : E}
  结论: ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0
  证明: by
  rw [inner_sub_right]; rw [sub_eq_zero]; rw [inner_self_eq_norm_sq_to_K]; rw [eq_comm]

Depends on / 依赖: eq_comm, inner_self_eq_norm_sq_to_K, inner_sub_right, sub_eq_zero
-/
theorem inner_eq_ofReal_norm_sq_left_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0 := by
  rw [inner_sub_right]; rw [sub_eq_zero]; rw [inner_self_eq_norm_sq_to_K]; rw [eq_comm]

/--
theorem `inner_eq_norm_sq_left_iff` / 定理 `inner_eq_norm_sq_left_iff`

English:
theorem inner_eq_norm_sq_left_iff
  given: {v w : F}
  statement: ⟪v, w⟫_Real = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_Real = 0
  proof: inner_eq_ofReal_norm_sq_left_iff

中文:
定理 inner_eq_norm_sq_left_iff
  条件: {v w : F}
  结论: ⟪v, w⟫_实数 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_实数 = 0
  证明: inner_eq_ofReal_norm_sq_left_iff

Depends on / 依赖: inner_eq_ofReal_norm_sq_left_iff
-/
theorem inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_Real = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_Real = 0 :=
  inner_eq_ofReal_norm_sq_left_iff

/--
theorem `inner_eq_ofReal_norm_sq_right_iff` / 定理 `inner_eq_ofReal_norm_sq_right_iff`

English:
theorem inner_eq_ofReal_norm_sq_right_iff
  given: {v w : E}
  statement: ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0
  proof: by
  rw [inner_sub_left]; rw [sub_eq_zero]; rw [inner_self_eq_norm_sq_to_K]; rw [eq_comm]

中文:
定理 inner_eq_of实数_norm_sq_right_iff
  条件: {v w : E}
  结论: ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0
  证明: by
  rw [inner_sub_left]; rw [sub_eq_zero]; rw [inner_self_eq_norm_sq_to_K]; rw [eq_comm]

Depends on / 依赖: eq_comm, inner_self_eq_norm_sq_to_K, inner_sub_left, sub_eq_zero
-/
theorem inner_eq_ofReal_norm_sq_right_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0 := by
  rw [inner_sub_left]; rw [sub_eq_zero]; rw [inner_self_eq_norm_sq_to_K]; rw [eq_comm]

/--
theorem `inner_eq_norm_sq_right_iff` / 定理 `inner_eq_norm_sq_right_iff`

English:
theorem inner_eq_norm_sq_right_iff
  given: {v w : F}
  statement: ⟪v, w⟫_Real = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_Real = 0
  proof: inner_eq_ofReal_norm_sq_right_iff

中文:
定理 inner_eq_norm_sq_right_iff
  条件: {v w : F}
  结论: ⟪v, w⟫_实数 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_实数 = 0
  证明: inner_eq_ofReal_norm_sq_right_iff

Depends on / 依赖: inner_eq_ofReal_norm_sq_right_iff
-/
theorem inner_eq_norm_sq_right_iff {v w : F} : ⟪v, w⟫_Real = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_Real = 0 :=
  inner_eq_ofReal_norm_sq_right_iff

end BasicProperties_Seminormed

section BasicProperties

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

export InnerProductSpace (norm_sq_eq_re_inner)

/--
theorem `inner_self_eq_zero` / 定理 `inner_self_eq_zero`

English:
theorem inner_self_eq_zero
  given: {x : E}
  statement: ⟪x, x⟫ = 0 ↔ x = 0
  proof: by
  rw [inner_self_eq_norm_sq_to_K]; rw [sq_eq_zero_iff]; rw [ofReal_eq_zero]; rw [norm_eq_zero]

中文:
定理 inner_self_eq_zero
  条件: {x : E}
  结论: ⟪x, x⟫ = 0 ↔ x = 0
  证明: by
  rw [inner_self_eq_norm_sq_to_K]; rw [sq_eq_zero_iff]; rw [ofReal_eq_zero]; rw [norm_eq_zero]

Depends on / 依赖: inner_self_eq_norm_sq_to_K, norm_eq_zero, ofReal_eq_zero, sq_eq_zero_iff
-/
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  rw [inner_self_eq_norm_sq_to_K]; rw [sq_eq_zero_iff]; rw [ofReal_eq_zero]; rw [norm_eq_zero]

/--
theorem `inner_self_ne_zero` / 定理 `inner_self_ne_zero`

English:
theorem inner_self_ne_zero
  given: {x : E}
  statement: ⟪x, x⟫ != 0 ↔ x != 0
  proof: inner_self_eq_zero.not

中文:
定理 inner_self_ne_zero
  条件: {x : E}
  结论: ⟪x, x⟫ != 0 ↔ x != 0
  证明: inner_self_eq_zero.not

Depends on / 依赖: inner_self_eq_zero, inner_self_eq_zero.not
-/
theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ != 0 ↔ x != 0 :=
  inner_self_eq_zero.not

variable (𝕜)

/--
theorem `ext_inner_left` / 定理 `ext_inner_left`

English:
theorem ext_inner_left
  given: {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
  statement: x = y
  proof: by
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]; rw [inner_sub_right]; rw [sub_eq_zero]; rw [h (x - y)]

中文:
定理 ext_inner_left
  条件: {x y : E} (h : 对任意 v, ⟪v, x⟫ = ⟪v, y⟫)
  结论: x = y
  证明: by
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]; rw [inner_sub_right]; rw [sub_eq_zero]; rw [h (x - y)]

Depends on / 依赖: inner_self_eq_zero, inner_sub_right, sub_eq_zero
-/
theorem ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]; rw [inner_sub_right]; rw [sub_eq_zero]; rw [h (x - y)]

/--
theorem `ext_iff_inner_left` / 定理 `ext_iff_inner_left`

English:
theorem ext_iff_inner_left
  given: {x y : E}
  statement: x = y ↔ forall v, ⟪v, x⟫ = ⟪v, y⟫
  proof: ⟨fun h _ => h ▸ rfl, ext_inner_left 𝕜⟩

中文:
定理 ext_iff_inner_left
  条件: {x y : E}
  结论: x = y ↔ 对任意 v, ⟪v, x⟫ = ⟪v, y⟫
  证明: ⟨fun h _ => h ▸ rfl, ext_inner_left 𝕜⟩

Depends on / 依赖: ext_inner_left
-/
theorem ext_iff_inner_left {x y : E} : x = y ↔ forall v, ⟪v, x⟫ = ⟪v, y⟫ :=
  ⟨fun h _ => h ▸ rfl, ext_inner_left 𝕜⟩

/--
theorem `ext_inner_right` / 定理 `ext_inner_right`

English:
theorem ext_inner_right
  given: {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v⟫)
  statement: x = y
  proof: by
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]; rw [inner_sub_left]; rw [sub_eq_zero]; rw [h (x - y)]

中文:
定理 ext_inner_right
  条件: {x y : E} (h : 对任意 v, ⟪x, v⟫ = ⟪y, v⟫)
  结论: x = y
  证明: by
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]; rw [inner_sub_left]; rw [sub_eq_zero]; rw [h (x - y)]

Depends on / 依赖: inner_self_eq_zero, inner_sub_left, sub_eq_zero
-/
theorem ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]; rw [inner_sub_left]; rw [sub_eq_zero]; rw [h (x - y)]

/--
theorem `ext_iff_inner_right` / 定理 `ext_iff_inner_right`

English:
theorem ext_iff_inner_right
  given: {x y : E}
  statement: x = y ↔ forall v, ⟪x, v⟫ = ⟪y, v⟫
  proof: ⟨fun h _ => h ▸ rfl, ext_inner_right 𝕜⟩

中文:
定理 ext_iff_inner_right
  条件: {x y : E}
  结论: x = y ↔ 对任意 v, ⟪x, v⟫ = ⟪y, v⟫
  证明: ⟨fun h _ => h ▸ rfl, ext_inner_right 𝕜⟩

Depends on / 依赖: ext_inner_right
-/
theorem ext_iff_inner_right {x y : E} : x = y ↔ forall v, ⟪x, v⟫ = ⟪y, v⟫ :=
  ⟨fun h _ => h ▸ rfl, ext_inner_right 𝕜⟩

variable {𝕜}

/--
theorem `re_inner_self_nonpos` / 定理 `re_inner_self_nonpos`

English:
theorem re_inner_self_nonpos
  given: {x : E}
  statement: re ⟪x, x⟫ <= 0 ↔ x = 0
  proof: by
  simp

中文:
定理 re_inner_self_nonpos
  条件: {x : E}
  结论: re ⟪x, x⟫ <= 0 ↔ x = 0
  证明: by
  simp
-/
theorem re_inner_self_nonpos {x : E} : re ⟪x, x⟫ <= 0 ↔ x = 0 := by
  simp

/--
lemma `re_inner_self_pos` / 引理 `re_inner_self_pos`

English:
lemma re_inner_self_pos
  given: {x : E}
  statement: 0 < re ⟪x, x⟫ ↔ x != 0
  proof: by
  simp [sq_pos_iff]

中文:
引理 re_inner_self_pos
  条件: {x : E}
  结论: 0 < re ⟪x, x⟫ ↔ x != 0
  证明: by
  simp [sq_pos_iff]

Depends on / 依赖: sq_pos_iff
-/
lemma re_inner_self_pos {x : E} : 0 < re ⟪x, x⟫ ↔ x != 0 := by
  simp [sq_pos_iff]

open scoped InnerProductSpace in
/--
theorem `real_inner_self_nonpos` / 定理 `real_inner_self_nonpos`

English:
theorem real_inner_self_nonpos
  given: {x : F}
  statement: ⟪x, x⟫_Real <= 0 ↔ x = 0
  proof: re_inner_self_nonpos (𝕜 := Real)

中文:
定理 real_inner_self_nonpos
  条件: {x : F}
  结论: ⟪x, x⟫_实数 <= 0 ↔ x = 0
  证明: re_inner_self_nonpos (𝕜 := Real)

Depends on / 依赖: re_inner_self_nonpos
-/
theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_Real <= 0 ↔ x = 0 := re_inner_self_nonpos (𝕜 := Real)

open scoped InnerProductSpace in
/--
theorem `real_inner_self_pos` / 定理 `real_inner_self_pos`

English:
theorem real_inner_self_pos
  given: {x : F}
  statement: 0 < ⟪x, x⟫_Real ↔ x != 0
  proof: re_inner_self_pos (𝕜 := Real)

中文:
定理 real_inner_self_pos
  条件: {x : F}
  结论: 0 < ⟪x, x⟫_实数 ↔ x != 0
  证明: re_inner_self_pos (𝕜 := Real)

Depends on / 依赖: re_inner_self_pos
-/
theorem real_inner_self_pos {x : F} : 0 < ⟪x, x⟫_Real ↔ x != 0 := re_inner_self_pos (𝕜 := Real)

/--
theorem `linearIndependent_of_ne_zero_of_inner_eq_zero` / 定理 `linearIndependent_of_ne_zero_of_inner_eq_zero`

English:
theorem linearIndependent_of_ne_zero_of_inner_eq_zero
  statement: {ι : Type*} {v : ι -> E} (hz : forall i, v i != 0)
  proof: by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * ⟪v i, v i⟫ = ⟪v i, ∑ j in s, g j • v j⟫ := by
    rw [inner_sum]
    symm
    convert! Finset.sum_eq_single (M := 𝕜) i ?_ ?_
    · rw [inner_smul_right]
    · intro j _hj hji
      rw [inner_smul_right]; rw [ho hji.symm]; rw [mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'

中文:
定理 linearIndependent_of_ne_zero_of_inner_eq_zero
  结论: {ι : 类型} {v : ι -> E} (hz : 对任意 i, v i != 0)
  证明: by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * ⟪v i, v i⟫ = ⟪v i, ∑ j in s, g j • v j⟫ := by
    rw [inner_sum]
    symm
    convert! Finset.sum_eq_single (M := 𝕜) i ?_ ?_
    · rw [inner_smul_right]
    · intro j _hj hji
      rw [inner_smul_right]; rw [ho hji.symm]; rw [mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'

Depends on / 依赖: False.elim, Finset, Finset.sum_eq_single, convert, hji.symm, inner_smul_right, inner_sum, linearIndependent_iff, mul_zero, sum_eq_single
-/
theorem linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι -> E} (hz : forall i, v i != 0)
    (ho : Pairwise fun i j => ⟪v i, v j⟫ = 0) : LinearIndependent 𝕜 v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * ⟪v i, v i⟫ = ⟪v i, ∑ j in s, g j • v j⟫ := by
    rw [inner_sum]
    symm
    convert! Finset.sum_eq_single (M := 𝕜) i ?_ ?_
    · rw [inner_smul_right]
    · intro j _hj hji
      rw [inner_smul_right]; rw [ho hji.symm]; rw [mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'

end BasicProperties

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "IK" => @RCLike.I 𝕜 _

/--
theorem `norm_eq_sqrt_re_inner` / 定理 `norm_eq_sqrt_re_inner`

English:
theorem norm_eq_sqrt_re_inner
  given: (x : E)
  statement: ‖x‖ = √(re ⟪x, x⟫)
  proof: calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_re_inner _)

中文:
定理 norm_eq_sqrt_re_inner
  条件: (x : E)
  结论: ‖x‖ = √(re ⟪x, x⟫)
  证明: calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_re_inner _)

Depends on / 依赖: congr_arg, norm_nonneg, norm_sq_eq_re_inner, sqrt_sq
-/
theorem norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫) :=
  calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_re_inner _)

/--
theorem `norm_eq_sqrt_real_inner` / 定理 `norm_eq_sqrt_real_inner`

English:
theorem norm_eq_sqrt_real_inner
  given: (x : F)
  statement: ‖x‖ = √⟪x, x⟫_Real
  proof: @norm_eq_sqrt_re_inner Real _ _ _ _ x

中文:
定理 norm_eq_sqrt_real_inner
  条件: (x : F)
  结论: ‖x‖ = √⟪x, x⟫_实数
  证明: @norm_eq_sqrt_re_inner Real _ _ _ _ x

Depends on / 依赖: norm_eq_sqrt_re_inner
-/
theorem norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫_Real :=
  @norm_eq_sqrt_re_inner Real _ _ _ _ x

/--
theorem `inner_self_eq_norm_mul_norm` / 定理 `inner_self_eq_norm_mul_norm`

English:
theorem inner_self_eq_norm_mul_norm
  given: (x : E)
  statement: re ⟪x, x⟫ = ‖x‖ * ‖x‖
  proof: by
  rw [@norm_eq_sqrt_re_inner 𝕜]; rw [← sqrt_mul inner_self_nonneg (re ⟪x]; rw [x⟫)]; rw [sqrt_mul_self inner_self_nonneg]

中文:
定理 inner_self_eq_norm_mul_norm
  条件: (x : E)
  结论: re ⟪x, x⟫ = ‖x‖ * ‖x‖
  证明: by
  rw [@norm_eq_sqrt_re_inner 𝕜]; rw [← sqrt_mul inner_self_nonneg (re ⟪x]; rw [x⟫)]; rw [sqrt_mul_self inner_self_nonneg]

Depends on / 依赖: inner_self_nonneg, norm_eq_sqrt_re_inner, sqrt_mul, sqrt_mul_self
-/
theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜]; rw [← sqrt_mul inner_self_nonneg (re ⟪x]; rw [x⟫)]; rw [sqrt_mul_self inner_self_nonneg]

/--
theorem `inner_self_eq_norm_sq` / 定理 `inner_self_eq_norm_sq`

English:
theorem inner_self_eq_norm_sq
  given: (x : E)
  statement: re ⟪x, x⟫ = ‖x‖ ^ 2
  proof: by
  rw [pow_two]; rw [inner_self_eq_norm_mul_norm]

中文:
定理 inner_self_eq_norm_sq
  条件: (x : E)
  结论: re ⟪x, x⟫ = ‖x‖ ^ 2
  证明: by
  rw [pow_two]; rw [inner_self_eq_norm_mul_norm]

Depends on / 依赖: inner_self_eq_norm_mul_norm, pow_two
-/
theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two]; rw [inner_self_eq_norm_mul_norm]

/--
theorem `real_inner_self_eq_norm_mul_norm` / 定理 `real_inner_self_eq_norm_mul_norm`

English:
theorem real_inner_self_eq_norm_mul_norm
  given: (x : F)
  statement: ⟪x, x⟫_Real = ‖x‖ * ‖x‖
  proof: by
  have h := @inner_self_eq_norm_mul_norm Real F _ _ _ x
  simpa using h

中文:
定理 real_inner_self_eq_norm_mul_norm
  条件: (x : F)
  结论: ⟪x, x⟫_实数 = ‖x‖ * ‖x‖
  证明: by
  have h := @inner_self_eq_norm_mul_norm Real F _ _ _ x
  simpa using h

Depends on / 依赖: inner_self_eq_norm_mul_norm
-/
theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖ := by
  have h := @inner_self_eq_norm_mul_norm Real F _ _ _ x
  simpa using h

/--
theorem `real_inner_self_eq_norm_sq` / 定理 `real_inner_self_eq_norm_sq`

English:
theorem real_inner_self_eq_norm_sq
  given: (x : F)
  statement: ⟪x, x⟫_Real = ‖x‖ ^ 2
  proof: by
  rw [pow_two]; rw [real_inner_self_eq_norm_mul_norm]

中文:
定理 real_inner_self_eq_norm_sq
  条件: (x : F)
  结论: ⟪x, x⟫_实数 = ‖x‖ ^ 2
  证明: by
  rw [pow_two]; rw [real_inner_self_eq_norm_mul_norm]

Depends on / 依赖: pow_two, real_inner_self_eq_norm_mul_norm
-/
theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_Real = ‖x‖ ^ 2 := by
  rw [pow_two]; rw [real_inner_self_eq_norm_mul_norm]

/--
theorem `norm_add_sq` / 定理 `norm_add_sq`

English:
theorem norm_add_sq
  given: (x y : E)
  statement: ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
  proof: by
  repeat' rw [sq (M := Real), ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self]; rw [two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, map_add]
  rw [← inner_conj_symm]; rw [conj_re]

alias norm_add_pow_two := norm_add_sq

中文:
定理 norm_add_sq
  条件: (x y : E)
  结论: ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
  证明: by
  repeat' rw [sq (M := Real), ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self]; rw [two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, map_add]
  rw [← inner_conj_symm]; rw [conj_re]

alias norm_add_pow_two := norm_add_sq

Depends on / 依赖: add_assoc, add_left_inj, add_right_inj, conj_re, inner_add_add_self, inner_conj_symm, inner_self_eq_norm_mul_norm, map_add, repeat, two_mul
-/
theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  repeat' rw [sq (M := Real), ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self]; rw [two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, map_add]
  rw [← inner_conj_symm]; rw [conj_re]

alias norm_add_pow_two := norm_add_sq

/--
theorem `norm_add_sq_real` / 定理 `norm_add_sq_real`

English:
theorem norm_add_sq_real
  given: (x y : F)
  statement: ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_Real + ‖y‖ ^ 2
  proof: by
  have h := @norm_add_sq Real _ _ _ _ x y
  simpa using h

alias norm_add_pow_two_real := norm_add_sq_real

中文:
定理 norm_add_sq_real
  条件: (x y : F)
  结论: ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_实数 + ‖y‖ ^ 2
  证明: by
  have h := @norm_add_sq Real _ _ _ _ x y
  simpa using h

alias norm_add_pow_two_real := norm_add_sq_real

Depends on / 依赖: norm_add_sq
-/
theorem norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_Real + ‖y‖ ^ 2 := by
  have h := @norm_add_sq Real _ _ _ _ x y
  simpa using h

alias norm_add_pow_two_real := norm_add_sq_real

/--
theorem `norm_add_mul_self` / 定理 `norm_add_mul_self`

English:
theorem norm_add_mul_self
  given: (x y : E)
  proof: by
  repeat' rw [← sq (M := Real)]
  exact norm_add_sq _ _

中文:
定理 norm_add_mul_self
  条件: (x y : E)
  证明: by
  repeat' rw [← sq (M := Real)]
  exact norm_add_sq _ _

Depends on / 依赖: norm_add_sq, repeat
-/
theorem norm_add_mul_self (x y : E) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := Real)]
  exact norm_add_sq _ _

/--
theorem `norm_add_mul_self_real` / 定理 `norm_add_mul_self_real`

English:
theorem norm_add_mul_self_real
  given: (x y : F)
  proof: by
  have h := @norm_add_mul_self Real _ _ _ _ x y
  simpa using h

中文:
定理 norm_add_mul_self_real
  条件: (x y : F)
  证明: by
  have h := @norm_add_mul_self Real _ _ _ _ x y
  simpa using h

Depends on / 依赖: norm_add_mul_self
-/
theorem norm_add_mul_self_real (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_Real + ‖y‖ * ‖y‖ := by
  have h := @norm_add_mul_self Real _ _ _ _ x y
  simpa using h

/--
theorem `norm_sub_sq` / 定理 `norm_sub_sq`

English:
theorem norm_sub_sq
  given: (x y : E)
  statement: ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
  proof: by
  rw [sub_eq_add_neg]; rw [@norm_add_sq 𝕜 _ _ _ _ x (-y)]; rw [norm_neg]; rw [inner_neg_right]; rw [map_neg]; rw [mul_neg]; rw [sub_eq_add_neg]

alias norm_sub_pow_two := norm_sub_sq

中文:
定理 norm_sub_sq
  条件: (x y : E)
  结论: ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
  证明: by
  rw [sub_eq_add_neg]; rw [@norm_add_sq 𝕜 _ _ _ _ x (-y)]; rw [norm_neg]; rw [inner_neg_right]; rw [map_neg]; rw [mul_neg]; rw [sub_eq_add_neg]

alias norm_sub_pow_two := norm_sub_sq

Depends on / 依赖: inner_neg_right, map_neg, mul_neg, norm_add_sq, norm_neg, sub_eq_add_neg
-/
theorem norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  rw [sub_eq_add_neg]; rw [@norm_add_sq 𝕜 _ _ _ _ x (-y)]; rw [norm_neg]; rw [inner_neg_right]; rw [map_neg]; rw [mul_neg]; rw [sub_eq_add_neg]

alias norm_sub_pow_two := norm_sub_sq

/--
theorem `norm_sub_sq_real` / 定理 `norm_sub_sq_real`

English:
theorem norm_sub_sq_real
  given: (x y : F)
  statement: ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_Real + ‖y‖ ^ 2
  proof: @norm_sub_sq Real _ _ _ _ _ _

alias norm_sub_pow_two_real := norm_sub_sq_real

中文:
定理 norm_sub_sq_real
  条件: (x y : F)
  结论: ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_实数 + ‖y‖ ^ 2
  证明: @norm_sub_sq Real _ _ _ _ _ _

alias norm_sub_pow_two_real := norm_sub_sq_real

Depends on / 依赖: norm_sub_sq
-/
theorem norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_Real + ‖y‖ ^ 2 :=
  @norm_sub_sq Real _ _ _ _ _ _

alias norm_sub_pow_two_real := norm_sub_sq_real

/--
theorem `norm_sub_mul_self` / 定理 `norm_sub_mul_self`

English:
theorem norm_sub_mul_self
  given: (x y : E)
  proof: by
  repeat' rw [← sq (M := Real)]
  exact norm_sub_sq _ _

中文:
定理 norm_sub_mul_self
  条件: (x y : E)
  证明: by
  repeat' rw [← sq (M := Real)]
  exact norm_sub_sq _ _

Depends on / 依赖: norm_sub_sq, repeat
-/
theorem norm_sub_mul_self (x y : E) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := Real)]
  exact norm_sub_sq _ _

/--
theorem `norm_sub_mul_self_real` / 定理 `norm_sub_mul_self_real`

English:
theorem norm_sub_mul_self_real
  given: (x y : F)
  proof: by
  have h := @norm_sub_mul_self Real _ _ _ _ x y
  simpa using h

中文:
定理 norm_sub_mul_self_real
  条件: (x y : F)
  证明: by
  have h := @norm_sub_mul_self Real _ _ _ _ x y
  simpa using h

Depends on / 依赖: norm_sub_mul_self
-/
theorem norm_sub_mul_self_real (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_Real + ‖y‖ * ‖y‖ := by
  have h := @norm_sub_mul_self Real _ _ _ _ x y
  simpa using h

/--
theorem `norm_inner_le_norm` / 定理 `norm_inner_le_norm`

English:
theorem norm_inner_le_norm
  given: (x y : E)
  statement: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
  proof: by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) x]; rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) y]
  let : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y

中文:
定理 norm_inner_le_norm
  条件: (x y : E)
  结论: ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
  证明: by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) x]; rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) y]
  let : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.norm_inner_le_norm, PreInnerProductSpace, PreInnerProductSpace.Core, PreInnerProductSpace.toCore, norm_eq_sqrt_re_inner, norm_inner_le_norm, toCore
-/
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) x]; rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) y]
  let : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y

/--
theorem `nnnorm_inner_le_nnnorm` / 定理 `nnnorm_inner_le_nnnorm`

English:
theorem nnnorm_inner_le_nnnorm
  given: (x y : E)
  statement: ‖⟪x, y⟫‖₊ <= ‖x‖₊ * ‖y‖₊
  proof: norm_inner_le_norm x y

中文:
定理 nnnorm_inner_le_nnnorm
  条件: (x y : E)
  结论: ‖⟪x, y⟫‖₊ <= ‖x‖₊ * ‖y‖₊
  证明: norm_inner_le_norm x y

Depends on / 依赖: norm_inner_le_norm
-/
theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ <= ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y

/--
theorem `re_inner_le_norm` / 定理 `re_inner_le_norm`

English:
theorem re_inner_le_norm
  given: (x y : E)
  statement: re ⟪x, y⟫ <= ‖x‖ * ‖y‖
  proof: le_trans (re_le_norm ⟪x, y⟫) (norm_inner_le_norm x y)

中文:
定理 re_inner_le_norm
  条件: (x y : E)
  结论: re ⟪x, y⟫ <= ‖x‖ * ‖y‖
  证明: le_trans (re_le_norm ⟪x, y⟫) (norm_inner_le_norm x y)

Depends on / 依赖: le_trans, norm_inner_le_norm, re_le_norm
-/
theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ <= ‖x‖ * ‖y‖ :=
  le_trans (re_le_norm ⟪x, y⟫) (norm_inner_le_norm x y)

/--
theorem `abs_real_inner_le_norm` / 定理 `abs_real_inner_le_norm`

English:
theorem abs_real_inner_le_norm
  given: (x y : F)
  statement: |⟪x, y⟫_Real| <= ‖x‖ * ‖y‖
  proof: (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)

中文:
定理 abs_real_inner_le_norm
  条件: (x y : F)
  结论: |⟪x, y⟫_实数| <= ‖x‖ * ‖y‖
  证明: (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)

Depends on / 依赖: Real.norm_eq_abs, ge.trans, norm_eq_abs, norm_inner_le_norm
-/
theorem abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_Real| <= ‖x‖ * ‖y‖ :=
  (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)

/--
theorem `real_inner_le_norm` / 定理 `real_inner_le_norm`

English:
theorem real_inner_le_norm
  given: (x y : F)
  statement: ⟪x, y⟫_Real <= ‖x‖ * ‖y‖
  proof: le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

中文:
定理 real_inner_le_norm
  条件: (x y : F)
  结论: ⟪x, y⟫_实数 <= ‖x‖ * ‖y‖
  证明: le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

Depends on / 依赖: abs_real_inner_le_norm, le_abs_self, le_trans
-/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_Real <= ‖x‖ * ‖y‖ :=
  le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

/--
lemma `inner_eq_zero_of_left` / 引理 `inner_eq_zero_of_left`

English:
lemma inner_eq_zero_of_left
  given: {x : E} (y : E) (h : ‖x‖ = 0)
  statement: ⟪x, y⟫_𝕜 = 0
  proof: by
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (by positivity)
.trans by simp [h] exact norm_inner_le_norm _ _

中文:
引理 inner_eq_zero_of_left
  条件: {x : E} (y : E) (h : ‖x‖ = 0)
  结论: ⟪x, y⟫_𝕜 = 0
  证明: by
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (by positivity)
.trans by simp [h] exact norm_inner_le_norm _ _

Depends on / 依赖: le_antisymm, norm_eq_zero, norm_inner_le_norm
-/
lemma inner_eq_zero_of_left {x : E} (y : E) (h : ‖x‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (by positivity)
.trans by simp [h] exact norm_inner_le_norm _ _

/--
lemma `inner_eq_zero_of_right` / 引理 `inner_eq_zero_of_right`

English:
lemma inner_eq_zero_of_right
  given: (x : E) {y : E} (h : ‖y‖ = 0)
  statement: ⟪x, y⟫_𝕜 = 0
  proof: by
  rw [inner_eq_zero_symm]; rw [inner_eq_zero_of_left _ h]

中文:
引理 inner_eq_zero_of_right
  条件: (x : E) {y : E} (h : ‖y‖ = 0)
  结论: ⟪x, y⟫_𝕜 = 0
  证明: by
  rw [inner_eq_zero_symm]; rw [inner_eq_zero_of_left _ h]

Depends on / 依赖: inner_eq_zero_of_left, inner_eq_zero_symm
-/
lemma inner_eq_zero_of_right (x : E) {y : E} (h : ‖y‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm]; rw [inner_eq_zero_of_left _ h]

variable (𝕜)

include 𝕜 in
/--
theorem `parallelogram_law_with_norm_mul` / 定理 `parallelogram_law_with_norm_mul`

English:
theorem parallelogram_law_with_norm_mul
  given: (x y : E)
  proof: by
  simp only [← @inner_self_eq_norm_mul_norm 𝕜]
  rw [← re.map_add]; rw [parallelogram_law]; rw [two_mul]; rw [two_mul]
  simp only [re.map_add]

include 𝕜 in

中文:
定理 parallelogram_law_with_norm_mul
  条件: (x y : E)
  证明: by
  simp only [← @inner_self_eq_norm_mul_norm 𝕜]
  rw [← re.map_add]; rw [parallelogram_law]; rw [two_mul]; rw [two_mul]
  simp only [re.map_add]

include 𝕜 in

Depends on / 依赖: inner_self_eq_norm_mul_norm, map_add, parallelogram_law, re.map_add, two_mul
-/
theorem parallelogram_law_with_norm_mul (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  simp only [← @inner_self_eq_norm_mul_norm 𝕜]
  rw [← re.map_add]; rw [parallelogram_law]; rw [two_mul]; rw [two_mul]
  simp only [re.map_add]

include 𝕜 in
/--
theorem `parallelogram_law_with_norm` / 定理 `parallelogram_law_with_norm`

English:
theorem parallelogram_law_with_norm
  given: (x y : E)
  proof: by
  simp_rw [sq, parallelogram_law_with_norm_mul 𝕜 x y]

include 𝕜 in

中文:
定理 parallelogram_law_with_norm
  条件: (x y : E)
  证明: by
  simp_rw [sq, parallelogram_law_with_norm_mul 𝕜 x y]

include 𝕜 in

Depends on / 依赖: parallelogram_law_with_norm_mul, simp_rw
-/
theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simp_rw [sq, parallelogram_law_with_norm_mul 𝕜 x y]

include 𝕜 in
/--
theorem `parallelogram_law_with_nnnorm_mul` / 定理 `parallelogram_law_with_nnnorm_mul`

English:
theorem parallelogram_law_with_nnnorm_mul
  given: (x y : E)
  proof: Subtype.ext parallelogram_law_with_norm_mul 𝕜 x y

include 𝕜 in

中文:
定理 parallelogram_law_with_nnnorm_mul
  条件: (x y : E)
  证明: Subtype.ext parallelogram_law_with_norm_mul 𝕜 x y

include 𝕜 in

Depends on / 依赖: Subtype, Subtype.ext, parallelogram_law_with_norm_mul
-/
theorem parallelogram_law_with_nnnorm_mul (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
Subtype.ext parallelogram_law_with_norm_mul 𝕜 x y

include 𝕜 in
/--
theorem `parallelogram_law_with_nnnorm` / 定理 `parallelogram_law_with_nnnorm`

English:
theorem parallelogram_law_with_nnnorm
  given: (x y : E)
  proof: by
  simp_rw [sq, parallelogram_law_with_nnnorm_mul 𝕜 x y]

中文:
定理 parallelogram_law_with_nnnorm
  条件: (x y : E)
  证明: by
  simp_rw [sq, parallelogram_law_with_nnnorm_mul 𝕜 x y]

Depends on / 依赖: parallelogram_law_with_nnnorm_mul, simp_rw
-/
theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ ^ 2 + ‖x - y‖₊ ^ 2 = 2 * (‖x‖₊ ^ 2 + ‖y‖₊ ^ 2) := by
  simp_rw [sq, parallelogram_law_with_nnnorm_mul 𝕜 x y]

variable {𝕜}

/--
theorem `re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two` / 定理 `re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two`

English:
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
  given: (x y : E)
  proof: by
  rw [@norm_add_mul_self 𝕜]
  ring

中文:
定理 re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
  条件: (x y : E)
  证明: by
  rw [@norm_add_mul_self 𝕜]
  ring

Depends on / 依赖: norm_add_mul_self
-/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 := by
  rw [@norm_add_mul_self 𝕜]
  ring

/--
theorem `re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two` / 定理 `re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two`

English:
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
  given: (x y : E)
  proof: by
  rw [@norm_sub_mul_self 𝕜]
  ring

中文:
定理 re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
  条件: (x y : E)
  证明: by
  rw [@norm_sub_mul_self 𝕜]
  ring

Depends on / 依赖: norm_sub_mul_self
-/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 := by
  rw [@norm_sub_mul_self 𝕜]
  ring

/--
theorem `re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four` / 定理 `re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four`

English:
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
  given: (x y : E)
  proof: by
  rw [@norm_add_mul_self 𝕜]; rw [@norm_sub_mul_self 𝕜]
  ring

中文:
定理 re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
  条件: (x y : E)
  证明: by
  rw [@norm_add_mul_self 𝕜]; rw [@norm_sub_mul_self 𝕜]
  ring

Depends on / 依赖: norm_add_mul_self, norm_sub_mul_self
-/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 := by
  rw [@norm_add_mul_self 𝕜]; rw [@norm_sub_mul_self 𝕜]
  ring

/--
theorem `im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four` / 定理 `im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four`

English:
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
  given: (x y : E)
  proof: by
  simp only [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜, inner_smul_right, I_mul_re]
  ring

中文:
定理 im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
  条件: (x y : E)
  证明: by
  simp only [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜, inner_smul_right, I_mul_re]
  ring

Depends on / 依赖: I_mul_re, inner_smul_right, norm_add_mul_self, norm_sub_mul_self
-/
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 := by
  simp only [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜, inner_smul_right, I_mul_re]
  ring

/--
theorem `inner_eq_sum_norm_sq_div_four` / 定理 `inner_eq_sum_norm_sq_div_four`

English:
theorem inner_eq_sum_norm_sq_div_four
  given: (x y : E)
  proof: by
  rw [← re_add_im ⟪x]; rw [y⟫]; rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four]; rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]

中文:
定理 inner_eq_sum_norm_sq_div_four
  条件: (x y : E)
  证明: by
  rw [← re_add_im ⟪x]; rw [y⟫]; rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four]; rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]

Depends on / 依赖: add_div, im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four, mul_div_right_comm, re_add_im, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
-/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = ((‖x + y‖ : 𝕜) ^ 2 - (‖x - y‖ : 𝕜) ^ 2 +
              ((‖x - IK • y‖ : 𝕜) ^ 2 - (‖x + IK • y‖ : 𝕜) ^ 2) * IK) / 4 := by
  rw [← re_add_im ⟪x]; rw [y⟫]; rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four]; rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]

/--
theorem `real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two` / 定理 `real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two`

English:
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
  given: (x y : F)
  proof: re_to_real.symm.trans
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

中文:
定理 real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
  条件: (x y : F)
  证明: re_to_real.symm.trans
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

Depends on / 依赖: re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, re_to_real, re_to_real.symm.trans
-/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_Real = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
re_to_real.symm.trans
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/--
theorem `real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two` / 定理 `real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two`

English:
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
  given: (x y : F)
  proof: re_to_real.symm.trans
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

中文:
定理 real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
  条件: (x y : F)
  证明: re_to_real.symm.trans
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

Depends on / 依赖: re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, re_to_real, re_to_real.symm.trans
-/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_Real = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
re_to_real.symm.trans
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/--
theorem `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero` / 定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`

English:
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
  given: (x y : F)
  proof: by
  rw [@norm_add_mul_self Real]; rw [add_right_cancel_iff]; rw [add_eq_left]; rw [mul_eq_zero]
  simp

中文:
定理 norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
  条件: (x y : F)
  证明: by
  rw [@norm_add_mul_self Real]; rw [add_right_cancel_iff]; rw [add_eq_left]; rw [mul_eq_zero]
  simp

Depends on / 依赖: add_eq_left, add_right_cancel_iff, mul_eq_zero, norm_add_mul_self
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0 := by
  rw [@norm_add_mul_self Real]; rw [add_right_cancel_iff]; rw [add_eq_left]; rw [mul_eq_zero]
  simp

/--
theorem `norm_add_eq_sqrt_iff_real_inner_eq_zero` / 定理 `norm_add_eq_sqrt_iff_real_inner_eq_zero`

English:
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero
  given: {x y : F}
  proof: by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]; rw [eq_comm]; rw [sqrt_eq_iff_mul_self_eq]; rw [eq_comm] <;> positivity

中文:
定理 norm_add_eq_sqrt_iff_real_inner_eq_zero
  条件: {x y : F}
  证明: by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]; rw [eq_comm]; rw [sqrt_eq_iff_mul_self_eq]; rw [eq_comm] <;> positivity

Depends on / 依赖: eq_comm, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, sqrt_eq_iff_mul_self_eq
-/
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0 := by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]; rw [eq_comm]; rw [sqrt_eq_iff_mul_self_eq]; rw [eq_comm] <;> positivity

/--
theorem `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` / 定理 `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`

English:
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
  given: (x y : E) (h : ⟪x, y⟫ = 0)
  proof: by
  rw [@norm_add_mul_self 𝕜]; rw [add_right_cancel_iff]; rw [add_eq_left]; rw [mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re]

中文:
定理 norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
  条件: (x y : E) (h : ⟪x, y⟫ = 0)
  证明: by
  rw [@norm_add_mul_self 𝕜]; rw [add_right_cancel_iff]; rw [add_eq_left]; rw [mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re]

Depends on / 依赖: Or.inr, add_eq_left, add_right_cancel_iff, mul_eq_zero, norm_add_mul_self, zero_re
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ := by
  rw [@norm_add_mul_self 𝕜]; rw [add_right_cancel_iff]; rw [add_eq_left]; rw [mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re]

/--
theorem `norm_add_sq_eq_norm_sq_add_norm_sq_real` / 定理 `norm_add_sq_eq_norm_sq_add_norm_sq_real`

English:
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real
  given: {x y : F} (h : ⟪x, y⟫_Real = 0)
  proof: (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

中文:
定理 norm_add_sq_eq_norm_sq_add_norm_sq_real
  条件: {x y : F} (h : ⟪x, y⟫_实数 = 0)
  证明: (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

Depends on / 依赖: norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/--
theorem `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero` / 定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`

English:
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
  given: (x y : F)
  proof: by
  rw [@norm_sub_mul_self Real]; rw [add_right_cancel_iff]; rw [sub_eq_add_neg]; rw [add_eq_left]; rw [neg_eq_zero]; rw [mul_eq_zero]
  simp

中文:
定理 norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
  条件: (x y : F)
  证明: by
  rw [@norm_sub_mul_self Real]; rw [add_right_cancel_iff]; rw [sub_eq_add_neg]; rw [add_eq_left]; rw [neg_eq_zero]; rw [mul_eq_zero]
  simp

Depends on / 依赖: add_eq_left, add_right_cancel_iff, mul_eq_zero, neg_eq_zero, norm_sub_mul_self, sub_eq_add_neg
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0 := by
  rw [@norm_sub_mul_self Real]; rw [add_right_cancel_iff]; rw [sub_eq_add_neg]; rw [add_eq_left]; rw [neg_eq_zero]; rw [mul_eq_zero]
  simp

/--
theorem `norm_sub_eq_sqrt_iff_real_inner_eq_zero` / 定理 `norm_sub_eq_sqrt_iff_real_inner_eq_zero`

English:
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero
  given: {x y : F}
  proof: by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]; rw [eq_comm]; rw [sqrt_eq_iff_mul_self_eq]; rw [eq_comm] <;> positivity

中文:
定理 norm_sub_eq_sqrt_iff_real_inner_eq_zero
  条件: {x y : F}
  证明: by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]; rw [eq_comm]; rw [sqrt_eq_iff_mul_self_eq]; rw [eq_comm] <;> positivity

Depends on / 依赖: eq_comm, norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, sqrt_eq_iff_mul_self_eq
-/
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x - y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0 := by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]; rw [eq_comm]; rw [sqrt_eq_iff_mul_self_eq]; rw [eq_comm] <;> positivity

/--
theorem `norm_sub_sq_eq_norm_sq_add_norm_sq_real` / 定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_real`

English:
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real
  given: {x y : F} (h : ⟪x, y⟫_Real = 0)
  proof: (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

中文:
定理 norm_sub_sq_eq_norm_sq_add_norm_sq_real
  条件: {x y : F} (h : ⟪x, y⟫_实数 = 0)
  证明: (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

Depends on / 依赖: norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/--
theorem `real_inner_add_sub_eq_zero_iff` / 定理 `real_inner_add_sub_eq_zero_iff`

English:
theorem real_inner_add_sub_eq_zero_iff
  given: (x y : F)
  statement: ⟪x + y, x - y⟫_Real = 0 ↔ ‖x‖ = ‖y‖
  proof: by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_mul_norm Real, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  grind

中文:
定理 real_inner_add_sub_eq_zero_iff
  条件: (x y : F)
  结论: ⟪x + y, x - y⟫_实数 = 0 ↔ ‖x‖ = ‖y‖
  证明: by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_mul_norm Real, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  grind

Depends on / 依赖: conv_rhs, inner_add_left, inner_self_eq_norm_mul_norm, inner_sub_right, mul_self_inj_of_nonneg, norm_nonneg, re_to_real, real_inner_comm, sub_eq_zero
-/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_Real = 0 ↔ ‖x‖ = ‖y‖ := by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_mul_norm Real, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  grind

/--
theorem `norm_sub_eq_norm_add` / 定理 `norm_sub_eq_norm_add`

English:
theorem norm_sub_eq_norm_add
  given: {v w : E} (h : ⟪v, w⟫ = 0)
  statement: ‖w - v‖ = ‖w + v‖
  proof: by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm 𝕜, sub_neg_eq_add, sub_zero, map_sub, zero_re,
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]

中文:
定理 norm_sub_eq_norm_add
  条件: {v w : E} (h : ⟪v, w⟫ = 0)
  结论: ‖w - v‖ = ‖w + v‖
  证明: by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm 𝕜, sub_neg_eq_add, sub_zero, map_sub, zero_re,
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]

Depends on / 依赖: add_zero, inner_add_right, inner_re_symm, inner_self_eq_norm_mul_norm, inner_sub_left, inner_sub_right, map_add, map_sub, mul_self_inj_of_nonneg, norm_nonneg, sub_neg_eq_add, sub_zero, zero_add, zero_re, zero_sub
-/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm 𝕜, sub_neg_eq_add, sub_zero, map_sub, zero_re,
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]

/--
theorem `abs_real_inner_div_norm_mul_norm_le_one` / 定理 `abs_real_inner_div_norm_mul_norm_le_one`

English:
theorem abs_real_inner_div_norm_mul_norm_le_one
  given: (x y : F)
  statement: |⟪x, y⟫_Real / (‖x‖ * ‖y‖)| <= 1
  proof: by
  rw [abs_div]; rw [abs_mul]; rw [abs_norm]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_real_inner_le_norm x y) (by positivity)

中文:
定理 abs_real_inner_div_norm_mul_norm_le_one
  条件: (x y : F)
  结论: |⟪x, y⟫_实数 / (‖x‖ * ‖y‖)| <= 1
  证明: by
  rw [abs_div]; rw [abs_mul]; rw [abs_norm]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_real_inner_le_norm x y) (by positivity)

Depends on / 依赖: abs_div, abs_mul, abs_norm, abs_real_inner_le_norm
-/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : |⟪x, y⟫_Real / (‖x‖ * ‖y‖)| <= 1 := by
  rw [abs_div]; rw [abs_mul]; rw [abs_norm]; rw [abs_norm]
  exact div_le_one_of_le₀ (abs_real_inner_le_norm x y) (by positivity)

/--
theorem `real_inner_smul_self_left` / 定理 `real_inner_smul_self_left`

English:
theorem real_inner_smul_self_left
  given: (x : F) (r : Real)
  statement: ⟪r • x, x⟫_Real = r * (‖x‖ * ‖x‖)
  proof: by
  rw [real_inner_smul_left]; rw [← real_inner_self_eq_norm_mul_norm]

中文:
定理 real_inner_smul_self_left
  条件: (x : F) (r : 实数)
  结论: ⟪r • x, x⟫_实数 = r * (‖x‖ * ‖x‖)
  证明: by
  rw [real_inner_smul_left]; rw [← real_inner_self_eq_norm_mul_norm]

Depends on / 依赖: real_inner_self_eq_norm_mul_norm, real_inner_smul_left
-/
theorem real_inner_smul_self_left (x : F) (r : Real) : ⟪r • x, x⟫_Real = r * (‖x‖ * ‖x‖) := by
  rw [real_inner_smul_left]; rw [← real_inner_self_eq_norm_mul_norm]

/--
theorem `real_inner_smul_self_right` / 定理 `real_inner_smul_self_right`

English:
theorem real_inner_smul_self_right
  given: (x : F) (r : Real)
  statement: ⟪x, r • x⟫_Real = r * (‖x‖ * ‖x‖)
  proof: by
  rw [inner_smul_right]; rw [← real_inner_self_eq_norm_mul_norm]

中文:
定理 real_inner_smul_self_right
  条件: (x : F) (r : 实数)
  结论: ⟪x, r • x⟫_实数 = r * (‖x‖ * ‖x‖)
  证明: by
  rw [inner_smul_right]; rw [← real_inner_self_eq_norm_mul_norm]

Depends on / 依赖: inner_smul_right, real_inner_self_eq_norm_mul_norm
-/
theorem real_inner_smul_self_right (x : F) (r : Real) : ⟪x, r • x⟫_Real = r * (‖x‖ * ‖x‖) := by
  rw [inner_smul_right]; rw [← real_inner_self_eq_norm_mul_norm]

/--
theorem `inner_sum_smul_sum_smul_of_sum_eq_zero` / 定理 `inner_sum_smul_sum_smul_of_sum_eq_zero`

English:
theorem inner_sum_smul_sum_smul_of_sum_eq_zero
  statement: {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ -> Real}
  proof: by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same,
    add_div, mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]

中文:
定理 inner_sum_smul_sum_smul_of_sum_eq_zero
  结论: {ι₁ : 类型} {s₁ : 有限集 ι₁} {w₁ : ι₁ -> 实数}
  证明: by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same,
    add_div, mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const_zero, Finset.sum_div, Finset.sum_mul, Finset.sum_sub_distrib, add_div, div_sub_div_same, inner_sum, left_distrib, mul_assoc, mul_div_assoc, mul_sub_left_distrib, mul_sum, mul_zero, neg_div, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, real_inner_smul_left, real_inner_smul_right
-/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ -> Real}
    (v₁ : ι₁ -> F) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset ι₂} {w₂ : ι₂ -> Real}
    (v₂ : ι₂ -> F) (h₂ : ∑ i in s₂, w₂ i = 0) :
    ⟪∑ i₁ in s₁, w₁ i₁ • v₁ i₁, ∑ i₂ in s₂, w₂ i₂ • v₂ i₂⟫_Real =
      (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2 := by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same,
    add_div, mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]

end Norm_Seminormed

section Norm

open scoped InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F]
variable {ι : Type*}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
theorem `dist_div_norm_sq_smul` / 定理 `dist_div_norm_sq_smul`

English:
theorem dist_div_norm_sq_smul
  given: {x y : F} (hx : x != 0) (hy : y != 0) (R : Real)
  proof: calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        √(‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) := by
      rw [dist_eq_norm]; rw [sqrt_sq (norm_nonneg _)]
    _ = √((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :=
congr_arg (√·) by
        simp [field, sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _), -mul_eq_mul_left_iff]
        ring
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul]; rw [sqrt_sq]; rw [sqrt_sq]; rw [dist_eq_norm] <;> positivity

中文:
定理 dist_div_norm_sq_smul
  条件: {x y : F} (hx : x != 0) (hy : y != 0) (R : 实数)
  证明: calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        √(‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) := by
      rw [dist_eq_norm]; rw [sqrt_sq (norm_nonneg _)]
    _ = √((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :=
congr_arg (√·) by
        simp [field, sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _), -mul_eq_mul_left_iff]
        ring
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul]; rw [sqrt_sq]; rw [sqrt_sq]; rw [dist_eq_norm] <;> positivity

Depends on / 依赖: Real.norm_of_nonneg, congr_arg, dist_eq_norm, inner_smul_right, mul_eq_mul_left_iff, mul_self_nonneg, norm_nonneg, norm_of_nonneg, norm_smul, norm_sub_mul_self_real, real_inner_smul_left, sqrt_mul, sqrt_sq
-/
theorem dist_div_norm_sq_smul {x y : F} (hx : x != 0) (hy : y != 0) (R : Real) :
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = R ^ 2 / (‖x‖ * ‖y‖) * dist x y :=
  calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        √(‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) := by
      rw [dist_eq_norm]; rw [sqrt_sq (norm_nonneg _)]
    _ = √((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :=
congr_arg (√·) by
        simp [field, sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _), -mul_eq_mul_left_iff]
        ring
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul]; rw [sqrt_sq]; rw [sqrt_sq]; rw [dist_eq_norm] <;> positivity

/--
theorem `norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul` / 定理 `norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul`

English:
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  statement: {x : E} {r : 𝕜} (hx : x != 0)
  proof: by
  have hx' : ‖x‖ != 0 := by simp [hx]
  have hr' : ‖r‖ != 0 := by simp [hr]
  rw [inner_smul_right]; rw [norm_mul]; rw [← inner_self_re_eq_norm]; rw [inner_self_eq_norm_mul_norm]; rw [norm_smul]
  rw [← mul_assoc]; rw [← div_div]; rw [mul_div_cancel_right₀ _ hx']; rw [← div_div]; rw [mul_comm]; rw [mul_div_cancel_right₀ _ hr']; rw [div_self hx']

中文:
定理 norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  结论: {x : E} {r : 𝕜} (hx : x != 0)
  证明: by
  have hx' : ‖x‖ != 0 := by simp [hx]
  have hr' : ‖r‖ != 0 := by simp [hr]
  rw [inner_smul_right]; rw [norm_mul]; rw [← inner_self_re_eq_norm]; rw [inner_self_eq_norm_mul_norm]; rw [norm_smul]
  rw [← mul_assoc]; rw [← div_div]; rw [mul_div_cancel_right₀ _ hx']; rw [← div_div]; rw [mul_comm]; rw [mul_div_cancel_right₀ _ hr']; rw [div_self hx']

Depends on / 依赖: div_div, div_self, inner_self_eq_norm_mul_norm, inner_self_re_eq_norm, inner_smul_right, mul_assoc, mul_comm, norm_mul, norm_smul
-/
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x != 0)
    (hr : r != 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1 := by
  have hx' : ‖x‖ != 0 := by simp [hx]
  have hr' : ‖r‖ != 0 := by simp [hr]
  rw [inner_smul_right]; rw [norm_mul]; rw [← inner_self_re_eq_norm]; rw [inner_self_eq_norm_mul_norm]; rw [norm_smul]
  rw [← mul_assoc]; rw [← div_div]; rw [mul_div_cancel_right₀ _ hx']; rw [← div_div]; rw [mul_comm]; rw [mul_div_cancel_right₀ _ hr']; rw [div_self hx']

/--
theorem `abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul` / 定理 `abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul`

English:
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  statement: {x : F} {r : Real}
  proof: norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

中文:
定理 abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  结论: {x : F} {r : 实数}
  证明: norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

Depends on / 依赖: norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
-/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : Real}
    (hx : x != 0) (hr : r != 0) : |⟪x, r • x⟫_Real| / (‖x‖ * ‖r • x‖) = 1 :=
  norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/--
theorem `real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul` / 定理 `real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul`

English:
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  statement: {x : F} {r : Real} (hx : x != 0)
  proof: by
  rw [real_inner_smul_self_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [← mul_assoc ‖x‖]; rw [mul_comm _ |r|]; rw [mul_assoc]; rw [abs_of_nonneg hr.le]; rw [div_self]
  exact mul_ne_zero hr.ne' (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

中文:
定理 real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  结论: {x : F} {r : 实数} (hx : x != 0)
  证明: by
  rw [real_inner_smul_self_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [← mul_assoc ‖x‖]; rw [mul_comm _ |r|]; rw [mul_assoc]; rw [abs_of_nonneg hr.le]; rw [div_self]
  exact mul_ne_zero hr.ne' (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

Depends on / 依赖: Real.norm_eq_abs, abs_of_nonneg, div_self, hr.le, hr.ne, mul_assoc, mul_comm, mul_ne_zero, mul_self_ne_zero, norm_eq_abs, norm_ne_zero_iff, norm_smul, real_inner_smul_self_right
-/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : Real} (hx : x != 0)
    (hr : 0 < r) : ⟪x, r • x⟫_Real / (‖x‖ * ‖r • x‖) = 1 := by
  rw [real_inner_smul_self_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [← mul_assoc ‖x‖]; rw [mul_comm _ |r|]; rw [mul_assoc]; rw [abs_of_nonneg hr.le]; rw [div_self]
  exact mul_ne_zero hr.ne' (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

/--
theorem `real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul` / 定理 `real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul`

English:
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  statement: {x : F} {r : Real} (hx : x != 0)
  proof: by
  rw [real_inner_smul_self_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [← mul_assoc ‖x‖]; rw [mul_comm _ |r|]; rw [mul_assoc]; rw [abs_of_neg hr]; rw [neg_mul]; rw [div_neg_eq_neg_div]; rw [div_self]
  exact mul_ne_zero hr.ne (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

中文:
定理 real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  结论: {x : F} {r : 实数} (hx : x != 0)
  证明: by
  rw [real_inner_smul_self_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [← mul_assoc ‖x‖]; rw [mul_comm _ |r|]; rw [mul_assoc]; rw [abs_of_neg hr]; rw [neg_mul]; rw [div_neg_eq_neg_div]; rw [div_self]
  exact mul_ne_zero hr.ne (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

Depends on / 依赖: Real.norm_eq_abs, abs_of_neg, div_neg_eq_neg_div, div_self, hr.ne, mul_assoc, mul_comm, mul_ne_zero, mul_self_ne_zero, neg_mul, norm_eq_abs, norm_ne_zero_iff, norm_smul, real_inner_smul_self_right
-/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : Real} (hx : x != 0)
    (hr : r < 0) : ⟪x, r • x⟫_Real / (‖x‖ * ‖r • x‖) = -1 := by
  rw [real_inner_smul_self_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [← mul_assoc ‖x‖]; rw [mul_comm _ |r|]; rw [mul_assoc]; rw [abs_of_neg hr]; rw [neg_mul]; rw [div_neg_eq_neg_div]; rw [div_self]
  exact mul_ne_zero hr.ne (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

variable (𝕜) in
/--
theorem `norm_inner_eq_norm_tfae` / 定理 `norm_inner_eq_norm_tfae`

English:
theorem norm_inner_eq_norm_tfae
  given: (x y : E)
  proof: by
  tfae_have 1 -> 2 := by
    refine fun h => or_iff_not_imp_left.2 fun hx₀ => ?_
    have : ‖x‖ ^ 2 != 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
    rw [← sq_eq_sq₀]; rw [mul_pow]; rw [← mul_right_inj' this]; rw [eq_comm]; rw [← sub_eq_zero]; rw [← mul_sub] at h <;>
      try positivity
    simp only [@norm_sq_eq_re_inner 𝕜] at h
    let : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
    erw [← InnerProductSpace.Core.cauchy_schwarz_aux (𝕜 := 𝕜) (F := E)] at h
    rw [InnerProductSpace.Core.normSq_eq_zero]; rw [sub_eq_zero] at h
    rw [div_eq_inv_mul]; rw [mul_smul]; rw [h]; rw [inv_smul_smul₀]
    rwa [inner_self_ne_zero]
  tfae_have 2 -> 3 := fun h => h.imp_right fun h' => ⟨_, h'⟩
  tfae_have 3 -> 1 := by
    rintro (rfl | ⟨r, rfl⟩) <;>
    simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K,
      sq, mul_left_comm]
  tfae_have 3 ↔ 4 := by simp only [Submodule.mem_span_singleton, eq_comm]
  tfae_finish

中文:
定理 norm_inner_eq_norm_tfae
  条件: (x y : E)
  证明: by
  tfae_have 1 -> 2 := by
    refine fun h => or_iff_not_imp_left.2 fun hx₀ => ?_
    have : ‖x‖ ^ 2 != 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
    rw [← sq_eq_sq₀]; rw [mul_pow]; rw [← mul_right_inj' this]; rw [eq_comm]; rw [← sub_eq_zero]; rw [← mul_sub] at h <;>
      try positivity
    simp only [@norm_sq_eq_re_inner 𝕜] at h
    let : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
    erw [← InnerProductSpace.Core.cauchy_schwarz_aux (𝕜 := 𝕜) (F := E)] at h
    rw [InnerProductSpace.Core.normSq_eq_zero]; rw [sub_eq_zero] at h
    rw [div_eq_inv_mul]; rw [mul_smul]; rw [h]; rw [inv_smul_smul₀]
    rwa [inner_self_ne_zero]
  tfae_have 2 -> 3 := fun h => h.imp_right fun h' => ⟨_, h'⟩
  tfae_have 3 -> 1 := by
    rintro (rfl | ⟨r, rfl⟩) <;>
    simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K,
      sq, mul_left_comm]
  tfae_have 3 ↔ 4 := by simp only [Submodule.mem_span_singleton, eq_comm]
  tfae_finish

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core, InnerProductSpace.Core.cauchy_schwarz_aux, InnerProductSpace.Core.normSq_eq_zero, InnerProductSpace.toCore, cauchy_schwarz_aux, eq_comm, mul_pow, mul_right_inj, mul_sub, normSq_eq_zero, norm_ne_zero_iff, norm_sq_eq_re_inner, or_iff_not_imp_left, pow_ne_zero, sub_e, sub_eq_zero, tfae_have, toCore
-/
theorem norm_inner_eq_norm_tfae (x y : E) :
    List.TFAE [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖,
      x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x,
      x = 0 ∨ exists r : 𝕜, y = r • x,
      x = 0 ∨ y in 𝕜 ∙ x] := by
  tfae_have 1 -> 2 := by
    refine fun h => or_iff_not_imp_left.2 fun hx₀ => ?_
    have : ‖x‖ ^ 2 != 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
    rw [← sq_eq_sq₀]; rw [mul_pow]; rw [← mul_right_inj' this]; rw [eq_comm]; rw [← sub_eq_zero]; rw [← mul_sub] at h <;>
      try positivity
    simp only [@norm_sq_eq_re_inner 𝕜] at h
    let : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
    erw [← InnerProductSpace.Core.cauchy_schwarz_aux (𝕜 := 𝕜) (F := E)] at h
    rw [InnerProductSpace.Core.normSq_eq_zero]; rw [sub_eq_zero] at h
    rw [div_eq_inv_mul]; rw [mul_smul]; rw [h]; rw [inv_smul_smul₀]
    rwa [inner_self_ne_zero]
  tfae_have 2 -> 3 := fun h => h.imp_right fun h' => ⟨_, h'⟩
  tfae_have 3 -> 1 := by
    rintro (rfl | ⟨r, rfl⟩) <;>
    simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K,
      sq, mul_left_comm]
  tfae_have 3 ↔ 4 := by simp only [Submodule.mem_span_singleton, eq_comm]
  tfae_finish

/--
theorem `norm_inner_eq_norm_iff` / 定理 `norm_inner_eq_norm_iff`

English:
theorem norm_inner_eq_norm_iff
  given: {x y : E} (hx₀ : x != 0) (hy₀ : y != 0)
  proof: calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ exists r : 𝕜, y = r • x :=
      (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ exists r : 𝕜, y = r • x := or_iff_right hx₀
    _ ↔ exists r : 𝕜, r != 0 ∧ y = r • x :=
⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ h.symm ▸ smul_eq_zero.2 Or.inl hr₀, h⟩,
        fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

中文:
定理 norm_inner_eq_norm_iff
  条件: {x y : E} (hx₀ : x != 0) (hy₀ : y != 0)
  证明: calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ exists r : 𝕜, y = r • x :=
      (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ exists r : 𝕜, y = r • x := or_iff_right hx₀
    _ ↔ exists r : 𝕜, r != 0 ∧ y = r • x :=
⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ h.symm ▸ smul_eq_zero.2 Or.inl hr₀, h⟩,
        fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

Depends on / 依赖: Or.inl, h.symm, norm_inner_eq_norm_tfae, or_iff_right, smul_eq_zero
-/
theorem norm_inner_eq_norm_iff {x y : E} (hx₀ : x != 0) (hy₀ : y != 0) :
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ exists r : 𝕜, r != 0 ∧ y = r • x :=
  calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ exists r : 𝕜, y = r • x :=
      (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ exists r : 𝕜, y = r • x := or_iff_right hx₀
    _ ↔ exists r : 𝕜, r != 0 ∧ y = r • x :=
⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ h.symm ▸ smul_eq_zero.2 Or.inl hr₀, h⟩,
        fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

/--
theorem `norm_inner_div_norm_mul_norm_eq_one_iff` / 定理 `norm_inner_div_norm_mul_norm_eq_one_iff`

English:
theorem norm_inner_div_norm_mul_norm_eq_one_iff
  given: (x y : E)
  proof: by
  constructor
  · intro h
    have hx₀ : x != 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y != 0 := fun h₀ => by simp [h₀] at h
refine ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 eq_of_div_eq_one ?_⟩
    simpa using h
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    simp only [norm_div, norm_mul, norm_ofReal, abs_norm]
    exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

中文:
定理 norm_inner_div_norm_mul_norm_eq_one_iff
  条件: (x y : E)
  证明: by
  constructor
  · intro h
    have hx₀ : x != 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y != 0 := fun h₀ => by simp [h₀] at h
refine ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 eq_of_div_eq_one ?_⟩
    simpa using h
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    simp only [norm_div, norm_mul, norm_ofReal, abs_norm]
    exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

Depends on / 依赖: abs_norm, eq_of_div_eq_one, norm_div, norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul, norm_inner_eq_norm_iff, norm_mul, norm_ofReal
-/
theorem norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x != 0 ∧ exists r : 𝕜, r != 0 ∧ y = r • x := by
  constructor
  · intro h
    have hx₀ : x != 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y != 0 := fun h₀ => by simp [h₀] at h
refine ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 eq_of_div_eq_one ?_⟩
    simpa using h
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    simp only [norm_div, norm_mul, norm_ofReal, abs_norm]
    exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/--
theorem `abs_real_inner_div_norm_mul_norm_eq_one_iff` / 定理 `abs_real_inner_div_norm_mul_norm_eq_one_iff`

English:
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff
  given: (x y : F)
  proof: @norm_inner_div_norm_mul_norm_eq_one_iff Real F _ _ _ x y

中文:
定理 abs_real_inner_div_norm_mul_norm_eq_one_iff
  条件: (x y : F)
  证明: @norm_inner_div_norm_mul_norm_eq_one_iff Real F _ _ _ x y

Depends on / 依赖: norm_inner_div_norm_mul_norm_eq_one_iff
-/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    |⟪x, y⟫_Real / (‖x‖ * ‖y‖)| = 1 ↔ x != 0 ∧ exists r : Real, r != 0 ∧ y = r • x :=
  @norm_inner_div_norm_mul_norm_eq_one_iff Real F _ _ _ x y

/--
theorem `inner_eq_norm_mul_iff_div` / 定理 `inner_eq_norm_mul_iff_div`

English:
theorem inner_eq_norm_mul_iff_div
  given: {x y : E} (h₀ : x != 0)
  proof: by
  have h₀' := h₀
  rw [← norm_ne_zero_iff]; rw [Ne]; rw [← @ofReal_eq_zero 𝕜] at h₀'
  constructor <;> intro h
  · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : 𝕜) • x :=
      ((norm_inner_eq_norm_tfae 𝕜 x y).out 0 1).1 (by simp [h])
    rw [this.resolve_left h₀]; rw [h]
    simp [norm_smul, mul_div_cancel_right₀ _ h₀']
  · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field

中文:
定理 inner_eq_norm_mul_iff_div
  条件: {x y : E} (h₀ : x != 0)
  证明: by
  have h₀' := h₀
  rw [← norm_ne_zero_iff]; rw [Ne]; rw [← @ofReal_eq_zero 𝕜] at h₀'
  constructor <;> intro h
  · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : 𝕜) • x :=
      ((norm_inner_eq_norm_tfae 𝕜 x y).out 0 1).1 (by simp [h])
    rw [this.resolve_left h₀]; rw [h]
    simp [norm_smul, mul_div_cancel_right₀ _ h₀']
  · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field

Depends on / 依赖: conv_lhs, inner_self_eq_norm_sq_to_K, inner_smul_right, norm_inner_eq_norm_tfae, norm_ne_zero_iff, norm_smul, ofReal_eq_zero, resolve_left, this.resolve_left
-/
theorem inner_eq_norm_mul_iff_div {x y : E} (h₀ : x != 0) :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y := by
  have h₀' := h₀
  rw [← norm_ne_zero_iff]; rw [Ne]; rw [← @ofReal_eq_zero 𝕜] at h₀'
  constructor <;> intro h
  · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : 𝕜) • x :=
      ((norm_inner_eq_norm_tfae 𝕜 x y).out 0 1).1 (by simp [h])
    rw [this.resolve_left h₀]; rw [h]
    simp [norm_smul, mul_div_cancel_right₀ _ h₀']
  · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field

/--
theorem `inner_eq_norm_mul_iff` / 定理 `inner_eq_norm_mul_iff`

English:
theorem inner_eq_norm_mul_iff
  given: {x y : E}
  proof: by
  rcases eq_or_ne x 0 with (rfl | h₀)
  · simp
  · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
    rwa [Ne, ofReal_eq_zero, norm_eq_zero]

中文:
定理 inner_eq_norm_mul_iff
  条件: {x y : E}
  证明: by
  rcases eq_or_ne x 0 with (rfl | h₀)
  · simp
  · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
    rwa [Ne, ofReal_eq_zero, norm_eq_zero]

Depends on / 依赖: div_eq_inv_mul, eq_or_ne, inner_eq_norm_mul_iff_div, mul_smul, norm_eq_zero, ofReal_eq_zero
-/
theorem inner_eq_norm_mul_iff {x y : E} :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y := by
  rcases eq_or_ne x 0 with (rfl | h₀)
  · simp
  · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
    rwa [Ne, ofReal_eq_zero, norm_eq_zero]

/--
theorem `inner_eq_norm_mul_iff_real` / 定理 `inner_eq_norm_mul_iff_real`

English:
theorem inner_eq_norm_mul_iff_real
  given: {x y : F}
  statement: ⟪x, y⟫_Real = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
  proof: inner_eq_norm_mul_iff

中文:
定理 inner_eq_norm_mul_iff_real
  条件: {x y : F}
  结论: ⟪x, y⟫_实数 = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
  证明: inner_eq_norm_mul_iff

Depends on / 依赖: inner_eq_norm_mul_iff
-/
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_Real = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
  inner_eq_norm_mul_iff

/--
theorem `real_inner_div_norm_mul_norm_eq_one_iff` / 定理 `real_inner_div_norm_mul_norm_eq_one_iff`

English:
theorem real_inner_div_norm_mul_norm_eq_one_iff
  given: (x y : F)
  proof: by
  constructor
  · intro h
    have hx₀ : x != 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y != 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, ‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy₀) (norm_pos_iff.2 hx₀), ?_⟩
    exact ((inner_eq_norm_mul_iff_div hx₀).1 (eq_of_div_eq_one h)).symm
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr

中文:
定理 real_inner_div_norm_mul_norm_eq_one_iff
  条件: (x y : F)
  证明: by
  constructor
  · intro h
    have hx₀ : x != 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y != 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, ‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy₀) (norm_pos_iff.2 hx₀), ?_⟩
    exact ((inner_eq_norm_mul_iff_div hx₀).1 (eq_of_div_eq_one h)).symm
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr

Depends on / 依赖: div_pos, eq_of_div_eq_one, inner_eq_norm_mul_iff_div, norm_pos_iff, real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
-/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_Real / (‖x‖ * ‖y‖) = 1 ↔ x != 0 ∧ exists r : Real, 0 < r ∧ y = r • x := by
  constructor
  · intro h
    have hx₀ : x != 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y != 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, ‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy₀) (norm_pos_iff.2 hx₀), ?_⟩
    exact ((inner_eq_norm_mul_iff_div hx₀).1 (eq_of_div_eq_one h)).symm
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr

/--
theorem `real_inner_div_norm_mul_norm_eq_neg_one_iff` / 定理 `real_inner_div_norm_mul_norm_eq_neg_one_iff`

English:
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff
  given: (x y : F)
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_div]; rw [← inner_neg_right]; rw [← norm_neg y]; rw [real_inner_div_norm_mul_norm_eq_one_iff]; rw [(@neg_surjective Real _).exists]
  refine Iff.rfl.and (exists_congr fun r => ?_)
  rw [neg_pos]; rw [neg_smul]; rw [neg_inj]

中文:
定理 real_inner_div_norm_mul_norm_eq_neg_one_iff
  条件: (x y : F)
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_div]; rw [← inner_neg_right]; rw [← norm_neg y]; rw [real_inner_div_norm_mul_norm_eq_one_iff]; rw [(@neg_surjective Real _).exists]
  refine Iff.rfl.and (exists_congr fun r => ?_)
  rw [neg_pos]; rw [neg_smul]; rw [neg_inj]

Depends on / 依赖: Iff.rfl.and, exists_congr, inner_neg_right, neg_div, neg_eq_iff_eq_neg, neg_inj, neg_pos, neg_smul, neg_surjective, norm_neg, real_inner_div_norm_mul_norm_eq_one_iff
-/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_Real / (‖x‖ * ‖y‖) = -1 ↔ x != 0 ∧ exists r : Real, r < 0 ∧ y = r • x := by
  rw [← neg_eq_iff_eq_neg]; rw [← neg_div]; rw [← inner_neg_right]; rw [← norm_neg y]; rw [real_inner_div_norm_mul_norm_eq_one_iff]; rw [(@neg_surjective Real _).exists]
  refine Iff.rfl.and (exists_congr fun r => ?_)
  rw [neg_pos]; rw [neg_smul]; rw [neg_inj]

/--
theorem `inner_eq_one_iff_of_norm_eq_one` / 定理 `inner_eq_one_iff_of_norm_eq_one`

English:
theorem inner_eq_one_iff_of_norm_eq_one
  given: {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by
  convert inner_eq_norm_mul_iff (𝕜 := 𝕜) (E := E) <;> simp [hx, hy]

中文:
定理 inner_eq_one_iff_of_norm_eq_one
  条件: {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by
  convert inner_eq_norm_mul_iff (𝕜 := 𝕜) (E := E) <;> simp [hx, hy]

Depends on / 依赖: convert, inner_eq_norm_mul_iff
-/
theorem inner_eq_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = 1 ↔ x = y := by
  convert inner_eq_norm_mul_iff (𝕜 := 𝕜) (E := E) <;> simp [hx, hy]

/--
theorem `inner_eq_neg_one_iff_of_norm_eq_one` / 定理 `inner_eq_neg_one_iff_of_norm_eq_one`

English:
theorem inner_eq_neg_one_iff_of_norm_eq_one
  given: {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by
  rw [← neg_eq_iff_eq_neg]; rw [← inner_neg_right]; rw [inner_eq_one_iff_of_norm_eq_one hx (norm_neg y ▸ hy)]

中文:
定理 inner_eq_neg_one_iff_of_norm_eq_one
  条件: {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by
  rw [← neg_eq_iff_eq_neg]; rw [← inner_neg_right]; rw [inner_eq_one_iff_of_norm_eq_one hx (norm_neg y ▸ hy)]

Depends on / 依赖: inner_eq_one_iff_of_norm_eq_one, inner_neg_right, neg_eq_iff_eq_neg, norm_neg
-/
theorem inner_eq_neg_one_iff_of_norm_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = -1 ↔ x = -y := by
  rw [← neg_eq_iff_eq_neg]; rw [← inner_neg_right]; rw [inner_eq_one_iff_of_norm_eq_one hx (norm_neg y ▸ hy)]

/--
theorem `real_inner_le_one_of_norm_eq_one` / 定理 `real_inner_le_one_of_norm_eq_one`

English:
theorem real_inner_le_one_of_norm_eq_one
  given: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by
  simpa [hx, hy] using real_inner_le_norm x y

中文:
定理 real_inner_le_one_of_norm_eq_one
  条件: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by
  simpa [hx, hy] using real_inner_le_norm x y

Depends on / 依赖: real_inner_le_norm
-/
theorem real_inner_le_one_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_Real <= 1 := by
  simpa [hx, hy] using real_inner_le_norm x y

/--
theorem `neg_one_le_real_inner_of_norm_eq_one` / 定理 `neg_one_le_real_inner_of_norm_eq_one`

English:
theorem neg_one_le_real_inner_of_norm_eq_one
  given: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by
  simpa [hx, hy] using neg_le_of_abs_le (abs_real_inner_le_norm x y)

中文:
定理 neg_one_le_real_inner_of_norm_eq_one
  条件: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by
  simpa [hx, hy] using neg_le_of_abs_le (abs_real_inner_le_norm x y)

Depends on / 依赖: abs_real_inner_le_norm, neg_le_of_abs_le
-/
theorem neg_one_le_real_inner_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 <= ⟪x, y⟫_Real := by
  simpa [hx, hy] using neg_le_of_abs_le (abs_real_inner_le_norm x y)

/--
theorem `real_inner_mem_Icc_of_norm_eq_one` / 定理 `real_inner_mem_Icc_of_norm_eq_one`

English:
theorem real_inner_mem_Icc_of_norm_eq_one
  given: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: ⟨neg_one_le_real_inner_of_norm_eq_one hx hy, real_inner_le_one_of_norm_eq_one hx hy⟩

中文:
定理 real_inner_mem_Icc_of_norm_eq_one
  条件: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: ⟨neg_one_le_real_inner_of_norm_eq_one hx hy, real_inner_le_one_of_norm_eq_one hx hy⟩

Depends on / 依赖: neg_one_le_real_inner_of_norm_eq_one, real_inner_le_one_of_norm_eq_one
-/
theorem real_inner_mem_Icc_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_Real in Set.Icc (-1) 1 :=
  ⟨neg_one_le_real_inner_of_norm_eq_one hx hy, real_inner_le_one_of_norm_eq_one hx hy⟩

/--
theorem `inner_self_eq_one_of_norm_eq_one` / 定理 `inner_self_eq_one_of_norm_eq_one`

English:
theorem inner_self_eq_one_of_norm_eq_one
  given: {x : E} (hx : ‖x‖ = 1)
  statement: ⟪x, x⟫_𝕜 = 1
  proof: (inner_eq_one_iff_of_norm_eq_one hx hx).mpr rfl

中文:
定理 inner_self_eq_one_of_norm_eq_one
  条件: {x : E} (hx : ‖x‖ = 1)
  结论: ⟪x, x⟫_𝕜 = 1
  证明: (inner_eq_one_iff_of_norm_eq_one hx hx).mpr rfl

Depends on / 依赖: inner_eq_one_iff_of_norm_eq_one
-/
theorem inner_self_eq_one_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_𝕜 = 1 :=
  (inner_eq_one_iff_of_norm_eq_one hx hx).mpr rfl

/--
theorem `inner_lt_norm_mul_iff_real` / 定理 `inner_lt_norm_mul_iff_real`

English:
theorem inner_lt_norm_mul_iff_real
  given: {x y : F}
  statement: ⟪x, y⟫_Real < ‖x‖ * ‖y‖ ↔ ‖y‖ • x != ‖x‖ • y
  proof: calc
    ⟪x, y⟫_Real < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_Real != ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x != ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real

中文:
定理 inner_lt_norm_mul_iff_real
  条件: {x y : F}
  结论: ⟪x, y⟫_实数 < ‖x‖ * ‖y‖ ↔ ‖y‖ • x != ‖x‖ • y
  证明: calc
    ⟪x, y⟫_Real < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_Real != ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x != ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real

Depends on / 依赖: _Real, inner_eq_norm_mul_iff_real, lt_of_le_of_ne, ne_of_lt, not_congr, real_inner_le_norm
-/
theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_Real < ‖x‖ * ‖y‖ ↔ ‖y‖ • x != ‖x‖ • y :=
  calc
    ⟪x, y⟫_Real < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_Real != ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x != ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real

/--
theorem `inner_lt_one_iff_real_of_norm_eq_one` / 定理 `inner_lt_one_iff_real_of_norm_eq_one`

English:
theorem inner_lt_one_iff_real_of_norm_eq_one
  given: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  proof: by convert! inner_lt_norm_mul_iff_real (F := F) <;> simp [hx, hy]

中文:
定理 inner_lt_one_iff_real_of_norm_eq_one
  条件: {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
  证明: by convert! inner_lt_norm_mul_iff_real (F := F) <;> simp [hx, hy]

Depends on / 依赖: convert, inner_lt_norm_mul_iff_real
-/
theorem inner_lt_one_iff_real_of_norm_eq_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_Real < 1 ↔ x != y := by convert! inner_lt_norm_mul_iff_real (F := F) <;> simp [hx, hy]

/--
theorem `eq_of_norm_le_re_inner_eq_norm_sq` / 定理 `eq_of_norm_le_re_inner_eq_norm_sq`

English:
theorem eq_of_norm_le_re_inner_eq_norm_sq
  given: {x y : E} (hle : ‖x‖ <= ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2)
  proof: by
  suffices H : re ⟪x - y, x - y⟫ <= 0 by rwa [re_inner_self_nonpos, sub_eq_zero] at H
  have H₁ : ‖x‖ ^ 2 <= ‖y‖ ^ 2 := by gcongr
  have H₂ : re ⟪y, x⟫ = ‖y‖ ^ 2 := by rwa [← inner_conj_symm, conj_re]
  simp only [inner_sub_left, inner_sub_right]
  simpa [h, H₂] using H₁

中文:
定理 eq_of_norm_le_re_inner_eq_norm_sq
  条件: {x y : E} (hle : ‖x‖ <= ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2)
  证明: by
  suffices H : re ⟪x - y, x - y⟫ <= 0 by rwa [re_inner_self_nonpos, sub_eq_zero] at H
  have H₁ : ‖x‖ ^ 2 <= ‖y‖ ^ 2 := by gcongr
  have H₂ : re ⟪y, x⟫ = ‖y‖ ^ 2 := by rwa [← inner_conj_symm, conj_re]
  simp only [inner_sub_left, inner_sub_right]
  simpa [h, H₂] using H₁

Depends on / 依赖: conj_re, inner_conj_symm, inner_sub_left, inner_sub_right, re_inner_self_nonpos, sub_eq_zero
-/
theorem eq_of_norm_le_re_inner_eq_norm_sq {x y : E} (hle : ‖x‖ <= ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2) :
    x = y := by
  suffices H : re ⟪x - y, x - y⟫ <= 0 by rwa [re_inner_self_nonpos, sub_eq_zero] at H
  have H₁ : ‖x‖ ^ 2 <= ‖y‖ ^ 2 := by gcongr
  have H₂ : re ⟪y, x⟫ = ‖y‖ ^ 2 := by rwa [← inner_conj_symm, conj_re]
  simp only [inner_sub_left, inner_sub_right]
  simpa [h, H₂] using H₁

/--
theorem `norm_add_eq_iff_real` / 定理 `norm_add_eq_iff_real`

English:
theorem norm_add_eq_iff_real
  given: {x y : F}
  statement: ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
  proof: by
  rw [← pow_left_inj₀ (norm_nonneg _) (Left.add_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero]; rw [norm_add_sq (𝕜 := Real)]; rw [add_pow_two]; rw [add_left_inj]; rw [add_right_inj]; rw [re_to_real]; rw [mul_assoc]; rw [mul_right_inj' two_ne_zero]; rw [← inner_eq_norm_mul_iff_real]

中文:
定理 norm_add_eq_iff_real
  条件: {x y : F}
  结论: ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y
  证明: by
  rw [← pow_left_inj₀ (norm_nonneg _) (Left.add_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero]; rw [norm_add_sq (𝕜 := Real)]; rw [add_pow_two]; rw [add_left_inj]; rw [add_right_inj]; rw [re_to_real]; rw [mul_assoc]; rw [mul_right_inj' two_ne_zero]; rw [← inner_eq_norm_mul_iff_real]

Depends on / 依赖: Left.add_nonneg, add_left_inj, add_nonneg, add_pow_two, add_right_inj, inner_eq_norm_mul_iff_real, mul_assoc, mul_right_inj, norm_add_sq, norm_nonneg, re_to_real, two_ne_zero
-/
theorem norm_add_eq_iff_real {x y : F} : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y := by
  rw [← pow_left_inj₀ (norm_nonneg _) (Left.add_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero]; rw [norm_add_sq (𝕜 := Real)]; rw [add_pow_two]; rw [add_left_inj]; rw [add_right_inj]; rw [re_to_real]; rw [mul_assoc]; rw [mul_right_inj' two_ne_zero]; rw [← inner_eq_norm_mul_iff_real]

end Norm

section Induced

variable {G : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] [AddCommGroup G]
    [Module 𝕜 G]

/--
Definition of `InnerProductSpace.induced` / `InnerProductSpace.induced` 的定义

English:
abbreviation InnerProductSpace.induced
  signature: {F : Type*} [FunLike F G E] [LinearMapClass F 𝕜 G E] (f : F)
  body: SeminormedAddCommGroup.induced G E f
    InnerProductSpace 𝕜 G :=
  letI := SeminormedAddCommGroup.induced G E f
  letI := NormedSpace.induced 𝕜 G E f
  { inner x y := inner 𝕜 (f x) (f y)
    add_left x y z := by rw [map_add, inner_add_left]
    smul_left x y r := by rw [map_smul, inner_smul_left]
    norm_sq_eq_re_inner x := norm_sq_eq_re_inner (f x)
    conj_inner_symm x y := inner_conj_symm (f x) (f y) }

中文:
缩写 内积空间.induced
  签名: {F : 类型} [函数状 F G E] [线性映射类 F 𝕜 G E] (f : F)
  定义体: SeminormedAddCommGroup.induced G E f
    InnerProductSpace 𝕜 G :=
  letI := SeminormedAddCommGroup.induced G E f
  letI := NormedSpace.induced 𝕜 G E f
  { inner x y := inner 𝕜 (f x) (f y)
    add_left x y z := by rw [map_add, inner_add_left]
    smul_left x y r := by rw [map_smul, inner_smul_left]
    norm_sq_eq_re_inner x := norm_sq_eq_re_inner (f x)
    conj_inner_symm x y := inner_conj_symm (f x) (f y) }

Depends on / 依赖: SeminormedAddCommGroup, SeminormedAddCommGroup.induced, induced
-/
abbrev InnerProductSpace.induced {F : Type*} [FunLike F G E] [LinearMapClass F 𝕜 G E] (f : F) :
    letI := SeminormedAddCommGroup.induced G E f
    InnerProductSpace 𝕜 G :=
  letI := SeminormedAddCommGroup.induced G E f
  letI := NormedSpace.induced 𝕜 G E f
  { inner x y := inner 𝕜 (f x) (f y)
    add_left x y z := by rw [map_add, inner_add_left]
    smul_left x y r := by rw [map_smul, inner_smul_left]
    norm_sq_eq_re_inner x := norm_sq_eq_re_inner (f x)
    conj_inner_symm x y := inner_conj_symm (f x) (f y) }

/--
theorem `inner_induced_eq` / 定理 `inner_induced_eq`

English:
theorem inner_induced_eq
  given: (g₁ g₂ : G) (f : G ->ₗ[𝕜] E)
  proof: InnerProductSpace.induced f
    inner 𝕜 g₁ g₂ = inner 𝕜 (f g₁) (f g₂) := rfl

中文:
定理 inner_induced_eq
  条件: (g₁ g₂ : G) (f : G ->ₗ[𝕜] E)
  证明: InnerProductSpace.induced f
    inner 𝕜 g₁ g₂ = inner 𝕜 (f g₁) (f g₂) := rfl

Depends on / 依赖: InnerProductSpace, InnerProductSpace.induced, induced
-/
theorem inner_induced_eq (g₁ g₂ : G) (f : G ->ₗ[𝕜] E) :
    letI := InnerProductSpace.induced f
    inner 𝕜 g₁ g₂ = inner 𝕜 (f g₁) (f g₂) := rfl

end Induced

section RCLike

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
Instance `RCLike.innerProductSpace` / 实例 `RCLike.innerProductSpace`

English:
instance RCLike.innerProductSpace
  signature: : InnerProductSpace 𝕜 𝕜 where
  body: y * star x
  norm_sq_eq_re_inner x := by rw [star_def, mul_conj, ← ofReal_pow, ofReal_re]
  conj_inner_symm x y := by rw [star_def, map_mul, starRingEnd_self_apply, mul_comm]
  add_left x y z := by rw [star_def, map_add, mul_add]
  smul_left x y z := by rw [star_def, smul_eq_mul, map_mul, mul_left_comm]

@[simp]

中文:
实例 RCLike.innerProductSpace
  签名: : 内积空间 𝕜 𝕜 where
  定义体: y * star x
  norm_sq_eq_re_inner x := by rw [star_def, mul_conj, ← ofReal_pow, ofReal_re]
  conj_inner_symm x y := by rw [star_def, map_mul, starRingEnd_self_apply, mul_comm]
  add_left x y z := by rw [star_def, map_add, mul_add]
  smul_left x y z := by rw [star_def, smul_eq_mul, map_mul, mul_left_comm]

@[simp]
-/
instance RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜 where
  inner x y := y * star x
  norm_sq_eq_re_inner x := by rw [star_def, mul_conj, ← ofReal_pow, ofReal_re]
  conj_inner_symm x y := by rw [star_def, map_mul, starRingEnd_self_apply, mul_comm]
  add_left x y z := by rw [star_def, map_add, mul_add]
  smul_left x y z := by rw [star_def, smul_eq_mul, map_mul, mul_left_comm]

@[simp]
/--
theorem `RCLike.inner_apply` / 定理 `RCLike.inner_apply`

English:
theorem RCLike.inner_apply
  given: (x y : 𝕜)
  statement: ⟪x, y⟫ = y * conj x
  proof: rfl

中文:
定理 RCLike.inner_apply
  条件: (x y : 𝕜)
  结论: ⟪x, y⟫ = y * conj x
  证明: rfl
-/
theorem RCLike.inner_apply (x y : 𝕜) : ⟪x, y⟫ = y * conj x :=
  rfl

/--
theorem `RCLike.inner_apply'` / 定理 `RCLike.inner_apply'`

English:
theorem RCLike.inner_apply'
  given: (x y : 𝕜)
  statement: ⟪x, y⟫ = conj x * y
  proof: mul_comm _ _

中文:
定理 RCLike.inner_apply'
  条件: (x y : 𝕜)
  结论: ⟪x, y⟫ = conj x * y
  证明: mul_comm _ _

Depends on / 依赖: mul_comm
-/
theorem RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y := mul_comm _ _

end RCLike

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}
variable (𝕜 E)
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A general inner product implies a real inner product. This is not registered as an instance
since `𝕜` does not appear in the return type `Inner ℝ E`. -/
@[instance_reducible]
/--
Definition of `Inner.rclikeToReal` / `Inner.rclikeToReal` 的定义

English:
definition Inner.rclikeToReal
  signature: : Inner Real E where inner x y
  body: re ⟪x, y⟫

中文:
定义 内积.rclikeTo实数
  签名: : 内积 实数 E where inner x y
  定义体: re ⟪x, y⟫
-/
def Inner.rclikeToReal : Inner Real E where inner x y := re ⟪x, y⟫

-- See note [reducible non-instances]
/--
Definition of `InnerProductSpace.rclikeToReal` / `InnerProductSpace.rclikeToReal` 的定义

English:
abbreviation InnerProductSpace.rclikeToReal
  signature: : InnerProductSpace Real E
  body: { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars Real 𝕜 E with
    norm_sq_eq_re_inner := norm_sq_eq_re_inner
    conj_inner_symm := fun _ _ => inner_re_symm _ _
    add_left := fun x y z => by
      simp +instances only [Inner.rclikeToReal, inner_add_left, map_add]
    smul_left := fun x y r => by
      let := NormedSpace.restrictScalars Real 𝕜 E
      have : r • x = (r : 𝕜) • x := rfl
      simp +instances only [Inner.rclikeToReal, this, conj_trivial, inner_smul_left, conj_ofReal,
        re_ofReal_mul] }

中文:
缩写 内积空间.rclikeTo实数
  签名: : 内积空间 实数 E
  定义体: { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars Real 𝕜 E with
    norm_sq_eq_re_inner := norm_sq_eq_re_inner
    conj_inner_symm := fun _ _ => inner_re_symm _ _
    add_left := fun x y z => by
      simp +instances only [Inner.rclikeToReal, inner_add_left, map_add]
    smul_left := fun x y r => by
      let := NormedSpace.restrictScalars Real 𝕜 E
      have : r • x = (r : 𝕜) • x := rfl
      simp +instances only [Inner.rclikeToReal, this, conj_trivial, inner_smul_left, conj_ofReal,
        re_ofReal_mul] }

Depends on / 依赖: Inner.rclikeToReal, NormedSpace, NormedSpace.restrictScalars, add_left, conj_inner_symm, conj_ofReal, conj_trivial, inner_add_left, inner_re_symm, inner_smul_left, instances, map_add, norm_sq_eq_re_inner, rclikeToReal, re_ofReal_mul, restrictScalars, smul_left
-/
abbrev InnerProductSpace.rclikeToReal : InnerProductSpace Real E :=
  { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars Real 𝕜 E with
    norm_sq_eq_re_inner := norm_sq_eq_re_inner
    conj_inner_symm := fun _ _ => inner_re_symm _ _
    add_left := fun x y z => by
      simp +instances only [Inner.rclikeToReal, inner_add_left, map_add]
    smul_left := fun x y r => by
      let := NormedSpace.restrictScalars Real 𝕜 E
      have : r • x = (r : 𝕜) • x := rfl
      simp +instances only [Inner.rclikeToReal, this, conj_trivial, inner_smul_left, conj_ofReal,
        re_ofReal_mul] }

variable {E}

/--
theorem `real_inner_eq_re_inner` / 定理 `real_inner_eq_re_inner`

English:
theorem real_inner_eq_re_inner
  given: (x y : E)
  proof: rfl

中文:
定理 real_inner_eq_re_inner
  条件: (x y : E)
  证明: rfl
-/
theorem real_inner_eq_re_inner (x y : E) :
    (Inner.rclikeToReal 𝕜 E).inner x y = re ⟪x, y⟫ :=
  rfl

/--
theorem `real_inner_I_smul_self` / 定理 `real_inner_I_smul_self`

English:
theorem real_inner_I_smul_self
  given: (x : E)
  proof: by
  simp [real_inner_eq_re_inner 𝕜, inner_smul_right]

中文:
定理 real_inner_I_smul_self
  条件: (x : E)
  证明: by
  simp [real_inner_eq_re_inner 𝕜, inner_smul_right]

Depends on / 依赖: inner_smul_right, real_inner_eq_re_inner
-/
theorem real_inner_I_smul_self (x : E) :
    (Inner.rclikeToReal 𝕜 E).inner x ((I : 𝕜) • x) = 0 := by
  simp [real_inner_eq_re_inner 𝕜, inner_smul_right]

/-- A complex inner product implies a real inner product. This cannot be an instance since it
creates a diamond with `PiLp.innerProductSpace` because `re (sum i, ⟪x i, y i⟫)` and
`sum i, re ⟪x i, y i⟫` are not defeq. -/
@[instance_reducible]
/--
Definition of `InnerProductSpace.complexToReal` / `InnerProductSpace.complexToReal` 的定义

English:
definition InnerProductSpace.complexToReal
  signature: [SeminormedAddCommGroup G] [InnerProductSpace Complex G]
  body: InnerProductSpace.rclikeToReal Complex G

中文:
定义 内积空间.complexTo实数
  签名: [SeminormedAddComm群 G] [内积空间 复形 G]
  定义体: InnerProductSpace.rclikeToReal Complex G

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, rclikeToReal
-/
def InnerProductSpace.complexToReal [SeminormedAddCommGroup G] [InnerProductSpace Complex G] :
    InnerProductSpace Real G :=
  InnerProductSpace.rclikeToReal Complex G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InnerProductSpace Real Complex
  body: InnerProductSpace.complexToReal

@[simp]

中文:
实例 :
  签名: 内积空间 实数 复形
  定义体: InnerProductSpace.complexToReal

@[simp]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.complexToReal, complexToReal
-/
instance : InnerProductSpace Real Complex := InnerProductSpace.complexToReal

@[simp]
/--
theorem `Complex.inner` / 定理 `Complex.inner`

English:
theorem Complex.inner
  given: (w z : Complex)
  statement: ⟪w, z⟫_Real = (z * conj w).re
  proof: rfl

中文:
定理 复形.inner
  条件: (w z : 复形)
  结论: ⟪w, z⟫_实数 = (z * conj w).re
  证明: rfl
-/
protected theorem Complex.inner (w z : Complex) : ⟪w, z⟫_Real = (z * conj w).re :=
  rfl

end RCLikeToReal

/--
Instance `RCLike.toInnerProductSpaceReal` / 实例 `RCLike.toInnerProductSpaceReal`

English:
instance RCLike.toInnerProductSpaceReal
  signature: : InnerProductSpace Real 𝕜 where
  body: Inner.rclikeToReal 𝕜 𝕜
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm x y := inner_re_symm ..
  add_left x y z :=
    show re (_ * _) = re (_ * _) + re (_ * _) by
      simp only [star_def, map_add, mul_re, conj_re, conj_im]; ring
  smul_left x y r :=
    show re (_ * _) = _ * re (_ * _) by
      simp only [star_def, mul_re, conj_re, conj_im, conj_trivial, smul_re, smul_im]; ring

中文:
实例 RCLike.toInnerProductSpace实数
  签名: : 内积空间 实数 𝕜 where
  定义体: Inner.rclikeToReal 𝕜 𝕜
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm x y := inner_re_symm ..
  add_left x y z :=
    show re (_ * _) = re (_ * _) + re (_ * _) by
      simp only [star_def, map_add, mul_re, conj_re, conj_im]; ring
  smul_left x y r :=
    show re (_ * _) = _ * re (_ * _) by
      simp only [star_def, mul_re, conj_re, conj_im, conj_trivial, smul_re, smul_im]; ring

Depends on / 依赖: Inner.rclikeToReal, rclikeToReal
-/
noncomputable instance RCLike.toInnerProductSpaceReal : InnerProductSpace Real 𝕜 where
  __ := Inner.rclikeToReal 𝕜 𝕜
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm x y := inner_re_symm ..
  add_left x y z :=
    show re (_ * _) = re (_ * _) + re (_ * _) by
      simp only [star_def, map_add, mul_re, conj_re, conj_im]; ring
  smul_left x y r :=
    show re (_ * _) = _ * re (_ * _) by
      simp only [star_def, mul_re, conj_re, conj_im, conj_trivial, smul_re, smul_im]; ring

-- The instance above does not create diamonds for concrete `𝕜`:
example : (innerProductSpace : InnerProductSpace Real Real) = RCLike.toInnerProductSpaceReal := rfl
example :
    (instInnerProductSpaceRealComplex : InnerProductSpace Real Complex) = RCLike.toInnerProductSpaceReal :=
  rfl

/--
theorem `Real.inner_apply` / 定理 `Real.inner_apply`

English:
theorem Real.inner_apply
  given: (x y : Real)
  statement: inner Real x y = x * y
  proof: by rw [mul_comm]; rfl

中文:
定理 实数.inner_apply
  条件: (x y : 实数)
  结论: inner 实数 x y = x * y
  证明: by rw [mul_comm]; rfl

Depends on / 依赖: mul_comm
-/
theorem Real.inner_apply (x y : Real) : inner Real x y = x * y := by rw [mul_comm]; rfl

section IsPosSemidef

variable [NormedAddCommGroup E] [InnerProductSpace Real E]

/--
lemma `isSymm_inner` / 引理 `isSymm_inner`

English:
lemma isSymm_inner
  statement: LinearMap.IsSymm (innerₗ E) where
  proof: by simp [real_inner_comm]

中文:
引理 isSymm_inner
  结论: 线性映射.是Symm (innerₗ E) where
  证明: by simp [real_inner_comm]

Depends on / 依赖: real_inner_comm
-/
lemma isSymm_inner : LinearMap.IsSymm (innerₗ E) where
  eq x y := by simp [real_inner_comm]

/--
lemma `isNonneg_inner` / 引理 `isNonneg_inner`

English:
lemma isNonneg_inner
  statement: LinearMap.IsNonneg (innerₗ E) where
  proof: by simp

中文:
引理 isNonneg_inner
  结论: 线性映射.是Nonneg (innerₗ E) where
  证明: by simp
-/
lemma isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where
  nonneg x := by simp

/--
lemma `isPosSemidef_inner` / 引理 `isPosSemidef_inner`

English:
lemma isPosSemidef_inner
  statement: LinearMap.IsPosSemidef (innerₗ E) where
  proof: isSymm_inner
  isNonneg := isNonneg_inner

中文:
引理 isPosSemidef_inner
  结论: 线性映射.是PosSemidef (innerₗ E) where
  证明: isSymm_inner
  isNonneg := isNonneg_inner

Depends on / 依赖: isSymm_inner
-/
lemma isPosSemidef_inner : LinearMap.IsPosSemidef (innerₗ E) where
  isSymm := isSymm_inner
  isNonneg := isNonneg_inner

end IsPosSemidef

example : (instInnerProductSpaceRealComplex.toSMul : SMul Real Complex) =
    Complex.instRCLike.toSMul := by
  with_reducible_and_instances rfl
