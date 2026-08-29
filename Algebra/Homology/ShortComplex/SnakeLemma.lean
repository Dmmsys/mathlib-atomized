/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The snake lemma

The snake lemma is a standard tool in homological algebra. The basic situation
is when we have a diagram as follows in an abelian category `C`, with exact rows:

    L₁.X₁ ⟶ L₁.X₂ ⟶ L₁.X₃ ⟶ 0
      | | |
      |v₁₂.τ₁ |v₁₂.τ₂ |v₁₂.τ₃
      v v v
0 ⟶ L₂.X₁ ⟶ L₂.X₂ ⟶ L₂.X₃

We shall think of this diagram as the datum of a morphism `v₁₂ : L₁ ⟶ L₂` in the
category `ShortComplex C` such that both `L₁` and `L₂` are exact, and `L₁.g` is epi
and `L₂.f` is a mono (which is equivalent to saying that `L₁.X₃` is the cokernel
of `L₁.f` and `L₂.X₁` is the kernel of `L₂.g`). Then, we may introduce the kernels
and cokernels of the vertical maps. In other words, we may introduce short complexes
`L₀` and `L₃` that are respectively the kernel and the cokernel of `v₁₂`. All these
data constitute a `SnakeInput C`.

Given such a `S : SnakeInput C`, we define a connecting homomorphism
`S.δ : L₀.X₃ ⟶ L₃.X₁` and show that it is part of an exact sequence
`L₀.X₁ ⟶ L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂ ⟶ L₃.X₃`. Each of the four exactness
statement is first stated separately as lemmas `L₀_exact`, `L₁'_exact`,
`L₂'_exact` and `L₃_exact` and the full 6-term exact sequence is stated
as `snake_lemma`. This sequence can even be extended with an extra `0`
on the left (see `mono_L₀_f`) if `L₁.X₁ ⟶ L₁.X₂` is a mono (i.e. `L₁` is short exact),
and similarly an extra `0` can be added on the right (`epi_L₃_g`)
if `L₂.X₂ ⟶ L₂.X₃` is an epi (i.e. `L₂` is short exact).

These results were also obtained in the Liquid Tensor Experiment. The code and the proof
here are slightly easier because of the use of the category `ShortComplex C`,
the use of duality (which allows to construct only half of the sequence, and deducing
the other half by arguing in the opposite category), and the use of "refinements"
(see `CategoryTheory.Abelian.Refinements`) instead of a weak form of pseudo-elements.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type*) [Category* C] [Abelian C]

namespace ShortComplex

/--
Definition of `SnakeInput` / `SnakeInput` 的定义

English:
structure SnakeInput
  parameters: where
  axioms and operations (15):
    - L₀ : ShortComplex C
    - L₁ : ShortComplex C
    - L₂ : ShortComplex C
    - L₃ : ShortComplex C
    - v₀₁ : L₀ ⟶ L₁
    - v₁₂ : L₁ ⟶ L₂
    - v₂₃ : L₂ ⟶ L₃
    - w₀₂ : v₀₁ ≫ v₁₂ = 0  [default: by cat_disch]
    - w₁₃ : v₁₂ ≫ v₂₃ = 0  [default: by cat_disch]
    - h₀ : IsLimit (KernelFork.ofι _ w₀₂)
    - h₃ : IsColimit (CokernelCofork.ofπ _ w₁₃)
    - L₁_exact : L₁.Exact
    - epi_L₁_g : Epi L₁.g
    - L₂_exact : L₂.Exact
    - mono_L₂_f : Mono L₂.f

中文:
结构 蛇输入
  参数: where
  公理与运算 (15 个):
    - L₀ : 短复形 C
    - L₁ : 短复形 C
    - L₂ : 短复形 C
    - L₃ : 短复形 C
    - v₀₁ : L₀ ⟶ L₁
    - v₁₂ : L₁ ⟶ L₂
    - v₂₃ : L₂ ⟶ L₃
    - w₀₂ : v₀₁ ≫ v₁₂ = 0  [默认: by cat_disch]
    - w₁₃ : v₁₂ ≫ v₂₃ = 0  [默认: by cat_disch]
    - h₀ : 是极限 (核叉.ofι _ w₀₂)
    - h₃ : 是余极限 (余核余叉.ofπ _ w₁₃)
    - L₁_exact : L₁.正合
    - epi_L₁_g : 满态射 L₁.g
    - L₂_exact : L₂.正合
    - mono_L₂_f : 单态射 L₂.f

Depends on / 依赖: cat_disch
-/
structure SnakeInput where
  /-- the zeroth row -/
  L₀ : ShortComplex C
  /-- the first row -/
  L₁ : ShortComplex C
  /-- the second row -/
  L₂ : ShortComplex C
  /-- the third row -/
  L₃ : ShortComplex C
  /-- the morphism from the zeroth row to the first row -/
  v₀₁ : L₀ ⟶ L₁
  /-- the morphism from the first row to the second row -/
  v₁₂ : L₁ ⟶ L₂
  /-- the morphism from the second row to the third row -/
  v₂₃ : L₂ ⟶ L₃
  w₀₂ : v₀₁ ≫ v₁₂ = 0 := by cat_disch
  w₁₃ : v₁₂ ≫ v₂₃ = 0 := by cat_disch
  /-- `L₀` is the kernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₀ : IsLimit (KernelFork.ofι _ w₀₂)
  /-- `L₃` is the cokernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₃ : IsColimit (CokernelCofork.ofπ _ w₁₃)
  L₁_exact : L₁.Exact
  epi_L₁_g : Epi L₁.g
  L₂_exact : L₂.Exact
  mono_L₂_f : Mono L₂.f

initialize_simps_projections SnakeInput (-h₀, -h₃)

namespace SnakeInput

attribute [reassoc (attr := simp)] w₀₂ w₁₃
attribute [instance] epi_L₁_g
attribute [instance] mono_L₂_f

variable {C}
variable (S : SnakeInput C)

set_option backward.defeqAttrib.useBackward true in
/-- The snake input in the opposite category that is deduced from a snake input. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : SnakeInput Cᵒᵖ where
  body: S.L₃.op
  L₁ := S.L₂.op
  L₂ := S.L₁.op
  L₃ := S.L₀.op
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance
  v₀₁ := opMap S.v₂₃
  v₁₂ := opMap S.v₁₂
  v₂₃ := opMap S.v₀₁
  w₀₂ := congr_arg opMap S.w₁₃
  w₁₃ := congr_arg opMap S.w₀₂
  h₀ := isLimitForkMapOfIsLimit' (ShortC

中文:
定义 op
  签名: : 蛇输入 Cᵒᵖ where
  定义体: S.L₃.op
  L₁ := S.L₂.op
  L₂ := S.L₁.op
  L₃ := S.L₀.op
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance
  v₀₁ := opMap S.v₂₃
  v₁₂ := opMap S.v₁₂
  v₂₃ := opMap S.v₀₁
  w₀₂ := congr_arg opMap S.w₁₃
  w₁₃ := congr_arg opMap S.w₀₂
  h₀ := isLimitForkMapOfIsLimit' (ShortC
-/
noncomputable def op : SnakeInput Cᵒᵖ where
  L₀ := S.L₃.op
  L₁ := S.L₂.op
  L₂ := S.L₁.op
  L₃ := S.L₀.op
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance
  v₀₁ := opMap S.v₂₃
  v₁₂ := opMap S.v₁₂
  v₂₃ := opMap S.v₀₁
  w₀₂ := congr_arg opMap S.w₁₃
  w₁₃ := congr_arg opMap S.w₀₂
  h₀ := isLimitForkMapOfIsLimit' (ShortComplex.opEquiv C).functor _
      (CokernelCofork.IsColimit.ofπOp _ _ S.h₃)
  h₃ := isColimitCoforkMapOfIsColimit' (ShortComplex.opEquiv C).functor _
      (KernelFork.IsLimit.ofιOp _ _ S.h₀)
  L₁_exact := S.L₂_exact.op
  L₂_exact := S.L₁_exact.op

/--
lemma `w₀₂_τ₁` / 引理 `w₀₂_τ₁`

English:
lemma w₀₂_τ₁
  statement: S.v₀₁.τ₁ ≫ S.v₁₂.τ₁ = 0
  proof: by
  rw [← comp_τ₁]; rw [S.w₀₂]; rw [zero_τ₁]

中文:
引理 w₀₂_τ₁
  结论: S.v₀₁.τ₁ ≫ S.v₁₂.τ₁ = 0
  证明: by
  rw [← comp_τ₁]; rw [S.w₀₂]; rw [zero_τ₁]
-/
@[reassoc (attr := simp)] lemma w₀₂_τ₁ : S.v₀₁.τ₁ ≫ S.v₁₂.τ₁ = 0 := by
  rw [← comp_τ₁]; rw [S.w₀₂]; rw [zero_τ₁]
/--
lemma `w₀₂_τ₂` / 引理 `w₀₂_τ₂`

English:
lemma w₀₂_τ₂
  statement: S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0
  proof: by
  rw [← comp_τ₂]; rw [S.w₀₂]; rw [zero_τ₂]

中文:
引理 w₀₂_τ₂
  结论: S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0
  证明: by
  rw [← comp_τ₂]; rw [S.w₀₂]; rw [zero_τ₂]
-/
@[reassoc (attr := simp)] lemma w₀₂_τ₂ : S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0 := by
  rw [← comp_τ₂]; rw [S.w₀₂]; rw [zero_τ₂]
/--
lemma `w₀₂_τ₃` / 引理 `w₀₂_τ₃`

English:
lemma w₀₂_τ₃
  statement: S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0
  proof: by
  rw [← comp_τ₃]; rw [S.w₀₂]; rw [zero_τ₃]

中文:
引理 w₀₂_τ₃
  结论: S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0
  证明: by
  rw [← comp_τ₃]; rw [S.w₀₂]; rw [zero_τ₃]
-/
@[reassoc (attr := simp)] lemma w₀₂_τ₃ : S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0 := by
  rw [← comp_τ₃]; rw [S.w₀₂]; rw [zero_τ₃]
/--
lemma `w₁₃_τ₁` / 引理 `w₁₃_τ₁`

English:
lemma w₁₃_τ₁
  statement: S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0
  proof: by
  rw [← comp_τ₁]; rw [S.w₁₃]; rw [zero_τ₁]

中文:
引理 w₁₃_τ₁
  结论: S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0
  证明: by
  rw [← comp_τ₁]; rw [S.w₁₃]; rw [zero_τ₁]
-/
@[reassoc (attr := simp)] lemma w₁₃_τ₁ : S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0 := by
  rw [← comp_τ₁]; rw [S.w₁₃]; rw [zero_τ₁]
/--
lemma `w₁₃_τ₂` / 引理 `w₁₃_τ₂`

English:
lemma w₁₃_τ₂
  statement: S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0
  proof: by
  rw [← comp_τ₂]; rw [S.w₁₃]; rw [zero_τ₂]

中文:
引理 w₁₃_τ₂
  结论: S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0
  证明: by
  rw [← comp_τ₂]; rw [S.w₁₃]; rw [zero_τ₂]
-/
@[reassoc (attr := simp)] lemma w₁₃_τ₂ : S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0 := by
  rw [← comp_τ₂]; rw [S.w₁₃]; rw [zero_τ₂]
/--
lemma `w₁₃_τ₃` / 引理 `w₁₃_τ₃`

English:
lemma w₁₃_τ₃
  statement: S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0
  proof: by
  rw [← comp_τ₃]; rw [S.w₁₃]; rw [zero_τ₃]

中文:
引理 w₁₃_τ₃
  结论: S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0
  证明: by
  rw [← comp_τ₃]; rw [S.w₁₃]; rw [zero_τ₃]
-/
@[reassoc (attr := simp)] lemma w₁₃_τ₃ : S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0 := by
  rw [← comp_τ₃]; rw [S.w₁₃]; rw [zero_τ₃]

/--
Definition of `h₀τ₁` / `h₀τ₁` 的定义

English:
definition h₀τ₁
  signature: : IsLimit (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁)
  body: isLimitForkMapOfIsLimit' π₁ S.w₀₂ S.h₀

中文:
定义 h₀τ₁
  签名: : 是极限 (核叉.ofι S.v₀₁.τ₁ S.w₀₂_τ₁)
  定义体: isLimitForkMapOfIsLimit' π₁ S.w₀₂ S.h₀

Depends on / 依赖: isLimitForkMapOfIsLimit
-/
noncomputable def h₀τ₁ : IsLimit (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁) :=
  isLimitForkMapOfIsLimit' π₁ S.w₀₂ S.h₀

/--
Definition of `h₀τ₂` / `h₀τ₂` 的定义

English:
definition h₀τ₂
  signature: : IsLimit (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂)
  body: isLimitForkMapOfIsLimit' π₂ S.w₀₂ S.h₀

中文:
定义 h₀τ₂
  签名: : 是极限 (核叉.ofι S.v₀₁.τ₂ S.w₀₂_τ₂)
  定义体: isLimitForkMapOfIsLimit' π₂ S.w₀₂ S.h₀

Depends on / 依赖: isLimitForkMapOfIsLimit
-/
noncomputable def h₀τ₂ : IsLimit (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂) :=
  isLimitForkMapOfIsLimit' π₂ S.w₀₂ S.h₀

/--
Definition of `h₀τ₃` / `h₀τ₃` 的定义

English:
definition h₀τ₃
  signature: : IsLimit (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃)
  body: isLimitForkMapOfIsLimit' π₃ S.w₀₂ S.h₀

中文:
定义 h₀τ₃
  签名: : 是极限 (核叉.ofι S.v₀₁.τ₃ S.w₀₂_τ₃)
  定义体: isLimitForkMapOfIsLimit' π₃ S.w₀₂ S.h₀

Depends on / 依赖: isLimitForkMapOfIsLimit
-/
noncomputable def h₀τ₃ : IsLimit (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃) :=
  isLimitForkMapOfIsLimit' π₃ S.w₀₂ S.h₀

/--
Instance `mono_v₀₁_τ₁` / 实例 `mono_v₀₁_τ₁`

English:
instance mono_v₀₁_τ₁
  signature: : Mono S.v₀₁.τ₁
  body: mono_of_isLimit_fork S.h₀τ₁

中文:
实例 mono_v₀₁_τ₁
  签名: : 单态射 S.v₀₁.τ₁
  定义体: mono_of_isLimit_fork S.h₀τ₁

Depends on / 依赖: mono_of_isLimit_fork
-/
instance mono_v₀₁_τ₁ : Mono S.v₀₁.τ₁ := mono_of_isLimit_fork S.h₀τ₁
/--
Instance `mono_v₀₁_τ₂` / 实例 `mono_v₀₁_τ₂`

English:
instance mono_v₀₁_τ₂
  signature: : Mono S.v₀₁.τ₂
  body: mono_of_isLimit_fork S.h₀τ₂

中文:
实例 mono_v₀₁_τ₂
  签名: : 单态射 S.v₀₁.τ₂
  定义体: mono_of_isLimit_fork S.h₀τ₂

Depends on / 依赖: mono_of_isLimit_fork
-/
instance mono_v₀₁_τ₂ : Mono S.v₀₁.τ₂ := mono_of_isLimit_fork S.h₀τ₂
/--
Instance `mono_v₀₁_τ₃` / 实例 `mono_v₀₁_τ₃`

English:
instance mono_v₀₁_τ₃
  signature: : Mono S.v₀₁.τ₃
  body: mono_of_isLimit_fork S.h₀τ₃

中文:
实例 mono_v₀₁_τ₃
  签名: : 单态射 S.v₀₁.τ₃
  定义体: mono_of_isLimit_fork S.h₀τ₃

Depends on / 依赖: mono_of_isLimit_fork
-/
instance mono_v₀₁_τ₃ : Mono S.v₀₁.τ₃ := mono_of_isLimit_fork S.h₀τ₃

/--
lemma `exact_C₁_up` / 引理 `exact_C₁_up`

English:
lemma exact_C₁_up
  statement: (ShortComplex.mk S.v₀₁.τ₁ S.v₁₂.τ₁
  proof: exact_of_f_is_kernel _ S.h₀τ₁

中文:
引理 exact_C₁_up
  结论: (短复形.mk S.v₀₁.τ₁ S.v₁₂.τ₁
  证明: exact_of_f_is_kernel _ S.h₀τ₁

Depends on / 依赖: exact_of_f_is_kernel
-/
lemma exact_C₁_up : (ShortComplex.mk S.v₀₁.τ₁ S.v₁₂.τ₁
    (by rw [← comp_τ₁, S.w₀₂, zero_τ₁])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₁

/--
lemma `exact_C₂_up` / 引理 `exact_C₂_up`

English:
lemma exact_C₂_up
  statement: (ShortComplex.mk S.v₀₁.τ₂ S.v₁₂.τ₂
  proof: exact_of_f_is_kernel _ S.h₀τ₂

中文:
引理 exact_C₂_up
  结论: (短复形.mk S.v₀₁.τ₂ S.v₁₂.τ₂
  证明: exact_of_f_is_kernel _ S.h₀τ₂

Depends on / 依赖: exact_of_f_is_kernel
-/
lemma exact_C₂_up : (ShortComplex.mk S.v₀₁.τ₂ S.v₁₂.τ₂
    (by rw [← comp_τ₂, S.w₀₂, zero_τ₂])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₂

/--
lemma `exact_C₃_up` / 引理 `exact_C₃_up`

English:
lemma exact_C₃_up
  statement: (ShortComplex.mk S.v₀₁.τ₃ S.v₁₂.τ₃
  proof: exact_of_f_is_kernel _ S.h₀τ₃

中文:
引理 exact_C₃_up
  结论: (短复形.mk S.v₀₁.τ₃ S.v₁₂.τ₃
  证明: exact_of_f_is_kernel _ S.h₀τ₃

Depends on / 依赖: exact_of_f_is_kernel
-/
lemma exact_C₃_up : (ShortComplex.mk S.v₀₁.τ₃ S.v₁₂.τ₃
    (by rw [← comp_τ₃, S.w₀₂, zero_τ₃])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₃

/--
Instance `mono_L₀_f` / 实例 `mono_L₀_f`

English:
instance mono_L₀_f
  signature: [Mono S.L₁.f]
  body: by
  have : Mono (S.L₀.f ≫ S.v₀₁.τ₂) := by
    rw [← S.v₀₁.comm₁₂]
    apply mono_comp
  exact mono_of_mono _ S.v₀₁.τ₂

中文:
实例 mono_L₀_f
  签名: [单态射 S.L₁.f]
  定义体: by
  have : Mono (S.L₀.f ≫ S.v₀₁.τ₂) := by
    rw [← S.v₀₁.comm₁₂]
    apply mono_comp
  exact mono_of_mono _ S.v₀₁.τ₂

Depends on / 依赖: mono_comp, mono_of_mono
-/
instance mono_L₀_f [Mono S.L₁.f] : Mono S.L₀.f := by
  have : Mono (S.L₀.f ≫ S.v₀₁.τ₂) := by
    rw [← S.v₀₁.comm₁₂]
    apply mono_comp
  exact mono_of_mono _ S.v₀₁.τ₂

/--
Definition of `h₃τ₁` / `h₃τ₁` 的定义

English:
definition h₃τ₁
  signature: : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁)
  body: isColimitCoforkMapOfIsColimit' π₁ S.w₁₃ S.h₃

中文:
定义 h₃τ₁
  签名: : 是余极限 (余核余叉.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁)
  定义体: isColimitCoforkMapOfIsColimit' π₁ S.w₁₃ S.h₃

Depends on / 依赖: isColimitCoforkMapOfIsColimit
-/
noncomputable def h₃τ₁ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁) :=
  isColimitCoforkMapOfIsColimit' π₁ S.w₁₃ S.h₃

/--
Definition of `h₃τ₂` / `h₃τ₂` 的定义

English:
definition h₃τ₂
  signature: : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₂ S.w₁₃_τ₂)
  body: isColimitCoforkMapOfIsColimit' π₂ S.w₁₃ S.h₃

中文:
定义 h₃τ₂
  签名: : 是余极限 (余核余叉.ofπ S.v₂₃.τ₂ S.w₁₃_τ₂)
  定义体: isColimitCoforkMapOfIsColimit' π₂ S.w₁₃ S.h₃

Depends on / 依赖: isColimitCoforkMapOfIsColimit
-/
noncomputable def h₃τ₂ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₂ S.w₁₃_τ₂) :=
  isColimitCoforkMapOfIsColimit' π₂ S.w₁₃ S.h₃

/--
Definition of `h₃τ₃` / `h₃τ₃` 的定义

English:
definition h₃τ₃
  signature: : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₃ S.w₁₃_τ₃)
  body: isColimitCoforkMapOfIsColimit' π₃ S.w₁₃ S.h₃

中文:
定义 h₃τ₃
  签名: : 是余极限 (余核余叉.ofπ S.v₂₃.τ₃ S.w₁₃_τ₃)
  定义体: isColimitCoforkMapOfIsColimit' π₃ S.w₁₃ S.h₃

Depends on / 依赖: isColimitCoforkMapOfIsColimit
-/
noncomputable def h₃τ₃ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₃ S.w₁₃_τ₃) :=
  isColimitCoforkMapOfIsColimit' π₃ S.w₁₃ S.h₃

/--
Instance `epi_v₂₃_τ₁` / 实例 `epi_v₂₃_τ₁`

English:
instance epi_v₂₃_τ₁
  signature: : Epi S.v₂₃.τ₁
  body: epi_of_isColimit_cofork S.h₃τ₁

中文:
实例 epi_v₂₃_τ₁
  签名: : 满态射 S.v₂₃.τ₁
  定义体: epi_of_isColimit_cofork S.h₃τ₁

Depends on / 依赖: epi_of_isColimit_cofork
-/
instance epi_v₂₃_τ₁ : Epi S.v₂₃.τ₁ := epi_of_isColimit_cofork S.h₃τ₁
/--
Instance `epi_v₂₃_τ₂` / 实例 `epi_v₂₃_τ₂`

English:
instance epi_v₂₃_τ₂
  signature: : Epi S.v₂₃.τ₂
  body: epi_of_isColimit_cofork S.h₃τ₂

中文:
实例 epi_v₂₃_τ₂
  签名: : 满态射 S.v₂₃.τ₂
  定义体: epi_of_isColimit_cofork S.h₃τ₂

Depends on / 依赖: epi_of_isColimit_cofork
-/
instance epi_v₂₃_τ₂ : Epi S.v₂₃.τ₂ := epi_of_isColimit_cofork S.h₃τ₂
/--
Instance `epi_v₂₃_τ₃` / 实例 `epi_v₂₃_τ₃`

English:
instance epi_v₂₃_τ₃
  signature: : Epi S.v₂₃.τ₃
  body: epi_of_isColimit_cofork S.h₃τ₃

中文:
实例 epi_v₂₃_τ₃
  签名: : 满态射 S.v₂₃.τ₃
  定义体: epi_of_isColimit_cofork S.h₃τ₃

Depends on / 依赖: epi_of_isColimit_cofork
-/
instance epi_v₂₃_τ₃ : Epi S.v₂₃.τ₃ := epi_of_isColimit_cofork S.h₃τ₃

/--
lemma `exact_C₁_down` / 引理 `exact_C₁_down`

English:
lemma exact_C₁_down
  statement: (ShortComplex.mk S.v₁₂.τ₁ S.v₂₃.τ₁
  proof: exact_of_g_is_cokernel _ S.h₃τ₁

中文:
引理 exact_C₁_down
  结论: (短复形.mk S.v₁₂.τ₁ S.v₂₃.τ₁
  证明: exact_of_g_is_cokernel _ S.h₃τ₁

Depends on / 依赖: exact_of_g_is_cokernel
-/
lemma exact_C₁_down : (ShortComplex.mk S.v₁₂.τ₁ S.v₂₃.τ₁
    (by rw [← comp_τ₁, S.w₁₃, zero_τ₁])).Exact :=
  exact_of_g_is_cokernel _ S.h₃τ₁

/--
lemma `exact_C₂_down` / 引理 `exact_C₂_down`

English:
lemma exact_C₂_down
  statement: (ShortComplex.mk S.v₁₂.τ₂ S.v₂₃.τ₂
  proof: exact_of_g_is_cokernel _ S.h₃τ₂

中文:
引理 exact_C₂_down
  结论: (短复形.mk S.v₁₂.τ₂ S.v₂₃.τ₂
  证明: exact_of_g_is_cokernel _ S.h₃τ₂

Depends on / 依赖: exact_of_g_is_cokernel
-/
lemma exact_C₂_down : (ShortComplex.mk S.v₁₂.τ₂ S.v₂₃.τ₂
    (by rw [← comp_τ₂, S.w₁₃, zero_τ₂])).Exact :=
  exact_of_g_is_cokernel _ S.h₃τ₂

/--
lemma `exact_C₃_down` / 引理 `exact_C₃_down`

English:
lemma exact_C₃_down
  statement: (ShortComplex.mk S.v₁₂.τ₃ S.v₂₃.τ₃
  proof: exact_of_g_is_cokernel _ S.h₃τ₃

中文:
引理 exact_C₃_down
  结论: (短复形.mk S.v₁₂.τ₃ S.v₂₃.τ₃
  证明: exact_of_g_is_cokernel _ S.h₃τ₃

Depends on / 依赖: exact_of_g_is_cokernel
-/
lemma exact_C₃_down : (ShortComplex.mk S.v₁₂.τ₃ S.v₂₃.τ₃
    (by rw [← comp_τ₃, S.w₁₃, zero_τ₃])).Exact :=
  exact_of_g_is_cokernel _ S.h₃τ₃

/--
Instance `epi_L₃_g` / 实例 `epi_L₃_g`

English:
instance epi_L₃_g
  signature: [Epi S.L₂.g]
  body: by
  have : Epi (S.v₂₃.τ₂ ≫ S.L₃.g) := by
    rw [S.v₂₃.comm₂₃]
    apply epi_comp
  exact epi_of_epi S.v₂₃.τ₂ _

中文:
实例 epi_L₃_g
  签名: [满态射 S.L₂.g]
  定义体: by
  have : Epi (S.v₂₃.τ₂ ≫ S.L₃.g) := by
    rw [S.v₂₃.comm₂₃]
    apply epi_comp
  exact epi_of_epi S.v₂₃.τ₂ _

Depends on / 依赖: epi_comp, epi_of_epi
-/
instance epi_L₃_g [Epi S.L₂.g] : Epi S.L₃.g := by
  have : Epi (S.v₂₃.τ₂ ≫ S.L₃.g) := by
    rw [S.v₂₃.comm₂₃]
    apply epi_comp
  exact epi_of_epi S.v₂₃.τ₂ _

/--
lemma `L₀_exact` / 引理 `L₀_exact`

English:
lemma L₀_exact
  statement: S.L₀.Exact
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ S.v₀₁.τ₂)
    (by rw [assoc, S.v₀₁.comm₂₃, reassoc_of% hx₂, zero_comp])
  have hy₁' : y₁ ≫ S.v₁₂.τ₁ = 0 := by
    simp only [← cancel_mono S.L₂.f, ass

中文:
引理 L₀_exact
  结论: S.L₀.正合
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ S.v₀₁.τ₂)
    (by rw [assoc, S.v₀₁.comm₂₃, reassoc_of% hx₂, zero_comp])
  have hy₁' : y₁ ≫ S.v₁₂.τ₁ = 0 := by
    simp only [← cancel_mono S.L₂.f, ass

Depends on / 依赖: S.exact_C, ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, _exact.exact_up_to_refinements, _up.lift_f, cancel_mono, comp_zero, exact_iff_exact_up_to_refinements, exact_up_to_refinements, lift_f, reassoc_of, zero_comp
-/
lemma L₀_exact : S.L₀.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ S.v₀₁.τ₂)
    (by rw [assoc, S.v₀₁.comm₂₃, reassoc_of% hx₂, zero_comp])
  have hy₁' : y₁ ≫ S.v₁₂.τ₁ = 0 := by
    simp only [← cancel_mono S.L₂.f, assoc, zero_comp, S.v₁₂.comm₁₂,
      ← reassoc_of% hy₁, w₀₂_τ₂, comp_zero]
  obtain ⟨x₁, hx₁⟩ : exists x₁, x₁ ≫ S.v₀₁.τ₁ = y₁ := ⟨_, S.exact_C₁_up.lift_f y₁ hy₁'⟩
  refine ⟨A₁, π₁, hπ₁, x₁, ?_⟩
  simp only [← cancel_mono S.v₀₁.τ₂, assoc, ← S.v₀₁.comm₁₂, reassoc_of% hx₁, hy₁]

/--
lemma `L₃_exact` / 引理 `L₃_exact`

English:
lemma L₃_exact
  statement: S.L₃.Exact
  proof: S.op.L₀_exact.unop

中文:
引理 L₃_exact
  结论: S.L₃.正合
  证明: S.op.L₀_exact.unop

Depends on / 依赖: S.op.L, _exact.unop
-/
lemma L₃_exact : S.L₃.Exact := S.op.L₀_exact.unop

/--
Definition of `P` / `P` 的定义

English:
definition P
  body: pullback S.L₁.g S.v₀₁.τ₃

中文:
定义 P
  定义体: pullback S.L₁.g S.v₀₁.τ₃

Depends on / 依赖: pullback
-/
noncomputable def P := pullback S.L₁.g S.v₀₁.τ₃

/--
Definition of `φ₂` / `φ₂` 的定义

English:
definition φ₂
  signature: : S.P ⟶ S.L₂.X₂
  body: pullback.fst _ _ ≫ S.v₁₂.τ₂

中文:
定义 φ₂
  签名: : S.P ⟶ S.L₂.X₂
  定义体: pullback.fst _ _ ≫ S.v₁₂.τ₂

Depends on / 依赖: pullback, pullback.fst
-/
noncomputable def φ₂ : S.P ⟶ S.L₂.X₂ := pullback.fst _ _ ≫ S.v₁₂.τ₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `lift_φ₂` / 引理 `lift_φ₂`

English:
lemma lift_φ₂
  given: {A : C} (a : A ⟶ S.L₁.X₂) (b : A ⟶ S.L₀.X₃) (h : a ≫ S.L₁.g = b ≫ S.v₀₁.τ₃)
  proof: by
  simp [φ₂]

中文:
引理 lift_φ₂
  条件: {A : C} (a : A ⟶ S.L₁.X₂) (b : A ⟶ S.L₀.X₃) (h : a ≫ S.L₁.g = b ≫ S.v₀₁.τ₃)
  证明: by
  simp [φ₂]
-/
lemma lift_φ₂ {A : C} (a : A ⟶ S.L₁.X₂) (b : A ⟶ S.L₀.X₃) (h : a ≫ S.L₁.g = b ≫ S.v₀₁.τ₃) :
    pullback.lift a b h ≫ S.φ₂ = a ≫ S.v₁₂.τ₂ := by
  simp [φ₂]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `φ₁` / `φ₁` 的定义

English:
definition φ₁
  signature: : S.P ⟶ S.L₂.X₁
  body: S.L₂_exact.lift S.φ₂
    (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

中文:
定义 φ₁
  签名: : S.P ⟶ S.L₂.X₁
  定义体: S.L₂_exact.lift S.φ₂
    (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

Depends on / 依赖: _exact.lift, comp_zero, condition_assoc, pullback, pullback.condition_assoc
-/
noncomputable def φ₁ : S.P ⟶ S.L₂.X₁ :=
  S.L₂_exact.lift S.φ₂
    (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

/--
lemma `φ₁_L₂_f` / 引理 `φ₁_L₂_f`

English:
lemma φ₁_L₂_f
  statement: S.φ₁ ≫ S.L₂.f = S.φ₂
  proof: S.L₂_exact.lift_f _ _

中文:
引理 φ₁_L₂_f
  结论: S.φ₁ ≫ S.L₂.f = S.φ₂
  证明: S.L₂_exact.lift_f _ _
-/
@[reassoc (attr := simp)] lemma φ₁_L₂_f : S.φ₁ ≫ S.L₂.f = S.φ₂ := S.L₂_exact.lift_f _ _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `L₀'` / `L₀'` 的定义

English:
definition L₀'
  signature: : ShortComplex C where
  body: S.L₁.X₁
  X₂ := S.P
  X₃ := S.L₀.X₃
  f := pullback.lift S.L₁.f 0 (by simp)
  g := pullback.snd _ _
  zero := by simp

中文:
定义 L₀'
  签名: : 短复形 C where
  定义体: S.L₁.X₁
  X₂ := S.P
  X₃ := S.L₀.X₃
  f := pullback.lift S.L₁.f 0 (by simp)
  g := pullback.snd _ _
  zero := by simp
-/
noncomputable def L₀' : ShortComplex C where
  X₁ := S.L₁.X₁
  X₂ := S.P
  X₃ := S.L₀.X₃
  f := pullback.lift S.L₁.f 0 (by simp)
  g := pullback.snd _ _
  zero := by simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `L₁_f_φ₁` / 引理 `L₁_f_φ₁`

English:
lemma L₁_f_φ₁
  statement: S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁
  proof: by
  dsimp only [L₀']
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂]

中文:
引理 L₁_f_φ₁
  结论: S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁
  证明: by
  dsimp only [L₀']
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂]
-/
@[reassoc (attr := simp)] lemma L₁_f_φ₁ : S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁ := by
  dsimp only [L₀']
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi S.L₀'.g
  body: by dsimp only [L₀']; infer_instance

中文:
实例 :
  签名: 满态射 S.L₀'.g
  定义体: by dsimp only [L₀']; infer_instance

Depends on / 依赖: infer_instance
-/
instance : Epi S.L₀'.g := by dsimp only [L₀']; infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: S.L₁.f] : Mono S.L₀'.f
  body: mono_of_mono_fac (show S.L₀'.f ≫ pullback.fst _ _ = S.L₁.f by simp [L₀'])

中文:
实例 [单态射
  签名: S.L₁.f] : 单态射 S.L₀'.f
  定义体: mono_of_mono_fac (show S.L₀'.f ≫ pullback.fst _ _ = S.L₁.f by simp [L₀'])

Depends on / 依赖: mono_of_mono_fac, pullback, pullback.fst
-/
instance [Mono S.L₁.f] : Mono S.L₀'.f :=
  mono_of_mono_fac (show S.L₀'.f ≫ pullback.fst _ _ = S.L₁.f by simp [L₀'])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `L₀'_exact` / 引理 `L₀'_exact`

English:
lemma L₀'_exact
  statement: S.L₀'.Exact
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp [L₀'] at x₂ hx₂
  obtain ⟨A', π, hπ, x₁, fac⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ pullback.fst _ _)
    (by rw [assoc, pullback.condition, reassoc_of% hx₂, zero_comp])
  exact ⟨A', π, hπ, x₁, pullback.hom_ext (

中文:
引理 L₀'_exact
  结论: S.L₀'.正合
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp [L₀'] at x₂ hx₂
  obtain ⟨A', π, hπ, x₁, fac⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ pullback.fst _ _)
    (by rw [assoc, pullback.condition, reassoc_of% hx₂, zero_comp])
  exact ⟨A', π, hπ, x₁, pullback.hom_ext (
-/
lemma L₀'_exact : S.L₀'.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp [L₀'] at x₂ hx₂
  obtain ⟨A', π, hπ, x₁, fac⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ pullback.fst _ _)
    (by rw [assoc, pullback.condition, reassoc_of% hx₂, zero_comp])
  exact ⟨A', π, hπ, x₁, pullback.hom_ext (by simpa [L₀'] using fac) (by simp [L₀', hx₂])⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: : S.L₀.X₃ ⟶ S.L₃.X₁
  body: S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

中文:
定义 δ
  签名: : S.L₀.X₃ ⟶ S.L₃.X₁
  定义体: S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

Depends on / 依赖: _exact, _exact.desc
-/
noncomputable def δ : S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

set_option backward.isDefEq.respectTransparency false in -- This is needed below.
@[reassoc (attr := simp)]
/--
lemma `snd_δ` / 引理 `snd_δ`

English:
lemma snd_δ
  statement: (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁
  proof: S.L₀'_exact.g_desc _ _

中文:
引理 snd_δ
  结论: (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁
  证明: S.L₀'_exact.g_desc _ _

Depends on / 依赖: _exact, _exact.g_desc, g_desc
-/
lemma snd_δ : (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁ :=
  S.L₀'_exact.g_desc _ _

/--
Definition of `P'` / `P'` 的定义

English:
definition P'
  body: pushout S.L₂.f S.v₂₃.τ₁

中文:
定义 P'
  定义体: pushout S.L₂.f S.v₂₃.τ₁

Depends on / 依赖: pushout
-/
noncomputable def P' := pushout S.L₂.f S.v₂₃.τ₁

set_option backward.isDefEq.respectTransparency false in
/--
lemma `snd_δ_inr` / 引理 `snd_δ_inr`

English:
lemma snd_δ_inr
  statement: (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr _ _ : _ ⟶ S.P') =
  proof: by
  simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

中文:
引理 snd_δ_inr
  结论: (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr _ _ : _ ⟶ S.P') =
  证明: by
  simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

Depends on / 依赖: condition, pushout, pushout.condition
-/
lemma snd_δ_inr : (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr _ _ : _ ⟶ S.P') =
    pullback.fst _ _ ≫ S.v₁₂.τ₂ ≫ pushout.inl _ _ := by
  simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

/-- The canonical morphism `L₀.X₂ ⟶ P`. -/
@[simp]
/--
Definition of `L₀X₂ToP` / `L₀X₂ToP` 的定义

English:
definition L₀X₂ToP
  signature: : S.L₀.X₂ ⟶ S.P
  body: pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

中文:
定义 L₀X₂ToP
  签名: : S.L₀.X₂ ⟶ S.P
  定义体: pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

Depends on / 依赖: pullback, pullback.lift
-/
noncomputable def L₀X₂ToP : S.L₀.X₂ ⟶ S.P := pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `L₀X₂ToP_comp_pullback_snd` / 引理 `L₀X₂ToP_comp_pullback_snd`

English:
lemma L₀X₂ToP_comp_pullback_snd
  statement: S.L₀X₂ToP ≫ pullback.snd _ _ = S.L₀.g
  proof: by simp

中文:
引理 L₀X₂ToP_comp_pullback_snd
  结论: S.L₀X₂ToP ≫ pullback.snd _ _ = S.L₀.g
  证明: by simp
-/
lemma L₀X₂ToP_comp_pullback_snd : S.L₀X₂ToP ≫ pullback.snd _ _ = S.L₀.g := by simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `L₀X₂ToP_comp_φ₁` / 引理 `L₀X₂ToP_comp_φ₁`

English:
lemma L₀X₂ToP_comp_φ₁
  statement: S.L₀X₂ToP ≫ S.φ₁ = 0
  proof: by
  simp only [← cancel_mono S.L₂.f, L₀X₂ToP, assoc, φ₂, φ₁_L₂_f,
    pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

中文:
引理 L₀X₂ToP_comp_φ₁
  结论: S.L₀X₂ToP ≫ S.φ₁ = 0
  证明: by
  simp only [← cancel_mono S.L₂.f, L₀X₂ToP, assoc, φ₂, φ₁_L₂_f,
    pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

Depends on / 依赖: cancel_mono, lift_fst_assoc, pullback, pullback.lift_fst_assoc, zero_comp
-/
lemma L₀X₂ToP_comp_φ₁ : S.L₀X₂ToP ≫ S.φ₁ = 0 := by
  simp only [← cancel_mono S.L₂.f, L₀X₂ToP, assoc, φ₂, φ₁_L₂_f,
    pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `L₀_g_δ` / 引理 `L₀_g_δ`

English:
lemma L₀_g_δ
  statement: S.L₀.g ≫ S.δ = 0
  proof: by
  rw [← L₀X₂ToP_comp_pullback_snd]; rw [assoc]; rw [S.snd_δ]; rw [L₀X₂ToP_comp_φ₁_assoc]; rw [zero_comp]

中文:
引理 L₀_g_δ
  结论: S.L₀.g ≫ S.δ = 0
  证明: by
  rw [← L₀X₂ToP_comp_pullback_snd]; rw [assoc]; rw [S.snd_δ]; rw [L₀X₂ToP_comp_φ₁_assoc]; rw [zero_comp]

Depends on / 依赖: S.snd_, zero_comp
-/
lemma L₀_g_δ : S.L₀.g ≫ S.δ = 0 := by
  rw [← L₀X₂ToP_comp_pullback_snd]; rw [assoc]; rw [S.snd_δ]; rw [L₀X₂ToP_comp_φ₁_assoc]; rw [zero_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_L₃_f` / 引理 `δ_L₃_f`

English:
lemma δ_L₃_f
  statement: S.δ ≫ S.L₃.f = 0
  proof: by
  simp [← cancel_epi S.L₀'.g, δ, S.v₂₃.comm₁₂, φ₂]

中文:
引理 δ_L₃_f
  结论: S.δ ≫ S.L₃.f = 0
  证明: by
  simp [← cancel_epi S.L₀'.g, δ, S.v₂₃.comm₁₂, φ₂]

Depends on / 依赖: cancel_epi
-/
lemma δ_L₃_f : S.δ ≫ S.L₃.f = 0 := by
  simp [← cancel_epi S.L₀'.g, δ, S.v₂₃.comm₁₂, φ₂]

/-- The short complex `L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁`. -/
@[simps]
/--
Definition of `L₁'` / `L₁'` 的定义

English:
definition L₁'
  signature: : ShortComplex C
  body: ShortComplex.mk _ _ S.L₀_g_δ

中文:
定义 L₁'
  签名: : 短复形 C
  定义体: ShortComplex.mk _ _ S.L₀_g_δ

Depends on / 依赖: ShortComplex, ShortComplex.mk
-/
noncomputable def L₁' : ShortComplex C := ShortComplex.mk _ _ S.L₀_g_δ

/-- The short complex `L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂`. -/
@[simps]
/--
Definition of `L₂'` / `L₂'` 的定义

English:
definition L₂'
  signature: : ShortComplex C
  body: ShortComplex.mk _ _ S.δ_L₃_f

中文:
定义 L₂'
  签名: : 短复形 C
  定义体: ShortComplex.mk _ _ S.δ_L₃_f

Depends on / 依赖: ShortComplex, ShortComplex.mk
-/
noncomputable def L₂' : ShortComplex C := ShortComplex.mk _ _ S.δ_L₃_f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `L₁'_exact` / 引理 `L₁'_exact`

English:
lemma L₁'_exact
  statement: S.L₁'.Exact
  proof: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ x₃ hx₃
  dsimp at x₃ hx₃
  obtain ⟨A₁, π₁, hπ₁, p, hp⟩ := surjective_up_to_refinements_of_epi S.L₀'.g x₃
  dsimp [L₀'] at p hp
  have hp' : (p ≫ S.φ₁) ≫ S.v₂₃.τ₁ = 0 := by
    rw [assoc]; rw [← S.snd_δ]; rw [← reassoc_of% hp]; rw [h

中文:
引理 L₁'_exact
  结论: S.L₁'.正合
  证明: by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ x₃ hx₃
  dsimp at x₃ hx₃
  obtain ⟨A₁, π₁, hπ₁, p, hp⟩ := surjective_up_to_refinements_of_epi S.L₀'.g x₃
  dsimp [L₀'] at p hp
  have hp' : (p ≫ S.φ₁) ≫ S.v₂₃.τ₁ = 0 := by
    rw [assoc]; rw [← S.snd_δ]; rw [← reassoc_of% hp]; rw [h
-/
lemma L₁'_exact : S.L₁'.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ x₃ hx₃
  dsimp at x₃ hx₃
  obtain ⟨A₁, π₁, hπ₁, p, hp⟩ := surjective_up_to_refinements_of_epi S.L₀'.g x₃
  dsimp [L₀'] at p hp
  have hp' : (p ≫ S.φ₁) ≫ S.v₂₃.τ₁ = 0 := by
    rw [assoc]; rw [← S.snd_δ]; rw [← reassoc_of% hp]; rw [hx₃]; rw [comp_zero]
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := S.exact_C₁_down.exact_up_to_refinements (p ≫ S.φ₁) hp'
  dsimp at x₁ hx₁
  let x₂' := x₁ ≫ S.L₁.f
  let x₂ := π₂ ≫ p ≫ pullback.fst _ _
  have hx₂' : (x₂ - x₂') ≫ S.v₁₂.τ₂ = 0 := by
    simp only [x₂, x₂', sub_comp, assoc, ← S.v₁₂.comm₁₂, ← reassoc_of% hx₁, φ₂, φ₁_L₂_f, sub_self]
  let k₂ : A₂ ⟶ S.L₀.X₂ := S.exact_C₂_up.lift _ hx₂'
  have hk₂ : k₂ ≫ S.v₀₁.τ₂ = x₂ - x₂' := S.exact_C₂_up.lift_f _ _
  have hk₂' : k₂ ≫ S.L₀.g = π₂ ≫ p ≫ pullback.snd _ _ := by
    simp only [x₂, x₂', ← cancel_mono S.v₀₁.τ₃, assoc, ← S.v₀₁.comm₂₃, reassoc_of% hk₂,
      sub_comp, S.L₁.zero, comp_zero, sub_zero, pullback.condition]
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, k₂, by simp only [assoc, L₁'_f, ← hk₂', hp]⟩

/--
Definition of `PIsoUnopOpP'` / `PIsoUnopOpP'` 的定义

English:
definition PIsoUnopOpP'
  signature: : S.P ≅ Opposite.unop S.op.P'
  body: pullbackIsoUnopPushout _ _

中文:
定义 PIsoUnopOpP'
  签名: : S.P ≅ 对偶.unop S.op.P'
  定义体: pullbackIsoUnopPushout _ _

Depends on / 依赖: pullbackIsoUnopPushout
-/
noncomputable def PIsoUnopOpP' : S.P ≅ Opposite.unop S.op.P' := pullbackIsoUnopPushout _ _

/--
Definition of `P'IsoUnopOpP` / `P'IsoUnopOpP` 的定义

English:
definition P'IsoUnopOpP
  signature: : S.P' ≅ Opposite.unop S.op.P
  body: pushoutIsoUnopPullback _ _

中文:
定义 P'IsoUnopOpP
  签名: : S.P' ≅ 对偶.unop S.op.P
  定义体: pushoutIsoUnopPullback _ _
-/
noncomputable def P'IsoUnopOpP : S.P' ≅ Opposite.unop S.op.P := pushoutIsoUnopPullback _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `op_δ` / 引理 `op_δ`

English:
lemma op_δ
  statement: S.op.δ = S.δ.op
  proof: Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op]; rw [← cancel_mono (pushout.inr _ _ : _ ⟶ S.P')]; rw [← cancel_epi (pullback.snd _ _ : S.P ⟶ _)]; rw [S.snd_δ_inr]; rw [← cancel_mono S.P'IsoUnopOpP.hom]; rw [← cancel_epi S.PIsoUnopOpP'.inv]; rw [P'IsoUnopOpP]; rw [PIsoUnopOpP']; rw [assoc]; rw [ass

中文:
引理 op_δ
  结论: S.op.δ = S.δ.op
  证明: Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op]; rw [← cancel_mono (pushout.inr _ _ : _ ⟶ S.P')]; rw [← cancel_epi (pullback.snd _ _ : S.P ⟶ _)]; rw [S.snd_δ_inr]; rw [← cancel_mono S.P'IsoUnopOpP.hom]; rw [← cancel_epi S.PIsoUnopOpP'.inv]; rw [P'IsoUnopOpP]; rw [PIsoUnopOpP']; rw [assoc]; rw [ass

Depends on / 依赖: IsoUnopOpP, IsoUnopOpP.hom, PIsoUnopOpP, Quiver, Quiver.H, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, S.PIsoUnopOpP, S.snd_, cancel_epi, cancel_mono, pullback, pullback.snd, pullbackIsoUnopPushout_inv_fst_assoc, pullbackIsoUnopPushout_inv_snd_assoc, pushout, pushout.inr, pushoutIsoUnopPullback_inl_hom, pushoutIsoUnopPullback_inr_hom, unop_inj
-/
lemma op_δ : S.op.δ = S.δ.op := Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op]; rw [← cancel_mono (pushout.inr _ _ : _ ⟶ S.P')]; rw [← cancel_epi (pullback.snd _ _ : S.P ⟶ _)]; rw [S.snd_δ_inr]; rw [← cancel_mono S.P'IsoUnopOpP.hom]; rw [← cancel_epi S.PIsoUnopOpP'.inv]; rw [P'IsoUnopOpP]; rw [PIsoUnopOpP']; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [pushoutIsoUnopPullback_inr_hom]; rw [pullbackIsoUnopPushout_inv_snd_assoc]; rw [pushoutIsoUnopPullback_inl_hom]; rw [pullbackIsoUnopPushout_inv_fst_assoc]
  apply Quiver.Hom.op_inj
  simpa only [op_comp, Quiver.Hom.op_unop, assoc] using! S.op.snd_δ_inr)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `L₂'OpIso` / `L₂'OpIso` 的定义

English:
definition L₂'OpIso
  signature: : S.L₂'.op ≅ S.op.L₁'
  body: ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by dsimp; simp only [id_comp, comp_id, S.op_δ])

中文:
定义 L₂'OpIso
  签名: : S.L₂'.op ≅ S.op.L₁'
  定义体: ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by dsimp; simp only [id_comp, comp_id, S.op_δ])
-/
noncomputable def L₂'OpIso : S.L₂'.op ≅ S.op.L₁' :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by dsimp; simp only [id_comp, comp_id, S.op_δ])

/--
lemma `L₂'_exact` / 引理 `L₂'_exact`

English:
lemma L₂'_exact
  statement: S.L₂'.Exact
  proof: by
  rw [← exact_op_iff]; rw [exact_iff_of_iso S.L₂'OpIso]
  exact S.op.L₁'_exact

中文:
引理 L₂'_exact
  结论: S.L₂'.正合
  证明: by
  rw [← exact_op_iff]; rw [exact_iff_of_iso S.L₂'OpIso]
  exact S.op.L₁'_exact
-/
lemma L₂'_exact : S.L₂'.Exact := by
  rw [← exact_op_iff]; rw [exact_iff_of_iso S.L₂'OpIso]
  exact S.op.L₁'_exact

/--
Definition of `composableArrows` / `composableArrows` 的定义

English:
abbreviation composableArrows
  signature: : ComposableArrows C 5
  body: ComposableArrows.mk₅ S.L₀.f S.L₀.g S.δ S.L₃.f S.L₃.g

中文:
缩写 composableArrows
  签名: : ComposableArrows C 5
  定义体: ComposableArrows.mk₅ S.L₀.f S.L₀.g S.δ S.L₃.f S.L₃.g

Depends on / 依赖: ComposableArrows, ComposableArrows.mk
-/
noncomputable abbrev composableArrows : ComposableArrows C 5 :=
  ComposableArrows.mk₅ S.L₀.f S.L₀.g S.δ S.L₃.f S.L₃.g

open ComposableArrows in
/--
lemma `snake_lemma` / 引理 `snake_lemma`

English:
lemma snake_lemma
  statement: S.composableArrows.Exact
  proof: exact_of_δ₀ S.L₀_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₁'_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₂'_exact.exact_toComposableArrows
    S.L₃_exact.exact_toComposableArrows))

中文:
引理 snake_lemma
  结论: S.composableArrows.正合
  证明: exact_of_δ₀ S.L₀_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₁'_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₂'_exact.exact_toComposableArrows
    S.L₃_exact.exact_toComposableArrows))

Depends on / 依赖: _exact, _exact.exact_toComposableArrows, exact_toComposableArrows
-/
lemma snake_lemma : S.composableArrows.Exact :=
  exact_of_δ₀ S.L₀_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₁'_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₂'_exact.exact_toComposableArrows
    S.L₃_exact.exact_toComposableArrows))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_eq` / 引理 `δ_eq`

English:
lemma δ_eq
  statement: {A : C} (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
  proof: by
  have H := (pullback.lift x₂ x₃ h₂) ≫= S.snd_δ
  rw [pullback.lift_snd_assoc] at H
  rw [H]; rw [← assoc]
  congr 1
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, lift_φ₂, h₁]

中文:
引理 δ_eq
  结论: {A : C} (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
  证明: by
  have H := (pullback.lift x₂ x₃ h₂) ≫= S.snd_δ
  rw [pullback.lift_snd_assoc] at H
  rw [H]; rw [← assoc]
  congr 1
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, lift_φ₂, h₁]

Depends on / 依赖: S.snd_, cancel_mono, lift_snd_assoc, pullback, pullback.lift, pullback.lift_snd_assoc
-/
lemma δ_eq {A : C} (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
    (h₂ : x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃) (h₁ : x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂) :
    x₃ ≫ S.δ = x₁ ≫ S.v₂₃.τ₁ := by
  have H := (pullback.lift x₂ x₃ h₂) ≫= S.snd_δ
  rw [pullback.lift_snd_assoc] at H
  rw [H]; rw [← assoc]
  congr 1
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, lift_φ₂, h₁]

/--
theorem `mono_δ` / 定理 `mono_δ`

English:
theorem mono_δ
  given: (h₀ : IsZero S.L₀.X₂)
  statement: Mono S.δ
  proof: (S.L₁'.exact_iff_mono (IsZero.eq_zero_of_src h₀ S.L₁'.f)).1 S.L₁'_exact

中文:
定理 mono_δ
  条件: (h₀ : 是零 S.L₀.X₂)
  结论: 单态射 S.δ
  证明: (S.L₁'.exact_iff_mono (IsZero.eq_zero_of_src h₀ S.L₁'.f)).1 S.L₁'_exact

Depends on / 依赖: IsZero, IsZero.eq_zero_of_src, _exact, eq_zero_of_src, exact_iff_mono
-/
theorem mono_δ (h₀ : IsZero S.L₀.X₂) : Mono S.δ :=
  (S.L₁'.exact_iff_mono (IsZero.eq_zero_of_src h₀ S.L₁'.f)).1 S.L₁'_exact

/--
theorem `epi_δ` / 定理 `epi_δ`

English:
theorem epi_δ
  given: (h₃ : IsZero S.L₃.X₂)
  statement: Epi S.δ
  proof: (S.L₂'.exact_iff_epi (IsZero.eq_zero_of_tgt h₃ S.L₂'.g)).1 S.L₂'_exact

中文:
定理 epi_δ
  条件: (h₃ : 是零 S.L₃.X₂)
  结论: 满态射 S.δ
  证明: (S.L₂'.exact_iff_epi (IsZero.eq_zero_of_tgt h₃ S.L₂'.g)).1 S.L₂'_exact

Depends on / 依赖: IsZero, IsZero.eq_zero_of_tgt, _exact, eq_zero_of_tgt, exact_iff_epi
-/
theorem epi_δ (h₃ : IsZero S.L₃.X₂) : Epi S.δ :=
  (S.L₂'.exact_iff_epi (IsZero.eq_zero_of_tgt h₃ S.L₂'.g)).1 S.L₂'_exact

/--
theorem `isIso_δ` / 定理 `isIso_δ`

English:
theorem isIso_δ
  given: (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂)
  statement: IsIso S.δ
  proof: @Balanced.isIso_of_mono_of_epi _ _ _ _ _ S.δ (S.mono_δ h₀) (S.epi_δ h₃)

中文:
定理 isIso_δ
  条件: (h₀ : 是零 S.L₀.X₂) (h₃ : 是零 S.L₃.X₂)
  结论: 是同构 S.δ
  证明: @Balanced.isIso_of_mono_of_epi _ _ _ _ _ S.δ (S.mono_δ h₀) (S.epi_δ h₃)

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, S.epi_, S.mono_, isIso_of_mono_of_epi
-/
theorem isIso_δ (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) : IsIso S.δ :=
  @Balanced.isIso_of_mono_of_epi _ _ _ _ _ S.δ (S.mono_δ h₀) (S.epi_δ h₃)

/--
Definition of `δIso` / `δIso` 的定义

English:
definition δIso
  signature: (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂)
  body: @asIso _ _ _ _ S.δ (SnakeInput.isIso_δ S h₀ h₃)

中文:
定义 δIso
  签名: (h₀ : 是零 S.L₀.X₂) (h₃ : 是零 S.L₃.X₂)
  定义体: @asIso _ _ _ _ S.δ (SnakeInput.isIso_δ S h₀ h₃)

Depends on / 依赖: SnakeInput, SnakeInput.isIso_
-/
noncomputable def δIso (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) :
    S.L₀.X₃ ≅ S.L₃.X₁ :=
  @asIso _ _ _ _ S.δ (SnakeInput.isIso_δ S h₀ h₃)

variable (S₁ S₂ S₃ : SnakeInput C)

/-- A morphism of snake inputs involve four morphisms of short complexes
which make the obvious diagram commute. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (7):
    - f₀ : S₁.L₀ ⟶ S₂.L₀
    - f₁ : S₁.L₁ ⟶ S₂.L₁
    - f₂ : S₁.L₂ ⟶ S₂.L₂
    - f₃ : S₁.L₃ ⟶ S₂.L₃
    - comm₀₁ : f₀ ≫ S₂.v₀₁ = S₁.v₀₁ ≫ f₁  [default: by cat_disch]
    - comm₁₂ : f₁ ≫ S₂.v₁₂ = S₁.v₁₂ ≫ f₂  [default: by cat_disch]
    - comm₂₃ : f₂ ≫ S₂.v₂₃ = S₁.v₂₃ ≫ f₃  [default: by cat_disch]

中文:
结构 态射
  参数: where
  公理与运算 (7 个):
    - f₀ : S₁.L₀ ⟶ S₂.L₀
    - f₁ : S₁.L₁ ⟶ S₂.L₁
    - f₂ : S₁.L₂ ⟶ S₂.L₂
    - f₃ : S₁.L₃ ⟶ S₂.L₃
    - comm₀₁ : f₀ ≫ S₂.v₀₁ = S₁.v₀₁ ≫ f₁  [默认: by cat_disch]
    - comm₁₂ : f₁ ≫ S₂.v₁₂ = S₁.v₁₂ ≫ f₂  [默认: by cat_disch]
    - comm₂₃ : f₂ ≫ S₂.v₂₃ = S₁.v₂₃ ≫ f₃  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom where
  /-- a morphism between the zeroth lines -/
  f₀ : S₁.L₀ ⟶ S₂.L₀
  /-- a morphism between the first lines -/
  f₁ : S₁.L₁ ⟶ S₂.L₁
  /-- a morphism between the second lines -/
  f₂ : S₁.L₂ ⟶ S₂.L₂
  /-- a morphism between the third lines -/
  f₃ : S₁.L₃ ⟶ S₂.L₃
  comm₀₁ : f₀ ≫ S₂.v₀₁ = S₁.v₀₁ ≫ f₁ := by cat_disch
  comm₁₂ : f₁ ≫ S₂.v₁₂ = S₁.v₁₂ ≫ f₂ := by cat_disch
  comm₂₃ : f₂ ≫ S₂.v₂₃ = S₁.v₂₃ ≫ f₃ := by cat_disch

namespace Hom

attribute [reassoc] comm₀₁ comm₁₂ comm₂₃

/-- The identity morphism of a snake input. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Hom S S where
  body: 𝟙 _
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  f₃ := 𝟙 _

中文:
定义 id
  签名: : 态射 S S where
  定义体: 𝟙 _
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  f₃ := 𝟙 _
-/
def id : Hom S S where
  f₀ := 𝟙 _
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  f₃ := 𝟙 _

variable {S₁ S₂ S₃}

/-- The composition of morphisms of snake inputs. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : Hom S₁ S₂) (g : Hom S₂ S₃)
  body: f.f₀ ≫ g.f₀
  f₁ := f.f₁ ≫ g.f₁
  f₂ := f.f₂ ≫ g.f₂
  f₃ := f.f₃ ≫ g.f₃
  comm₀₁ := by simp only [assoc, comm₀₁, comm₀₁_assoc]
  comm₁₂ := by simp only [assoc, comm₁₂, comm₁₂_assoc]
  comm₂₃ := by simp only [assoc, comm₂₃, comm₂₃_assoc]

中文:
定义 comp
  签名: (f : 态射 S₁ S₂) (g : 态射 S₂ S₃)
  定义体: f.f₀ ≫ g.f₀
  f₁ := f.f₁ ≫ g.f₁
  f₂ := f.f₂ ≫ g.f₂
  f₃ := f.f₃ ≫ g.f₃
  comm₀₁ := by simp only [assoc, comm₀₁, comm₀₁_assoc]
  comm₁₂ := by simp only [assoc, comm₁₂, comm₁₂_assoc]
  comm₂₃ := by simp only [assoc, comm₂₃, comm₂₃_assoc]
-/
def comp (f : Hom S₁ S₂) (g : Hom S₂ S₃) : Hom S₁ S₃ where
  f₀ := f.f₀ ≫ g.f₀
  f₁ := f.f₁ ≫ g.f₁
  f₂ := f.f₂ ≫ g.f₂
  f₃ := f.f₃ ≫ g.f₃
  comm₀₁ := by simp only [assoc, comm₀₁, comm₀₁_assoc]
  comm₁₂ := by simp only [assoc, comm₁₂, comm₁₂_assoc]
  comm₂₃ := by simp only [assoc, comm₂₃, comm₂₃_assoc]

end Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SnakeInput C)
  body: Hom
  id := Hom.id
  comp := Hom.comp

中文:
实例 :
  签名: 范畴 (蛇输入 C)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp
-/
instance : Category (SnakeInput C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {S₁ S₂ S₃}

/--
lemma `id_f₀` / 引理 `id_f₀`

English:
lemma id_f₀
  statement: Hom.f₀ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_f₀
  结论: 态射.f₀ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_f₀ : Hom.f₀ (𝟙 S) = 𝟙 _ := rfl
/--
lemma `id_f₁` / 引理 `id_f₁`

English:
lemma id_f₁
  statement: Hom.f₁ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_f₁
  结论: 态射.f₁ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_f₁ : Hom.f₁ (𝟙 S) = 𝟙 _ := rfl
/--
lemma `id_f₂` / 引理 `id_f₂`

English:
lemma id_f₂
  statement: Hom.f₂ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_f₂
  结论: 态射.f₂ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_f₂ : Hom.f₂ (𝟙 S) = 𝟙 _ := rfl
/--
lemma `id_f₃` / 引理 `id_f₃`

English:
lemma id_f₃
  statement: Hom.f₃ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_f₃
  结论: 态射.f₃ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_f₃ : Hom.f₃ (𝟙 S) = 𝟙 _ := rfl

section

variable (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)

/--
lemma `comp_f₀` / 引理 `comp_f₀`

English:
lemma comp_f₀
  statement: (f ≫ g).f₀ = f.f₀ ≫ g.f₀
  proof: rfl

中文:
引理 comp_f₀
  结论: (f ≫ g).f₀ = f.f₀ ≫ g.f₀
  证明: rfl
-/
@[simp, reassoc] lemma comp_f₀ : (f ≫ g).f₀ = f.f₀ ≫ g.f₀ := rfl
/--
lemma `comp_f₁` / 引理 `comp_f₁`

English:
lemma comp_f₁
  statement: (f ≫ g).f₁ = f.f₁ ≫ g.f₁
  proof: rfl

中文:
引理 comp_f₁
  结论: (f ≫ g).f₁ = f.f₁ ≫ g.f₁
  证明: rfl
-/
@[simp, reassoc] lemma comp_f₁ : (f ≫ g).f₁ = f.f₁ ≫ g.f₁ := rfl
/--
lemma `comp_f₂` / 引理 `comp_f₂`

English:
lemma comp_f₂
  statement: (f ≫ g).f₂ = f.f₂ ≫ g.f₂
  proof: rfl

中文:
引理 comp_f₂
  结论: (f ≫ g).f₂ = f.f₂ ≫ g.f₂
  证明: rfl
-/
@[simp, reassoc] lemma comp_f₂ : (f ≫ g).f₂ = f.f₂ ≫ g.f₂ := rfl
/--
lemma `comp_f₃` / 引理 `comp_f₃`

English:
lemma comp_f₃
  statement: (f ≫ g).f₃ = f.f₃ ≫ g.f₃
  proof: rfl

中文:
引理 comp_f₃
  结论: (f ≫ g).f₃ = f.f₃ ≫ g.f₃
  证明: rfl
-/
@[simp, reassoc] lemma comp_f₃ : (f ≫ g).f₃ = f.f₃ ≫ g.f₃ := rfl

end

/-- The functor which sends `S : SnakeInput C` to its zeroth line `S.L₀`. -/
@[simps]
/--
Definition of `functorL₀` / `functorL₀` 的定义

English:
definition functorL₀
  signature: : SnakeInput C ⥤ ShortComplex C where
  body: S.L₀
  map f := f.f₀

中文:
定义 functorL₀
  签名: : 蛇输入 C ⥤ 短复形 C where
  定义体: S.L₀
  map f := f.f₀
-/
def functorL₀ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₀
  map f := f.f₀

/-- The functor which sends `S : SnakeInput C` to its zeroth line `S.L₁`. -/
@[simps]
/--
Definition of `functorL₁` / `functorL₁` 的定义

English:
definition functorL₁
  signature: : SnakeInput C ⥤ ShortComplex C where
  body: S.L₁
  map f := f.f₁

中文:
定义 functorL₁
  签名: : 蛇输入 C ⥤ 短复形 C where
  定义体: S.L₁
  map f := f.f₁
-/
def functorL₁ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁
  map f := f.f₁

/-- The functor which sends `S : SnakeInput C` to its second line `S.L₂`. -/
@[simps]
/--
Definition of `functorL₂` / `functorL₂` 的定义

English:
definition functorL₂
  signature: : SnakeInput C ⥤ ShortComplex C where
  body: S.L₂
  map f := f.f₂

中文:
定义 functorL₂
  签名: : 蛇输入 C ⥤ 短复形 C where
  定义体: S.L₂
  map f := f.f₂
-/
def functorL₂ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₂
  map f := f.f₂

/-- The functor which sends `S : SnakeInput C` to its third line `S.L₃`. -/
@[simps]
/--
Definition of `functorL₃` / `functorL₃` 的定义

English:
definition functorL₃
  signature: : SnakeInput C ⥤ ShortComplex C where
  body: S.L₃
  map f := f.f₃

中文:
定义 functorL₃
  签名: : 蛇输入 C ⥤ 短复形 C where
  定义体: S.L₃
  map f := f.f₃
-/
def functorL₃ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₃
  map f := f.f₃

set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends `S : SnakeInput C` to the auxiliary object `S.P`,
which is `pullback S.L₁.g S.v₀₁.τ₃`. -/
@[simps]
/--
Definition of `functorP` / `functorP` 的定义

English:
definition functorP
  signature: : SnakeInput C ⥤ C where
  body: S.P
  map f := pullback.map _ _ _ _ f.f₁.τ₂ f.f₀.τ₃ f.f₁.τ₃ f.f₁.comm₂₃.symm
      (congr_arg ShortComplex.Hom.τ₃ f.comm₀₁.symm)
  map_id _ := by dsimp [P]; simp
  map_comp _ _ := by dsimp [P]; cat_disch

中文:
定义 functorP
  签名: : 蛇输入 C ⥤ C where
  定义体: S.P
  map f := pullback.map _ _ _ _ f.f₁.τ₂ f.f₀.τ₃ f.f₁.τ₃ f.f₁.comm₂₃.symm
      (congr_arg ShortComplex.Hom.τ₃ f.comm₀₁.symm)
  map_id _ := by dsimp [P]; simp
  map_comp _ _ := by dsimp [P]; cat_disch
-/
noncomputable def functorP : SnakeInput C ⥤ C where
  obj S := S.P
  map f := pullback.map _ _ _ _ f.f₁.τ₂ f.f₀.τ₃ f.f₁.τ₃ f.f₁.comm₂₃.symm
      (congr_arg ShortComplex.Hom.τ₃ f.comm₀₁.symm)
  map_id _ := by dsimp [P]; simp
  map_comp _ _ := by dsimp [P]; cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `naturality_φ₂` / 引理 `naturality_φ₂`

English:
lemma naturality_φ₂
  given: (f : S₁ ⟶ S₂)
  statement: S₁.φ₂ ≫ f.f₂.τ₂ = functorP.map f ≫ S₂.φ₂
  proof: by
  dsimp [φ₂]
  simp only [assoc, pullback.lift_fst_assoc, ← comp_τ₂, f.comm₁₂]

中文:
引理 naturality_φ₂
  条件: (f : S₁ ⟶ S₂)
  结论: S₁.φ₂ ≫ f.f₂.τ₂ = functorP.map f ≫ S₂.φ₂
  证明: by
  dsimp [φ₂]
  simp only [assoc, pullback.lift_fst_assoc, ← comp_τ₂, f.comm₁₂]

Depends on / 依赖: f.comm, lift_fst_assoc, pullback, pullback.lift_fst_assoc
-/
lemma naturality_φ₂ (f : S₁ ⟶ S₂) : S₁.φ₂ ≫ f.f₂.τ₂ = functorP.map f ≫ S₂.φ₂ := by
  dsimp [φ₂]
  simp only [assoc, pullback.lift_fst_assoc, ← comp_τ₂, f.comm₁₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `naturality_φ₁` / 引理 `naturality_φ₁`

English:
lemma naturality_φ₁
  given: (f : S₁ ⟶ S₂)
  statement: S₁.φ₁ ≫ f.f₂.τ₁ = functorP.map f ≫ S₂.φ₁
  proof: by
  simp only [← cancel_mono S₂.L₂.f, assoc, φ₁_L₂_f, ← naturality_φ₂, f.f₂.comm₁₂, φ₁_L₂_f_assoc]

中文:
引理 naturality_φ₁
  条件: (f : S₁ ⟶ S₂)
  结论: S₁.φ₁ ≫ f.f₂.τ₁ = functorP.map f ≫ S₂.φ₁
  证明: by
  simp only [← cancel_mono S₂.L₂.f, assoc, φ₁_L₂_f, ← naturality_φ₂, f.f₂.comm₁₂, φ₁_L₂_f_assoc]

Depends on / 依赖: cancel_mono
-/
lemma naturality_φ₁ (f : S₁ ⟶ S₂) : S₁.φ₁ ≫ f.f₂.τ₁ = functorP.map f ≫ S₂.φ₁ := by
  simp only [← cancel_mono S₂.L₂.f, assoc, φ₁_L₂_f, ← naturality_φ₂, f.f₂.comm₁₂, φ₁_L₂_f_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `naturality_δ` / 引理 `naturality_δ`

English:
lemma naturality_δ
  given: (f : S₁ ⟶ S₂)
  statement: S₁.δ ≫ f.f₃.τ₁ = f.f₀.τ₃ ≫ S₂.δ
  proof: by
  rw [← cancel_epi (pullback.snd _ _ : S₁.P ⟶ _)]; rw [S₁.snd_δ_assoc]; rw [← comp_τ₁]; rw [← f.comm₂₃]; rw [comp_τ₁]; rw [naturality_φ₁_assoc]; rw [← S₂.snd_δ]; rw [functorP_map]; rw [pullback.lift_snd_assoc]; rw [assoc]

中文:
引理 naturality_δ
  条件: (f : S₁ ⟶ S₂)
  结论: S₁.δ ≫ f.f₃.τ₁ = f.f₀.τ₃ ≫ S₂.δ
  证明: by
  rw [← cancel_epi (pullback.snd _ _ : S₁.P ⟶ _)]; rw [S₁.snd_δ_assoc]; rw [← comp_τ₁]; rw [← f.comm₂₃]; rw [comp_τ₁]; rw [naturality_φ₁_assoc]; rw [← S₂.snd_δ]; rw [functorP_map]; rw [pullback.lift_snd_assoc]; rw [assoc]

Depends on / 依赖: cancel_epi, f.comm, functorP_map, lift_snd_assoc, pullback, pullback.lift_snd_assoc, pullback.snd
-/
lemma naturality_δ (f : S₁ ⟶ S₂) : S₁.δ ≫ f.f₃.τ₁ = f.f₀.τ₃ ≫ S₂.δ := by
  rw [← cancel_epi (pullback.snd _ _ : S₁.P ⟶ _)]; rw [S₁.snd_δ_assoc]; rw [← comp_τ₁]; rw [← f.comm₂₃]; rw [comp_τ₁]; rw [naturality_φ₁_assoc]; rw [← S₂.snd_δ]; rw [functorP_map]; rw [pullback.lift_snd_assoc]; rw [assoc]

/-- The functor which sends `S : SnakeInput C` to `S.L₁'` which is
`S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁`. -/
@[simps]
/--
Definition of `functorL₁'` / `functorL₁'` 的定义

English:
definition functorL₁'
  signature: : SnakeInput C ⥤ ShortComplex C where
  body: S.L₁'
  map f :=
    { τ₁ := f.f₀.τ₂
      τ₂ := f.f₀.τ₃
      τ₃ := f.f₃.τ₁
      comm₁₂ := f.f₀.comm₂₃
      comm₂₃ := (naturality_δ f).symm }

中文:
定义 functorL₁'
  签名: : 蛇输入 C ⥤ 短复形 C where
  定义体: S.L₁'
  map f :=
    { τ₁ := f.f₀.τ₂
      τ₂ := f.f₀.τ₃
      τ₃ := f.f₃.τ₁
      comm₁₂ := f.f₀.comm₂₃
      comm₂₃ := (naturality_δ f).symm }
-/
noncomputable def functorL₁' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁'
  map f :=
    { τ₁ := f.f₀.τ₂
      τ₂ := f.f₀.τ₃
      τ₃ := f.f₃.τ₁
      comm₁₂ := f.f₀.comm₂₃
      comm₂₃ := (naturality_δ f).symm }

/-- The functor which sends `S : SnakeInput C` to `S.L₂'` which is
`S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂`. -/
@[simps]
/--
Definition of `functorL₂'` / `functorL₂'` 的定义

English:
definition functorL₂'
  signature: : SnakeInput C ⥤ ShortComplex C where
  body: S.L₂'
  map f :=
    { τ₁ := f.f₀.τ₃
      τ₂ := f.f₃.τ₁
      τ₃ := f.f₃.τ₂
      comm₁₂ := (naturality_δ f).symm
      comm₂₃ := f.f₃.comm₁₂ }

中文:
定义 functorL₂'
  签名: : 蛇输入 C ⥤ 短复形 C where
  定义体: S.L₂'
  map f :=
    { τ₁ := f.f₀.τ₃
      τ₂ := f.f₃.τ₁
      τ₃ := f.f₃.τ₂
      comm₁₂ := (naturality_δ f).symm
      comm₂₃ := f.f₃.comm₁₂ }
-/
noncomputable def functorL₂' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₂'
  map f :=
    { τ₁ := f.f₀.τ₃
      τ₂ := f.f₃.τ₁
      τ₃ := f.f₃.τ₂
      comm₁₂ := (naturality_δ f).symm
      comm₂₃ := f.f₃.comm₁₂ }

/-- The functor which maps `S : SnakeInput C` to the diagram
`S.L₀.X₁ ⟶ S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂ ⟶ S.L₃.X₃`. -/
@[simps]
/--
Definition of `composableArrowsFunctor` / `composableArrowsFunctor` 的定义

English:
definition composableArrowsFunctor
  signature: : SnakeInput C ⥤ ComposableArrows C 5 where
  body: S.composableArrows
  map f := ComposableArrows.homMk₅ f.f₀.τ₁ f.f₀.τ₂ f.f₀.τ₃ f.f₃.τ₁ f.f₃.τ₂ f.f₃.τ₃
    f.f₀.comm₁₂.symm f.f₀.comm₂₃.symm (naturality_δ f) f.f₃.comm₁₂.symm f.f₃.comm₂₃.symm

中文:
定义 composableArrowsFunctor
  签名: : 蛇输入 C ⥤ ComposableArrows C 5 where
  定义体: S.composableArrows
  map f := ComposableArrows.homMk₅ f.f₀.τ₁ f.f₀.τ₂ f.f₀.τ₃ f.f₃.τ₁ f.f₃.τ₂ f.f₃.τ₃
    f.f₀.comm₁₂.symm f.f₀.comm₂₃.symm (naturality_δ f) f.f₃.comm₁₂.symm f.f₃.comm₂₃.symm

Depends on / 依赖: S.composableArrows, composableArrows
-/
noncomputable def composableArrowsFunctor : SnakeInput C ⥤ ComposableArrows C 5 where
  obj S := S.composableArrows
  map f := ComposableArrows.homMk₅ f.f₀.τ₁ f.f₀.τ₂ f.f₀.τ₃ f.f₃.τ₁ f.f₃.τ₂ f.f₃.τ₃
    f.f₀.comm₁₂.symm f.f₀.comm₂₃.symm (naturality_δ f) f.f₃.comm₁₂.symm f.f₃.comm₂₃.symm

end SnakeInput

end ShortComplex

end CategoryTheory
