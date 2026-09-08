/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# `C^n` monoid

A `C^n` monoid is a monoid that is also a `C^n` manifold, in which multiplication is a `C^n` map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about `C^n` monoids: `ContMDiffMul` and its
additive counterpart `ContMDiffAdd`. These structures are general enough to also talk about `C^n`
semigroups.
-/

@[expose] public section

open scoped Manifold ContDiff

library_note «Design choices about smooth algebraic structures» /--
1. All `C^n` algebraic structures on `G` are `Prop`-valued classes that extend
   `IsManifold I n G`. This way we save users from adding both
   `[IsManifold I n G]` and `[ContMDiffMul I n G]` to the assumptions. While many API
   lemmas hold true without the `IsManifold I n G` assumption, we're not aware of a
   mathematically interesting monoid on a topological manifold such that (a) the space is not a
   `IsManifold`; (b) the multiplication is `C^n` at `(a, b)` in the charts
   `extChartAt I a`, `extChartAt I b`, `extChartAt I (a * b)`.

2. Because of `ModelProd` we can't assume, e.g., that a `LieGroup` is modelled on `𝓘(𝕜, E)`. So,
   we formulate the definitions and lemmas for any model.

3. While smoothness of an operation implies its continuity, lemmas like
   `continuousMul_of_contMDiffMul` can't be instances because otherwise Lean would have to search
   for `ContMDiffMul I n G` with unknown `𝕜`, `E`, `H`, and `I : ModelWithCorners 𝕜 E H`. If users
   need `[ContinuousMul G]` in a proof about a `C^n` monoid, then they need to either add
   `[ContinuousMul G]` as an assumption (worse) or use `haveI` in the proof (better).
-/

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a `C^n` (Lie) additive monoid or a `C^n` additive
semigroup. A `C^n` additive monoid over `G`, for example, is obtained by requiring both the
instances `AddMonoid G` and `ContMDiffAdd I n G`.

See also `ContMDiffVAdd I I' n G M` for `C^n` actions of `G` on a manifold `M`. -/
/-
**ContMDiffAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     ModelWithCorners 𝕜 E H →                 WithTop ℕ∞ → (G : Type u_4) → [Add
 G] → [inst : TopologicalSpace G] → [ChartedSpace H G] → Prop
参数：G : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a `C^n` (Lie) additive monoid or a `C^n` additive
semigroup. A `C^n` additive monoid over `G`, for example, is obtained by requiri
ng both the
instances `AddMonoid G` and `ContMDiffAdd I n G`.

See also `ContMDiffVAdd I I' n G M` for `C^n` actions of `G` on a manifold `M`.
-/
class ContMDiffAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (G : Type*) [Add G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_add : CMDiff n fun p : G × G ↦ p.1 + p.2

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a `C^n` (Lie) monoid or a `C^n` semigroup.
A `C^n` monoid over `G`, for example, is obtained by requiring both the instances `Monoid G`
and `ContMDiffMul I n G`.

See also `ContMDiffSMul I I' n G M` for `C^n` actions of `G` on a manifold `M`. -/
@[to_additive]
/-
**ContMDiffMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     ModelWithCorners 𝕜 E H →                 WithTop ℕ∞ → (G : Type u_4) → [Mul
 G] → [inst : TopologicalSpace G] → [ChartedSpace H G] → Prop
参数：G : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Basic hypothesis to talk about a `C^n` (Lie) monoid or a `C^n` semigroup.
A `C^n` monoid over `G`, for example, is obtained by requiring both the instance
s `Monoid G`
and `ContMDiffMul I n G`.

See also `ContMDiffSMul I I' n G M` for `C^n` actions of `G` on a manifold `M`.
-/
class ContMDiffMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (G : Type*) [Mul G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_mul : CMDiff n fun p : G × G ↦ p.1 * p.2

section ContMDiffMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

@[to_additive]
/-
**ContMDiffMul.of_le** 是 Mathlib 中的一个定理，位于命名空间 `ContMDiffMul`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}   [inst_4 : Mul G
] [inst_5 : TopologicalSpace G] [inst_6 : ChartedSpace H G] {m n : WithTop ℕ∞}, 
  m ≤ n → ∀ [h : ContMDiffMul I n G], ContMDiffMul I m G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.of_le`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `ContMDiffMul.contMDiff_mul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedF
ield 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : 
NormedAddCommGro…
-/
protected theorem ContMDiffMul.of_le {m n : ℕ∞ω} (hmn : m ≤ n)
    [h : ContMDiffMul I n G] : ContMDiffMul I m G := by
  have : IsManifold I m G := IsManifold.of_le hmn
  exact ⟨h.contMDiff_mul.of_le hmn⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [ContMDiffMul I ∞ G] [h : ENat.LEInfty a] : ContMDiffMul I a G :=
  ContMDiffMul.of_le h.out

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [ContMDiffMul I ω G] : ContMDiffMul I a G :=
  ContMDiffMul.of_le le_top

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousMul G] : ContMDiffMul I 0 G := by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_mul

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContMDiffMul I 2 G] : ContMDiffMul I 1 G :=
  ContMDiffMul.of_le one_le_two

section

variable (I n)

@[to_additive]
/-
**contMDiff_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_mul [ContMDiffMul I n G] : CMDiff n fun p : G × G => p.1 * p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMul.contMDiff_mul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedF
ield 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : 
NormedAddCommGro…
-/
theorem contMDiff_mul [ContMDiffMul I n G] : CMDiff n fun p : G × G ↦ p.1 * p.2 :=
  ContMDiffMul.contMDiff_mul

include I n in
/-- If the multiplication is `C^n`, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive /-- If the addition is `C^n`, then it is continuous. This is not an instance for
technical reasons, see note [Design choices about smooth algebraic structures]. -/]
/-
**continuousMul_of_contMDiffMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousMul_of_contMDiffMul [ContMDiffMul I n G] : ContinuousMul G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `contMDiff_mul`：contMDiff_mul [ContMDiffMul I n G] : CMDiff n fun p : G ×
 G => p.1 * p.2
-/
theorem continuousMul_of_contMDiffMul [ContMDiffMul I n G] : ContinuousMul G :=
  ⟨(contMDiff_mul I n).continuous⟩

end

section

variable [ContMDiffMul I n G] {f g : M → G} {s : Set M} {x : M}

@[to_additive]
/-
**ContMDiffWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) : 
CMDiffAt[s] n (f * g) x
参数：hf : CMDiffAt[s] n f x；hg : CMDiffAt[s] n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_mul`：contMDiff_mul [ContMDiffMul I n G] : CMDiff n fun p : G ×
 G => p.1 * p.2
· 使用定理 `ContMDiffWithinAt.prodMk`：ContMDiffWithinAt.prodMk {f : M -> M'} {g : M 
-> N'} (hf : ContMDiffWithinAt I I' n f s x) (hg : ContMDiffWithinAt I J' n g s 
x) : ContMDiff…
-/
theorem ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
    CMDiffAt[s] n (f * g) x :=
  (contMDiff_mul I n).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) : CMDiffAt n (f * g) x :=
  hf.mul hg

@[to_additive]
/-
**ContMDiffOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.mul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) : CMDiff[s] n (f
 * g)
参数：hf : CMDiff[s] n f；hg : CMDiff[s] n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mul`：ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (h
g : CMDiffAt[s] n g x) : CMDiffAt[s] n (f * g) x
-/
theorem ContMDiffOn.mul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) : CMDiff[s] n (f * g) :=
  fun x hx ↦ (hf x hx).mul (hg x hx)

@[to_additive]
/-
**ContMDiff.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDiff n (f * g)
参数：hf : CMDiff n f；hg : CMDiff n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H 
: Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCo
mmGro…
-/
theorem ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDiff n (f * g) :=
  fun x ↦ (hf x).mul (hg x)

@[to_additive]
/-
**contMDiff_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_mul_left {a : G} : CMDiff n (a * ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mul`：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDif
f n (f * g)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
-/
theorem contMDiff_mul_left {a : G} : CMDiff n (a * ·) :=
  contMDiff_const.mul contMDiff_id

@[to_additive]
/-
**contMDiffAt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_mul_left {a b : G} : CMDiffAt n (a * ·) b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_mul_left`：contMDiff_mul_left {a : G} : CMDiff n (a * ·)
-/
theorem contMDiffAt_mul_left {a b : G} : CMDiffAt n (a * ·) b :=
  contMDiff_mul_left.contMDiffAt

@[to_additive]
/-
**contMDiff_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_mul_right {a : G} : CMDiff n (· * a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mul`：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDif
f n (f * g)
· 使用定理 `contMDiff_id`：contMDiff_id : ContMDiff I I n (id : M -> M)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
-/
theorem contMDiff_mul_right {a : G} : CMDiff n (· * a) :=
  contMDiff_id.mul contMDiff_const

@[to_additive]
/-
**contMDiffAt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_mul_right {a b : G} : CMDiffAt n (· * a) b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_mul_right`：contMDiff_mul_right {a : G} : CMDiff n (· * a)
-/
theorem contMDiffAt_mul_right {a b : G} : CMDiffAt n (· * a) b :=
  contMDiff_mul_right.contMDiffAt

end

section

variable [ContMDiffMul I 1 G]

@[to_additive]
/-
**mdifferentiable_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_mul_left {a : G} : MDiff (a * ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `contMDiff_mul_left`：contMDiff_mul_left {a : G} : CMDiff n (a * ·)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiable_mul_left {a : G} : MDiff (a * ·) :=
  contMDiff_mul_left.mdifferentiable one_ne_zero

@[to_additive]
/-
**mdifferentiableAt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_mul_left {a b : G} : MDiffAt (a * ·) b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_mul_left`：contMDiffAt_mul_left {a b : G} : CMDiffAt n (a * ·
) b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableAt_mul_left {a b : G} : MDiffAt (a * ·) b :=
  contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

@[to_additive]
/-
**mdifferentiable_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_mul_right {a : G} : MDiff (· * a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `contMDiff_mul_right`：contMDiff_mul_right {a : G} : CMDiff n (· * a)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiable_mul_right {a : G} : MDiff (· * a) :=
  contMDiff_mul_right.mdifferentiable one_ne_zero

@[to_additive]
/-
**mdifferentiableAt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_mul_right {a b : G} : MDiffAt (· * a) b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_mul_right`：contMDiffAt_mul_right {a b : G} : CMDiffAt n (· *
 a) b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem mdifferentiableAt_mul_right {a b : G} : MDiffAt (· * a) b :=
  contMDiffAt_mul_right.mdifferentiableAt one_ne_zero

end

variable (I) (g h : G)
variable [ContMDiffMul I ∞ G]

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Used mostly through the notation `𝑳`.
Lemmas involving `smoothLeftMul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
/-
**smoothLeftMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothLeftMul : C^∞⟮I, G; I, G⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by `g`. It is meant to mimic the usual notation in Lie group
s.
Used mostly through the notation `𝑳`.
Lemmas involving `smoothLeftMul` with the notation `𝑳` usually use `L` instead o
f `𝑳` in the
names.
-/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(g * ·), contMDiff_mul_left⟩

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Used mostly through the notation `𝑹`.
Lemmas involving `smoothRightMul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
/-
**smoothRightMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothRightMul : C^∞⟮I, G; I, G⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by `g`. It is meant to mimic the usual notation in Lie grou
ps.
Used mostly through the notation `𝑹`.
Lemmas involving `smoothRightMul` with the notation `𝑹` usually use `R` instead 
of `𝑹` in the
names.
-/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(· * g), contMDiff_mul_right⟩

-- Left multiplication. The abbreviation is `MIL`.
@[inherit_doc] scoped[LieGroup] notation "𝑳" => smoothLeftMul

-- Right multiplication. The abbreviation is `MIR`.
@[inherit_doc] scoped[LieGroup] notation "𝑹" => smoothRightMul

open scoped LieGroup

@[simp]
/-
**L_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：L_apply : (𝑳 I g) h = g * h
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl

@[simp]
/-
**R_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：R_apply : (𝑹 I g) h = h * g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl

@[simp]
/-
**L_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [C
ontMDiffMul I ∞ G] (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h)
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]

@[simp]
/-
**R_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：R_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [C
ontMDiffMul I ∞ G] (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g)
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem R_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]

section

variable {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [ContMDiffMul I ∞ G']
  (g' : G')

/-
**smoothLeftMul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothLeftMul_one : (𝑳 I g') 1 = g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smoothLeftMul_one : (𝑳 I g') 1 = g' :=
  mul_one g'
/-
**smoothRightMul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothRightMul_one : (𝑹 I g') 1 = g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem smoothRightMul_one : (𝑹 I g') 1 = g' :=
  one_mul g'

end

-- Instance of product
@[to_additive prod]
/-
**ContMDiffMul.prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContMDiffMul.prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [Nor
medAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : Model
WithCorners 𝕜 E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Mul G] [
ContMDiffMul I n G] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' 
: Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (G' : Type*) [Top
ologicalSpace G'] [ChartedSpace H' G'] [Mul G'] [ContMDiffMul I' n G'] : ContMDi
ffMul (I.prod I') n (G × G
参数：I : ModelWithCorners 𝕜 E H；G : Type*；I' : ModelWithCorners 𝕜 E' H'；G' : Type*
。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `ContMDiff.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContMDiff.mul`：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDif
f n (f * g)
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `contMDiff_fst`：contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N)
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
-/
instance ContMDiffMul.prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Mul G]
    [ContMDiffMul I n G] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (G' : Type*) [TopologicalSpace G']
    [ChartedSpace H' G'] [Mul G'] [ContMDiffMul I' n G'] : ContMDiffMul (I.prod I') n (G × G') :=
  { IsManifold.prod G G' with
    contMDiff_mul :=
      ((contMDiff_fst.comp contMDiff_fst).mul (contMDiff_fst.comp contMDiff_snd)).prodMk
        ((contMDiff_snd.comp contMDiff_fst).mul (contMDiff_snd.comp contMDiff_snd)) }

end ContMDiffMul

section Monoid

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G] {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [ContMDiffMul I' n G']

@[to_additive]
/-
**contMDiff_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {H : 
Type u_2} [inst_1 : TopologicalSpace H]   {E : Type u_3} [inst_2 : NormedAddComm
Group E] [inst_3 : NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type u_4} 
  [inst_4 : Monoid G] [inst_5 : TopologicalSpace G] [inst_6 : ChartedSpace H G] 
[ContMDiffMul I n G] (i : ℕ),   ContMDiff I I n fun a => a ^ i
参数：i : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contMDiff_pow : ∀ i : ℕ, CMDiff n fun a : G ↦ a ^ i
  | 0 => by simp only [pow_zero, contMDiff_const]
  | k + 1 => by simpa [pow_succ] using! (contMDiff_pow _).mul contMDiff_id

/-- Morphism of additive `C^n` monoids. -/
/-
**ContMDiffAddMonoidMorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     {H' : Type u_5} →                 [inst_4 : TopologicalSpace H'] →         
          {E' : Type u_6} →                     [inst_5 : NormedAddCommGroup E']
 →                       [inst_6 : NormedSpace 𝕜 E'] →                         M
odelWithCorners 𝕜 E H →                           ModelWithCorners 𝕜 E' H' →    
                         WithTop ℕ∞ →                               (G : Type u_
8) →                                 [inst : TopologicalSpace G] →              
                     [ChartedSpace H G] →                                     [A
ddMonoid G] →                                       (G' : Type u_9) →           
                              [inst : TopologicalSpace G'] →                    
                       [ChartedSpace H' G'] → [AddMonoid G'] → Type (max u_8 u_9
)
参数：G : Type u_8；G' : Type u_9；max u_8 u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphism of additive `C^n` monoids.
-/
structure ContMDiffAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : ℕ∞ω) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G]
    (G' : Type*) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
    extends G →+ G' where
  contMDiff_toFun : CMDiff n toFun

/-- Morphism of `C^n` monoids. -/
@[to_additive]
/-
**ContMDiffMonoidMorphism** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     {H' : Type u_5} →                 [inst_4 : TopologicalSpace H'] →         
          {E' : Type u_6} →                     [inst_5 : NormedAddCommGroup E']
 →                       [inst_6 : NormedSpace 𝕜 E'] →                         M
odelWithCorners 𝕜 E H →                           ModelWithCorners 𝕜 E' H' →    
                         WithTop ℕ∞ →                               (G : Type u_
8) →                                 [inst : TopologicalSpace G] →              
                     [ChartedSpace H G] →                                     [M
onoid G] →                                       (G' : Type u_9) →              
                           [inst : TopologicalSpace G'] →                       
                    [ChartedSpace H' G'] → [Monoid G'] → Type (max u_8 u_9)
参数：G : Type u_8；G' : Type u_9；max u_8 u_9。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphism of `C^n` monoids.
-/
structure ContMDiffMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : ℕ∞ω) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] (G' : Type*)
    [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] extends
    G →* G' where
  contMDiff_toFun : CMDiff n toFun

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (ContMDiffMonoidMorphism I I' n G G') :=
  ⟨{  contMDiff_toFun := contMDiff_const
      toMonoidHom := 1 }⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ContMDiffMonoidMorphism I I' n G G') :=
  ⟨1⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (ContMDiffMonoidMorphism I I' n G G') G G' where
  coe a := a.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidHomClass (ContMDiffMonoidMorphism I I' n G G') G G' where
  map_one f := f.map_one
  map_mul f := f.map_mul

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMapClass (ContMDiffMonoidMorphism I I' n G G') G G' where
  map_continuous f := f.contMDiff_toFun.continuous

end Monoid

/-! ### Differentiability of finite point-wise sums and products, and powers

  Finite point-wise products (resp. sums), and powers, of `C^n` functions `M → G` (at `x`/on `s`)
  into a commutative monoid `G` are `C^n` at `x`/on `s`. -/
section CommMonoid

open Function

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {s : Set M} {x x₀ : M} {t : Finset ι} {f : ι → M → G} {p : ι → Prop}

@[to_additive]
/-
**ContMDiffWithinAt.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.prod (h : forall i in t, CMDiffAt[s] n (f i) x₀) : CMDif
fAt[s] n (fun x => ∏ i in t, f i x) x₀
参数：h : forall i in t, CMDiffAt[s] n (f i) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ContMDiffWithinAt.mul`：ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (h
g : CMDiffAt[s] n g x) : CMDiffAt[s] n (f * g) x
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem ContMDiffWithinAt.prod (h : ∀ i ∈ t, CMDiffAt[s] n (f i) x₀) :
    CMDiffAt[s] n (fun x ↦ ∏ i ∈ t, f i x) x₀ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [contMDiffWithinAt_const]
  | insert i K iK IH =>
    simp only [iK, Finset.prod_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).mul (IH fun j hj ↦ h _ <| Finset.mem_insert_of_mem hj)

@[to_additive]
/-
**contMDiffWithinAt_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_finprod (lf : LocallyFinite fun i => mulSupport <| f i) 
{x₀ : M} (h : forall i, CMDiffAt[s] n (f i) x₀) : CMDiffAt[s] n (fun x => ∏ᶠ i, 
f i x) x₀
参数：lf : LocallyFinite fun i => mulSupport <| f i；h : forall i, CMDiffAt[s] n (f 
i) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finprod_eventually_eq_prod`：finprod_eventually_eq_prod {M : Type*} [Comm
Monoid M] {f : ι -> X -> M} (hf : LocallyFinite fun i => mulSupport (f i)) (x : 
X) : exists s : …
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq`：ContMDiffWithinAt.congr_of_even
tuallyEq (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x 
= f x) : ContMDiffWithinAt I …
· 使用定理 `ContMDiffWithinAt.prod`：ContMDiffWithinAt.prod (h : forall i in t, CMDif
fAt[s] n (f i) x₀) : CMDiffAt[s] n (fun x => ∏ i in t, f i x) x₀
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem contMDiffWithinAt_finprod (lf : LocallyFinite fun i ↦ mulSupport <| f i) {x₀ : M}
    (h : ∀ i, CMDiffAt[s] n (f i) x₀) :
    CMDiffAt[s] n (fun x ↦ ∏ᶠ i, f i x) x₀ :=
  let ⟨_I, hI⟩ := finprod_eventually_eq_prod lf x₀
  (ContMDiffWithinAt.prod fun i _hi ↦ h i).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

@[to_additive]
/-
**contMDiffWithinAt_finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_finsetProd' (h : forall i in t, CMDiffAt[s] n (f i) x) :
 CMDiffAt[s] n (∏ i in t, f i) x
参数：h : forall i in t, CMDiffAt[s] n (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `ContMDiffWithinAt.mul`：ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (h
g : CMDiffAt[s] n g x) : CMDiffAt[s] n (f * g) x
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x
-/
theorem contMDiffWithinAt_finsetProd' (h : ∀ i ∈ t, CMDiffAt[s] n (f i) x) :
    CMDiffAt[s] n (∏ i ∈ t, f i) x :=
  Finset.prod_induction f (fun f ↦ CMDiffAt[s] n f x) (fun _ _ hf hg ↦ hf.mul hg)
    (contMDiffWithinAt_const (c := 1)) h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum' := contMDiffWithinAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_prod' := contMDiffWithinAt_finsetProd'

@[to_additive]
/-
**contMDiffWithinAt_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_finsetProd (h : forall i in t, CMDiffAt[s] n (f i) x) : 
CMDiffAt[s] n (fun x => ∏ i in t, f i x) x
参数：h : forall i in t, CMDiffAt[s] n (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `contMDiffWithinAt_finsetProd'`：contMDiffWithinAt_finsetProd' (h : forall
 i in t, CMDiffAt[s] n (f i) x) : CMDiffAt[s] n (∏ i in t, f i) x
-/
theorem contMDiffWithinAt_finsetProd (h : ∀ i ∈ t, CMDiffAt[s] n (f i) x) :
    CMDiffAt[s] n (fun x ↦ ∏ i ∈ t, f i x) x := by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum := contMDiffWithinAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_prod := contMDiffWithinAt_finsetProd

@[to_additive]
/-
**ContMDiffAt.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.prod (h : forall i in t, CMDiffAt n (f i) x₀) : CMDiffAt n (fu
n x => ∏ i in t, f i x) x₀
参数：h : forall i in t, CMDiffAt n (f i) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.prod`：ContMDiffWithinAt.prod (h : forall i in t, CMDif
fAt[s] n (f i) x₀) : CMDiffAt[s] n (fun x => ∏ i in t, f i x) x₀
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem ContMDiffAt.prod (h : ∀ i ∈ t, CMDiffAt n (f i) x₀) :
    CMDiffAt n (fun x ↦ ∏ i ∈ t, f i x) x₀ := by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.prod h

@[to_additive]
/-
**contMDiffAt_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_finprod (lf : LocallyFinite fun i => mulSupport <| f i) (h : f
orall i, CMDiffAt n (f i) x₀) : CMDiffAt n (fun x => ∏ᶠ i, f i x) x₀
参数：lf : LocallyFinite fun i => mulSupport <| f i；h : forall i, CMDiffAt n (f i) 
x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_finprod`：contMDiffWithinAt_finprod (lf : LocallyFinite
 fun i => mulSupport <| f i) {x₀ : M} (h : forall i, CMDiffAt[s] n (f i) x₀) : C
MDiffAt[s] n (f…
-/
theorem contMDiffAt_finprod
    (lf : LocallyFinite fun i ↦ mulSupport <| f i) (h : ∀ i, CMDiffAt n (f i) x₀) :
    CMDiffAt n (fun x ↦ ∏ᶠ i, f i x) x₀ :=
  contMDiffWithinAt_finprod lf h

@[to_additive]
/-
**contMDiffAt_finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_finsetProd' (h : forall i in t, CMDiffAt n (f i) x) : CMDiffAt
 n (∏ i in t, f i) x
参数：h : forall i in t, CMDiffAt n (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_finsetProd'`：contMDiffWithinAt_finsetProd' (h : forall
 i in t, CMDiffAt[s] n (f i) x) : CMDiffAt[s] n (∏ i in t, f i) x
-/
theorem contMDiffAt_finsetProd' (h : ∀ i ∈ t, CMDiffAt n (f i) x) :
    CMDiffAt n (∏ i ∈ t, f i) x :=
  contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum' := contMDiffAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod' := contMDiffAt_finsetProd'

@[to_additive]
/-
**contMDiffAt_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_finsetProd (h : forall i in t, CMDiffAt n (f i) x) : CMDiffAt 
n (fun x => ∏ i in t, f i x) x
参数：h : forall i in t, CMDiffAt n (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_finsetProd`：contMDiffWithinAt_finsetProd (h : forall i
 in t, CMDiffAt[s] n (f i) x) : CMDiffAt[s] n (fun x => ∏ i in t, f i x) x
-/
theorem contMDiffAt_finsetProd (h : ∀ i ∈ t, CMDiffAt n (f i) x) :
    CMDiffAt n (fun x ↦ ∏ i ∈ t, f i x) x :=
  contMDiffWithinAt_finsetProd h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum := contMDiffAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod := contMDiffAt_finsetProd

@[to_additive]
/-
**contMDiffOn_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_finprod (lf : LocallyFinite fun i => Function.mulSupport <| f 
i) (h : forall i, CMDiff[s] n (f i)) : CMDiff[s] n (fun x => ∏ᶠ i, f i x)
参数：lf : LocallyFinite fun i => Function.mulSupport <| f i；h : forall i, CMDiff[s
] n (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_finprod`：contMDiffWithinAt_finprod (lf : LocallyFinite
 fun i => mulSupport <| f i) {x₀ : M} (h : forall i, CMDiffAt[s] n (f i) x₀) : C
MDiffAt[s] n (f…
-/
theorem contMDiffOn_finprod
    (lf : LocallyFinite fun i ↦ Function.mulSupport <| f i) (h : ∀ i, CMDiff[s] n (f i)) :
    CMDiff[s] n (fun x ↦ ∏ᶠ i, f i x) := fun x hx ↦
  contMDiffWithinAt_finprod lf fun i ↦ h i x hx

@[to_additive]
/-
**contMDiffOn_finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_finsetProd' (h : forall i in t, CMDiff[s] n (f i)) : CMDiff[s]
 n (∏ i in t, f i)
参数：h : forall i in t, CMDiff[s] n (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_finsetProd'`：contMDiffWithinAt_finsetProd' (h : forall
 i in t, CMDiffAt[s] n (f i) x) : CMDiffAt[s] n (∏ i in t, f i) x
-/
theorem contMDiffOn_finsetProd' (h : ∀ i ∈ t, CMDiff[s] n (f i)) :
    CMDiff[s] n (∏ i ∈ t, f i) :=
  fun x hx ↦ contMDiffWithinAt_finsetProd' fun i hi ↦ h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum' := contMDiffOn_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod' := contMDiffOn_finsetProd'

@[to_additive]
/-
**contMDiffOn_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_finsetProd (h : forall i in t, CMDiff[s] n (f i)) : CMDiff[s] 
n (fun x => ∏ i in t, f i x)
参数：h : forall i in t, CMDiff[s] n (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffWithinAt_finsetProd`：contMDiffWithinAt_finsetProd (h : forall i
 in t, CMDiffAt[s] n (f i) x) : CMDiffAt[s] n (fun x => ∏ i in t, f i x) x
-/
theorem contMDiffOn_finsetProd (h : ∀ i ∈ t, CMDiff[s] n (f i)) :
    CMDiff[s] n (fun x ↦ ∏ i ∈ t, f i x) :=
  fun x hx ↦ contMDiffWithinAt_finsetProd fun i hi ↦ h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum := contMDiffOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod := contMDiffOn_finsetProd

@[to_additive]
/-
**ContMDiff.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.prod (h : forall i in t, CMDiff n (f i)) : CMDiff n fun x => ∏ i
 in t, f i x
参数：h : forall i in t, CMDiff n (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.prod`：ContMDiffAt.prod (h : forall i in t, CMDiffAt n (f i) 
x₀) : CMDiffAt n (fun x => ∏ i in t, f i x) x₀
-/
theorem ContMDiff.prod (h : ∀ i ∈ t, CMDiff n (f i)) :
    CMDiff n fun x ↦ ∏ i ∈ t, f i x :=
  fun x ↦ ContMDiffAt.prod fun j hj ↦ h j hj x

@[to_additive]
/-
**contMDiff_finsetProd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_finsetProd' (h : forall i in t, CMDiff n (f i)) : CMDiff n (∏ i 
in t, f i)
参数：h : forall i in t, CMDiff n (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_finsetProd'`：contMDiffAt_finsetProd' (h : forall i in t, CMD
iffAt n (f i) x) : CMDiffAt n (∏ i in t, f i) x
-/
theorem contMDiff_finsetProd' (h : ∀ i ∈ t, CMDiff n (f i)) :
    CMDiff n (∏ i ∈ t, f i) := fun x ↦ contMDiffAt_finsetProd' fun i hi ↦ h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum' := contMDiff_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod' := contMDiff_finsetProd'

@[to_additive]
/-
**contMDiff_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_finsetProd (h : forall i in t, CMDiff n (f i)) : CMDiff n fun x 
=> ∏ i in t, f i x
参数：h : forall i in t, CMDiff n (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_finsetProd`：contMDiffAt_finsetProd (h : forall i in t, CMDif
fAt n (f i) x) : CMDiffAt n (fun x => ∏ i in t, f i x) x
-/
theorem contMDiff_finsetProd (h : ∀ i ∈ t, CMDiff n (f i)) :
    CMDiff n fun x ↦ ∏ i ∈ t, f i x :=
  fun x ↦ contMDiffAt_finsetProd fun i hi ↦ h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum := contMDiff_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod := contMDiff_finsetProd

@[to_additive]
/-
**contMDiff_finprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_finprod (h : forall i, CMDiff n (f i)) (hfin : LocallyFinite fun
 i => mulSupport (f i)) : CMDiff n fun x => ∏ᶠ i, f i x
参数：h : forall i, CMDiff n (f i)；hfin : LocallyFinite fun i => mulSupport (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_finprod`：contMDiffAt_finprod (lf : LocallyFinite fun i => mu
lSupport <| f i) (h : forall i, CMDiffAt n (f i) x₀) : CMDiffAt n (fun x => ∏ᶠ i
, f i x) …
-/
theorem contMDiff_finprod (h : ∀ i, CMDiff n (f i))
    (hfin : LocallyFinite fun i ↦ mulSupport (f i)) : CMDiff n fun x ↦ ∏ᶠ i, f i x :=
  fun x ↦ contMDiffAt_finprod hfin fun i ↦ h i x

@[to_additive]
/-
**contMDiff_finprod_cond** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_finprod_cond (hc : forall i, p i -> CMDiff n (f i)) (hf : Locall
yFinite fun i => mulSupport (f i)) : CMDiff n fun x => ∏ᶠ (i) (_ : p i), f i x
参数：hc : forall i, p i -> CMDiff n (f i)；hf : LocallyFinite fun i => mulSupport (
f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `contMDiff_finprod`：contMDiff_finprod (h : forall i, CMDiff n (f i)) (hfi
n : LocallyFinite fun i => mulSupport (f i)) : CMDiff n fun x => ∏ᶠ i, f i x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LocallyFinite.comp_injective`：comp_injective {g : ι' -> ι} (hf : Locally
Finite f) (hg : Injective g) : LocallyFinite (f ∘ g)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem contMDiff_finprod_cond (hc : ∀ i, p i → CMDiff n (f i))
    (hf : LocallyFinite fun i ↦ mulSupport (f i)) :
    CMDiff n fun x ↦ ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i ↦ hc i i.2) (hf.comp_injective Subtype.coe_injective)

variable {g : M → G}

@[to_additive]
/-
**ContMDiffWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.pow (hg : CMDiffAt[s] n g x) (m : Nat) : CMDiffAt[s] n (
fun x => g x ^ m) x
参数：hg : CMDiffAt[s] n g x；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {n : 
WithTop ℕ∞} {H : Type u_2} [inst_1 : TopologicalSpace H]   {E : Type u_3} [inst_
2 :…
-/
theorem ContMDiffWithinAt.pow (hg : CMDiffAt[s] n g x) (m : ℕ) :
    CMDiffAt[s] n (fun x ↦ g x ^ m) x :=
  (contMDiff_pow m).contMDiffAt.comp_contMDiffWithinAt x hg

@[to_additive]
nonrec theorem ContMDiffAt.pow (hg : CMDiffAt n g x) (m : ℕ) :
    CMDiffAt n (fun x ↦ g x ^ m) x :=
  hg.pow m

@[to_additive]
/-
**ContMDiffOn.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.pow (hg : CMDiff[s] n g) (m : Nat) : CMDiff[s] n (fun x => g x
 ^ m)
参数：hg : CMDiff[s] n g；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.pow`：ContMDiffWithinAt.pow (hg : CMDiffAt[s] n g x) (m
 : Nat) : CMDiffAt[s] n (fun x => g x ^ m) x
-/
theorem ContMDiffOn.pow (hg : CMDiff[s] n g) (m : ℕ) :
    CMDiff[s] n (fun x ↦ g x ^ m) :=
  fun x hx ↦ (hg x hx).pow m

@[to_additive]
/-
**ContMDiff.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.pow (hg : CMDiff n g) (m : Nat) : CMDiff n (fun x => g x ^ m)
参数：hg : CMDiff n g；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.pow`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {n 
: WithTop ℕ∞} {H : Type u_3} [inst_1 : TopologicalSpace H]   {E : Type u_4} [ins
t_2 :…
-/
theorem ContMDiff.pow (hg : CMDiff n g) (m : ℕ) :
    CMDiff n (fun x ↦ g x ^ m) :=
  fun x ↦ (hg x).pow m

end CommMonoid

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n : ℕ∞ω}

/-
**instContMDiffAddSelf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instContMDiffAddSelf : ContMDiffAdd 𝓘(𝕜, E) n E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `ContDiff.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…
· 使用定理 `contDiff_add`：contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2
-/
instance instContMDiffAddSelf : ContMDiffAdd 𝓘(𝕜, E) n E := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact contDiff_add.contMDiff

end

section DivConst

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [DivInvMonoid G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

variable {f : M → G} {s : Set M} {x : M} (c : G)

@[to_additive]
/-
**ContMDiffWithinAt.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.div_const (hf : CMDiffAt[s] n f x) : CMDiffAt[s] n (fun 
x => f x / c) x
参数：hf : CMDiffAt[s] n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ContMDiffWithinAt.mul`：ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (h
g : CMDiffAt[s] n g x) : CMDiffAt[s] n (f * g) x
· 使用定理 `contMDiffWithinAt_const`：contMDiffWithinAt_const : ContMDiffWithinAt I I
' n (fun _ : M => c) s x
-/
theorem ContMDiffWithinAt.div_const (hf : CMDiffAt[s] n f x) :
    CMDiffAt[s] n (fun x ↦ f x / c) x := by
  simpa only [div_eq_mul_inv] using! hf.mul contMDiffWithinAt_const

@[to_additive]
nonrec theorem ContMDiffAt.div_const (hf : CMDiffAt n f x) :
    CMDiffAt n (fun x ↦ f x / c) x :=
  hf.div_const c

@[to_additive]
/-
**ContMDiffOn.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.div_const (hf : CMDiff[s] n f) : CMDiff[s] n (fun x => f x / c
)
参数：hf : CMDiff[s] n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.div_const`：ContMDiffWithinAt.div_const (hf : CMDiffAt[
s] n f x) : CMDiffAt[s] n (fun x => f x / c) x
-/
theorem ContMDiffOn.div_const (hf : CMDiff[s] n f) :
    CMDiff[s] n (fun x ↦ f x / c) := fun x hx ↦ (hf x hx).div_const c

@[to_additive]
/-
**ContMDiff.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.div_const (hf : CMDiff n f) : CMDiff n (fun x => f x / c)
参数：hf : CMDiff n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.div_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {n : WithTop ℕ∞} {H : Type u_2} [inst_1 : TopologicalSpace H]   {E : Type u_3
} [inst_2 :…
-/
theorem ContMDiff.div_const (hf : CMDiff n f) :
    CMDiff n (fun x ↦ f x / c) := fun x ↦ (hf x).div_const c

end DivConst

