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
/--
Definition of `ContMDiffAdd` / `ContMDiffAdd` 的定义

English:
class ContMDiffAdd
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  extends: IsManifold I n G
  axioms and operations (1):
    - contMDiff_add : CMDiff n fun p : G × G => p.1 + p.2

中文:
类 ContMDiffAdd
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  继承: IsManifold I n G
  公理与运算 (1 个):
    - contMDiff_add : CMDiff n fun p : G × G => p.1 + p.2
-/
class ContMDiffAdd {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : Nat∞ω)
    (G : Type*) [Add G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_add : CMDiff n fun p : G × G => p.1 + p.2

-- See note [Design choices about smooth algebraic structures]
/-- Basic hypothesis to talk about a `C^n` (Lie) monoid or a `C^n` semigroup.
A `C^n` monoid over `G`, for example, is obtained by requiring both the instances `Monoid G`
and `ContMDiffMul I n G`.

See also `ContMDiffSMul I I' n G M` for `C^n` actions of `G` on a manifold `M`. -/
@[to_additive]
/--
Definition of `ContMDiffMul` / `ContMDiffMul` 的定义

English:
class ContMDiffMul
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  extends: IsManifold I n G
  axioms and operations (1):
    - contMDiff_mul : CMDiff n fun p : G × G => p.1 * p.2

中文:
类 ContMDiffMul
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  继承: IsManifold I n G
  公理与运算 (1 个):
    - contMDiff_mul : CMDiff n fun p : G × G => p.1 * p.2
-/
class ContMDiffMul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H) (n : Nat∞ω)
    (G : Type*) [Mul G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends IsManifold I n G where
  contMDiff_mul : CMDiff n fun p : G × G => p.1 * p.2

section ContMDiffMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω}
  {G : Type*} [Mul G] [TopologicalSpace G] [ChartedSpace H G] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

@[to_additive]
/--
theorem `ContMDiffMul.of_le` / 定理 `ContMDiffMul.of_le`

English:
theorem ContMDiffMul.of_le
  statement: {m n : Nat∞ω} (hmn : m <= n)
  proof: by
  have : IsManifold I m G := IsManifold.of_le hmn
  exact ⟨h.contMDiff_mul.of_le hmn⟩

@[to_additive]

中文:
定理 ContMDiffMul.of_le
  结论: {m n : 自然数∞ω} (hmn : m <= n)
  证明: by
  have : IsManifold I m G := IsManifold.of_le hmn
  exact ⟨h.contMDiff_mul.of_le hmn⟩

@[to_additive]
-/
protected theorem ContMDiffMul.of_le {m n : Nat∞ω} (hmn : m <= n)
    [h : ContMDiffMul I n G] : ContMDiffMul I m G := by
  have : IsManifold I m G := IsManifold.of_le hmn
  exact ⟨h.contMDiff_mul.of_le hmn⟩

@[to_additive]
instance {a : Nat∞ω} [ContMDiffMul I ∞ G] [h : ENat.LEInfty a] : ContMDiffMul I a G :=
  ContMDiffMul.of_le h.out

@[to_additive]
instance {a : Nat∞ω} [ContMDiffMul I ω G] : ContMDiffMul I a G :=
  ContMDiffMul.of_le le_top

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousMul
  signature: G] : ContMDiffMul I 0 G
  body: by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_mul

@[to_additive]

中文:
实例 [ContinuousMul
  签名: G] : ContMDiffMul I 0 G
  定义体: by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_mul

@[to_additive]

Depends on / 依赖: contMDiff_zero_iff, continuous_mul
-/
instance [ContinuousMul G] : ContMDiffMul I 0 G := by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_mul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContMDiffMul
  signature: I 2 G] : ContMDiffMul I 1 G
  body: ContMDiffMul.of_le one_le_two

中文:
实例 [ContMDiffMul
  签名: I 2 G] : ContMDiffMul I 1 G
  定义体: ContMDiffMul.of_le one_le_two

Depends on / 依赖: ContMDiffMul, ContMDiffMul.of_le, of_le, one_le_two
-/
instance [ContMDiffMul I 2 G] : ContMDiffMul I 1 G :=
  ContMDiffMul.of_le one_le_two

section

variable (I n)

@[to_additive]
/--
theorem `contMDiff_mul` / 定理 `contMDiff_mul`

English:
theorem contMDiff_mul
  given: [ContMDiffMul I n G]
  statement: CMDiff n fun p : G × G => p.1 * p.2
  proof: ContMDiffMul.contMDiff_mul

include I n in

中文:
定理 contMDiff_mul
  条件: [ContMDiffMul I n G]
  结论: CMDiff n fun p : G × G => p.1 * p.2
  证明: ContMDiffMul.contMDiff_mul

include I n in

Depends on / 依赖: ContMDiffMul, ContMDiffMul.contMDiff_mul, contMDiff_mul
-/
theorem contMDiff_mul [ContMDiffMul I n G] : CMDiff n fun p : G × G => p.1 * p.2 :=
  ContMDiffMul.contMDiff_mul

include I n in
/-- If the multiplication is `C^n`, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive /-- If the addition is `C^n`, then it is continuous. This is not an instance for
technical reasons, see note [Design choices about smooth algebraic structures]. -/]
/--
theorem `continuousMul_of_contMDiffMul` / 定理 `continuousMul_of_contMDiffMul`

English:
theorem continuousMul_of_contMDiffMul
  given: [ContMDiffMul I n G]
  statement: ContinuousMul G
  proof: ⟨(contMDiff_mul I n).continuous⟩

中文:
定理 continuousMul_of_contMDiffMul
  条件: [ContMDiffMul I n G]
  结论: ContinuousMul G
  证明: ⟨(contMDiff_mul I n).continuous⟩

Depends on / 依赖: contMDiff_mul, continuous
-/
theorem continuousMul_of_contMDiffMul [ContMDiffMul I n G] : ContinuousMul G :=
  ⟨(contMDiff_mul I n).continuous⟩

end

section

variable [ContMDiffMul I n G] {f g : M -> G} {s : Set M} {x : M}

@[to_additive]
/--
theorem `ContMDiffWithinAt.mul` / 定理 `ContMDiffWithinAt.mul`

English:
theorem ContMDiffWithinAt.mul
  given: (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x)
  proof: (contMDiff_mul I n).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) : CMDiffAt n (f * g) x :=
  hf.mul hg

@[to_additive]

中文:
定理 ContMDiffWithinAt.mul
  条件: (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x)
  证明: (contMDiff_mul I n).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) : CMDiffAt n (f * g) x :=
  hf.mul hg

@[to_additive]

Depends on / 依赖: comp_contMDiffWithinAt, contMDiffAt, contMDiffAt.comp_contMDiffWithinAt, contMDiff_mul, hf.prodMk, prodMk
-/
theorem ContMDiffWithinAt.mul (hf : CMDiffAt[s] n f x) (hg : CMDiffAt[s] n g x) :
    CMDiffAt[s] n (f * g) x :=
  (contMDiff_mul I n).contMDiffAt.comp_contMDiffWithinAt x (hf.prodMk hg)

@[to_additive]
nonrec theorem ContMDiffAt.mul (hf : CMDiffAt n f x) (hg : CMDiffAt n g x) : CMDiffAt n (f * g) x :=
  hf.mul hg

@[to_additive]
/--
theorem `ContMDiffOn.mul` / 定理 `ContMDiffOn.mul`

English:
theorem ContMDiffOn.mul
  given: (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
  statement: CMDiff[s] n (f * g)
  proof: fun x hx => (hf x hx).mul (hg x hx)

@[to_additive]

中文:
定理 ContMDiffOn.mul
  条件: (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
  结论: CMDiff[s] n (f * g)
  证明: fun x hx => (hf x hx).mul (hg x hx)

@[to_additive]
-/
theorem ContMDiffOn.mul (hf : CMDiff[s] n f) (hg : CMDiff[s] n g) : CMDiff[s] n (f * g) :=
  fun x hx => (hf x hx).mul (hg x hx)

@[to_additive]
/--
theorem `ContMDiff.mul` / 定理 `ContMDiff.mul`

English:
theorem ContMDiff.mul
  given: (hf : CMDiff n f) (hg : CMDiff n g)
  statement: CMDiff n (f * g)
  proof: fun x => (hf x).mul (hg x)

@[to_additive]

中文:
定理 ContMDiff.mul
  条件: (hf : CMDiff n f) (hg : CMDiff n g)
  结论: CMDiff n (f * g)
  证明: fun x => (hf x).mul (hg x)

@[to_additive]
-/
theorem ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDiff n (f * g) :=
  fun x => (hf x).mul (hg x)

@[to_additive]
/--
theorem `contMDiff_mul_left` / 定理 `contMDiff_mul_left`

English:
theorem contMDiff_mul_left
  given: {a : G}
  statement: CMDiff n (a * ·)
  proof: contMDiff_const.mul contMDiff_id

@[to_additive]

中文:
定理 contMDiff_mul_left
  条件: {a : G}
  结论: CMDiff n (a * ·)
  证明: contMDiff_const.mul contMDiff_id

@[to_additive]

Depends on / 依赖: contMDiff_const, contMDiff_const.mul, contMDiff_id
-/
theorem contMDiff_mul_left {a : G} : CMDiff n (a * ·) :=
  contMDiff_const.mul contMDiff_id

@[to_additive]
/--
theorem `contMDiffAt_mul_left` / 定理 `contMDiffAt_mul_left`

English:
theorem contMDiffAt_mul_left
  given: {a b : G}
  statement: CMDiffAt n (a * ·) b
  proof: contMDiff_mul_left.contMDiffAt

@[to_additive]

中文:
定理 contMDiffAt_mul_left
  条件: {a b : G}
  结论: CMDiffAt n (a * ·) b
  证明: contMDiff_mul_left.contMDiffAt

@[to_additive]

Depends on / 依赖: contMDiffAt, contMDiff_mul_left, contMDiff_mul_left.contMDiffAt
-/
theorem contMDiffAt_mul_left {a b : G} : CMDiffAt n (a * ·) b :=
  contMDiff_mul_left.contMDiffAt

@[to_additive]
/--
theorem `contMDiff_mul_right` / 定理 `contMDiff_mul_right`

English:
theorem contMDiff_mul_right
  given: {a : G}
  statement: CMDiff n (· * a)
  proof: contMDiff_id.mul contMDiff_const

@[to_additive]

中文:
定理 contMDiff_mul_right
  条件: {a : G}
  结论: CMDiff n (· * a)
  证明: contMDiff_id.mul contMDiff_const

@[to_additive]

Depends on / 依赖: contMDiff_const, contMDiff_id, contMDiff_id.mul
-/
theorem contMDiff_mul_right {a : G} : CMDiff n (· * a) :=
  contMDiff_id.mul contMDiff_const

@[to_additive]
/--
theorem `contMDiffAt_mul_right` / 定理 `contMDiffAt_mul_right`

English:
theorem contMDiffAt_mul_right
  given: {a b : G}
  statement: CMDiffAt n (· * a) b
  proof: contMDiff_mul_right.contMDiffAt

中文:
定理 contMDiffAt_mul_right
  条件: {a b : G}
  结论: CMDiffAt n (· * a) b
  证明: contMDiff_mul_right.contMDiffAt

Depends on / 依赖: contMDiffAt, contMDiff_mul_right, contMDiff_mul_right.contMDiffAt
-/
theorem contMDiffAt_mul_right {a b : G} : CMDiffAt n (· * a) b :=
  contMDiff_mul_right.contMDiffAt

end

section

variable [ContMDiffMul I 1 G]

@[to_additive]
/--
theorem `mdifferentiable_mul_left` / 定理 `mdifferentiable_mul_left`

English:
theorem mdifferentiable_mul_left
  given: {a : G}
  statement: MDiff (a * ·)
  proof: contMDiff_mul_left.mdifferentiable one_ne_zero

@[to_additive]

中文:
定理 mdifferentiable_mul_left
  条件: {a : G}
  结论: MDiff (a * ·)
  证明: contMDiff_mul_left.mdifferentiable one_ne_zero

@[to_additive]

Depends on / 依赖: contMDiff_mul_left, contMDiff_mul_left.mdifferentiable, mdifferentiable, one_ne_zero
-/
theorem mdifferentiable_mul_left {a : G} : MDiff (a * ·) :=
  contMDiff_mul_left.mdifferentiable one_ne_zero

@[to_additive]
/--
theorem `mdifferentiableAt_mul_left` / 定理 `mdifferentiableAt_mul_left`

English:
theorem mdifferentiableAt_mul_left
  given: {a b : G}
  statement: MDiffAt (a * ·) b
  proof: contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

@[to_additive]

中文:
定理 mdifferentiableAt_mul_left
  条件: {a b : G}
  结论: MDiffAt (a * ·) b
  证明: contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

@[to_additive]

Depends on / 依赖: contMDiffAt_mul_left, contMDiffAt_mul_left.mdifferentiableAt, mdifferentiableAt, one_ne_zero
-/
theorem mdifferentiableAt_mul_left {a b : G} : MDiffAt (a * ·) b :=
  contMDiffAt_mul_left.mdifferentiableAt one_ne_zero

@[to_additive]
/--
theorem `mdifferentiable_mul_right` / 定理 `mdifferentiable_mul_right`

English:
theorem mdifferentiable_mul_right
  given: {a : G}
  statement: MDiff (· * a)
  proof: contMDiff_mul_right.mdifferentiable one_ne_zero

@[to_additive]

中文:
定理 mdifferentiable_mul_right
  条件: {a : G}
  结论: MDiff (· * a)
  证明: contMDiff_mul_right.mdifferentiable one_ne_zero

@[to_additive]

Depends on / 依赖: contMDiff_mul_right, contMDiff_mul_right.mdifferentiable, mdifferentiable, one_ne_zero
-/
theorem mdifferentiable_mul_right {a : G} : MDiff (· * a) :=
  contMDiff_mul_right.mdifferentiable one_ne_zero

@[to_additive]
/--
theorem `mdifferentiableAt_mul_right` / 定理 `mdifferentiableAt_mul_right`

English:
theorem mdifferentiableAt_mul_right
  given: {a b : G}
  statement: MDiffAt (· * a) b
  proof: contMDiffAt_mul_right.mdifferentiableAt one_ne_zero

中文:
定理 mdifferentiableAt_mul_right
  条件: {a b : G}
  结论: MDiffAt (· * a) b
  证明: contMDiffAt_mul_right.mdifferentiableAt one_ne_zero

Depends on / 依赖: contMDiffAt_mul_right, contMDiffAt_mul_right.mdifferentiableAt, mdifferentiableAt, one_ne_zero
-/
theorem mdifferentiableAt_mul_right {a b : G} : MDiffAt (· * a) b :=
  contMDiffAt_mul_right.mdifferentiableAt one_ne_zero

end

variable (I) (g h : G)
variable [ContMDiffMul I ∞ G]

/--
Definition of `smoothLeftMul` / `smoothLeftMul` 的定义

English:
definition smoothLeftMul
  signature: : C^∞⟮I, G; I, G⟯
  body: ⟨(g * ·), contMDiff_mul_left⟩

中文:
定义 smoothLeftMul
  签名: : C^∞⟮I, G; I, G⟯
  定义体: ⟨(g * ·), contMDiff_mul_left⟩

Depends on / 依赖: contMDiff_mul_left
-/
def smoothLeftMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(g * ·), contMDiff_mul_left⟩

/--
Definition of `smoothRightMul` / `smoothRightMul` 的定义

English:
definition smoothRightMul
  signature: : C^∞⟮I, G; I, G⟯
  body: ⟨(· * g), contMDiff_mul_right⟩

中文:
定义 smoothRightMul
  签名: : C^∞⟮I, G; I, G⟯
  定义体: ⟨(· * g), contMDiff_mul_right⟩

Depends on / 依赖: contMDiff_mul_right
-/
def smoothRightMul : C^∞⟮I, G; I, G⟯ :=
  ⟨(· * g), contMDiff_mul_right⟩

-- Left multiplication. The abbreviation is `MIL`.
@[inherit_doc] scoped[LieGroup] notation "𝑳" => smoothLeftMul

-- Right multiplication. The abbreviation is `MIR`.
@[inherit_doc] scoped[LieGroup] notation "𝑹" => smoothRightMul

open scoped LieGroup

@[simp]
/--
theorem `L_apply` / 定理 `L_apply`

English:
theorem L_apply
  statement: (𝑳 I g) h = g * h
  proof: rfl

@[simp]

中文:
定理 L_apply
  结论: (𝑳 I g) h = g * h
  证明: rfl

@[simp]
-/
theorem L_apply : (𝑳 I g) h = g * h :=
  rfl

@[simp]
/--
theorem `R_apply` / 定理 `R_apply`

English:
theorem R_apply
  statement: (𝑹 I g) h = h * g
  proof: rfl

@[simp]

中文:
定理 R_apply
  结论: (𝑹 I g) h = h * g
  证明: rfl

@[simp]
-/
theorem R_apply : (𝑹 I g) h = h * g :=
  rfl

@[simp]
/--
theorem `L_mul` / 定理 `L_mul`

English:
theorem L_mul
  statement: {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
  proof: by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]

@[simp]

中文:
定理 L_mul
  结论: {G : 类型} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
  证明: by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]

@[simp]

Depends on / 依赖: ContMDiffMap, ContMDiffMap.comp_apply, L_apply, comp_apply, mul_assoc
-/
theorem L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
    (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) := by
  ext
  simp only [ContMDiffMap.comp_apply, L_apply, mul_assoc]

@[simp]
/--
theorem `R_mul` / 定理 `R_mul`

English:
theorem R_mul
  statement: {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
  proof: by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]

中文:
定理 R_mul
  结论: {G : 类型} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
  证明: by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]

Depends on / 依赖: ContMDiffMap, ContMDiffMap.comp_apply, R_apply, comp_apply, mul_assoc
-/
theorem R_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]
    (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) := by
  ext
  simp only [ContMDiffMap.comp_apply, R_apply, mul_assoc]

section

variable {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H G'] [ContMDiffMul I ∞ G']
  (g' : G')

/--
theorem `smoothLeftMul_one` / 定理 `smoothLeftMul_one`

English:
theorem smoothLeftMul_one
  statement: (𝑳 I g') 1 = g'
  proof: mul_one g'

中文:
定理 smoothLeftMul_one
  结论: (𝑳 I g') 1 = g'
  证明: mul_one g'

Depends on / 依赖: mul_one
-/
theorem smoothLeftMul_one : (𝑳 I g') 1 = g' :=
  mul_one g'

/--
theorem `smoothRightMul_one` / 定理 `smoothRightMul_one`

English:
theorem smoothRightMul_one
  statement: (𝑹 I g') 1 = g'
  proof: one_mul g'

中文:
定理 smoothRightMul_one
  结论: (𝑹 I g') 1 = g'
  证明: one_mul g'

Depends on / 依赖: one_mul
-/
theorem smoothRightMul_one : (𝑹 I g') 1 = g' :=
  one_mul g'

end

-- Instance of product
@[to_additive prod]
/--
Instance `ContMDiffMul.prod` / 实例 `ContMDiffMul.prod`

English:
instance ContMDiffMul.prod
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  body: { IsManifold.prod G G' with
    contMDiff_mul :=
      ((contMDiff_fst.comp contMDiff_fst).mul (contMDiff_fst.comp contMDiff_snd)).prodMk
        ((contMDiff_snd.comp contMDiff_fst).mul (contMDiff_snd.comp contMDiff_snd)) }

中文:
实例 ContMDiffMul.prod
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  定义体: { IsManifold.prod G G' with
    contMDiff_mul :=
      ((contMDiff_fst.comp contMDiff_fst).mul (contMDiff_fst.comp contMDiff_snd)).prodMk
        ((contMDiff_snd.comp contMDiff_fst).mul (contMDiff_snd.comp contMDiff_snd)) }

Depends on / 依赖: IsManifold, IsManifold.prod, contMDiff_fst, contMDiff_fst.comp, contMDiff_mul, contMDiff_snd, contMDiff_snd.comp, prodMk
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*} [Monoid G]
  [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G] {H' : Type*} [TopologicalSpace H']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ChartedSpace H' G'] [ContMDiffMul I' n G']

@[to_additive]
/--
theorem `contMDiff_pow` / 定理 `contMDiff_pow`

English:
theorem contMDiff_pow
  statement: forall i : Nat, CMDiff n fun a : G => a ^ i

中文:
定理 contMDiff_pow
  结论: 对任意 i : 自然数, CMDiff n fun a : G => a ^ i
-/
theorem contMDiff_pow : forall i : Nat, CMDiff n fun a : G => a ^ i
  | 0 => by simp only [pow_zero, contMDiff_const]
  | k + 1 => by simpa [pow_succ] using! (contMDiff_pow _).mul contMDiff_id

/--
Definition of `ContMDiffAddMonoidMorphism` / `ContMDiffAddMonoidMorphism` 的定义

English:
structure ContMDiffAddMonoidMorphism
  parameters: (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  extends: G ->+ G'
  axioms and operations (1):
    - contMDiff_toFun : CMDiff n toFun

中文:
结构 ContMDiffAddMonoidMorphism
  参数: (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  继承: G ->+ G'
  公理与运算 (1 个):
    - contMDiff_toFun : CMDiff n toFun
-/
structure ContMDiffAddMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : Nat∞ω) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [AddMonoid G]
    (G' : Type*) [TopologicalSpace G'] [ChartedSpace H' G'] [AddMonoid G']
    extends G ->+ G' where
  contMDiff_toFun : CMDiff n toFun

/-- Morphism of `C^n` monoids. -/
@[to_additive]
/--
Definition of `ContMDiffMonoidMorphism` / `ContMDiffMonoidMorphism` 的定义

English:
structure ContMDiffMonoidMorphism
  parameters: (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  axioms and operations (1):
    - contMDiff_toFun : CMDiff n toFun

中文:
结构 ContMDiffMonoidMorphism
  参数: (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  公理与运算 (1 个):
    - contMDiff_toFun : CMDiff n toFun
-/
structure ContMDiffMonoidMorphism (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    (n : Nat∞ω) (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Monoid G] (G' : Type*)
    [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G'] extends
    G ->* G' where
  contMDiff_toFun : CMDiff n toFun

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (ContMDiffMonoidMorphism I I' n G G')
  body: ⟨{ contMDiff_toFun := contMDiff_const
      toMonoidHom := 1 }⟩

@[to_additive]

中文:
实例 :
  签名: One (ContMDiffMonoidMorphism I I' n G G')
  定义体: ⟨{ contMDiff_toFun := contMDiff_const
      toMonoidHom := 1 }⟩

@[to_additive]

Depends on / 依赖: contMDiff_const, contMDiff_toFun, toMonoidHom
-/
instance : One (ContMDiffMonoidMorphism I I' n G G') :=
  ⟨{ contMDiff_toFun := contMDiff_const
      toMonoidHom := 1 }⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ContMDiffMonoidMorphism I I' n G G')
  body: ⟨1⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited (ContMDiffMonoidMorphism I I' n G G')
  定义体: ⟨1⟩

@[to_additive]
-/
instance : Inhabited (ContMDiffMonoidMorphism I I' n G G') :=
  ⟨1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (ContMDiffMonoidMorphism I I' n G G') G G'
  body: a.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

@[to_additive]

中文:
实例 :
  签名: FunLike (ContMDiffMonoidMorphism I I' n G G') G G'
  定义体: a.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

@[to_additive]

Depends on / 依赖: a.toFun
-/
instance : FunLike (ContMDiffMonoidMorphism I I' n G G') G G' where
  coe a := a.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidHomClass (ContMDiffMonoidMorphism I I' n G G') G G'
  body: f.map_one
  map_mul f := f.map_mul

@[to_additive]

中文:
实例 :
  签名: MonoidHomClass (ContMDiffMonoidMorphism I I' n G G') G G'
  定义体: f.map_one
  map_mul f := f.map_mul

@[to_additive]

Depends on / 依赖: f.map_one, map_one
-/
instance : MonoidHomClass (ContMDiffMonoidMorphism I I' n G G') G G' where
  map_one f := f.map_one
  map_mul f := f.map_mul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMapClass (ContMDiffMonoidMorphism I I' n G G') G G'
  body: f.contMDiff_toFun.continuous

中文:
实例 :
  签名: ContinuousMapClass (ContMDiffMonoidMorphism I I' n G G') G G'
  定义体: f.contMDiff_toFun.continuous

Depends on / 依赖: contMDiff_toFun, continuous, f.contMDiff_toFun.continuous
-/
instance : ContinuousMapClass (ContMDiffMonoidMorphism I I' n G G') G G' where
  map_continuous f := f.contMDiff_toFun.continuous

end Monoid

/-! ### Differentiability of finite point-wise sums and products, and powers

  Finite point-wise products (resp. sums), and powers, of `C^n` functions `M → G` (at `x`/on `s`)
  into a commutative monoid `G` are `C^n` at `x`/on `s`. -/
section CommMonoid

open Function

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω} {H : Type*} [TopologicalSpace H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [CommMonoid G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {s : Set M} {x x₀ : M} {t : Finset ι} {f : ι -> M -> G} {p : ι -> Prop}

@[to_additive]
/--
theorem `ContMDiffWithinAt.prod` / 定理 `ContMDiffWithinAt.prod`

English:
theorem ContMDiffWithinAt.prod
  given: (h : forall i in t, CMDiffAt[s] n (f i) x₀)
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp [contMDiffWithinAt_const]
  | insert i K iK IH =>
    simp only [iK, Finset.prod_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).mul (IH fun j hj => h _ <| Finset.mem_insert_of_mem hj)

@[to_additive]

中文:
定理 ContMDiffWithinAt.prod
  条件: (h : 对任意 i in t, CMDiffAt[s] n (f i) x₀)
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp [contMDiffWithinAt_const]
  | insert i K iK IH =>
    simp only [iK, Finset.prod_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).mul (IH fun j hj => h _ <| Finset.mem_insert_of_mem hj)

@[to_additive]

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_insert, classical, contMDiffWithinAt_const, induction_on, insert, mem_insert_of_mem, mem_insert_self, not_false_iff, prod_insert
-/
theorem ContMDiffWithinAt.prod (h : forall i in t, CMDiffAt[s] n (f i) x₀) :
    CMDiffAt[s] n (fun x => ∏ i in t, f i x) x₀ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [contMDiffWithinAt_const]
  | insert i K iK IH =>
    simp only [iK, Finset.prod_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).mul (IH fun j hj => h _ <| Finset.mem_insert_of_mem hj)

@[to_additive]
/--
theorem `contMDiffWithinAt_finprod` / 定理 `contMDiffWithinAt_finprod`

English:
theorem contMDiffWithinAt_finprod
  statement: (lf : LocallyFinite fun i => mulSupport <| f i) {x₀ : M}
  proof: let ⟨_I, hI⟩ := finprod_eventually_eq_prod lf x₀
  (ContMDiffWithinAt.prod fun i _hi => h i).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

@[to_additive]

中文:
定理 contMDiffWithinAt_finprod
  结论: (lf : LocallyFinite fun i => mulSupport <| f i) {x₀ : M}
  证明: let ⟨_I, hI⟩ := finprod_eventually_eq_prod lf x₀
  (ContMDiffWithinAt.prod fun i _hi => h i).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

@[to_additive]

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.prod, Quotient, RingCon, RingCon.Quotient, congr_of_eventuallyEq, eventually_nhdsWithin_of_eventually_nhds, finprod_eventually_eq_prod, hI.self_of_nhds, self_of_nhds
-/
theorem contMDiffWithinAt_finprod (lf : LocallyFinite fun i => mulSupport <| f i) {x₀ : M}
    (h : forall i, CMDiffAt[s] n (f i) x₀) :
    CMDiffAt[s] n (fun x => ∏ᶠ i, f i x) x₀ :=
  let ⟨_I, hI⟩ := finprod_eventually_eq_prod lf x₀
  (ContMDiffWithinAt.prod fun i _hi => h i).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

@[to_additive]
/--
theorem `contMDiffWithinAt_finsetProd'` / 定理 `contMDiffWithinAt_finsetProd'`

English:
theorem contMDiffWithinAt_finsetProd'
  given: (h : forall i in t, CMDiffAt[s] n (f i) x)
  proof: Finset.prod_induction f (fun f => CMDiffAt[s] n f x) (fun _ _ hf hg => hf.mul hg)
    (contMDiffWithinAt_const (c := 1)) h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum' := contMDiffWithinAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias con

中文:
定理 contMDiffWithinAt_finsetProd'
  条件: (h : 对任意 i in t, CMDiffAt[s] n (f i) x)
  证明: Finset.prod_induction f (fun f => CMDiffAt[s] n f x) (fun _ _ hf hg => hf.mul hg)
    (contMDiffWithinAt_const (c := 1)) h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum' := contMDiffWithinAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias con

Depends on / 依赖: AddCommGroup, CMDiffAt, CommRing, CommSemiring, Finset, Finset.prod_induction, contMDiffWithinAt_const, hf.mul, instAlgebra, prod_induction
-/
theorem contMDiffWithinAt_finsetProd' (h : forall i in t, CMDiffAt[s] n (f i) x) :
    CMDiffAt[s] n (∏ i in t, f i) x :=
  Finset.prod_induction f (fun f => CMDiffAt[s] n f x) (fun _ _ hf hg => hf.mul hg)
    (contMDiffWithinAt_const (c := 1)) h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum' := contMDiffWithinAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_prod' := contMDiffWithinAt_finsetProd'

@[to_additive]
/--
theorem `contMDiffWithinAt_finsetProd` / 定理 `contMDiffWithinAt_finsetProd`

English:
theorem contMDiffWithinAt_finsetProd
  given: (h : forall i in t, CMDiffAt[s] n (f i) x)
  proof: by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum := contMDiffWithinAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_prod := contMDiffWithinAt_

中文:
定理 contMDiffWithinAt_finsetProd
  条件: (h : 对任意 i in t, CMDiffAt[s] n (f i) x)
  证明: by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum := contMDiffWithinAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_prod := contMDiffWithinAt_

Depends on / 依赖: Finset, Finset.prod_apply, contMDiffWithinAt_finsetProd, prod_apply
-/
theorem contMDiffWithinAt_finsetProd (h : forall i in t, CMDiffAt[s] n (f i) x) :
    CMDiffAt[s] n (fun x => ∏ i in t, f i x) x := by
  simp only [← Finset.prod_apply]
  exact contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_sum := contMDiffWithinAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffWithinAt_finset_prod := contMDiffWithinAt_finsetProd

@[to_additive]
/--
theorem `ContMDiffAt.prod` / 定理 `ContMDiffAt.prod`

English:
theorem ContMDiffAt.prod
  given: (h : forall i in t, CMDiffAt n (f i) x₀)
  proof: by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.prod h

@[to_additive]

中文:
定理 ContMDiffAt.prod
  条件: (h : 对任意 i in t, CMDiffAt n (f i) x₀)
  证明: by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.prod h

@[to_additive]

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.prod, RingCon, RingCon.instSMulCommClassQuotient, contMDiffWithinAt_univ, instSMulCommClassQuotient
-/
theorem ContMDiffAt.prod (h : forall i in t, CMDiffAt n (f i) x₀) :
    CMDiffAt n (fun x => ∏ i in t, f i x) x₀ := by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.prod h

@[to_additive]
/--
theorem `contMDiffAt_finprod` / 定理 `contMDiffAt_finprod`

English:
theorem contMDiffAt_finprod
  proof: contMDiffWithinAt_finprod lf h

@[to_additive]

中文:
定理 contMDiffAt_finprod
  证明: contMDiffWithinAt_finprod lf h

@[to_additive]

Depends on / 依赖: RingCon, RingCon.instIsScalarTowerQuotient, contMDiffWithinAt_finprod, instIsScalarTowerQuotient
-/
theorem contMDiffAt_finprod
    (lf : LocallyFinite fun i => mulSupport <| f i) (h : forall i, CMDiffAt n (f i) x₀) :
    CMDiffAt n (fun x => ∏ᶠ i, f i x) x₀ :=
  contMDiffWithinAt_finprod lf h

@[to_additive]
/--
theorem `contMDiffAt_finsetProd'` / 定理 `contMDiffAt_finsetProd'`

English:
theorem contMDiffAt_finsetProd'
  given: (h : forall i in t, CMDiffAt n (f i) x)
  proof: contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum' := contMDiffAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod' := contMDiffAt_finsetProd'

@[to_additive]

中文:
定理 contMDiffAt_finsetProd'
  条件: (h : 对任意 i in t, CMDiffAt n (f i) x)
  证明: contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum' := contMDiffAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod' := contMDiffAt_finsetProd'

@[to_additive]

Depends on / 依赖: contMDiffWithinAt_finsetProd
-/
theorem contMDiffAt_finsetProd' (h : forall i in t, CMDiffAt n (f i) x) :
    CMDiffAt n (∏ i in t, f i) x :=
  contMDiffWithinAt_finsetProd' h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum' := contMDiffAt_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod' := contMDiffAt_finsetProd'

@[to_additive]
/--
theorem `contMDiffAt_finsetProd` / 定理 `contMDiffAt_finsetProd`

English:
theorem contMDiffAt_finsetProd
  given: (h : forall i in t, CMDiffAt n (f i) x)
  proof: contMDiffWithinAt_finsetProd h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum := contMDiffAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod := contMDiffAt_finsetProd

@[to_additive]

中文:
定理 contMDiffAt_finsetProd
  条件: (h : 对任意 i in t, CMDiffAt n (f i) x)
  证明: contMDiffWithinAt_finsetProd h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum := contMDiffAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod := contMDiffAt_finsetProd

@[to_additive]

Depends on / 依赖: contMDiffWithinAt_finsetProd
-/
theorem contMDiffAt_finsetProd (h : forall i in t, CMDiffAt n (f i) x) :
    CMDiffAt n (fun x => ∏ i in t, f i x) x :=
  contMDiffWithinAt_finsetProd h

@[deprecated (since := "2026-04-08")] alias contMDiffAt_finset_sum := contMDiffAt_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffAt_finset_prod := contMDiffAt_finsetProd

@[to_additive]
/--
theorem `contMDiffOn_finprod` / 定理 `contMDiffOn_finprod`

English:
theorem contMDiffOn_finprod
  proof: fun x hx =>
  contMDiffWithinAt_finprod lf fun i => h i x hx

@[to_additive]

中文:
定理 contMDiffOn_finprod
  证明: fun x hx =>
  contMDiffWithinAt_finprod lf fun i => h i x hx

@[to_additive]
-/
theorem contMDiffOn_finprod
    (lf : LocallyFinite fun i => Function.mulSupport <| f i) (h : forall i, CMDiff[s] n (f i)) :
    CMDiff[s] n (fun x => ∏ᶠ i, f i x) := fun x hx =>
  contMDiffWithinAt_finprod lf fun i => h i x hx

@[to_additive]
/--
theorem `contMDiffOn_finsetProd'` / 定理 `contMDiffOn_finsetProd'`

English:
theorem contMDiffOn_finsetProd'
  given: (h : forall i in t, CMDiff[s] n (f i))
  proof: fun x hx => contMDiffWithinAt_finsetProd' fun i hi => h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum' := contMDiffOn_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod' := contMDiffOn_finsetProd'

@[to_additive]

中文:
定理 contMDiffOn_finsetProd'
  条件: (h : 对任意 i in t, CMDiff[s] n (f i))
  证明: fun x hx => contMDiffWithinAt_finsetProd' fun i hi => h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum' := contMDiffOn_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod' := contMDiffOn_finsetProd'

@[to_additive]

Depends on / 依赖: contMDiffWithinAt_finsetProd
-/
theorem contMDiffOn_finsetProd' (h : forall i in t, CMDiff[s] n (f i)) :
    CMDiff[s] n (∏ i in t, f i) :=
  fun x hx => contMDiffWithinAt_finsetProd' fun i hi => h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum' := contMDiffOn_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod' := contMDiffOn_finsetProd'

@[to_additive]
/--
theorem `contMDiffOn_finsetProd` / 定理 `contMDiffOn_finsetProd`

English:
theorem contMDiffOn_finsetProd
  given: (h : forall i in t, CMDiff[s] n (f i))
  proof: fun x hx => contMDiffWithinAt_finsetProd fun i hi => h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum := contMDiffOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod := contMDiffOn_finsetProd

@[to_additive]

中文:
定理 contMDiffOn_finsetProd
  条件: (h : 对任意 i in t, CMDiff[s] n (f i))
  证明: fun x hx => contMDiffWithinAt_finsetProd fun i hi => h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum := contMDiffOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod := contMDiffOn_finsetProd

@[to_additive]

Depends on / 依赖: contMDiffWithinAt_finsetProd
-/
theorem contMDiffOn_finsetProd (h : forall i in t, CMDiff[s] n (f i)) :
    CMDiff[s] n (fun x => ∏ i in t, f i x) :=
  fun x hx => contMDiffWithinAt_finsetProd fun i hi => h i hi x hx

@[deprecated (since := "2026-04-08")] alias contMDiffOn_finset_sum := contMDiffOn_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiffOn_finset_prod := contMDiffOn_finsetProd

@[to_additive]
/--
theorem `ContMDiff.prod` / 定理 `ContMDiff.prod`

English:
theorem ContMDiff.prod
  given: (h : forall i in t, CMDiff n (f i))
  proof: fun x => ContMDiffAt.prod fun j hj => h j hj x

@[to_additive]

中文:
定理 ContMDiff.prod
  条件: (h : 对任意 i in t, CMDiff n (f i))
  证明: fun x => ContMDiffAt.prod fun j hj => h j hj x

@[to_additive]

Depends on / 依赖: ContMDiffAt, ContMDiffAt.prod
-/
theorem ContMDiff.prod (h : forall i in t, CMDiff n (f i)) :
    CMDiff n fun x => ∏ i in t, f i x :=
  fun x => ContMDiffAt.prod fun j hj => h j hj x

@[to_additive]
/--
theorem `contMDiff_finsetProd'` / 定理 `contMDiff_finsetProd'`

English:
theorem contMDiff_finsetProd'
  given: (h : forall i in t, CMDiff n (f i))
  proof: fun x => contMDiffAt_finsetProd' fun i hi => h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum' := contMDiff_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod' := contMDiff_finsetProd'

@[to_additive]

中文:
定理 contMDiff_finsetProd'
  条件: (h : 对任意 i in t, CMDiff n (f i))
  证明: fun x => contMDiffAt_finsetProd' fun i hi => h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum' := contMDiff_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod' := contMDiff_finsetProd'

@[to_additive]

Depends on / 依赖: contMDiffAt_finsetProd
-/
theorem contMDiff_finsetProd' (h : forall i in t, CMDiff n (f i)) :
    CMDiff n (∏ i in t, f i) := fun x => contMDiffAt_finsetProd' fun i hi => h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum' := contMDiff_finsetSum'

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod' := contMDiff_finsetProd'

@[to_additive]
/--
theorem `contMDiff_finsetProd` / 定理 `contMDiff_finsetProd`

English:
theorem contMDiff_finsetProd
  given: (h : forall i in t, CMDiff n (f i))
  proof: fun x => contMDiffAt_finsetProd fun i hi => h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum := contMDiff_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod := contMDiff_finsetProd

@[to_additive]

中文:
定理 contMDiff_finsetProd
  条件: (h : 对任意 i in t, CMDiff n (f i))
  证明: fun x => contMDiffAt_finsetProd fun i hi => h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum := contMDiff_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod := contMDiff_finsetProd

@[to_additive]

Depends on / 依赖: contMDiffAt_finsetProd
-/
theorem contMDiff_finsetProd (h : forall i in t, CMDiff n (f i)) :
    CMDiff n fun x => ∏ i in t, f i x :=
  fun x => contMDiffAt_finsetProd fun i hi => h i hi x

@[deprecated (since := "2026-04-08")] alias contMDiff_finset_sum := contMDiff_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias contMDiff_finset_prod := contMDiff_finsetProd

@[to_additive]
/--
theorem `contMDiff_finprod` / 定理 `contMDiff_finprod`

English:
theorem contMDiff_finprod
  statement: (h : forall i, CMDiff n (f i))
  proof: fun x => contMDiffAt_finprod hfin fun i => h i x

@[to_additive]

中文:
定理 contMDiff_finprod
  结论: (h : 对任意 i, CMDiff n (f i))
  证明: fun x => contMDiffAt_finprod hfin fun i => h i x

@[to_additive]

Depends on / 依赖: contMDiffAt_finprod
-/
theorem contMDiff_finprod (h : forall i, CMDiff n (f i))
    (hfin : LocallyFinite fun i => mulSupport (f i)) : CMDiff n fun x => ∏ᶠ i, f i x :=
  fun x => contMDiffAt_finprod hfin fun i => h i x

@[to_additive]
/--
theorem `contMDiff_finprod_cond` / 定理 `contMDiff_finprod_cond`

English:
theorem contMDiff_finprod_cond
  statement: (hc : forall i, p i -> CMDiff n (f i))
  proof: by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

中文:
定理 contMDiff_finprod_cond
  结论: (hc : 对任意 i, p i -> CMDiff n (f i))
  证明: by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective, comp_injective, contMDiff_finprod, finprod_subtype_eq_finprod_cond, hf.comp_injective
-/
theorem contMDiff_finprod_cond (hc : forall i, p i -> CMDiff n (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    CMDiff n fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact contMDiff_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

variable {g : M -> G}

@[to_additive]
/--
theorem `ContMDiffWithinAt.pow` / 定理 `ContMDiffWithinAt.pow`

English:
theorem ContMDiffWithinAt.pow
  given: (hg : CMDiffAt[s] n g x) (m : Nat)
  proof: (contMDiff_pow m).contMDiffAt.comp_contMDiffWithinAt x hg

@[to_additive]
nonrec theorem ContMDiffAt.pow (hg : CMDiffAt n g x) (m : Nat) :
    CMDiffAt n (fun x => g x ^ m) x :=
  hg.pow m

@[to_additive]

中文:
定理 ContMDiffWithinAt.pow
  条件: (hg : CMDiffAt[s] n g x) (m : 自然数)
  证明: (contMDiff_pow m).contMDiffAt.comp_contMDiffWithinAt x hg

@[to_additive]
nonrec theorem ContMDiffAt.pow (hg : CMDiffAt n g x) (m : Nat) :
    CMDiffAt n (fun x => g x ^ m) x :=
  hg.pow m

@[to_additive]

Depends on / 依赖: comp_contMDiffWithinAt, contMDiffAt, contMDiffAt.comp_contMDiffWithinAt, contMDiff_pow
-/
theorem ContMDiffWithinAt.pow (hg : CMDiffAt[s] n g x) (m : Nat) :
    CMDiffAt[s] n (fun x => g x ^ m) x :=
  (contMDiff_pow m).contMDiffAt.comp_contMDiffWithinAt x hg

@[to_additive]
nonrec theorem ContMDiffAt.pow (hg : CMDiffAt n g x) (m : Nat) :
    CMDiffAt n (fun x => g x ^ m) x :=
  hg.pow m

@[to_additive]
/--
theorem `ContMDiffOn.pow` / 定理 `ContMDiffOn.pow`

English:
theorem ContMDiffOn.pow
  given: (hg : CMDiff[s] n g) (m : Nat)
  proof: fun x hx => (hg x hx).pow m

@[to_additive]

中文:
定理 ContMDiffOn.pow
  条件: (hg : CMDiff[s] n g) (m : 自然数)
  证明: fun x hx => (hg x hx).pow m

@[to_additive]
-/
theorem ContMDiffOn.pow (hg : CMDiff[s] n g) (m : Nat) :
    CMDiff[s] n (fun x => g x ^ m) :=
  fun x hx => (hg x hx).pow m

@[to_additive]
/--
theorem `ContMDiff.pow` / 定理 `ContMDiff.pow`

English:
theorem ContMDiff.pow
  given: (hg : CMDiff n g) (m : Nat)
  proof: fun x => (hg x).pow m

中文:
定理 ContMDiff.pow
  条件: (hg : CMDiff n g) (m : 自然数)
  证明: fun x => (hg x).pow m
-/
theorem ContMDiff.pow (hg : CMDiff n g) (m : Nat) :
    CMDiff n (fun x => g x ^ m) :=
  fun x => (hg x).pow m

end CommMonoid

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n : Nat∞ω}

/--
Instance `instContMDiffAddSelf` / 实例 `instContMDiffAddSelf`

English:
instance instContMDiffAddSelf
  signature: : ContMDiffAdd 𝓘(𝕜, E) n E
  body: by
  constructor
  rw [← modelWithCornersSelf_prod]; rw [chartedSpaceSelf_prod]
  exact contDiff_add.contMDiff

中文:
实例 instContMDiffAddSelf
  签名: : ContMDiffAdd 𝓘(𝕜, E) n E
  定义体: by
  constructor
  rw [← modelWithCornersSelf_prod]; rw [chartedSpaceSelf_prod]
  exact contDiff_add.contMDiff

Depends on / 依赖: chartedSpaceSelf_prod, contDiff_add, contDiff_add.contMDiff, contMDiff, modelWithCornersSelf_prod
-/
instance instContMDiffAddSelf : ContMDiffAdd 𝓘(𝕜, E) n E := by
  constructor
  rw [← modelWithCornersSelf_prod]; rw [chartedSpaceSelf_prod]
  exact contDiff_add.contMDiff

end

section DivConst

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [DivInvMonoid G] [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

variable {f : M -> G} {s : Set M} {x : M} (c : G)

@[to_additive]
/--
theorem `ContMDiffWithinAt.div_const` / 定理 `ContMDiffWithinAt.div_const`

English:
theorem ContMDiffWithinAt.div_const
  given: (hf : CMDiffAt[s] n f x)
  proof: by
  simpa only [div_eq_mul_inv] using! hf.mul contMDiffWithinAt_const

@[to_additive]
nonrec theorem ContMDiffAt.div_const (hf : CMDiffAt n f x) :
    CMDiffAt n (fun x => f x / c) x :=
  hf.div_const c

@[to_additive]

中文:
定理 ContMDiffWithinAt.div_const
  条件: (hf : CMDiffAt[s] n f x)
  证明: by
  simpa only [div_eq_mul_inv] using! hf.mul contMDiffWithinAt_const

@[to_additive]
nonrec theorem ContMDiffAt.div_const (hf : CMDiffAt n f x) :
    CMDiffAt n (fun x => f x / c) x :=
  hf.div_const c

@[to_additive]

Depends on / 依赖: contMDiffWithinAt_const, div_eq_mul_inv, hf.mul
-/
theorem ContMDiffWithinAt.div_const (hf : CMDiffAt[s] n f x) :
    CMDiffAt[s] n (fun x => f x / c) x := by
  simpa only [div_eq_mul_inv] using! hf.mul contMDiffWithinAt_const

@[to_additive]
nonrec theorem ContMDiffAt.div_const (hf : CMDiffAt n f x) :
    CMDiffAt n (fun x => f x / c) x :=
  hf.div_const c

@[to_additive]
/--
theorem `ContMDiffOn.div_const` / 定理 `ContMDiffOn.div_const`

English:
theorem ContMDiffOn.div_const
  given: (hf : CMDiff[s] n f)
  proof: fun x hx => (hf x hx).div_const c

@[to_additive]

中文:
定理 ContMDiffOn.div_const
  条件: (hf : CMDiff[s] n f)
  证明: fun x hx => (hf x hx).div_const c

@[to_additive]

Depends on / 依赖: div_const
-/
theorem ContMDiffOn.div_const (hf : CMDiff[s] n f) :
    CMDiff[s] n (fun x => f x / c) := fun x hx => (hf x hx).div_const c

@[to_additive]
/--
theorem `ContMDiff.div_const` / 定理 `ContMDiff.div_const`

English:
theorem ContMDiff.div_const
  given: (hf : CMDiff n f)
  proof: fun x => (hf x).div_const c

中文:
定理 ContMDiff.div_const
  条件: (hf : CMDiff n f)
  证明: fun x => (hf x).div_const c

Depends on / 依赖: div_const
-/
theorem ContMDiff.div_const (hf : CMDiff n f) :
    CMDiff n (fun x => f x / c) := fun x => (hf x).div_const c

end DivConst
