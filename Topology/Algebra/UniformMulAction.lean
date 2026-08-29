/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Multiplicative action on the completion of a uniform space

In this file we define typeclasses `UniformContinuousConstVAdd` and
`UniformContinuousConstSMul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `UniformSpace.Completion X`.

In later files once the additive group structure is set up, we provide
* `UniformSpace.Completion.DistribMulAction`
* `UniformSpace.Completion.MulActionWithZero`
* `UniformSpace.Completion.Module`

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/

@[expose] public section


universe u v w x y

open scoped Uniformity

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X]
  [UniformSpace Y]

/--
Definition of `UniformContinuousConstVAdd` / `UniformContinuousConstVAdd` 的定义

English:
class UniformContinuousConstVAdd
  parameters: [VAdd M X]
  axioms and operations (1):
    - uniformContinuous_const_vadd : forall c : M, UniformContinuous (c +ᵥ · : X -> X)

中文:
类 一致连续常数向量加法
  参数: [向量加法 M X]
  公理与运算 (1 个):
    - uniformContinuous_const_vadd : 对任意 c : M, 一致连续 (c +ᵥ · : X -> X)
-/
class UniformContinuousConstVAdd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : forall c : M, UniformContinuous (c +ᵥ · : X -> X)

/-- A multiplicative action such that for all `c`,
the map `fun x ↦ c • x` is uniformly continuous. -/
@[to_additive]
/--
Definition of `UniformContinuousConstSMul` / `UniformContinuousConstSMul` 的定义

English:
class UniformContinuousConstSMul
  parameters: [SMul M X]
  axioms and operations (1):
    - uniformContinuous_const_smul : forall c : M, UniformContinuous (c • · : X -> X)

中文:
类 一致连续常数标量乘法
  参数: [标量乘法 M X]
  公理与运算 (1 个):
    - uniformContinuous_const_smul : 对任意 c : M, 一致连续 (c • · : X -> X)
-/
class UniformContinuousConstSMul [SMul M X] : Prop where
  uniformContinuous_const_smul : forall c : M, UniformContinuous (c • · : X -> X)

export UniformContinuousConstVAdd (uniformContinuous_const_vadd)

export UniformContinuousConstSMul (uniformContinuous_const_smul)

/--
Instance `AddMonoid.uniformContinuousConstSMul_nat` / 实例 `AddMonoid.uniformContinuousConstSMul_nat`

English:
instance AddMonoid.uniformContinuousConstSMul_nat
  signature: [AddGroup X] [IsUniformAddGroup X]
  body: ⟨uniformContinuous_const_nsmul⟩

中文:
实例 加法幺半群.uniformContinuousConstSMul_nat
  签名: [加法群 X] [是UniformAdd群 X]
  定义体: ⟨uniformContinuous_const_nsmul⟩

Depends on / 依赖: uniformContinuous_const_nsmul
-/
instance AddMonoid.uniformContinuousConstSMul_nat [AddGroup X] [IsUniformAddGroup X] :
    UniformContinuousConstSMul Nat X :=
  ⟨uniformContinuous_const_nsmul⟩

/--
Instance `AddGroup.uniformContinuousConstSMul_int` / 实例 `AddGroup.uniformContinuousConstSMul_int`

English:
instance AddGroup.uniformContinuousConstSMul_int
  signature: [AddGroup X] [IsUniformAddGroup X]
  body: ⟨uniformContinuous_const_zsmul⟩

中文:
实例 加法群.uniformContinuousConstSMul_int
  签名: [加法群 X] [是UniformAdd群 X]
  定义体: ⟨uniformContinuous_const_zsmul⟩

Depends on / 依赖: uniformContinuous_const_zsmul
-/
instance AddGroup.uniformContinuousConstSMul_int [AddGroup X] [IsUniformAddGroup X] :
    UniformContinuousConstSMul Int X :=
  ⟨uniformContinuous_const_zsmul⟩

/--
theorem `uniformContinuousConstSMul_of_continuousConstSMul` / 定理 `uniformContinuousConstSMul_of_continuousConstSMul`

English:
theorem uniformContinuousConstSMul_of_continuousConstSMul
  statement: [AddGroup M]
  proof: ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩

中文:
定理 uniformContinuousConstSMul_of_continuousConstSMul
  结论: [加法群 M]
  证明: ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩

Depends on / 依赖: Continuous, Continuous.continuousAt, DistribSMul, DistribSMul.toAddMonoidHom, continuousAt, continuous_const_smul, toAddMonoidHom, uniformContinuous_of_continuousAt_zero
-/
theorem uniformContinuousConstSMul_of_continuousConstSMul [AddGroup M]
    [DistribSMul R M] [UniformSpace M] [IsUniformAddGroup M] [ContinuousConstSMul R M] :
    UniformContinuousConstSMul R M :=
  ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩

/--
Instance `Ring.uniformContinuousConstSMul` / 实例 `Ring.uniformContinuousConstSMul`

English:
instance Ring.uniformContinuousConstSMul
  signature: [Ring R] [UniformSpace R] [IsUniformAddGroup R]
  body: uniformContinuousConstSMul_of_continuousConstSMul _ _

中文:
实例 环.uniformContinuousConstSMul
  签名: [环 R] [一致空间 R] [是UniformAdd群 R]
  定义体: uniformContinuousConstSMul_of_continuousConstSMul _ _

Depends on / 依赖: uniformContinuousConstSMul_of_continuousConstSMul
-/
instance Ring.uniformContinuousConstSMul [Ring R] [UniformSpace R] [IsUniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul R R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

/--
Instance `Ring.uniformContinuousConstSMul_op` / 实例 `Ring.uniformContinuousConstSMul_op`

English:
instance Ring.uniformContinuousConstSMul_op
  signature: [Ring R] [UniformSpace R] [IsUniformAddGroup R]
  body: uniformContinuousConstSMul_of_continuousConstSMul _ _

中文:
实例 环.uniformContinuousConstSMul_op
  签名: [环 R] [一致空间 R] [是UniformAdd群 R]
  定义体: uniformContinuousConstSMul_of_continuousConstSMul _ _

Depends on / 依赖: uniformContinuousConstSMul_of_continuousConstSMul
-/
instance Ring.uniformContinuousConstSMul_op [Ring R] [UniformSpace R] [IsUniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul Rᵐᵒᵖ R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

section SMul

variable [SMul M X]

@[to_additive]
instance (priority := 100) UniformContinuousConstSMul.instContinuousConstSMul
    [UniformContinuousConstSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (uniformContinuous_const_smul c).continuous⟩

variable {M X Y}

@[to_additive (attr := fun_prop)]
/--
theorem `UniformContinuous.const_smul` / 定理 `UniformContinuous.const_smul`

English:
theorem UniformContinuous.const_smul
  statement: [UniformContinuousConstSMul M X] {f : Y -> X}
  proof: (uniformContinuous_const_smul c).comp hf

@[to_additive]

中文:
定理 一致连续.const_smul
  结论: [一致连续常数标量乘法 M X] {f : Y -> X}
  证明: (uniformContinuous_const_smul c).comp hf

@[to_additive]

Depends on / 依赖: uniformContinuous_const_smul
-/
theorem UniformContinuous.const_smul [UniformContinuousConstSMul M X] {f : Y -> X}
    (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f) :=
  (uniformContinuous_const_smul c).comp hf

@[to_additive]
/--
lemma `IsUniformInducing.uniformContinuousConstSMul` / 引理 `IsUniformInducing.uniformContinuousConstSMul`

English:
lemma IsUniformInducing.uniformContinuousConstSMul
  statement: [SMul M Y] [UniformContinuousConstSMul M Y]
  proof: by
    simpa only [hf.uniformContinuous_iff, Function.comp_def, hsmul]
      using! hf.uniformContinuous.const_smul c

中文:
引理 是UniformInducing.uniformContinuousConstSMul
  结论: [标量乘法 M Y] [一致连续常数标量乘法 M Y]
  证明: by
    simpa only [hf.uniformContinuous_iff, Function.comp_def, hsmul]
      using! hf.uniformContinuous.const_smul c

Depends on / 依赖: Function, Function.comp_def, comp_def, const_smul, hf.uniformContinuous.const_smul, hf.uniformContinuous_iff, uniformContinuous, uniformContinuous_iff
-/
lemma IsUniformInducing.uniformContinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y]
    {f : X -> Y} (hf : IsUniformInducing f) (hsmul : forall (c : M) x, f (c • x) = c • f x) :
    UniformContinuousConstSMul M X where
  uniformContinuous_const_smul c := by
    simpa only [hf.uniformContinuous_iff, Function.comp_def, hsmul]
      using! hf.uniformContinuous.const_smul c

/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[to_additive /-- If an additive action is central, then its right action is uniform
continuous when its left action is. -/]
instance (priority := 100) UniformContinuousConstSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
    [UniformContinuousConstSMul M X] : UniformContinuousConstSMul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using uniformContinuous_const_smul c⟩

@[to_additive]
/--
Instance `MulOpposite.uniformContinuousConstSMul` / 实例 `MulOpposite.uniformContinuousConstSMul`

English:
instance MulOpposite.uniformContinuousConstSMul
  signature: [UniformContinuousConstSMul M X]
  body: ⟨fun c =>
MulOpposite.uniformContinuous_op.comp MulOpposite.uniformContinuous_unop.const_smul c⟩

中文:
实例 MulOpposite.uniformContinuousConstSMul
  签名: [一致连续常数标量乘法 M X]
  定义体: ⟨fun c =>
MulOpposite.uniformContinuous_op.comp MulOpposite.uniformContinuous_unop.const_smul c⟩

Depends on / 依赖: MulOpposite, MulOpposite.uniformContinuous_op.comp, MulOpposite.uniformContinuous_unop.const_smul, const_smul, uniformContinuous_op, uniformContinuous_unop
-/
instance MulOpposite.uniformContinuousConstSMul [UniformContinuousConstSMul M X] :
    UniformContinuousConstSMul M Xᵐᵒᵖ :=
  ⟨fun c =>
MulOpposite.uniformContinuous_op.comp MulOpposite.uniformContinuous_unop.const_smul c⟩

end SMul

@[to_additive]
/--
Instance `IsUniformGroup.instUniformContinuousConstSMul` / 实例 `IsUniformGroup.instUniformContinuousConstSMul`

English:
instance IsUniformGroup.instUniformContinuousConstSMul
  signature: {G : Type u} [Group G] [UniformSpace G]
  body: ⟨fun _ => uniformContinuous_const.mul uniformContinuous_id⟩

中文:
实例 是一致群.instUniformContinuousConstSMul
  签名: {G : 类型u} [群 G] [一致空间 G]
  定义体: ⟨fun _ => uniformContinuous_const.mul uniformContinuous_id⟩

Depends on / 依赖: uniformContinuous_const, uniformContinuous_const.mul, uniformContinuous_id
-/
instance IsUniformGroup.instUniformContinuousConstSMul {G : Type u} [Group G] [UniformSpace G]
    [IsUniformGroup G] : UniformContinuousConstSMul G G :=
  ⟨fun _ => uniformContinuous_const.mul uniformContinuous_id⟩

section Ring

variable {R β : Type*} [Ring R] [UniformSpace R] [UniformSpace β]

@[fun_prop]
/--
theorem `UniformContinuous.const_mul'` / 定理 `UniformContinuous.const_mul'`

English:
theorem UniformContinuous.const_mul'
  statement: [UniformContinuousConstSMul R R] {f : β -> R}
  proof: hf.const_smul a

@[fun_prop]

中文:
定理 一致连续.const_mul'
  结论: [一致连续常数标量乘法 R R] {f : β -> R}
  证明: hf.const_smul a

@[fun_prop]

Depends on / 依赖: const_smul, hf.const_smul
-/
theorem UniformContinuous.const_mul' [UniformContinuousConstSMul R R] {f : β -> R}
    (hf : UniformContinuous f) (a : R) : UniformContinuous fun x => a * f x :=
  hf.const_smul a

@[fun_prop]
/--
theorem `UniformContinuous.mul_const'` / 定理 `UniformContinuous.mul_const'`

English:
theorem UniformContinuous.mul_const'
  statement: [UniformContinuousConstSMul Rᵐᵒᵖ R] {f : β -> R}
  proof: hf.const_smul (MulOpposite.op a)

中文:
定理 一致连续.mul_const'
  结论: [一致连续常数标量乘法 Rᵐᵒᵖ R] {f : β -> R}
  证明: hf.const_smul (MulOpposite.op a)

Depends on / 依赖: MulOpposite, MulOpposite.op, const_smul, hf.const_smul
-/
theorem UniformContinuous.mul_const' [UniformContinuousConstSMul Rᵐᵒᵖ R] {f : β -> R}
    (hf : UniformContinuous f) (a : R) : UniformContinuous fun x => f x * a :=
  hf.const_smul (MulOpposite.op a)

/--
theorem `uniformContinuous_mul_left'` / 定理 `uniformContinuous_mul_left'`

English:
theorem uniformContinuous_mul_left'
  given: [UniformContinuousConstSMul R R] (a : R)
  proof: uniformContinuous_id.const_mul' _

中文:
定理 uniformContinuous_mul_left'
  条件: [一致连续常数标量乘法 R R] (a : R)
  证明: uniformContinuous_id.const_mul' _

Depends on / 依赖: const_mul, uniformContinuous_id, uniformContinuous_id.const_mul
-/
theorem uniformContinuous_mul_left' [UniformContinuousConstSMul R R] (a : R) :
    UniformContinuous fun b : R => a * b :=
  uniformContinuous_id.const_mul' _

/--
theorem `uniformContinuous_mul_right'` / 定理 `uniformContinuous_mul_right'`

English:
theorem uniformContinuous_mul_right'
  given: [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R)
  proof: uniformContinuous_id.mul_const' _

@[fun_prop]

中文:
定理 uniformContinuous_mul_right'
  条件: [一致连续常数标量乘法 Rᵐᵒᵖ R] (a : R)
  证明: uniformContinuous_id.mul_const' _

@[fun_prop]

Depends on / 依赖: mul_const, uniformContinuous_id, uniformContinuous_id.mul_const
-/
theorem uniformContinuous_mul_right' [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) :
    UniformContinuous fun b : R => b * a :=
  uniformContinuous_id.mul_const' _

@[fun_prop]
/--
theorem `UniformContinuous.div_const'` / 定理 `UniformContinuous.div_const'`

English:
theorem UniformContinuous.div_const'
  statement: {R β : Type*} [DivisionRing R] [UniformSpace R]
  proof: by
  simpa [div_eq_mul_inv] using hf.mul_const' a⁻¹

中文:
定理 一致连续.div_const'
  结论: {R β : 类型} [除环 R] [一致空间 R]
  证明: by
  simpa [div_eq_mul_inv] using hf.mul_const' a⁻¹

Depends on / 依赖: div_eq_mul_inv, hf.mul_const, mul_const
-/
theorem UniformContinuous.div_const' {R β : Type*} [DivisionRing R] [UniformSpace R]
    [UniformContinuousConstSMul Rᵐᵒᵖ R] [UniformSpace β] {f : β -> R}
    (hf : UniformContinuous f) (a : R) :
    UniformContinuous fun x => f x / a := by
  simpa [div_eq_mul_inv] using hf.mul_const' a⁻¹

/--
theorem `uniformContinuous_div_const'` / 定理 `uniformContinuous_div_const'`

English:
theorem uniformContinuous_div_const'
  statement: {R : Type*} [DivisionRing R] [UniformSpace R]
  proof: uniformContinuous_id.div_const' _

中文:
定理 uniformContinuous_div_const'
  结论: {R : 类型} [除环 R] [一致空间 R]
  证明: uniformContinuous_id.div_const' _

Depends on / 依赖: div_const, uniformContinuous_id, uniformContinuous_id.div_const
-/
theorem uniformContinuous_div_const' {R : Type*} [DivisionRing R] [UniformSpace R]
    [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) :
    UniformContinuous fun b : R => b / a :=
  uniformContinuous_id.div_const' _

end Ring

section Unit

open scoped Pointwise

variable {M X}

@[to_additive]
/--
theorem `IsUnit.smul_uniformity` / 定理 `IsUnit.smul_uniformity`

English:
theorem IsUnit.smul_uniformity
  statement: [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] {c : M}
  proof: let ⟨d, hcd⟩ := hc.exists_right_inv
  have cU : c • 𝓤 X <= 𝓤 X := uniformContinuous_const_smul c
  have dU : d • 𝓤 X <= 𝓤 X := uniformContinuous_const_smul d
le_antisymm cU by simpa [smul_smul, hcd] using Filter.smul_filter_le_smul_filter (a := c) dU

@[to_additive (attr := simp)]

中文:
定理 是单位.smul_uniformity
  结论: [幺半群 M] [乘法作用 M X] [一致连续常数标量乘法 M X] {c : M}
  证明: let ⟨d, hcd⟩ := hc.exists_right_inv
  have cU : c • 𝓤 X <= 𝓤 X := uniformContinuous_const_smul c
  have dU : d • 𝓤 X <= 𝓤 X := uniformContinuous_const_smul d
le_antisymm cU by simpa [smul_smul, hcd] using Filter.smul_filter_le_smul_filter (a := c) dU

@[to_additive (attr := simp)]

Depends on / 依赖: Filter, Filter.smul_filter_le_smul_filter, exists_right_inv, hc.exists_right_inv, le_antisymm, smul_filter_le_smul_filter, smul_smul, uniformContinuous_const_smul
-/
theorem IsUnit.smul_uniformity [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] {c : M}
    (hc : IsUnit c) : c • 𝓤 X = 𝓤 X :=
  let ⟨d, hcd⟩ := hc.exists_right_inv
  have cU : c • 𝓤 X <= 𝓤 X := uniformContinuous_const_smul c
  have dU : d • 𝓤 X <= 𝓤 X := uniformContinuous_const_smul d
le_antisymm cU by simpa [smul_smul, hcd] using Filter.smul_filter_le_smul_filter (a := c) dU

@[to_additive (attr := simp)]
/--
theorem `smul_uniformity` / 定理 `smul_uniformity`

English:
theorem smul_uniformity
  given: [Group M] [MulAction M X] [UniformContinuousConstSMul M X] (c : M)
  proof: .smul_uniformity Group.isUnit _

中文:
定理 smul_uniformity
  条件: [群 M] [乘法作用 M X] [一致连续常数标量乘法 M X] (c : M)
  证明: .smul_uniformity Group.isUnit _

Depends on / 依赖: Group.isUnit, isUnit, smul_uniformity
-/
theorem smul_uniformity [Group M] [MulAction M X] [UniformContinuousConstSMul M X] (c : M) :
    c • 𝓤 X = 𝓤 X :=
.smul_uniformity Group.isUnit _

/--
theorem `smul_uniformity₀` / 定理 `smul_uniformity₀`

English:
theorem smul_uniformity₀
  statement: [GroupWithZero M] [MulAction M X] [UniformContinuousConstSMul M X] {c : M}
  proof: hc.isUnit.smul_uniformity

中文:
定理 smul_uniformity₀
  结论: [带零群 M] [乘法作用 M X] [一致连续常数标量乘法 M X] {c : M}
  证明: hc.isUnit.smul_uniformity

Depends on / 依赖: hc.isUnit.smul_uniformity, isUnit, smul_uniformity
-/
theorem smul_uniformity₀ [GroupWithZero M] [MulAction M X] [UniformContinuousConstSMul M X] {c : M}
    (hc : c != 0) : c • 𝓤 X = 𝓤 X :=
  hc.isUnit.smul_uniformity

end Unit

namespace UniformSpace

namespace Completion

section SMul

variable [SMul M X]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul M (Completion X)
  body: ⟨fun c => Completion.map (c • ·)⟩

@[to_additive]

中文:
实例 :
  签名: 标量乘法 M (完备化 X)
  定义体: ⟨fun c => Completion.map (c • ·)⟩

@[to_additive]

Depends on / 依赖: Completion, Completion.map
-/
noncomputable instance : SMul M (Completion X) :=
  ⟨fun c => Completion.map (c • ·)⟩

@[to_additive]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (c : M) (x : Completion X)
  statement: c • x = Completion.map (c • ·) x
  proof: rfl

@[to_additive]

中文:
定理 smul_def
  条件: (c : M) (x : 完备化 X)
  结论: c • x = 完备化.map (c • ·) x
  证明: rfl

@[to_additive]
-/
theorem smul_def (c : M) (x : Completion X) : c • x = Completion.map (c • ·) x :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformContinuousConstSMul M (Completion X)
  body: ⟨fun _ => uniformContinuous_map⟩

@[to_additive]

中文:
实例 :
  签名: 一致连续常数标量乘法 M (完备化 X)
  定义体: ⟨fun _ => uniformContinuous_map⟩

@[to_additive]

Depends on / 依赖: uniformContinuous_map
-/
instance : UniformContinuousConstSMul M (Completion X) :=
  ⟨fun _ => uniformContinuous_map⟩

@[to_additive]
/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul N X] [SMul M N] [UniformContinuousConstSMul M X]
  body: ⟨fun m n x => by
    have : _ = (_ : Completion X -> Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine Eq.trans ?_ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]

中文:
实例 instIsScalarTower
  签名: [标量乘法 N X] [标量乘法 M N] [一致连续常数标量乘法 M X]
  定义体: ⟨fun m n x => by
    have : _ = (_ : Completion X -> Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine Eq.trans ?_ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]

Depends on / 依赖: Completion, Completion.map, Eq.trans, congr_arg, congr_fun, map_comp, smul_assoc, this.symm, uniformContinuous_const_smul
-/
instance instIsScalarTower [SMul N X] [SMul M N] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x => by
    have : _ = (_ : Completion X -> Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine Eq.trans ?_ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: N X] [SMulCommClass M N X] [UniformContinuousConstSMul M X]
  body: ⟨fun m n x => by
    have hmn : m • n • x = (Completion.map (SMul.smul m) ∘ Completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (Completion.map (SMul.smul n) ∘ Completion.map (SMul.smul m)) x := rfl
    rw [hmn]; rw [hnm]; rw [map_comp]; rw [map_comp]
    · exact congr_arg (fun f => Co

中文:
实例 [标量乘法
  签名: N X] [标量交换类 M N X] [一致连续常数标量乘法 M X]
  定义体: ⟨fun m n x => by
    have hmn : m • n • x = (Completion.map (SMul.smul m) ∘ Completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (Completion.map (SMul.smul n) ∘ Completion.map (SMul.smul m)) x := rfl
    rw [hmn]; rw [hnm]; rw [map_comp]; rw [map_comp]
    · exact congr_arg (fun f => Co

Depends on / 依赖: Completion, Completion.map, SMul.smul, congr_arg, map_comp, repeat, smul_comm, uniformContinuous_const_smul
-/
instance [SMul N X] [SMulCommClass M N X] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] : SMulCommClass M N (Completion X) :=
  ⟨fun m n x => by
    have hmn : m • n • x = (Completion.map (SMul.smul m) ∘ Completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (Completion.map (SMul.smul n) ∘ Completion.map (SMul.smul m)) x := rfl
    rw [hmn]; rw [hnm]; rw [map_comp]; rw [map_comp]
    · exact congr_arg (fun f => Completion.map f x) (funext (smul_comm _ _))
    repeat' exact uniformContinuous_const_smul _⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X)
  body: ⟨fun c a => (congr_arg fun f => Completion.map f a) funext (op_smul_eq_smul c)⟩

中文:
实例 [标量乘法
  签名: Mᵐᵒᵖ X] [中心标量 M X] : 中心标量 M (完备化 X)
  定义体: ⟨fun c a => (congr_arg fun f => Completion.map f a) funext (op_smul_eq_smul c)⟩

Depends on / 依赖: Completion, Completion.map, congr_arg, op_smul_eq_smul
-/
instance [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
⟨fun c a => (congr_arg fun f => Completion.map f a) funext (op_smul_eq_smul c)⟩

variable {M X}
variable [UniformContinuousConstSMul M X]

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (c : M) (x : X)
  statement: (↑(c • x) : Completion X) = c • (x : Completion X)
  proof: (map_coe (uniformContinuous_const_smul c) x).symm

中文:
定理 coe_smul
  条件: (c : M) (x : X)
  结论: (↑(c • x) : 完备化 X) = c • (x : 完备化 X)
  证明: (map_coe (uniformContinuous_const_smul c) x).symm

Depends on / 依赖: map_coe, uniformContinuous_const_smul
-/
theorem coe_smul (c : M) (x : X) : (↑(c • x) : Completion X) = c • (x : Completion X) :=
  (map_coe (uniformContinuous_const_smul c) x).symm

end SMul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [MulAction M X] [UniformContinuousConstSMul M X] :
  body: ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).fun_const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

中文:
实例 [幺半群
  签名: M] [乘法作用 M X] [一致连续常数标量乘法 M X] :
  定义体: ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).fun_const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

Depends on / 依赖: coe_smul, continuous_const_smul, continuous_id, one_smul
-/
noncomputable instance [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] :
    MulAction M (Completion X) where
  one_smul := ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).fun_const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

end Completion

end UniformSpace
