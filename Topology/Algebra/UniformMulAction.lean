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

/-- An additive action such that for all `c`, the map `fun x ↦ c +ᵥ x` is uniformly continuous. -/
/-
**UniformContinuousConstVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type v) → (X : Type x) → [UniformSpace X] → [VAdd M X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive action such that for all `c`, the map `fun x ↦ c +ᵥ x` is uniformly 
continuous.
-/
class UniformContinuousConstVAdd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : ∀ c : M, UniformContinuous (c +ᵥ · : X → X)

/-- A multiplicative action such that for all `c`,
the map `fun x ↦ c • x` is uniformly continuous. -/
@[to_additive]
/-
**UniformContinuousConstSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type v) → (X : Type x) → [UniformSpace X] → [SMul M X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative action such that for all `c`,
the map `fun x ↦ c • x` is uniformly continuous.
-/
class UniformContinuousConstSMul [SMul M X] : Prop where
  uniformContinuous_const_smul : ∀ c : M, UniformContinuous (c • · : X → X)

export UniformContinuousConstVAdd (uniformContinuous_const_vadd)

export UniformContinuousConstSMul (uniformContinuous_const_smul)
/-
**AddMonoid.uniformContinuousConstSMul_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.uniformContinuousConstSMul_nat [AddGroup X] [IsUniformAddGroup X
] : UniformContinuousConstSMul Nat X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_const_nsmul`：∀ {α : Type u_1} [inst : UniformSpace α] 
[inst_1 : AddGroup α] [IsUniformAddGroup α] (n : ℕ),   UniformContinuous fun x =
> n • x
-/
instance AddMonoid.uniformContinuousConstSMul_nat [AddGroup X] [IsUniformAddGroup X] :
    UniformContinuousConstSMul ℕ X :=
  ⟨uniformContinuous_const_nsmul⟩
/-
**AddGroup.uniformContinuousConstSMul_int** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGroup.uniformContinuousConstSMul_int [AddGroup X] [IsUniformAddGroup X]
 : UniformContinuousConstSMul Int X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_const_zsmul`：∀ {α : Type u_1} [inst : UniformSpace α] 
[inst_1 : AddGroup α] [IsUniformAddGroup α] (n : ℤ),   UniformContinuous fun x =
> n • x
-/
instance AddGroup.uniformContinuousConstSMul_int [AddGroup X] [IsUniformAddGroup X] :
    UniformContinuousConstSMul ℤ X :=
  ⟨uniformContinuous_const_zsmul⟩

/-- A `DistribSMul` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`UniformContinuousConstSMul.instContinuousConstSMul` -/
/-
**uniformContinuousConstSMul_of_continuousConstSMul** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：uniformContinuousConstSMul_of_continuousConstSMul [AddGroup M] [DistribSMu
l R M] [UniformSpace M] [IsUniformAddGroup M] [ContinuousConstSMul R M] : Unifor
mContinuousConstSMul R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_of_continuousAt_zero`：∀ {α : Type u_1} {β : Type u_2} 
[inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom : Type 
u_3}   [inst_3 : UniformSpac…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…

--- 原说明 ---
A `DistribSMul` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`UniformContinuousConstSMul.instContinuousConstSMul`
-/
theorem uniformContinuousConstSMul_of_continuousConstSMul [AddGroup M]
    [DistribSMul R M] [UniformSpace M] [IsUniformAddGroup M] [ContinuousConstSMul R M] :
    UniformContinuousConstSMul R M :=
  ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩

/-- The action of `Semiring.toModule` is uniformly continuous. -/
/-
**Ring.uniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ring.uniformContinuousConstSMul [Ring R] [UniformSpace R] [IsUniformAddGro
up R] [ContinuousMul R] : UniformContinuousConstSMul R R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuousConstSMul_of_continuousConstSMul`：uniformContinuousCons
tSMul_of_continuousConstSMul [AddGroup M] [DistribSMul R M] [UniformSpace M] [Is
UniformAddGroup M] [ContinuousConstSMul…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M

--- 原说明 ---
The action of `Semiring.toModule` is uniformly continuous.
-/
instance Ring.uniformContinuousConstSMul [Ring R] [UniformSpace R] [IsUniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul R R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

/-- The action of `Semiring.toOppositeModule` is uniformly continuous. -/
/-
**Ring.uniformContinuousConstSMul_op** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ring.uniformContinuousConstSMul_op [Ring R] [UniformSpace R] [IsUniformAdd
Group R] [ContinuousMul R] : UniformContinuousConstSMul Rᵐᵒᵖ R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuousConstSMul_of_continuousConstSMul`：uniformContinuousCons
tSMul_of_continuousConstSMul [AddGroup M] [DistribSMul R M] [UniformSpace M] [Is
UniformAddGroup M] [ContinuousConstSMul…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M

--- 原说明 ---
The action of `Semiring.toOppositeModule` is uniformly continuous.
-/
instance Ring.uniformContinuousConstSMul_op [Ring R] [UniformSpace R] [IsUniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul Rᵐᵒᵖ R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

section SMul

variable [SMul M X]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) UniformContinuousConstSMul.instContinuousConstSMul
    [UniformContinuousConstSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (uniformContinuous_const_smul c).continuous⟩

variable {M X Y}

@[to_additive (attr := fun_prop)]
/-
**UniformContinuous.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.const_smul [UniformContinuousConstSMul M X] {f : Y -> X}
 (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f)
参数：hf : UniformContinuous f；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
-/
theorem UniformContinuous.const_smul [UniformContinuousConstSMul M X] {f : Y → X}
    (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f) :=
  (uniformContinuous_const_smul c).comp hf

@[to_additive]
/-
**IsUniformInducing.uniformContinuousConstSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.uniformContinuousConstSMul [SMul M Y] [UniformContinuous
ConstSMul M Y] {f : X -> Y} (hf : IsUniformInducing f) (hsmul : forall (c : M) x
, f (c • x) = c • f x) : UniformContinuousConstSMul M X where uniformContinuous_
const_smul c
参数：hf : IsUniformInducing f；hsmul : forall (c : M) x, f (c • x) = c • f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UniformContinuous.const_smul`：UniformContinuous.const_smul [UniformConti
nuousConstSMul M X] {f : Y -> X} (hf : UniformContinuous f) (c : M) : UniformCon
tinuous (c • f)
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
-/
lemma IsUniformInducing.uniformContinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y]
    {f : X → Y} (hf : IsUniformInducing f) (hsmul : ∀ (c : M) x, f (c • x) = c • f x) :
    UniformContinuousConstSMul M X where
  uniformContinuous_const_smul c := by
    simpa only [hf.uniformContinuous_iff, Function.comp_def, hsmul]
      using! hf.uniformContinuous.const_smul c

/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[to_additive /-- If an additive action is central, then its right action is uniform
continuous when its left action is. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) UniformContinuousConstSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
    [UniformContinuousConstSMul M X] : UniformContinuousConstSMul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec' fun c ↦ by simpa only [op_smul_eq_smul] using uniformContinuous_const_smul c⟩

@[to_additive]
/-
**MulOpposite.uniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.uniformContinuousConstSMul [UniformContinuousConstSMul M X] : 
UniformContinuousConstSMul M Xᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `MulOpposite.uniformContinuous_op`：uniformContinuous_op [UniformSpace α] 
: UniformContinuous (op : α -> αᵐᵒᵖ)
· 使用定理 `UniformContinuous.const_smul`：UniformContinuous.const_smul [UniformConti
nuousConstSMul M X] {f : Y -> X} (hf : UniformContinuous f) (c : M) : UniformCon
tinuous (c • f)
· 使用定理 `MulOpposite.uniformContinuous_unop`：uniformContinuous_unop [UniformSpace
 α] : UniformContinuous (unop : αᵐᵒᵖ -> α)
-/
instance MulOpposite.uniformContinuousConstSMul [UniformContinuousConstSMul M X] :
    UniformContinuousConstSMul M Xᵐᵒᵖ :=
  ⟨fun c =>
    MulOpposite.uniformContinuous_op.comp <| MulOpposite.uniformContinuous_unop.const_smul c⟩

end SMul

@[to_additive]
/-
**IsUniformGroup.instUniformContinuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUniformGroup.instUniformContinuousConstSMul {G : Type u} [Group G] [Unif
ormSpace G] [IsUniformGroup G] : UniformContinuousConstSMul G G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.mul`：UniformContinuous.mul [UniformSpace β] {f : β -> 
α} {g : β -> α} (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformC
ontinuous f…
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
instance IsUniformGroup.instUniformContinuousConstSMul {G : Type u} [Group G] [UniformSpace G]
    [IsUniformGroup G] : UniformContinuousConstSMul G G :=
  ⟨fun _ => uniformContinuous_const.mul uniformContinuous_id⟩

section Ring

variable {R β : Type*} [Ring R] [UniformSpace R] [UniformSpace β]

@[fun_prop]
/-
**UniformContinuous.const_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.const_mul' [UniformContinuousConstSMul R R] {f : β -> R}
 (hf : UniformContinuous f) (a : R) : UniformContinuous fun x => a * f x
参数：hf : UniformContinuous f；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.const_smul`：UniformContinuous.const_smul [UniformConti
nuousConstSMul M X] {f : Y -> X} (hf : UniformContinuous f) (c : M) : UniformCon
tinuous (c • f)
-/
theorem UniformContinuous.const_mul' [UniformContinuousConstSMul R R] {f : β → R}
    (hf : UniformContinuous f) (a : R) : UniformContinuous fun x ↦ a * f x :=
  hf.const_smul a

@[fun_prop]
/-
**UniformContinuous.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.mul_const' [UniformContinuousConstSMul Rᵐᵒᵖ R] {f : β ->
 R} (hf : UniformContinuous f) (a : R) : UniformContinuous fun x => f x * a
参数：hf : UniformContinuous f；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.const_smul`：UniformContinuous.const_smul [UniformConti
nuousConstSMul M X] {f : Y -> X} (hf : UniformContinuous f) (c : M) : UniformCon
tinuous (c • f)
-/
theorem UniformContinuous.mul_const' [UniformContinuousConstSMul Rᵐᵒᵖ R] {f : β → R}
    (hf : UniformContinuous f) (a : R) : UniformContinuous fun x ↦ f x * a :=
  hf.const_smul (MulOpposite.op a)
/-
**uniformContinuous_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_mul_left' [UniformContinuousConstSMul R R] (a : R) : Uni
formContinuous fun b : R => a * b
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.const_mul'`：UniformContinuous.const_mul' [UniformConti
nuousConstSMul R R] {f : β -> R} (hf : UniformContinuous f) (a : R) : UniformCon
tinuous fun x => a…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_mul_left' [UniformContinuousConstSMul R R] (a : R) :
    UniformContinuous fun b : R => a * b :=
  uniformContinuous_id.const_mul' _
/-
**uniformContinuous_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_mul_right' [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) :
 UniformContinuous fun b : R => b * a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.mul_const'`：UniformContinuous.mul_const' [UniformConti
nuousConstSMul Rᵐᵒᵖ R] {f : β -> R} (hf : UniformContinuous f) (a : R) : Uniform
Continuous fun x =…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem uniformContinuous_mul_right' [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) :
    UniformContinuous fun b : R => b * a :=
  uniformContinuous_id.mul_const' _

@[fun_prop]
/-
**UniformContinuous.div_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.div_const' {R β : Type*} [DivisionRing R] [UniformSpace 
R] [UniformContinuousConstSMul Rᵐᵒᵖ R] [UniformSpace β] {f : β -> R} (hf : Unifo
rmContinuous f) (a : R) : UniformContinuous fun x => f x / a
参数：hf : UniformContinuous f；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `UniformContinuous.mul_const'`：UniformContinuous.mul_const' [UniformConti
nuousConstSMul Rᵐᵒᵖ R] {f : β -> R} (hf : UniformContinuous f) (a : R) : Uniform
Continuous fun x =…
-/
theorem UniformContinuous.div_const' {R β : Type*} [DivisionRing R] [UniformSpace R]
    [UniformContinuousConstSMul Rᵐᵒᵖ R] [UniformSpace β] {f : β → R}
    (hf : UniformContinuous f) (a : R) :
    UniformContinuous fun x ↦ f x / a := by
  simpa [div_eq_mul_inv] using hf.mul_const' a⁻¹
/-
**uniformContinuous_div_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_div_const' {R : Type*} [DivisionRing R] [UniformSpace R]
 [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) : UniformContinuous fun b : R => b 
/ a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.div_const'`：UniformContinuous.div_const' {R β : Type*}
 [DivisionRing R] [UniformSpace R] [UniformContinuousConstSMul Rᵐᵒᵖ R] [UniformS
pace β] {f : β -> …
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
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
/-
**IsUnit.smul_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.smul_uniformity [Monoid M] [MulAction M X] [UniformContinuousConstS
Mul M X] {c : M} (hc : IsUnit c) : c • 𝓤 X = 𝓤 X
参数：hc : IsUnit c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Filter.smul_filter_le_smul_filter`：smul_filter_le_smul_filter (hf : f₁ <
= f₂) : a • f₁ <= a • f₂
-/
theorem IsUnit.smul_uniformity [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] {c : M}
    (hc : IsUnit c) : c • 𝓤 X = 𝓤 X :=
  let ⟨d, hcd⟩ := hc.exists_right_inv
  have cU : c • 𝓤 X ≤ 𝓤 X := uniformContinuous_const_smul c
  have dU : d • 𝓤 X ≤ 𝓤 X := uniformContinuous_const_smul d
  le_antisymm cU <| by simpa [smul_smul, hcd] using Filter.smul_filter_le_smul_filter (a := c) dU

@[to_additive (attr := simp)]
/-
**smul_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_uniformity [Group M] [MulAction M X] [UniformContinuousConstSMul M X]
 (c : M) : c • 𝓤 X = 𝓤 X
参数：c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.smul_uniformity`：IsUnit.smul_uniformity [Monoid M] [MulAction M X
] [UniformContinuousConstSMul M X] {c : M} (hc : IsUnit c) : c • 𝓤 X = 𝓤 X
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem smul_uniformity [Group M] [MulAction M X] [UniformContinuousConstSMul M X] (c : M) :
    c • 𝓤 X = 𝓤 X :=
  Group.isUnit _ |>.smul_uniformity
/-
**smul_uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_uniformity [Group M] [MulAction M X] [UniformContinuousConstSMul M X]
 (c : M) : c • 𝓤 X = 𝓤 X
参数：c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.smul_uniformity`：IsUnit.smul_uniformity [Monoid M] [MulAction M X
] [UniformContinuousConstSMul M X] {c : M} (hc : IsUnit c) : c • 𝓤 X = 𝓤 X
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem smul_uniformity₀ [GroupWithZero M] [MulAction M X] [UniformContinuousConstSMul M X] {c : M}
    (hc : c ≠ 0) : c • 𝓤 X = 𝓤 X :=
  hc.isUnit.smul_uniformity

end Unit

namespace UniformSpace

namespace Completion

section SMul

variable [SMul M X]

@[to_additive]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SMul M (Completion X) :=
  ⟨fun c => Completion.map (c • ·)⟩

@[to_additive]
/-
**UniformSpace.Completion.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：smul_def (c : M) (x : Completion X) : c • x = Completion.map (c • ·) x
参数：c : M；x : Completion X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def (c : M) (x : Completion X) : c • x = Completion.map (c • ·) x :=
  rfl

@[to_additive]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformContinuousConstSMul M (Completion X) :=
  ⟨fun _ => uniformContinuous_map⟩

@[to_additive]
/-
**UniformSpace.Completion.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `UniformSp
ace.Completion`。
形式化陈述：instIsScalarTower [SMul N X] [SMul M N] [UniformContinuousConstSMul M X] [
UniformContinuousConstSMul N X] [IsScalarTower M N X] : IsScalarTower M N (Compl
etion X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.map_comp`：map_comp {g : β -> γ} {f : α -> β} (hg
 : UniformContinuous g) (hf : UniformContinuous f) : Completion.map g ∘ Completi
on.map f = Completion.…
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instIsScalarTower [SMul N X] [SMul M N] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x => by
    have : _ = (_ : Completion X → Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine Eq.trans ?_ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul N X] [SMulCommClass M N X] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] : SMulCommClass M N (Completion X) :=
  ⟨fun m n x => by
    have hmn : m • n • x = (Completion.map (SMul.smul m) ∘ Completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (Completion.map (SMul.smul n) ∘ Completion.map (SMul.smul m)) x := rfl
    rw [hmn, hnm, map_comp, map_comp]
    · exact congr_arg (fun f => Completion.map f x) (funext (smul_comm _ _))
    repeat' exact uniformContinuous_const_smul _⟩

@[to_additive]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
  ⟨fun c a => (congr_arg fun f => Completion.map f a) <| funext (op_smul_eq_smul c)⟩

variable {M X}
variable [UniformContinuousConstSMul M X]

@[to_additive (attr := simp, norm_cast)]
/-
**UniformSpace.Completion.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：coe_smul (c : M) (x : X) : (↑(c • x) : Completion X) = c • (x : Completion
 X)
参数：c : M；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
-/
theorem coe_smul (c : M) (x : X) : (↑(c • x) : Completion X) = c • (x : Completion X) :=
  (map_coe (uniformContinuous_const_smul c) x).symm

end SMul

@[to_additive]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] :
    MulAction M (Completion X) where
  one_smul := ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).fun_const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

end Completion

end UniformSpace

