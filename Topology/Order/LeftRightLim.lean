/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Separation.Regular

/-!
# Left and right limits

We define the (strict) left and right limits of a function.

* `leftLim f x` is the strict left limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its left).
* `rightLim f x` is the strict right limit of `f` at `x` (using `f x` as a garbage value if `x`
  is isolated to its right).

We develop a comprehensive API for monotone functions. Notably,

* `Monotone.continuousAt_iff_leftLim_eq_rightLim` states that a monotone function is continuous
  at a point if and only if its left and right limits coincide.
* `Monotone.countable_not_continuousAt` asserts that a monotone function taking values in a
  second-countable space has at most countably many discontinuity points.

We also port the API to antitone functions.

## TODO

Prove corresponding stronger results for `StrictMono` and `StrictAnti` functions.
-/

@[expose] public section


open Set Filter

open Topology

section

variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
/-
**Function.leftLim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.leftLim (f : α -> β) (a : α) : β
参数：f : α -> β；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : α → β` be a function from a linear order `α` to a topological space `β`
, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim
 f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the functi
on has no left
limit, we use `f a` instead to guarantee a good behavior in most cases.
-/
noncomputable def Function.leftLim (f : α → β) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[<] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[<] a) (𝓝 y) then f a else limUnder (𝓝[<] a) f

/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
/-
**Function.rightLim** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.rightLim (f : α -> β) (a : α) : β
参数：f : α -> β；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : α → β` be a function from a linear order `α` to a topological space `β`
, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightL
im f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the funct
ion has no right
limit, we use `f a` instead to guarantee a good behavior in most cases.
-/
noncomputable def Function.rightLim (f : α → β) (a : α) : β :=
  @Function.leftLim αᵒᵈ β _ _ f a

open Function
/-
**leftLim_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T
2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).NeBot] (h' : Tendsto f (𝓝[<
] a) (𝓝 y)) : leftLim f a = y
参数：𝓝[<] a；h' : Tendsto f (𝓝[<] a) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `OrderTopology.topology_eq_generate_intervals`：∀ {α : Type u_1} {t : Topo
logicalSpace α} {inst : Preorder α} [self : OrderTopology α], t = Preorder.topol
ogy α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `lim_eq`：lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x
-/
theorem leftLim_eq_of_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} [h : (𝓝[<] a).NeBot] (h' : Tendsto f (𝓝[<] a) (𝓝 y)) :
    leftLim f a = y := by
  have h'' : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y) := ⟨y, h'⟩
  rw [h'α.topology_eq_generate_intervals] at h h' h''
  simp only [leftLim, neBot_iff.mp h, h'', not_true, or_self_iff, if_false]
  exact lim_eq h'
/-
**rightLim_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightLim_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β] 
{f : α -> β} {a : α} {y : β} [h : (𝓝[>] a).NeBot] (h' : Tendsto f (𝓝[>] a) (𝓝 y)
) : Function.rightLim f a = y
参数：𝓝[>] a；h' : Tendsto f (𝓝[>] a) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_tendsto`：leftLim_eq_of_tendsto [hα : TopologicalSpace α] [
h'α : OrderTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).Ne
Bot] (h' : …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem rightLim_eq_of_tendsto [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} {y : β} [h : (𝓝[>] a).NeBot] (h' : Tendsto f (𝓝[>] a) (𝓝 y)) :
    Function.rightLim f a = y :=
  leftLim_eq_of_tendsto (α := αᵒᵈ) (h := h) h'
/-
**leftLim_eq_of_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f 
: α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
参数：f : α -> β；h : 𝓝[<] a = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderTopology.topology_eq_generate_intervals`：∀ {α : Type u_1} {t : Topo
logicalSpace α} {inst : Preorder α} [self : OrderTopology α], t = Preorder.topol
ogy α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[<] a = ⊥) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]
/-
**rightLim_eq_of_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightLim_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α -> β) 
{a : α} (h : 𝓝[>] a = ⊥) : rightLim f a = f a
参数：f : α -> β；h : 𝓝[>] a = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem rightLim_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β) {a : α}
    (h : 𝓝[>] a = ⊥) : rightLim f a = f a :=
  leftLim_eq_of_eq_bot (α := αᵒᵈ) f h
/-
**leftLim_eq_of_not_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftLim_eq_of_not_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology α
] (f : α -> β) {a : α} (h : ¬ exists y, Tendsto f (𝓝[<] a) (𝓝 y)) : leftLim f a 
= f a
参数：f : α -> β；h : ¬ exists y, Tendsto f (𝓝[<] a) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `OrderTopology.topology_eq_generate_intervals`：∀ {α : Type u_1} {t : Topo
logicalSpace α} {inst : Preorder α} [self : OrderTopology α], t = Preorder.topol
ogy α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)) : leftLim f a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLim, h]
/-
**rightLim_eq_of_not_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightLim_eq_of_not_tendsto [hα : TopologicalSpace α] [h'α : OrderTopology 
α] (f : α -> β) {a : α} (h : ¬ exists y, Tendsto f (𝓝[>] a) (𝓝 y)) : rightLim f 
a = f a
参数：f : α -> β；h : ¬ exists y, Tendsto f (𝓝[>] a) (𝓝 y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_not_tendsto`：leftLim_eq_of_not_tendsto [hα : TopologicalSp
ace α] [h'α : OrderTopology α] (f : α -> β) {a : α} (h : ¬ exists y, Tendsto f (
𝓝[<] a) (𝓝 y)) …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem rightLim_eq_of_not_tendsto
    [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β) {a : α}
    (h : ¬ ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)) : rightLim f a = f a :=
  leftLim_eq_of_not_tendsto (α := αᵒᵈ) f h
/-
**leftLim_eq_of_isBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftLim_eq_of_isBot {f : α -> β} {a : α} (ha : IsBot a) : leftLim f a = f 
a
参数：ha : IsBot a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_empty`：nhdsWithin_empty (a : α) : 𝓝[∅] a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftLim_eq_of_isBot {f : α → β} {a : α} (ha : IsBot a) :
    leftLim f a = f a := by
  let A : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  apply leftLim_eq_of_eq_bot
  have : Iio a = ∅ := by simp; grind [IsBot, IsMin]
  simp [this]
/-
**rightLim_eq_of_isTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightLim_eq_of_isTop {f : α -> β} {a : α} (ha : IsTop a) : rightLim f a = 
f a
参数：ha : IsTop a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_isBot`：leftLim_eq_of_isBot {f : α -> β} {a : α} (ha : IsBo
t a) : leftLim f a = f a
-/
theorem rightLim_eq_of_isTop {f : α → β} {a : α} (ha : IsTop a) :
    rightLim f a = f a :=
  leftLim_eq_of_isBot (α := αᵒᵈ) ha
/-
**ContinuousWithinAt.leftLim_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.leftLim_eq [TopologicalSpace α] [OrderTopology α] [T2Sp
ace β] {f : α -> β} {a : α} (hf : ContinuousWithinAt f (Iic a) a) : leftLim f a 
= f a
参数：hf : ContinuousWithinAt f (Iic a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `leftLim_eq_of_tendsto`：leftLim_eq_of_tendsto [hα : TopologicalSpace α] [
h'α : OrderTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).Ne
Bot] (h' : …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem ContinuousWithinAt.leftLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} (hf : ContinuousWithinAt f (Iic a) a) : leftLim f a = f a := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h']
  apply leftLim_eq_of_tendsto
  exact hf.tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
/-
**ContinuousWithinAt.rightLim_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.rightLim_eq [TopologicalSpace α] [OrderTopology α] [T2S
pace β] {f : α -> β} {a : α} (hf : ContinuousWithinAt f (Ici a) a) : rightLim f 
a = f a
参数：hf : ContinuousWithinAt f (Ici a) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.leftLim_eq`：ContinuousWithinAt.leftLim_eq [Topologica
lSpace α] [OrderTopology α] [T2Space β] {f : α -> β} {a : α} (hf : ContinuousWit
hinAt f (Iic a) a) …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem ContinuousWithinAt.rightLim_eq [TopologicalSpace α] [OrderTopology α] [T2Space β]
    {f : α → β} {a : α} (hf : ContinuousWithinAt f (Ici a) a) : rightLim f a = f a :=
  ContinuousWithinAt.leftLim_eq (α := αᵒᵈ) hf
/-
**tendsto_leftLim_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_leftLim_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α] {f
 : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[<] a) (𝓝 y)) : Tendsto f (𝓝[<] a)
 (𝓝 (f.leftLim a))
参数：h : exists y, Tendsto f (𝓝[<] a) (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderTopology.topology_eq_generate_intervals`：∀ {α : Type u_1} {t : Topo
logicalSpace α} {inst : Preorder α} [self : OrderTopology α], t = Preorder.topol
ogy α
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
-/
theorem tendsto_leftLim_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α → β} {a : α} (h : ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)) :
    Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a)) := by
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLim, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h
/-
**tendsto_rightLim_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rightLim_of_tendsto [TopologicalSpace α] [OrderTopology α] {f : α 
-> β} {a : α} (h : exists y, Tendsto f (𝓝[>] a) (𝓝 y)) : Tendsto f (𝓝[>] a) (𝓝 (
f.rightLim a))
参数：h : exists y, Tendsto f (𝓝[>] a) (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_leftLim_of_tendsto`：tendsto_leftLim_of_tendsto [TopologicalSpace
 α] [h'α : OrderTopology α] {f : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[<] 
a) (𝓝 y)) : Tend…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem tendsto_rightLim_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α → β} {a : α} (h : ∃ y, Tendsto f (𝓝[>] a) (𝓝 y)) :
    Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a)) :=
  tendsto_leftLim_of_tendsto (α := αᵒᵈ) h
/-
**mapClusterPt_leftLim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_leftLim [TopologicalSpace α] [OrderTopology α] (f : α -> β) (
a : α) : MapClusterPt (f.leftLim a) (𝓝[<=] a) f
参数：f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.inf_neBot_iff`：inf_neBot_iff : NeBot (l ⊓ l') ↔ forall ⦃s : Set α
⦄, s in l -> forall ⦃s'⦄, s' in l' -> (s inter s').Nonempty
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `leftLim_eq_of_not_tendsto`：leftLim_eq_of_not_tendsto [hα : TopologicalSp
ace α] [h'α : OrderTopology α] (f : α -> β) {a : α} (h : ¬ exists y, Tendsto f (
𝓝[<] a) (𝓝 y)) …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.Tendsto.mapClusterPt`：Filter.Tendsto.mapClusterPt [NeBot F] (h : 
Tendsto u F (𝓝 x)) : MapClusterPt x F u
· 使用定理 `tendsto_leftLim_of_tendsto`：tendsto_leftLim_of_tendsto [TopologicalSpace
 α] [h'α : OrderTopology α] {f : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[<] 
a) (𝓝 y)) : Tend…
· 使用定理 `MapClusterPt.mono`：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x 
F u) (hle : F <= G) : MapClusterPt x G u
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem mapClusterPt_leftLim [TopologicalSpace α] [OrderTopology α]
    (f : α → β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[≤] a) f := by
  have A : (𝓝 (f a) ⊓ map f (𝓝[≤] a)).NeBot := by
    refine inf_neBot_iff.mpr (fun s hs s' hs' ↦ ?_)
    refine ⟨f a, mem_of_mem_nhds hs, ?_⟩
    simp only [mem_map] at hs'
    apply mem_of_mem_nhdsWithin self_mem_Iic hs'
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp only [MapClusterPt, ClusterPt, h', leftLim_eq_of_eq_bot, A]
  by_cases! H : ¬ ∃ y, Tendsto f (𝓝[<] a) (𝓝 y)
  · simp [MapClusterPt, ClusterPt, H, leftLim_eq_of_not_tendsto, A]
  have : MapClusterPt (f.leftLim a) (𝓝[<] a) f := (tendsto_leftLim_of_tendsto H).mapClusterPt
  exact MapClusterPt.mono this (nhdsWithin_mono _ Iio_subset_Iic_self)
/-
**mapClusterPt_rightLim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_rightLim [TopologicalSpace α] [OrderTopology α] (f : α -> β) 
(a : α) : MapClusterPt (f.rightLim a) (𝓝[>=] a) f
参数：f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mapClusterPt_leftLim`：mapClusterPt_leftLim [TopologicalSpace α] [OrderTo
pology α] (f : α -> β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[<=] a) f
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem mapClusterPt_rightLim [TopologicalSpace α] [OrderTopology α]
    (f : α → β) (a : α) : MapClusterPt (f.rightLim a) (𝓝[≥] a) f :=
  mapClusterPt_leftLim (α := αᵒᵈ) _ _
/-
**continuousWithinAt_leftLim_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_leftLim_Iic [TopologicalSpace α] [OrderTopology α] [T3S
pace β] {f : α -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) : Contin
uousWithinAt f.leftLim (Iic a) a
参数：h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_Icc_eq_Iic`：Iio_union_Icc_eq_Iic (h : a <= b) : Iio a unio
n Icc a b = Iic b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.tendsto_sup`：tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Fil
ter β} : Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset'`：mem_nhdsLT_iff_exists_Ioo_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a su
bseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
（共 37 条，此处仅展示前 30 条）
-/
theorem continuousWithinAt_leftLim_Iic [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    ContinuousWithinAt f.leftLim (Iic a) a := by
  have : 𝓝[≤] a = 𝓝[<] a ⊔ pure a := by
    rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
    simp
  rw [ContinuousWithinAt, this, tendsto_sup]
  simp only [tendsto_pure_nhds, and_true]
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  rcases eq_or_neBot (𝓝[<] a) with h' | h'
  · simp [h']
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[<] c) with h'c | h'c
  · simpa [h'c, leftLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[<] c) (𝓝 y)
  · simpa [leftLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsLT_of_mem ⟨hc.1, hc.2.le⟩] with d hd using hu hd
/-
**leftLim_leftLim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β] {f : α 
-> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) : f.leftLim.leftLim a =
 f.leftLim a
参数：h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.leftLim_eq`：ContinuousWithinAt.leftLim_eq [Topologica
lSpace α] [OrderTopology α] [T2Space β] {f : α -> β} {a : α} (hf : ContinuousWit
hinAt f (Iic a) a) …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `continuousWithinAt_leftLim_Iic`：continuousWithinAt_leftLim_Iic [Topologi
calSpace α] [OrderTopology α] [T3Space β] {f : α -> β} {a : α} (h : Tendsto f (𝓝
[<] a) (𝓝 (f.leftLim…
-/
theorem leftLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) :
    f.leftLim.leftLim a = f.leftLim a :=
  (continuousWithinAt_leftLim_Iic h).leftLim_eq
/-
**continuousWithinAt_rightLim_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_rightLim_Ici [TopologicalSpace α] [OrderTopology α] [T3
Space β] {f : α -> β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) : Cont
inuousWithinAt f.rightLim (Ici a) a
参数：h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_leftLim_Iic`：continuousWithinAt_leftLim_Iic [Topologi
calSpace α] [OrderTopology α] [T3Space β] {f : α -> β} {a : α} (h : Tendsto f (𝓝
[<] a) (𝓝 (f.leftLim…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem continuousWithinAt_rightLim_Ici [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    ContinuousWithinAt f.rightLim (Ici a) a :=
  continuousWithinAt_leftLim_Iic (α := αᵒᵈ) h
/-
**rightLim_rightLim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β] {f : 
α -> β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) : f.rightLim.rightLi
m a = f.rightLim a
参数：h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_leftLim`：leftLim_leftLim [TopologicalSpace α] [OrderTopology α] 
[T3Space β] {f : α -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) : f.
leftL…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem rightLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) :
    f.rightLim.rightLim a = f.rightLim a :=
  leftLim_leftLim (α := αᵒᵈ) h
/-
**leftLim_rightLim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β] {f : α
 -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) [h' : (𝓝[<] a).NeBot] 
: f.rightLim.leftLim a = f.leftLim a
参数：h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))；𝓝[<] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `leftLim_eq_of_tendsto`：leftLim_eq_of_tendsto [hα : TopologicalSpace α] [
h'α : OrderTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).Ne
Bot] (h' : …
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mem_nhdsLT_iff_exists_Ioo_subset'`：mem_nhdsLT_iff_exists_Ioo_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<] a ↔ exists l in Iio a, Ioo l a su
bseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `rightLim_eq_of_eq_bot`：rightLim_eq_of_eq_bot [TopologicalSpace α] [Order
Topology α] (f : α -> β) {a : α} (h : 𝓝[>] a = ⊥) : rightLim f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `rightLim_eq_of_not_tendsto`：rightLim_eq_of_not_tendsto [hα : Topological
Space α] [h'α : OrderTopology α] (f : α -> β) {a : α} (h : ¬ exists y, Tendsto f
 (𝓝[>] a) (𝓝 y))…
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `tendsto_rightLim_of_tendsto`：tendsto_rightLim_of_tendsto [TopologicalSpa
ce α] [OrderTopology α] {f : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[>] a) (
𝓝 y)) : Tendsto f…
· 使用定理 `Ioo_mem_nhdsGT_of_mem`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : LinearOrder α] [ClosedIciTopology α] {a b c : α},   b ∈ Set.Ico c a → Set.Io
o c a ∈ nhd…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 32 条，此处仅展示前 30 条）
-/
theorem leftLim_rightLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) [h' : (𝓝[<] a).NeBot] :
    f.rightLim.leftLim a = f.leftLim a := by
  obtain ⟨b, hb⟩ : (Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  apply leftLim_eq_of_tendsto
  apply (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have := (closed_nhds_basis (f.leftLim a)).tendsto_right_iff.1 h s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 this
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[>] c) with h'c | h'c
  · simpa [h'c, rightLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[>] c) (𝓝 y)
  · simpa [rightLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_rightLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hc.1.le, hc.2⟩] with d hd using hu hd
/-
**rightLim_leftLim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β] {f : α
 -> β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) [h' : (𝓝[>] a).NeBot]
 : f.leftLim.rightLim a = f.rightLim a
参数：h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))；𝓝[>] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_rightLim`：leftLim_rightLim [TopologicalSpace α] [OrderTopology α
] [T3Space β] {f : α -> β} {a : α} (h : Tendsto f (𝓝[<] a) (𝓝 (f.leftLim a))) [h
' : (𝓝…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem rightLim_leftLim [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {a : α} (h : Tendsto f (𝓝[>] a) (𝓝 (f.rightLim a))) [h' : (𝓝[>] a).NeBot] :
    f.leftLim.rightLim a = f.rightLim a :=
  leftLim_rightLim (α := αᵒᵈ) h (h' := h')
/-
**tendsto_atTop_of_mapClusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_of_mapClusterPt [TopologicalSpace α] [OrderTopology α] [T3Sp
ace β] [NoTopOrder α] {f g : α -> β} {b : β} (h : Tendsto f atTop (𝓝 b)) (h' : f
orallᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f) : Tendsto g atTop (𝓝 b)
参数：h : Tendsto f atTop (𝓝 b)；h' : forallᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsClosed.mem_of_mapClusterPt`：IsClosed.mem_of_mapClusterPt {l : X} {s : 
Set X} {f : α -> X} {b : Filter α} (hs : IsClosed s) (hf : MapClusterPt l b f) (
h : forallᶠ (x : α…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ici_mem_nhds`：Ici_mem_nhds (h : a < b) : Ici a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_atTop_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atTop (𝓝 b)) (h' : ∀ᶠ x in atTop, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atTop (𝓝 b) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [filter_eq_bot_of_isEmpty atTop]
  apply (closed_nhds_basis b).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  obtain ⟨u, hu⟩ : ∃ a, ∀ (b : α), a ≤ b → MapClusterPt (g b) (𝓝 b) f ∧ f b ∈ s := by
    simpa [eventually_atTop] using h'.and (h s_mem)
  filter_upwards [Ioi_mem_atTop u] with a (ha : u < a)
  apply s_closed.mem_of_mapClusterPt (hu a ha.le).1
  filter_upwards [Ici_mem_nhds ha] with y hy using (hu y hy).2
/-
**tendsto_atBot_of_mapClusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atBot_of_mapClusterPt [TopologicalSpace α] [OrderTopology α] [T3Sp
ace β] [NoBotOrder α] {f g : α -> β} {b : β} (h : Tendsto f atBot (𝓝 b)) (h' : f
orallᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f) : Tendsto g atBot (𝓝 b)
参数：h : Tendsto f atBot (𝓝 b)；h' : forallᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_mapClusterPt`：tendsto_atTop_of_mapClusterPt [Topologica
lSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α -> β} {b : β} (h
 : Tendsto f atTop …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noTopOrder`：∀ {α : Type u_1} [inst : LE α] [NoBotOrder α], NoT
opOrder αᵒᵈ
-/
theorem tendsto_atBot_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] [T3Space β] [NoBotOrder α] {f g : α → β} {b : β}
    (h : Tendsto f atBot (𝓝 b)) (h' : ∀ᶠ x in atBot, MapClusterPt (g x) (𝓝 x) f) :
    Tendsto g atBot (𝓝 b) :=
  tendsto_atTop_of_mapClusterPt (α := αᵒᵈ) h h'
/-
**tendsto_leftLim_atTop_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_leftLim_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α] [N
oTopOrder α] [T3Space β] {f : α -> β} {b : β} (h : Tendsto f atTop (𝓝 b)) : Tend
sto f.leftLim atTop (𝓝 b)
参数：h : Tendsto f atTop (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_mapClusterPt`：tendsto_atTop_of_mapClusterPt [Topologica
lSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α -> β} {b : β} (h
 : Tendsto f atTop …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MapClusterPt.mono`：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x 
F u) (hle : F <= G) : MapClusterPt x G u
· 使用定理 `mapClusterPt_leftLim`：mapClusterPt_leftLim [TopologicalSpace α] [OrderTo
pology α] (f : α -> β) (a : α) : MapClusterPt (f.leftLim a) (𝓝[<=] a) f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem tendsto_leftLim_atTop_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoTopOrder α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.leftLim atTop (𝓝 b) := by
  apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
  exact MapClusterPt.mono (mapClusterPt_leftLim _ _) nhdsWithin_le_nhds
/-
**tendsto_rightLim_atTop_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rightLim_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α] [
T3Space β] {f : α -> β} {b : β} (h : Tendsto f atTop (𝓝 b)) : Tendsto f.rightLim
 atTop (𝓝 b)
参数：h : Tendsto f atTop (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.OrderTop.atTop_eq`：∀ (α : Type u_6) [inst : PartialOrder α] [inst
_1 : OrderTop α], Filter.atTop = pure ⊤
· 使用定理 `rightLim_eq_of_isTop`：rightLim_eq_of_isTop {f : α -> β} {a : α} (ha : Is
Top a) : rightLim f a = f a
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `tendsto_pure_nhds`：tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (p
ure a) (𝓝 (f a))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_atTop_of_mapClusterPt`：tendsto_atTop_of_mapClusterPt [Topologica
lSpace α] [OrderTopology α] [T3Space β] [NoTopOrder α] {f g : α -> β} {b : β} (h
 : Tendsto f atTop …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MapClusterPt.mono`：MapClusterPt.mono {G : Filter α} (h : MapClusterPt x 
F u) (hle : F <= G) : MapClusterPt x G u
· 使用定理 `mapClusterPt_rightLim`：mapClusterPt_rightLim [TopologicalSpace α] [Order
Topology α] (f : α -> β) (a : α) : MapClusterPt (f.rightLim a) (𝓝[>=] a) f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem tendsto_rightLim_atTop_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atTop (𝓝 b)) :
    Tendsto f.rightLim atTop (𝓝 b) := by
  cases topOrderOrNoTopOrder α
  · simp only [OrderTop.atTop_eq α] at h ⊢
    have : f.rightLim ⊤ = f ⊤ := rightLim_eq_of_isTop isTop_top
    rw [tendsto_nhds_unique h (tendsto_pure_nhds f ⊤), ← this]
    apply tendsto_pure_nhds
  · apply tendsto_atTop_of_mapClusterPt h (Eventually.of_forall (fun x ↦ ?_))
    exact MapClusterPt.mono (mapClusterPt_rightLim _ _) nhdsWithin_le_nhds
/-
**tendsto_rightLim_atBot_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rightLim_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α] [
NoBotOrder α] [T3Space β] {f : α -> β} {b : β} (h : Tendsto f atBot (𝓝 b)) : Ten
dsto f.rightLim atBot (𝓝 b)
参数：h : Tendsto f atBot (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_leftLim_atTop_of_tendsto`：tendsto_leftLim_atTop_of_tendsto [Topo
logicalSpace α] [OrderTopology α] [NoTopOrder α] [T3Space β] {f : α -> β} {b : β
} (h : Tendsto f atTop…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noTopOrder`：∀ {α : Type u_1} [inst : LE α] [NoBotOrder α], NoT
opOrder αᵒᵈ
-/
theorem tendsto_rightLim_atBot_of_tendsto
    [TopologicalSpace α] [OrderTopology α] [NoBotOrder α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.rightLim atBot (𝓝 b) :=
  tendsto_leftLim_atTop_of_tendsto (α := αᵒᵈ) h
/-
**tendsto_leftLim_atBot_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_leftLim_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α] [T
3Space β] {f : α -> β} {b : β} (h : Tendsto f atBot (𝓝 b)) : Tendsto f.leftLim a
tBot (𝓝 b)
参数：h : Tendsto f atBot (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_rightLim_atTop_of_tendsto`：tendsto_rightLim_atTop_of_tendsto [To
pologicalSpace α] [OrderTopology α] [T3Space β] {f : α -> β} {b : β} (h : Tendst
o f atTop (𝓝 b)) : Tend…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem tendsto_leftLim_atBot_of_tendsto [TopologicalSpace α] [OrderTopology α] [T3Space β]
    {f : α → β} {b : β} (h : Tendsto f atBot (𝓝 b)) :
    Tendsto f.leftLim atBot (𝓝 b) :=
  tendsto_rightLim_atTop_of_tendsto (α := αᵒᵈ) h

end

open Function

namespace Monotone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Monotone f) {x y : α}
include hf

/-
**Monotone.leftLim_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：leftLim_eq_sSup [TopologicalSpace α] [OrderTopology α] [(𝓝[<] x).NeBot] : 
leftLim f x = sSup (f '' Iio x)
参数：𝓝[<] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_tendsto`：leftLim_eq_of_tendsto [hα : TopologicalSpace α] [
h'α : OrderTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[<] a).Ne
Bot] (h' : …
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Monotone.tendsto_nhdsLT`：Monotone.tendsto_nhdsLT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
-/
theorem leftLim_eq_sSup [TopologicalSpace α] [OrderTopology α] [(𝓝[<] x).NeBot] :
    leftLim f x = sSup (f '' Iio x) :=
  leftLim_eq_of_tendsto (hf.tendsto_nhdsLT x)
/-
**Monotone.rightLim_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：rightLim_eq_sInf [TopologicalSpace α] [OrderTopology α] [(𝓝[>] x).NeBot] :
 rightLim f x = sInf (f '' Ioi x)
参数：𝓝[>] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rightLim_eq_of_tendsto`：rightLim_eq_of_tendsto [TopologicalSpace α] [Ord
erTopology α] [T2Space β] {f : α -> β} {a : α} {y : β} [h : (𝓝[>] a).NeBot] (h' 
: Tendsto f …
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Monotone.tendsto_nhdsGT`：Monotone.tendsto_nhdsGT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
-/
theorem rightLim_eq_sInf [TopologicalSpace α] [OrderTopology α] [(𝓝[>] x).NeBot] :
    rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto (hf.tendsto_nhdsGT x)
/-
**Monotone.leftLim_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：leftLim_le (h : x <= y) : leftLim f x <= f y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Monotone.leftLim_eq_sSup`：leftLim_eq_sSup [TopologicalSpace α] [OrderTop
ology α] [(𝓝[<] x).NeBot] : leftLim f x = sSup (f '' Iio x)
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.forall_mem_nonempty_iff_neBot`：forall_mem_nonempty_iff_neBot {f :
 Filter α} : (forall s : Set α, s in f -> s.Nonempty) ↔ NeBot f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem leftLim_le (h : x ≤ y) : leftLim f x ≤ f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simpa [leftLim, h'] using hf h
  rw [leftLim_eq_sSup hf]
  refine csSup_le ?_ ?_
  · simp only [image_nonempty]
    exact (forall_mem_nonempty_iff_neBot.2 h') _ self_mem_nhdsWithin
  · simp only [mem_image, mem_Iio, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro z hz
    exact hf (hz.le.trans h)
/-
**Monotone.le_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：le_leftLim (h : x < y) : f x <= leftLim f y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Monotone.leftLim_eq_sSup`：leftLim_eq_sSup [TopologicalSpace α] [OrderTop
ology α] [(𝓝[<] x).NeBot] : leftLim f x = sSup (f '' Iio x)
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem le_leftLim (h : x < y) : f x ≤ leftLim f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with h' | h'
  · rw [leftLim_eq_of_eq_bot _ h']
    exact hf h.le
  rw [leftLim_eq_sSup hf]
  refine le_csSup ⟨f y, ?_⟩ (mem_image_of_mem _ h)
  simp only [upperBounds, mem_image, mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, mem_ofPred_eq]
  intro z hz
  exact hf hz.le

@[gcongr, mono]
/-
**Monotone.leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Condition
allyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [OrderTopology β] {f 
: α → β}, Monotone f → Monotone (Function.leftLim f)
参数：Function.leftLim f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `Monotone.le_leftLim`：le_leftLim (h : x < y) : f x <= leftLim f y
-/
protected theorem leftLim : Monotone (leftLim f) := by
  intro x y h
  rcases eq_or_lt_of_le h with (rfl | hxy)
  · exact le_rfl
  · exact (hf.leftLim_le le_rfl).trans (hf.le_leftLim hxy)
/-
**Monotone.le_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：le_rightLim (h : x <= y) : f x <= rightLim f y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem le_rightLim (h : x ≤ y) : f x ≤ rightLim f y :=
  hf.dual.leftLim_le h
/-
**Monotone.rightLim_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：rightLim_le (h : x < y) : rightLim f x <= f y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_leftLim`：le_leftLim (h : x < y) : f x <= leftLim f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem rightLim_le (h : x < y) : rightLim f x ≤ f y :=
  hf.dual.le_leftLim h

@[gcongr, mono]
/-
**Monotone.rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Condition
allyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [OrderTopology β] {f 
: α → β}, Monotone f → Monotone (Function.rightLim f)
参数：Function.rightLim f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.leftLim`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α]
 [inst_1 : ConditionallyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [
OrderT…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
protected theorem rightLim : Monotone (rightLim f) := fun _ _ h => hf.dual.leftLim h
/-
**Monotone.leftLim_le_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：leftLim_le_rightLim (h : x <= y) : leftLim f x <= rightLim f y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Monotone.le_rightLim`：le_rightLim (h : x <= y) : f x <= rightLim f y
-/
theorem leftLim_le_rightLim (h : x ≤ y) : leftLim f x ≤ rightLim f y :=
  (hf.leftLim_le le_rfl).trans (hf.le_rightLim h)
/-
**Monotone.rightLim_le_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：rightLim_le_leftLim (h : x < y) : rightLim f x <= leftLim f y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Monotone.rightLim_le`：rightLim_le (h : x < y) : rightLim f x <= f y
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Monotone.le_leftLim`：le_leftLim (h : x < y) : f x <= leftLim f y
-/
theorem rightLim_le_leftLim (h : x < y) : rightLim f x ≤ leftLim f y := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] y) with (h' | h')
  · simpa [leftLim, h'] using rightLim_le hf h
  obtain ⟨a, ⟨xa, ay⟩⟩ : (Ioo x y).Nonempty := nonempty_of_mem (Ioo_mem_nhdsLT h)
  calc
    rightLim f x ≤ f a := hf.rightLim_le xa
    _ ≤ leftLim f y := hf.le_leftLim ay

variable [TopologicalSpace α] [OrderTopology α]
/-
**Monotone.tendsto_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_leftLim_of_tendsto`：tendsto_leftLim_of_tendsto [TopologicalSpace
 α] [h'α : OrderTopology α] {f : α -> β} {a : α} (h : exists y, Tendsto f (𝓝[<] 
a) (𝓝 y)) : Tend…
· 使用定理 `Monotone.tendsto_nhdsLT`：Monotone.tendsto_nhdsLT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
-/
theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  tendsto_leftLim_of_tendsto ⟨_, hf.tendsto_nhdsLT x⟩
/-
**Monotone.tendsto_leftLim_within** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[<=] leftLim f x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Monotone.tendsto_leftLim`：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (
𝓝 (leftLim f x))
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Monotone.le_leftLim`：le_leftLim (h : x < y) : f x <= leftLim f y
-/
theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≤] leftLim f x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f (hf.tendsto_leftLim x)
  filter_upwards [@self_mem_nhdsWithin _ _ x (Iio x)] with y hy using hf.le_leftLim hy
/-
**Monotone.tendsto_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_leftLim`：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (
𝓝 (leftLim f x))
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual.tendsto_leftLim x
/-
**Monotone.tendsto_rightLim_within** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[>=] rightLim f x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_leftLim_within`：tendsto_leftLim_within (x : α) : Tendst
o f (𝓝[<] x) (𝓝[<=] leftLim f x)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≥] rightLim f x) :=
  hf.dual.tendsto_leftLim_within x

/-- A monotone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
/-
**Monotone.continuousWithinAt_Iio_iff_leftLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mono
tone`。
形式化陈述：continuousWithinAt_Iio_iff_leftLim_eq : ContinuousWithinAt f (Iio x) x ↔ l
eftLim f x = f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Monotone.tendsto_leftLim`：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (
𝓝 (leftLim f x))
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))

--- 原说明 ---
A monotone function is continuous to the left at a point if and only if its left
 limit
coincides with the value of the function.
-/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x := by
  rcases eq_or_neBot (𝓝[<] x) with h' | h'
  · simp [leftLim_eq_of_eq_bot f h', ContinuousWithinAt, h']
  refine ⟨fun h => tendsto_nhds_unique (hf.tendsto_leftLim x) h.tendsto, fun h => ?_⟩
  have := hf.tendsto_leftLim x
  rwa [h] at this

/-- A monotone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
/-
**Monotone.continuousWithinAt_Ioi_iff_rightLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mon
otone`。
形式化陈述：continuousWithinAt_Ioi_iff_rightLim_eq : ContinuousWithinAt f (Ioi x) x ↔ 
rightLim f x = f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.continuousWithinAt_Iio_iff_leftLim_eq`：continuousWithinAt_Iio_i
ff_leftLim_eq : ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
A monotone function is continuous to the right at a point if and only if its rig
ht limit
coincides with the value of the function.
-/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual.continuousWithinAt_Iio_iff_leftLim_eq

/-- A monotone function is continuous at a point if and only if its left and right limits
coincide. -/
/-
**Monotone.continuousAt_iff_leftLim_eq_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Monot
one`。
形式化陈述：continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = ri
ghtLim f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Monotone.continuousWithinAt_Iio_iff_leftLim_eq`：continuousWithinAt_Iio_i
ff_leftLim_eq : ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Monotone.continuousWithinAt_Ioi_iff_rightLim_eq`：continuousWithinAt_Ioi_
iff_rightLim_eq : ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.le_rightLim`：le_rightLim (h : x <= y) : f x <= rightLim f y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_iff_continuous_left'_right'`：∀ {α : Type u_1} {β : Type u_2
} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [inst_2 : TopologicalSpac
e β]   {a : α} {f : α → β}, Co…

--- 原说明 ---
A monotone function is continuous at a point if and only if its left and right l
imits
coincide.
-/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have A : leftLim f x = f x :=
      hf.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousWithinAt
    have B : rightLim f x = f x :=
      hf.continuousWithinAt_Ioi_iff_rightLim_eq.1 h.continuousWithinAt
    exact A.trans B.symm
  · have h' : leftLim f x = f x := by
      apply le_antisymm (leftLim_le hf (le_refl _))
      rw [h]
      exact le_rightLim hf (le_refl _)
    refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
    · exact hf.continuousWithinAt_Iio_iff_leftLim_eq.2 h'
    · rw [h] at h'
      exact hf.continuousWithinAt_Ioi_iff_rightLim_eq.2 h'

end Monotone

namespace Antitone

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] {f : α → β} (hf : Antitone f) {x y : α}
include hf

/-
**Antitone.le_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：le_leftLim (h : x <= y) : f y <= leftLim f x
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem le_leftLim (h : x ≤ y) : f y ≤ leftLim f x :=
  hf.dual_right.leftLim_le h
/-
**Antitone.leftLim_le** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：leftLim_le (h : x < y) : leftLim f y <= f x
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_leftLim`：le_leftLim (h : x < y) : f x <= leftLim f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem leftLim_le (h : x < y) : leftLim f y ≤ f x :=
  hf.dual_right.le_leftLim h

@[gcongr, mono]
/-
**Antitone.leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Condition
allyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [OrderTopology β] {f 
: α → β}, Antitone f → Antitone (Function.leftLim f)
参数：Function.leftLim f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.leftLim`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α]
 [inst_1 : ConditionallyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [
OrderT…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
protected theorem leftLim : Antitone (leftLim f) :=
  hf.dual_right.leftLim
/-
**Antitone.rightLim_le** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：rightLim_le (h : x <= y) : rightLim f y <= f x
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_rightLim`：le_rightLim (h : x <= y) : f x <= rightLim f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem rightLim_le (h : x ≤ y) : rightLim f y ≤ f x :=
  hf.dual_right.le_rightLim h
/-
**Antitone.le_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：le_rightLim (h : x < y) : f y <= rightLim f x
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.rightLim_le`：rightLim_le (h : x < y) : rightLim f x <= f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem le_rightLim (h : x < y) : f y ≤ rightLim f x :=
  hf.dual_right.rightLim_le h

@[gcongr, mono]
/-
**Antitone.rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Condition
allyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [OrderTopology β] {f 
: α → β}, Antitone f → Antitone (Function.rightLim f)
参数：Function.rightLim f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.rightLim`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α
] [inst_1 : ConditionallyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] 
[OrderT…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
protected theorem rightLim : Antitone (rightLim f) :=
  hf.dual_right.rightLim
/-
**Antitone.rightLim_le_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：rightLim_le_leftLim (h : x <= y) : rightLim f y <= leftLim f x
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.leftLim_le_rightLim`：leftLim_le_rightLim (h : x <= y) : leftLim
 f x <= rightLim f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem rightLim_le_leftLim (h : x ≤ y) : rightLim f y ≤ leftLim f x :=
  hf.dual_right.leftLim_le_rightLim h
/-
**Antitone.leftLim_le_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：leftLim_le_rightLim (h : x < y) : leftLim f y <= rightLim f x
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.rightLim_le_leftLim`：rightLim_le_leftLim (h : x < y) : rightLim
 f x <= leftLim f y
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem leftLim_le_rightLim (h : x < y) : leftLim f y ≤ rightLim f x :=
  hf.dual_right.rightLim_le_leftLim h

variable [TopologicalSpace α] [OrderTopology α]
/-
**Antitone.tendsto_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_leftLim`：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (
𝓝 (leftLim f x))
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (𝓝 (leftLim f x)) :=
  hf.dual_right.tendsto_leftLim x
/-
**Antitone.tendsto_leftLim_within** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[>=] leftLim f x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_leftLim_within`：tendsto_leftLim_within (x : α) : Tendst
o f (𝓝[<] x) (𝓝[<=] leftLim f x)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem tendsto_leftLim_within (x : α) : Tendsto f (𝓝[<] x) (𝓝[≥] leftLim f x) :=
  hf.dual_right.tendsto_leftLim_within x
/-
**Antitone.tendsto_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_rightLim`：tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x)
 (𝓝 (rightLim f x))
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem tendsto_rightLim (x : α) : Tendsto f (𝓝[>] x) (𝓝 (rightLim f x)) :=
  hf.dual_right.tendsto_rightLim x
/-
**Antitone.tendsto_rightLim_within** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[<=] rightLim f x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_rightLim_within`：tendsto_rightLim_within (x : α) : Tend
sto f (𝓝[>] x) (𝓝[>=] rightLim f x)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem tendsto_rightLim_within (x : α) : Tendsto f (𝓝[>] x) (𝓝[≤] rightLim f x) :=
  hf.dual_right.tendsto_rightLim_within x

/-- An antitone function is continuous to the left at a point if and only if its left limit
coincides with the value of the function. -/
/-
**Antitone.continuousWithinAt_Iio_iff_leftLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `Anti
tone`。
形式化陈述：continuousWithinAt_Iio_iff_leftLim_eq : ContinuousWithinAt f (Iio x) x ↔ l
eftLim f x = f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.continuousWithinAt_Iio_iff_leftLim_eq`：continuousWithinAt_Iio_i
ff_leftLim_eq : ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone function is continuous to the left at a point if and only if its lef
t limit
coincides with the value of the function.
-/
theorem continuousWithinAt_Iio_iff_leftLim_eq :
    ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x :=
  hf.dual_right.continuousWithinAt_Iio_iff_leftLim_eq

/-- An antitone function is continuous to the right at a point if and only if its right limit
coincides with the value of the function. -/
/-
**Antitone.continuousWithinAt_Ioi_iff_rightLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ant
itone`。
形式化陈述：continuousWithinAt_Ioi_iff_rightLim_eq : ContinuousWithinAt f (Ioi x) x ↔ 
rightLim f x = f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.continuousWithinAt_Ioi_iff_rightLim_eq`：continuousWithinAt_Ioi_
iff_rightLim_eq : ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone function is continuous to the right at a point if and only if its ri
ght limit
coincides with the value of the function.
-/
theorem continuousWithinAt_Ioi_iff_rightLim_eq :
    ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x :=
  hf.dual_right.continuousWithinAt_Ioi_iff_rightLim_eq

/-- An antitone function is continuous at a point if and only if its left and right limits
coincide. -/
/-
**Antitone.continuousAt_iff_leftLim_eq_rightLim** 是 Mathlib 中的一个定理，位于命名空间 `Antit
one`。
形式化陈述：continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = ri
ghtLim f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.continuousAt_iff_leftLim_eq_rightLim`：continuousAt_iff_leftLim_
eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)

--- 原说明 ---
An antitone function is continuous at a point if and only if its left and right 
limits
coincide.
-/
theorem continuousAt_iff_leftLim_eq_rightLim : ContinuousAt f x ↔ leftLim f x = rightLim f x :=
  hf.dual_right.continuousAt_iff_leftLim_eq_rightLim

end Antitone

