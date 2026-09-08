/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Control.ULift
public import Mathlib.Logic.Equiv.Basic

/-!
# Extra lemmas about `ULift` and `PLift`

In this file we provide `Subsingleton`, `Unique`, `DecidableEq`, and `isEmpty` instances for
`ULift α` and `PLift α`. We also prove `ULift.forall`, `ULift.exists`, `PLift.forall`, and
`PLift.exists`.
-/

public section

universe u v u' v'

open Function

namespace PLift

variable {α : Sort u} {β : Sort v} {f : α → β}

/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (PLift α) :=
  Equiv.plift.nonempty
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (PLift α) :=
  Equiv.plift.unique
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (PLift α) :=
  Equiv.plift.decidableEq
/-
**PLift.** 是 Mathlib 中的一个实例，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty (PLift α) :=
  Equiv.plift.isEmpty
/-
**PLift.up_injective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：up_injective : Injective (@up α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_injective : Injective (@up α) :=
  Equiv.plift.symm.injective
/-
**PLift.up_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：up_surjective : Surjective (@up α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_surjective : Surjective (@up α) :=
  Equiv.plift.symm.surjective
/-
**PLift.up_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：up_bijective : Bijective (@up α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_bijective : Bijective (@up α) :=
  Equiv.plift.symm.bijective
/-
**PLift.up_inj** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：up_inj {x y : α} : up x = up y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PLift.up.injEq`：∀ {α : Sort u} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem up_inj {x y : α} : up x = up y ↔ x = y := by simp
/-
**PLift.down_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：down_surjective : Surjective (@down α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem down_surjective : Surjective (@down α) :=
  Equiv.plift.surjective
/-
**PLift.down_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：down_bijective : Bijective (@down α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem down_bijective : Bijective (@down α) :=
  Equiv.plift.bijective

-- This is not a good simp lemma, as its discrimination tree key is just an arrow.
/-
**PLift.** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : PLift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (PLift.up x) :=
  up_surjective.forall

@[simp]
/-
**PLift.** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «exists» {p : PLift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (PLift.up x) :=
  up_surjective.exists
/-
**PLift.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f : α → β}, Function.Injective (PLift.map f) 
↔ Function.Injective f
参数：PLift.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `PLift.down_bijective`：down_bijective : Bijective (@down α)
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `PLift.up_injective`：up_injective : Injective (@up α)
-/
@[simp] lemma map_injective : Injective (PLift.map f) ↔ Injective f :=
  (Injective.of_comp_iff' _ down_bijective).trans <| up_injective.of_comp_iff _
/-
**PLift.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f : α → β}, Function.Surjective (PLift.map f)
 ↔ Function.Surjective f
参数：PLift.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Surjective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Surjective g → (Function.Surjective 
(f ∘ g) ↔ Function.Su…
· 使用定理 `PLift.down_surjective`：down_surjective : Surjective (@down α)
· 使用定理 `Function.Surjective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Surjectiv
e (f ∘ g) ↔ Function.S…
· 使用定理 `PLift.up_bijective`：up_bijective : Bijective (@up α)
-/
@[simp] lemma map_surjective : Surjective (PLift.map f) ↔ Surjective f :=
  (down_surjective.of_comp_iff _).trans <| Surjective.of_comp_iff' up_bijective _
/-
**PLift.map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PLift`。
形式化陈述：∀ {α : Sort u} {β : Sort v} {f : α → β}, Function.Bijective (PLift.map f) 
↔ Function.Bijective f
参数：PLift.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `PLift.down_bijective`：down_bijective : Bijective (@down α)
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `PLift.up_bijective`：up_bijective : Bijective (@up α)
-/
@[simp] lemma map_bijective : Bijective (PLift.map f) ↔ Bijective f :=
  (down_bijective.of_comp_iff _).trans <| Bijective.of_comp_iff' up_bijective _

end PLift

namespace ULift

variable {α : Type u} {β : Type v} {f : α → β}

/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (ULift α) :=
  Equiv.ulift.nonempty
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (ULift α) :=
  Equiv.ulift.unique
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (ULift α) :=
  Equiv.ulift.decidableEq
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty (ULift α) :=
  Equiv.ulift.isEmpty
/-
**ULift.up_injective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_injective : Injective (@up α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_injective : Injective (@up α) :=
  Equiv.ulift.symm.injective
/-
**ULift.up_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_surjective : Surjective (@up α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_surjective : Surjective (@up α) :=
  Equiv.ulift.symm.surjective
/-
**ULift.up_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_bijective : Bijective (@up α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem up_bijective : Bijective (@up α) :=
  Equiv.ulift.symm.bijective
/-
**ULift.up_inj** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_inj {x y : α} : up x = up y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ULift.up.injEq`：∀ {α : Type s} (down down_1 : α), ({ down := down } = { 
down := down_1 }) = (down = down_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem up_inj {x y : α} : up x = up y ↔ x = y := by simp
/-
**ULift.down_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_surjective : Surjective (@down α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem down_surjective : Surjective (@down α) :=
  Equiv.ulift.surjective
/-
**ULift.down_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_bijective : Bijective (@down α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem down_bijective : Bijective (@down α) :=
  Equiv.ulift.bijective

@[simp]
/-
**ULift.** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : ULift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ULift.up x) :=
  up_surjective.forall

@[simp]
/-
**ULift.** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «exists» {p : ULift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ULift.up x) :=
  up_surjective.exists
/-
**ULift.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β}, Function.Injective (ULift.map f) 
↔ Function.Injective f
参数：ULift.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `ULift.down_bijective`：down_bijective : Bijective (@down α)
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `ULift.up_injective`：up_injective : Injective (@up α)
-/
@[simp] lemma map_injective : Injective (ULift.map f : ULift.{u'} α → ULift.{v'} β) ↔ Injective f :=
  (Injective.of_comp_iff' _ down_bijective).trans <| up_injective.of_comp_iff _
/-
**ULift.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β}, Function.Surjective (ULift.map f)
 ↔ Function.Surjective f
参数：ULift.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Surjective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Surjective g → (Function.Surjective 
(f ∘ g) ↔ Function.Su…
· 使用定理 `ULift.down_surjective`：down_surjective : Surjective (@down α)
· 使用定理 `Function.Surjective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Surjectiv
e (f ∘ g) ↔ Function.S…
· 使用定理 `ULift.up_bijective`：up_bijective : Bijective (@up α)
-/
@[simp] lemma map_surjective :
    Surjective (ULift.map f : ULift.{u'} α → ULift.{v'} β) ↔ Surjective f :=
  (down_surjective.of_comp_iff _).trans <| Surjective.of_comp_iff' up_bijective _
/-
**ULift.map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β}, Function.Bijective (ULift.map f) 
↔ Function.Bijective f
参数：ULift.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `ULift.down_bijective`：down_bijective : Bijective (@down α)
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `ULift.up_bijective`：up_bijective : Bijective (@up α)
-/
@[simp] lemma map_bijective : Bijective (ULift.map f : ULift.{u'} α → ULift.{v'} β) ↔ Bijective f :=
  (down_bijective.of_comp_iff _).trans <| Bijective.of_comp_iff' up_bijective _

@[ext]
/-
**ULift.ext** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：ext (x y : ULift α) (h : x.down = y.down) : x = y
参数：x y : ULift α；h : x.down = y.down。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ext (x y : ULift α) (h : x.down = y.down) : x = y :=
  congrArg up h

@[simp]
/-
**ULift.rec_update** 是 Mathlib 中的一个引理，位于命名空间 `ULift`。
形式化陈述：rec_update {β : ULift α -> Type*} [DecidableEq α] (f : forall a, β (.up a)
) (a : α) (x : β (.up a)) : ULift.rec (update f a x) = update (ULift.rec f) (.up
 a) x
参数：f : forall a, β (.up a)；a : α；x : β (.up a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.rec_update`：rec_update {ι κ : Sort*} {α : κ -> Sort*} [Decidabl
eEq ι] [DecidableEq κ] {ctor : ι -> κ} (_ : Function.Injective ctor) (recursor :
 ((i : ι)…
· 使用定理 `ULift.up_injective`：up_injective : Injective (@up α)
-/
lemma rec_update {β : ULift α → Type*} [DecidableEq α]
    (f : ∀ a, β (.up a)) (a : α) (x : β (.up a)) :
    ULift.rec (update f a x) = update (ULift.rec f) (.up a) x :=
  Function.rec_update up_injective (ULift.rec ·) (fun _ _ => rfl) (fun
    | _, _, .up _, h => (h _ rfl).elim) _ _ _

end ULift

