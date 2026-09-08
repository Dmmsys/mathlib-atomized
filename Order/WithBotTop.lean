/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kevin Buzzard
-/
module

public import Mathlib.Order.WithBot

/-!
# Adding both `⊥` and `⊤` to a type

This files defines an abbreviation `WithBotTop ι` for `WithBot (WithTop ι)`.
We also introduce an abbreviation `EInt` for `WithBotTop ℤ`.
-/

@[expose] public section

variable {ι : Type*}

variable (ι) in
/-- The type obtained by adding both `⊥` and `⊤` to a type. -/
@[to_dual /-- The type obtained by adding both `⊤` and `⊥` to a type. -/]
/-
**WithBotTop** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：WithBotTop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type obtained by adding both `⊥` and `⊤` to a type.
-/
abbrev WithBotTop := WithBot (WithTop ι)

/-- The canonical inclusion `ι → WithBotTop ι`. Registered as a coercion. -/
/-
**WithBotTop.coe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WithBotTop.coe : ι -> WithBotTop ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `ι → WithBotTop ι`. Registered as a coercion.
-/
def WithBotTop.coe : ι → WithBotTop ι :=
  WithBot.some ∘ WithTop.some

namespace WithBotTop

/-
**WithBotTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithBotTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ι (WithBotTop ι) := ⟨WithBotTop.coe⟩
/-
**WithBotTop.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：coe_injective : Function.Injective (WithBotTop.coe : ι -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_injective : Function.Injective (WithBotTop.coe : ι → _) := by rintro _ _ ⟨⟩; rfl
/-
**WithBotTop.coe_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：∀ {ι : Type u_1} (a : ι), WithBotTop.coe a ≠ ⊥
参数：a : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
@[simp] lemma coe_ne_bot (a : ι) : (a : WithBotTop ι) ≠ ⊥ := by rintro ⟨⟩
/-
**WithBotTop.coe_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：∀ {ι : Type u_1} (a : ι), WithBotTop.coe a ≠ ⊤
参数：a : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] lemma coe_ne_top (a : ι) : (a : WithBotTop ι) ≠ ⊤ := by rintro ⟨⟩
/-
**WithBotTop.top_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：∀ {ι : Type u_1}, ⊤ ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
@[simp] lemma top_ne_bot : (⊤ : WithBotTop ι) ≠ ⊥ := by rintro ⟨⟩

section

variable {motive : (WithBotTop ι) → Sort*}
  (bot : motive ⊥) (coe : ∀ a : ι, motive a) (top : motive ⊤)

/-- A recursor for `WithBotTop` in terms of the coercion. -/
@[elab_as_elim]
/-
**WithBotTop.rec** 是 Mathlib 中的一个定义，位于命名空间 `WithBotTop`。
形式化陈述：{ι : Type u_1} →   {motive : WithBotTop ι → Sort u_2} →     motive ⊥ → ((a
 : ι) → motive (WithBotTop.coe a)) → motive ⊤ → (a : WithBotTop ι) → motive a
参数：(a : ι) → motive (WithBotTop.coe a)；a : WithBotTop ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `WithBotTop` in terms of the coercion.
-/
protected def rec : ∀ a, motive a
  | ⊥ => bot
  | (a : ι) => coe a
  | ⊤ => top
/-
**WithBotTop.rec_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：∀ {ι : Type u_1} {motive : WithBotTop ι → Sort u_2} (bot : motive ⊥) (coe 
: (a : ι) → motive (WithBotTop.coe a))   (top : motive ⊤), WithBotTop.rec bot co
e top ⊥ = bot
参数：bot : motive ⊥；coe : (a : ι) → motive (WithBotTop.coe a)；top : motive ⊤。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rec_bot : WithBotTop.rec (motive := motive) bot coe top ⊥ = bot := rfl
/-
**WithBotTop.rec_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：∀ {ι : Type u_1} {motive : WithBotTop ι → Sort u_2} (bot : motive ⊥) (coe 
: (a : ι) → motive (WithBotTop.coe a))   (top : motive ⊤) (a : ι), WithBotTop.re
c bot coe top (WithBotTop.coe a) = coe a
参数：bot : motive ⊥；coe : (a : ι) → motive (WithBotTop.coe a)；top : motive ⊤；a : ι
；WithBotTop.coe a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rec_coe (a : ι) : WithBotTop.rec (motive := motive) bot coe top a = coe a := rfl
/-
**WithBotTop.rec_top** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：∀ {ι : Type u_1} {motive : WithBotTop ι → Sort u_2} (bot : motive ⊥) (coe 
: (a : ι) → motive (WithBotTop.coe a))   (top : motive ⊤), WithBotTop.rec bot co
e top ⊤ = top
参数：bot : motive ⊥；coe : (a : ι) → motive (WithBotTop.coe a)；top : motive ⊤。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rec_top : WithBotTop.rec (motive := motive) bot coe top ⊤ = top := rfl

end

@[simp]
/-
**WithBotTop.coe_le_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBotTop`。
形式化陈述：coe_le_coe [LE ι] {a b : ι} : (a : WithBotTop ι) <= b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
lemma coe_le_coe [LE ι] {a b : ι} :
    (a : WithBotTop ι) ≤ b ↔ a ≤ b := by
  rw [← WithTop.coe_le_coe (α := ι)]
  exact WithBot.coe_le_coe

@[simp]
/-
**WithBotTop.coe_lt_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithBotTop`。
形式化陈述：coe_lt_coe [LT ι] {a b : ι} : (a : WithBotTop ι) < b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
-/
lemma coe_lt_coe [LT ι] {a b : ι} :
    (a : WithBotTop ι) < b ↔ a < b := by
  rw [← WithTop.coe_lt_coe (α := ι)]
  exact WithBot.coe_lt_coe

@[simp]
/-
**WithBotTop.coe_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithBotTop`。
形式化陈述：coe_strictMono [Preorder ι] : StrictMono (WithBotTop.coe : ι -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `WithBot.coe_strictMono`：coe_strictMono : StrictMono (fun (a : α) => (a :
 WithBot α))
· 使用定理 `WithTop.coe_strictMono`：∀ {α : Type u_1} [inst : Preorder α], StrictMono
 fun a => ↑a
-/
theorem coe_strictMono [Preorder ι] : StrictMono (WithBotTop.coe : ι → _) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono
/-
**WithBotTop.coe_monotone** 是 Mathlib 中的一个引理，位于命名空间 `WithBotTop`。
形式化陈述：coe_monotone [Preorder ι] : Monotone (WithBotTop.coe : ι -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_monotone [Preorder ι] :
    Monotone (WithBotTop.coe : ι → _) :=
  fun _ _ _ ↦ by simpa

end WithBotTop

/-- The type of extended integers `[-∞, ∞]`, constructed as `WithBot (WithTop ℤ)`. -/
/-
**EInt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EInt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of extended integers `[-∞, ∞]`, constructed as `WithBot (WithTop ℤ)`.
-/
abbrev EInt := WithBotTop ℤ
