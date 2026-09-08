/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.ENNReal.Operations

/-!
# The extended real numbers

This file defines `EReal`, `ℝ` with a top element `⊤` and a bottom element `⊥`, implemented as
`WithBot (WithTop ℝ)`.

`EReal` is a `CompleteLinearOrder`, deduced by typeclass inference from the fact that
`WithBot (WithTop L)` completes a conditionally complete linear order `L`.

Coercions from `ℝ` (called `coe` in lemmas) and from `ℝ≥0∞` (`coe_ennreal`) are registered
and their basic properties proved. The latter takes up most of the rest of this file.

## Tags

real, ereal, complete lattice
-/

@[expose] public section

open Function ENNReal NNReal Set

noncomputable section

/-- The type of extended real numbers `[-∞, ∞]`, constructed as `WithBot (WithTop ℝ)`. -/
@[wikidata Q2039387]
/-
**EReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of extended real numbers `[-∞, ∞]`, constructed as `WithBot (WithTop ℝ)
`.
-/
def EReal := WithBot (WithTop ℝ)
deriving Nontrivial,
  Zero, One, AddMonoid, AddCommMonoid, AddCommMonoidWithOne, CharZero,
  Top, Bot, SupSet, InfSet, PartialOrder, LinearOrder, CompleteLinearOrder, DenselyOrdered,
  ZeroLEOneClass, IsOrderedAddMonoid

/-- The canonical inclusion from reals to ereals. Registered as a coercion. -/
/-
**Real.toEReal** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：ℝ → EReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from reals to ereals. Registered as a coercion.
-/
@[coe] def Real.toEReal : ℝ → EReal := WithBot.some ∘ WithTop.some

namespace EReal

/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ℝ EReal := ⟨Real.toEReal⟩
/-
**EReal.coe_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_strictMono : StrictMono Real.toEReal
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
theorem coe_strictMono : StrictMono Real.toEReal :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono
/-
**EReal.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_injective : Injective Real.toEReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `EReal.coe_strictMono`：coe_strictMono : StrictMono Real.toEReal
-/
theorem coe_injective : Injective Real.toEReal :=
  coe_strictMono.injective

@[simp, norm_cast]
/-
**EReal.coe_le_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `EReal.coe_strictMono`：coe_strictMono : StrictMono Real.toEReal
-/
protected theorem coe_le_coe_iff {x y : ℝ} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := EReal.coe_le_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_lt_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `EReal.coe_strictMono`：coe_strictMono : StrictMono Real.toEReal
-/
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := EReal.coe_lt_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_eq_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x y : ℝ}, ↑x = ↑y ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `EReal.coe_injective`：coe_injective : Injective Real.toEReal
-/
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff
/-
**EReal.coe_ne_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x y : ℝ}, ↑x ≠ ↑y ↔ x ≠ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `EReal.coe_injective`：coe_injective : Injective Real.toEReal
-/
protected theorem coe_ne_coe_iff {x y : ℝ} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
/-
**EReal.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {n : ℕ}, ↑↑n = ↑n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_natCast {n : ℕ} : ((n : ℝ) : EReal) = n := rfl

/-- The order embedding of `ℝ` into `EReal`. -/
/-
**EReal.orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：orderEmbedding : Real ↪o EReal where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_injective`：coe_injective : Injective Real.toEReal

--- 原说明 ---
The order embedding of `ℝ` into `EReal`.
-/
def orderEmbedding : ℝ ↪o EReal where
  toFun := Real.toEReal
  inj' := EReal.coe_injective
  map_rel_iff' {x y} := by simp
/-
**EReal.coe_orderEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_orderEmbedding : ⇑orderEmbedding = Real.toEReal
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_orderEmbedding : ⇑orderEmbedding = Real.toEReal := rfl

/-- The canonical map from nonnegative extended reals to extended reals. -/
/-
**EReal._root_.ENNReal.toEReal** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from nonnegative extended reals to extended reals.
-/
@[coe] def _root_.ENNReal.toEReal : ℝ≥0∞ → EReal
  | ⊤ => ⊤
  | .some x => x.1
/-
**EReal.hasCoeENNReal** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
形式化陈述：hasCoeENNReal : Coe Real>=0∞ EReal
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeENNReal : Coe ℝ≥0∞ EReal :=
  ⟨ENNReal.toEReal⟩
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited EReal := ⟨0⟩

@[simp, norm_cast]
/-
**EReal.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_zero : ((0 : Real) : EReal) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : ℝ) : EReal) = 0 := rfl

@[simp, norm_cast]
/-
**EReal.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_one : ((1 : Real) : EReal) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : ℝ) : EReal) = 1 := rfl

/-- A recursor for `EReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly,
although this is prone to leaking the implementation details in terms of `Option`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**EReal.rec** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：{motive : EReal → Sort u_1} → motive ⊥ → ((a : ℝ) → motive ↑a) → motive ⊤ 
→ (a : EReal) → motive a
参数：(a : ℝ) → motive ↑a；a : EReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `EReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly,
although this is prone to leaking the implementation details in terms of `Option
`.
-/
protected def rec {motive : EReal → Sort*}
    (bot : motive ⊥) (coe : ∀ a : ℝ, motive a) (top : motive ⊤) : ∀ a : EReal, motive a
  | ⊥ => bot
  | (a : ℝ) => coe a
  | ⊤ => top
/-
**EReal.rec_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {motive : EReal → Sort u_1} (bot : motive ⊥) (coe : (a : ℝ) → motive ↑a)
 (top : motive ⊤),   EReal.rec bot coe top ⊥ = bot
参数：bot : motive ⊥；coe : (a : ℝ) → motive ↑a；top : motive ⊤。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rec_bot {motive : EReal → Sort*}
    (bot : motive ⊥) (coe : ∀ a : ℝ, motive a) (top : motive ⊤) : EReal.rec bot coe top ⊥ = bot :=
  rfl
/-
**EReal.rec_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {motive : EReal → Sort u_1} (bot : motive ⊥) (coe : (a : ℝ) → motive ↑a)
 (top : motive ⊤),   EReal.rec bot coe top ⊤ = top
参数：bot : motive ⊥；coe : (a : ℝ) → motive ↑a；top : motive ⊤。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rec_top {motive : EReal → Sort*}
    (bot : motive ⊥) (coe : ∀ a : ℝ, motive a) (top : motive ⊤) : EReal.rec bot coe top ⊤ = top :=
  rfl
/-
**EReal.rec_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {motive : EReal → Sort u_1} (bot : motive ⊥) (coe : (a : ℝ) → motive ↑a)
 (top : motive ⊤) (a : ℝ),   EReal.rec bot coe top ↑a = coe a
参数：bot : motive ⊥；coe : (a : ℝ) → motive ↑a；top : motive ⊤；a : ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rec_coe {motive : EReal → Sort*}
    (bot : motive ⊥) (coe : ∀ a : ℝ, motive a) (top : motive ⊤) (a : ℝ) :
    EReal.rec bot coe top a = coe a := rfl
/-
**EReal.** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «forall» {p : EReal → Prop} : (∀ r, p r) ↔ p ⊥ ∧ p ⊤ ∧ ∀ r : ℝ, p r where
  mp h := ⟨h _, h _, fun _ ↦ h _⟩
  mpr h := EReal.rec h.1 h.2.2 h.2.1
/-
**EReal.** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «exists» {p : EReal → Prop} : (∃ r, p r) ↔ p ⊥ ∨ p ⊤ ∨ ∃ r : ℝ, p r where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

/-- The multiplication on `EReal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
/-
**EReal.mul** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：EReal → EReal → EReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication on `EReal`. Our definition satisfies `0 * x = x * 0 = 0` for 
any `x`, and
picks the only sensible value elsewhere.
-/
protected def mul : EReal → EReal → EReal
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : ℝ) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : ℝ) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : ℝ), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : ℝ), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : ℝ), (y : ℝ) => (x * y : ℝ)
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul EReal := ⟨EReal.mul⟩

@[simp, norm_cast]
/-
**EReal.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : ℝ) : (↑(x * y) : EReal) = x * y :=
  rfl

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
/-
**EReal.induction** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induct on two `EReal`s by performing case splits on the sign of one whenever the
 other is
infinite.
-/
theorem induction₂ {P : EReal → EReal → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : ℝ, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : ℝ, x < 0 → P x ⊤)
    (neg_bot : ∀ x : ℝ, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : ℝ, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : ℝ, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : ℝ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : ℝ), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : ℝ), (y : ℝ) => coe_coe _ _
  | (x : ℝ), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℝ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
/-
**EReal.induction** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induct on two `EReal`s by performing case splits on the sign of one whenever the
 other is
infinite. This version eliminates some cases by assuming that the relation is sy
mmetric.
-/
theorem induction₂_symm {P : EReal → EReal → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℝ, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : ℝ, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot
/-
**EReal.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x y : EReal), x * y = y * x
参数：x y : EReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
protected theorem mul_comm (x y : EReal) : x * y = y * x := by
  induction x <;> induction y <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]
/-
**EReal.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), 1 * x = x
参数：x : EReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem one_mul : ∀ x : EReal, 1 * x = x
  | ⊤ => if_pos one_pos
  | ⊥ => if_pos one_pos
  | (x : ℝ) => congr_arg Real.toEReal (one_mul x)
/-
**EReal.zero_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), 0 * x = 0
参数：x : EReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected theorem zero_mul : ∀ x : EReal, 0 * x = 0
  | ⊤ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | ⊥ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | (x : ℝ) => congr_arg Real.toEReal (zero_mul x)
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulZeroOneClass EReal where
  one_mul := EReal.one_mul
  mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]

/-! ### Real coercion -/

/-
**EReal.canLift** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
形式化陈述：canLift : CanLift EReal Real (↑) fun r => r != ⊤ ∧ r != ⊥ where prf x hx
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
### Real coercion
-/
instance canLift : CanLift EReal ℝ (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x
    · simp at hx
    · simp
    · simp at hx

/-- The map from extended reals to reals sending infinities to zero. -/
/-
**EReal.toReal** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：EReal → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from extended reals to reals sending infinities to zero.
-/
def toReal : EReal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x

@[simp]
/-
**EReal.toReal_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_top : toReal ⊤ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_top : toReal ⊤ = 0 :=
  rfl

@[simp]
/-
**EReal.toReal_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_bot : toReal ⊥ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_bot : toReal ⊥ = 0 :=
  rfl

@[simp]
/-
**EReal.toReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_zero : toReal 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_zero : toReal 0 = 0 :=
  rfl

@[simp]
/-
**EReal.toReal_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_one : toReal 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_one : toReal 1 = 1 :=
  rfl

@[simp]
/-
**EReal.toReal_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_coe (x : Real) : toReal (x : EReal) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_coe (x : ℝ) : toReal (x : EReal) = x :=
  rfl

@[simp]
/-
**EReal.bot_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_lt_coe (x : Real) : (⊥ : EReal) < x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
-/
theorem bot_lt_coe (x : ℝ) : (⊥ : EReal) < x :=
  WithBot.bot_lt_coe _

@[simp]
/-
**EReal.coe_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ne_bot (x : Real) : (x : EReal) != ⊥
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
-/
theorem coe_ne_bot (x : ℝ) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
/-
**EReal.bot_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_ne_coe (x : Real) : (⊥ : EReal) != x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
-/
theorem bot_ne_coe (x : ℝ) : (⊥ : EReal) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
/-
**EReal.coe_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_lt_top (x : Real) : (x : EReal) < ⊤
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem coe_lt_top (x : ℝ) : (x : EReal) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
/-
**EReal.coe_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ne_top (x : Real) : (x : EReal) != ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
-/
theorem coe_ne_top (x : ℝ) : (x : EReal) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
/-
**EReal.top_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_ne_coe (x : Real) : (⊤ : EReal) != x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
-/
theorem top_ne_coe (x : ℝ) : (⊤ : EReal) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
/-
**EReal.bot_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_lt_zero : (⊥ : EReal) < 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
-/
theorem bot_lt_zero : (⊥ : EReal) < 0 :=
  bot_lt_coe 0

@[simp]
/-
**EReal.bot_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_ne_zero : (⊥ : EReal) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `EReal.coe_ne_bot`：coe_ne_bot (x : Real) : (x : EReal) != ⊥
-/
theorem bot_ne_zero : (⊥ : EReal) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
/-
**EReal.zero_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：zero_ne_bot : (0 : EReal) != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_ne_bot`：coe_ne_bot (x : Real) : (x : EReal) != ⊥
-/
theorem zero_ne_bot : (0 : EReal) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
/-
**EReal.zero_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：zero_lt_top : (0 : EReal) < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
-/
theorem zero_lt_top : (0 : EReal) < ⊤ :=
  coe_lt_top 0

@[simp]
/-
**EReal.zero_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：zero_ne_top : (0 : EReal) != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_ne_top`：coe_ne_top (x : Real) : (x : EReal) != ⊤
-/
theorem zero_ne_top : (0 : EReal) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
/-
**EReal.top_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：top_ne_zero : (⊤ : EReal) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `EReal.coe_ne_top`：coe_ne_top (x : Real) : (x : EReal) != ⊤
-/
theorem top_ne_zero : (⊤ : EReal) ≠ 0 :=
  (coe_ne_top 0).symm
/-
**EReal.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：range_coe : range Real.toEReal = {⊥, ⊤}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem range_coe : range Real.toEReal = {⊥, ⊤}ᶜ := by
  ext x
  induction x <;> simp
/-
**EReal.range_coe_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤ := by
  ext x
  induction x <;> simp

@[simp, norm_cast]
/-
**EReal.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_add (x y : Real) : (↑(x + y) : EReal) = x + y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : ℝ) : (↑(x + y) : EReal) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
/-
**EReal.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_nsmul (n : Nat) (x : Real) : (↑(n • x) : EReal) = n • (x : EReal)
参数：n : Nat；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `EReal.coe_zero`：coe_zero : ((0 : Real) : EReal) = 0
· 使用定理 `EReal.coe_add`：coe_add (x y : Real) : (↑(x + y) : EReal) = x + y
-/
theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : ℝ →+ EReal) _ _

@[simp, norm_cast]
/-
**EReal.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_eq_zero {x : Real} : (x : EReal) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_eq_coe_iff`：∀ {x y : ℝ}, ↑x = ↑y ↔ x = y
-/
theorem coe_eq_zero {x : ℝ} : (x : EReal) = 0 ↔ x = 0 :=
  EReal.coe_eq_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_eq_one {x : Real} : (x : EReal) = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_eq_coe_iff`：∀ {x y : ℝ}, ↑x = ↑y ↔ x = y
-/
theorem coe_eq_one {x : ℝ} : (x : EReal) = 1 ↔ x = 1 :=
  EReal.coe_eq_coe_iff
/-
**EReal.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ne_zero {x : Real} : (x : EReal) != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_ne_coe_iff`：∀ {x y : ℝ}, ↑x ≠ ↑y ↔ x ≠ y
-/
theorem coe_ne_zero {x : ℝ} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  EReal.coe_ne_coe_iff
/-
**EReal.coe_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ne_one {x : Real} : (x : EReal) != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_ne_coe_iff`：∀ {x y : ℝ}, ↑x ≠ ↑y ↔ x ≠ y
-/
theorem coe_ne_one {x : ℝ} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  EReal.coe_ne_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : ℝ}, 0 ≤ ↑x ↔ 0 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
-/
protected theorem coe_nonneg {x : ℝ} : (0 : EReal) ≤ x ↔ 0 ≤ x :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : ℝ}, ↑x ≤ 0 ↔ x ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
-/
protected theorem coe_nonpos {x : ℝ} : (x : EReal) ≤ 0 ↔ x ≤ 0 :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
-/
protected theorem coe_pos {x : ℝ} : (0 : EReal) < x ↔ 0 < x :=
  EReal.coe_lt_coe_iff

@[simp, norm_cast]
/-
**EReal.coe_neg'** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : ℝ}, ↑x < 0 ↔ x < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
-/
protected theorem coe_neg' {x : ℝ} : (x : EReal) < 0 ↔ x < 0 :=
  EReal.coe_lt_coe_iff
/-
**EReal.toReal_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  cases x <;> norm_num
/-
**EReal.toReal_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_ne_zero_iff {x : EReal} : x.toReal != 0 ↔ x != 0 ∧ x != ⊤ ∧ x != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toReal_ne_zero_iff {x : EReal} : x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  simp only [ne_eq, toReal_eq_zero_iff, not_or]
/-
**EReal.toReal_eq_toReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_eq_toReal {x y : EReal} (hx_top : x != ⊤) (hx_bot : x != ⊥) (hy_top
 : y != ⊤) (hy_bot : y != ⊥) : x.toReal = y.toReal ↔ x = y
参数：hx_top : x != ⊤；hx_bot : x != ⊥；hy_top : y != ⊤；hy_bot : y != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toReal_eq_toReal {x y : EReal} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥)
    (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x.toReal = y.toReal ↔ x = y := by
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  lift y to ℝ using ⟨hy_top, hy_bot⟩
  simp
/-
**EReal.toReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_nonneg {x : EReal} (hx : 0 <= x) : 0 <= x.toReal
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_nonneg`：∀ {x : ℝ}, 0 ≤ ↑x ↔ 0 ≤ x
· 使用定理 `EReal.toReal_coe`：toReal_coe (x : Real) : toReal (x : EReal) = x
-/
lemma toReal_nonneg {x : EReal} (hx : 0 ≤ x) : 0 ≤ x.toReal := by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · simp
/-
**EReal.toReal_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_nonpos {x : EReal} (hx : x <= 0) : x.toReal <= 0
参数：hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_nonpos`：∀ {x : ℝ}, ↑x ≤ 0 ↔ x ≤ 0
· 使用定理 `EReal.toReal_coe`：toReal_coe (x : Real) : toReal (x : EReal) = x
-/
lemma toReal_nonpos {x : EReal} (hx : x ≤ 0) : x.toReal ≤ 0 := by
  cases x
  · simp
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · simp
/-
**EReal.toReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_pos {x : EReal} (hx : 0 < x) (h'x : x != ⊤) : 0 < x.toReal
参数：hx : 0 < x；h'x : x != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toReal_pos {x : EReal} (hx : 0 < x) (h'x : x ≠ ⊤) : 0 < x.toReal := by
  lift x to ℝ using by aesop
  simpa using hx
/-
**EReal.toReal_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_neg {x : EReal} (hx : x < 0) (h'x : x != ⊥) : x.toReal < 0
参数：hx : x < 0；h'x : x != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toReal_neg {x : EReal} (hx : x < 0) (h'x : x ≠ ⊥) : x.toReal < 0 := by
  lift x to ℝ using by aesop
  simpa using hx
/-
**EReal.toReal_image_Ioo_zero_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：EReal.toReal '' Set.Ioo 0 ⊤ = Set.Ioi 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toReal_image_Ioo_zero_top : toReal '' (Ioo 0 ⊤) = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy0, _⟩, rfl⟩
    lift y to ℝ using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx
/-
**EReal.toReal_image_Ioo_bot_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：EReal.toReal '' Set.Ioo ⊥ 0 = Set.Iio 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
@[simp] lemma toReal_image_Ioo_bot_zero : toReal '' (Ioo ⊥ 0) = Iio 0 := by
  ext x
  constructor
  · rintro ⟨y, ⟨_, hy0⟩, rfl⟩
    lift y to ℝ using by aesop
    simpa using hy0
  · intro hx
    use (x : EReal)
    simpa using hx
/-
**EReal.toReal_le_toReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：toReal_le_toReal {x y : EReal} (h : x <= y) (hx : x != ⊥) (hy : y != ⊤) : 
x.toReal <= y.toReal
参数：h : x <= y；hx : x != ⊥；hy : y != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
-/
theorem toReal_le_toReal {x y : EReal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toReal ≤ y.toReal := by
  lift x to ℝ using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to ℝ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h
/-
**EReal.coe_toReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : (x.toReal : EReal) =
 x
参数：hx : x != ⊤；h'x : x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x := by
  lift x to ℝ using ⟨hx, h'x⟩
  rfl
/-
**EReal.le_coe_toReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：le_coe_toReal {x : EReal} (h : x != ⊤) : x <= x.toReal
参数：h : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
-/
theorem le_coe_toReal {x : EReal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toReal h h']
/-
**EReal.coe_toReal_le** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_toReal_le {x : EReal} (h : x != ⊥) : ↑x.toReal <= x
参数：h : x != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
-/
theorem coe_toReal_le {x : EReal} (h : x ≠ ⊥) : ↑x.toReal ≤ x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toReal h' h]
/-
**EReal.eq_top_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ forall y : Real, (y : EReal) < 
x
参数：x : EReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EReal.le_coe_toReal`：le_coe_toReal {x : EReal} (h : x != ⊤) : x <= x.toR
eal
-/
theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ ∀ y : ℝ, (y : EReal) < x := by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩
/-
**EReal.eq_bot_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ forall y : Real, x < (y : EReal
)
参数：x : EReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EReal.coe_toReal_le`：coe_toReal_le {x : EReal} (h : x != ⊥) : ↑x.toReal 
<= x
-/
theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ ∀ y : ℝ, x < (y : EReal) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toReal, coe_toReal_le h⟩

/-! ### Intervals and coercion from reals -/

/-
**EReal.exists_between_coe_real** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exists_between_coe_real {x z : EReal} (h : x < z) : exists y : Real, x < y
 ∧ y < z
参数：h : x < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a

--- 原说明 ---
### Intervals and coercion from reals
-/
lemma exists_between_coe_real {x z : EReal} (h : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | bot => exact (not_lt_bot ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

@[simp]
/-
**EReal.image_coe_Icc** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Icc (x y : Real) : Real.toEReal '' Icc x y = Icc ↑x ↑y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Icc`：image_coe_Icc : (some : α -> WithTop α) '' Icc a 
b = Icc (a : WithTop α) b
· 使用定理 `WithBot.image_coe_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, W
ithBot.some '' Set.Icc b a = Set.Icc ↑b ↑a
-/
lemma image_coe_Icc (x y : ℝ) : Real.toEReal '' Icc x y = Icc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
  rfl

@[simp]
/-
**EReal.image_coe_Ico** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Ico (x y : Real) : Real.toEReal '' Ico x y = Ico ↑x ↑y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Ico`：image_coe_Ico : (some : α -> WithTop α) '' Ico a 
b = Ico (a : WithTop α) b
· 使用定理 `WithBot.image_coe_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, W
ithBot.some '' Set.Ico b a = Set.Ico ↑b ↑a
-/
lemma image_coe_Ico (x y : ℝ) : Real.toEReal '' Ico x y = Ico ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
  rfl

@[simp]
/-
**EReal.image_coe_Ici** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Ici (x : Real) : Real.toEReal '' Ici x = Ico ↑x ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Ici`：image_coe_Ici : (some : α -> WithTop α) '' Ici a 
= Ico (a : WithTop α) ⊤
· 使用定理 `WithBot.image_coe_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, W
ithBot.some '' Set.Ico b a = Set.Ico ↑b ↑a
-/
lemma image_coe_Ici (x : ℝ) : Real.toEReal '' Ici x = Ico ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici, WithBot.image_coe_Ico]
  rfl

@[simp]
/-
**EReal.image_coe_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Ioc (x y : Real) : Real.toEReal '' Ioc x y = Ioc ↑x ↑y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Ioc`：image_coe_Ioc : (some : α -> WithTop α) '' Ioc a 
b = Ioc (a : WithTop α) b
· 使用定理 `WithBot.image_coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, W
ithBot.some '' Set.Ioc b a = Set.Ioc ↑b ↑a
-/
lemma image_coe_Ioc (x y : ℝ) : Real.toEReal '' Ioc x y = Ioc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc, WithBot.image_coe_Ioc]
  rfl

@[simp]
/-
**EReal.image_coe_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Ioo (x y : Real) : Real.toEReal '' Ioo x y = Ioo ↑x ↑y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Ioo`：image_coe_Ioo : (some : α -> WithTop α) '' Ioo a 
b = Ioo (a : WithTop α) b
· 使用定理 `WithBot.image_coe_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, W
ithBot.some '' Set.Ioo b a = Set.Ioo ↑b ↑a
-/
lemma image_coe_Ioo (x y : ℝ) : Real.toEReal '' Ioo x y = Ioo ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo, WithBot.image_coe_Ioo]
  rfl

@[simp]
/-
**EReal.image_coe_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Ioi (x : Real) : Real.toEReal '' Ioi x = Ioo ↑x ⊤
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Ioi`：image_coe_Ioi : (some : α -> WithTop α) '' Ioi a 
= Ioo (a : WithTop α) ⊤
· 使用定理 `WithBot.image_coe_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, W
ithBot.some '' Set.Ioo b a = Set.Ioo ↑b ↑a
-/
lemma image_coe_Ioi (x : ℝ) : Real.toEReal '' Ioi x = Ioo ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi, WithBot.image_coe_Ioo]
  rfl

@[simp]
/-
**EReal.image_coe_Iic** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Iic (x : Real) : Real.toEReal '' Iic x = Ioc ⊥ ↑x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Iic`：image_coe_Iic : (some : α -> WithTop α) '' Iic a 
= Iic (a : WithTop α)
· 使用定理 `WithBot.image_coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Wit
hBot.some '' Set.Iic a = Set.Ioc ⊥ ↑a
-/
lemma image_coe_Iic (x : ℝ) : Real.toEReal '' Iic x = Ioc ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic, WithBot.image_coe_Iic]
  rfl

@[simp]
/-
**EReal.image_coe_Iio** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：image_coe_Iio (x : Real) : Real.toEReal '' Iio x = Ioo ⊥ ↑x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.image_coe_Iio`：image_coe_Iio : (some : α -> WithTop α) '' Iio a 
= Iio (a : WithTop α)
· 使用定理 `WithBot.image_coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Wit
hBot.some '' Set.Iio a = Set.Ioo ⊥ ↑a
-/
lemma image_coe_Iio (x : ℝ) : Real.toEReal '' Iio x = Ioo ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio, WithBot.image_coe_Iio]
  rfl

@[simp]
/-
**EReal.preimage_coe_Ici** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ici (x : Real) : Real.toEReal ⁻¹' Ici x = Ici x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.preimage_coe_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, 
WithBot.some ⁻¹' Set.Ici ↑a = Set.Ici a
· 使用定理 `WithTop.preimage_coe_Ici`：preimage_coe_Ici : (some : α -> WithTop α) ⁻¹'
 Ici a = Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ici (x : ℝ) : Real.toEReal ⁻¹' Ici x = Ici x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]
/-
**EReal.preimage_coe_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioi (x : Real) : Real.toEReal ⁻¹' Ioi x = Ioi x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.preimage_coe_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, 
WithBot.some ⁻¹' Set.Ioi ↑a = Set.Ioi a
· 使用定理 `WithTop.preimage_coe_Ioi`：preimage_coe_Ioi : (some : α -> WithTop α) ⁻¹'
 Ioi a = Ioi a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioi (x : ℝ) : Real.toEReal ⁻¹' Ioi x = Ioi x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]
/-
**EReal.preimage_coe_Ioi_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi ⊥ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.preimage_coe_Ioi_bot`：∀ {α : Type u_1} [inst : Preorder α], With
Bot.some ⁻¹' Set.Ioi ⊥ = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi ⊥ = univ := by
  change ((WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (⊥ : WithBot (WithTop ℝ))) : Set ℝ) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]
/-
**EReal.preimage_coe_Iic** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Iic (y : Real) : Real.toEReal ⁻¹' Iic y = Iic y
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.preimage_coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, 
WithBot.some ⁻¹' Set.Iic ↑a = Set.Iic a
· 使用定理 `WithTop.preimage_coe_Iic`：preimage_coe_Iic : (some : α -> WithTop α) ⁻¹'
 Iic a = Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Iic (y : ℝ) : Real.toEReal ⁻¹' Iic y = Iic y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]
/-
**EReal.preimage_coe_Iio** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Iio (y : Real) : Real.toEReal ⁻¹' Iio y = Iio y
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.preimage_coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, 
WithBot.some ⁻¹' Set.Iio ↑a = Set.Iio a
· 使用定理 `WithTop.preimage_coe_Iio`：preimage_coe_Iio : (some : α -> WithTop α) ⁻¹'
 Iio a = Iio a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Iio (y : ℝ) : Real.toEReal ⁻¹' Iio y = Iio y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]
/-
**EReal.preimage_coe_Iio_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio ⊤ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithBot.preimage_coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, 
WithBot.some ⁻¹' Set.Iio ↑a = Set.Iio a
· 使用定理 `WithTop.preimage_coe_Iio_top`：preimage_coe_Iio_top : (some : α -> WithTo
p α) ⁻¹' Iio ⊤ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio ⊤ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (⊤ : WithTop ℝ))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]
/-
**EReal.preimage_coe_Icc** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Icc (x y : Real) : Real.toEReal ⁻¹' Icc x y = Icc x y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ici`：preimage_coe_Ici (x : Real) : Real.toEReal ⁻¹' I
ci x = Ici x
· 使用引理 `EReal.preimage_coe_Iic`：preimage_coe_Iic (y : Real) : Real.toEReal ⁻¹' I
ic y = Iic y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Icc (x y : ℝ) : Real.toEReal ⁻¹' Icc x y = Icc x y := by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]
/-
**EReal.preimage_coe_Ico** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ico (x y : Real) : Real.toEReal ⁻¹' Ico x y = Ico x y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ici`：preimage_coe_Ici (x : Real) : Real.toEReal ⁻¹' I
ci x = Ici x
· 使用引理 `EReal.preimage_coe_Iio`：preimage_coe_Iio (y : Real) : Real.toEReal ⁻¹' I
io y = Iio y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ico (x y : ℝ) : Real.toEReal ⁻¹' Ico x y = Ico x y := by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]
/-
**EReal.preimage_coe_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioc (x y : Real) : Real.toEReal ⁻¹' Ioc x y = Ioc x y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ioi`：preimage_coe_Ioi (x : Real) : Real.toEReal ⁻¹' I
oi x = Ioi x
· 使用引理 `EReal.preimage_coe_Iic`：preimage_coe_Iic (y : Real) : Real.toEReal ⁻¹' I
ic y = Iic y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioc (x y : ℝ) : Real.toEReal ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]
/-
**EReal.preimage_coe_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioo (x y : Real) : Real.toEReal ⁻¹' Ioo x y = Ioo x y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ioi`：preimage_coe_Ioi (x : Real) : Real.toEReal ⁻¹' I
oi x = Ioi x
· 使用引理 `EReal.preimage_coe_Iio`：preimage_coe_Iio (y : Real) : Real.toEReal ⁻¹' I
io y = Iio y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioo (x y : ℝ) : Real.toEReal ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]
/-
**EReal.preimage_coe_Ico_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ico_top (x : Real) : Real.toEReal ⁻¹' Ico x ⊤ = Ici x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ici`：preimage_coe_Ici (x : Real) : Real.toEReal ⁻¹' I
ci x = Ici x
· 使用引理 `EReal.preimage_coe_Iio_top`：preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio 
⊤ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ico_top (x : ℝ) : Real.toEReal ⁻¹' Ico x ⊤ = Ici x := by
  rw [← Ici_inter_Iio]
  simp

@[simp]
/-
**EReal.preimage_coe_Ioo_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioo_top (x : Real) : Real.toEReal ⁻¹' Ioo x ⊤ = Ioi x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ioi`：preimage_coe_Ioi (x : Real) : Real.toEReal ⁻¹' I
oi x = Ioi x
· 使用引理 `EReal.preimage_coe_Iio_top`：preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio 
⊤ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioo_top (x : ℝ) : Real.toEReal ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
/-
**EReal.preimage_coe_Ioc_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioc_bot (y : Real) : Real.toEReal ⁻¹' Ioc ⊥ y = Iic y
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ioi_bot`：preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi 
⊥ = univ
· 使用引理 `EReal.preimage_coe_Iic`：preimage_coe_Iic (y : Real) : Real.toEReal ⁻¹' I
ic y = Iic y
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioc_bot (y : ℝ) : Real.toEReal ⁻¹' Ioc ⊥ y = Iic y := by
  rw [← Ioi_inter_Iic]
  simp

@[simp]
/-
**EReal.preimage_coe_Ioo_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioo_bot (y : Real) : Real.toEReal ⁻¹' Ioo ⊥ y = Iio y
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ioi_bot`：preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi 
⊥ = univ
· 使用引理 `EReal.preimage_coe_Iio`：preimage_coe_Iio (y : Real) : Real.toEReal ⁻¹' I
io y = Iio y
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioo_bot (y : ℝ) : Real.toEReal ⁻¹' Ioo ⊥ y = Iio y := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
/-
**EReal.preimage_coe_Ioo_bot_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：preimage_coe_Ioo_bot_top : Real.toEReal ⁻¹' Ioo ⊥ ⊤ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.preimage_coe_Ioi_bot`：preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi 
⊥ = univ
· 使用引理 `EReal.preimage_coe_Iio_top`：preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio 
⊤ = univ
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_coe_Ioo_bot_top : Real.toEReal ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [← Ioi_inter_Iio]
  simp

/-! ### ennreal coercion -/

@[simp]
/-
**EReal.toReal_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {x : ENNReal}, (↑x).toReal = x.toReal
参数：↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### ennreal coercion
-/
theorem toReal_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : EReal) = ENNReal.toReal x
  | ⊤ => rfl
  | .some _ => rfl

@[simp]
/-
**EReal.coe_ennreal_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_ofReal {x : Real} : (ENNReal.ofReal x : EReal) = max x 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : EReal) = max x 0 :=
  rfl
/-
**EReal.coe_ennreal_toReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_toReal {x : Real>=0∞} (hx : x != ∞) : (x.toReal : EReal) = x
参数：hx : x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
lemma coe_ennreal_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : (x.toReal : EReal) = x := by
  lift x to ℝ≥0 using hx
  rfl
/-
**EReal.coe_nnreal_eq_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_nnreal_eq_coe_real (x : Real>=0) : ((x : Real>=0∞) : EReal) = (x : Rea
l)
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) = (x : ℝ) :=
  rfl

@[simp, norm_cast]
/-
**EReal.coe_ennreal_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ennreal_zero : ((0 : ℝ≥0∞) : EReal) = 0 :=
  rfl

@[simp, norm_cast]
/-
**EReal.coe_ennreal_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_one : ((1 : Real>=0∞) : EReal) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ennreal_one : ((1 : ℝ≥0∞) : EReal) = 1 :=
  rfl

@[simp, norm_cast]
/-
**EReal.coe_ennreal_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_top : ((⊤ : Real>=0∞) : EReal) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ennreal_top : ((⊤ : ℝ≥0∞) : EReal) = ⊤ :=
  rfl
/-
**EReal.coe_ennreal_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_strictMono : StrictMono ((↑) : Real>=0∞ -> EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.strictMono_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder
 α] [inst_1 : Preorder β] {f : WithTop α → β},   StrictMono f ↔ (StrictMono fun 
a => f ↑a) ∧…
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
-/
theorem coe_ennreal_strictMono : StrictMono ((↑) : ℝ≥0∞ → EReal) :=
  WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩
/-
**EReal.coe_ennreal_injective** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_injective : Injective ((↑) : Real>=0∞ -> EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `EReal.coe_ennreal_strictMono`：coe_ennreal_strictMono : StrictMono ((↑) :
 Real>=0∞ -> EReal)
-/
theorem coe_ennreal_injective : Injective ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.injective

@[simp]
/-
**EReal.coe_ennreal_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_eq_top_iff {x : Real>=0∞} : (x : EReal) = ⊤ ↔ x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `EReal.coe_ennreal_injective`：coe_ennreal_injective : Injective ((↑) : Re
al>=0∞ -> EReal)
-/
theorem coe_ennreal_eq_top_iff {x : ℝ≥0∞} : (x : EReal) = ⊤ ↔ x = ⊤ :=
  coe_ennreal_injective.eq_iff' rfl
/-
**EReal.coe_nnreal_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_nnreal_ne_top (x : Real>=0) : ((x : Real>=0∞) : EReal) != ⊤
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_ne_top`：coe_ne_top (x : Real) : (x : EReal) != ⊤
-/
theorem coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) ≠ ⊤ := coe_ne_top x

@[simp]
/-
**EReal.coe_nnreal_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_nnreal_lt_top (x : Real>=0) : ((x : Real>=0∞) : EReal) < ⊤
参数：x : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
-/
theorem coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) < ⊤ := coe_lt_top x

@[simp, norm_cast]
/-
**EReal.coe_ennreal_le_coe_ennreal_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_le_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) <= (y : ERea
l) ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `EReal.coe_ennreal_strictMono`：coe_ennreal_strictMono : StrictMono ((↑) :
 Real>=0∞ -> EReal)
-/
theorem coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_ennreal_strictMono.le_iff_le

@[simp, norm_cast]
/-
**EReal.coe_ennreal_lt_coe_ennreal_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_lt_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) < (y : EReal
) ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `EReal.coe_ennreal_strictMono`：coe_ennreal_strictMono : StrictMono ((↑) :
 Real>=0∞ -> EReal)
-/
theorem coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_ennreal_strictMono.lt_iff_lt

@[simp, norm_cast]
/-
**EReal.coe_ennreal_eq_coe_ennreal_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_eq_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) = (y : EReal
) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `EReal.coe_ennreal_injective`：coe_ennreal_injective : Injective ((↑) : Re
al>=0∞ -> EReal)
-/
theorem coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_ennreal_injective.eq_iff
/-
**EReal.coe_ennreal_ne_coe_ennreal_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_ne_coe_ennreal_iff {x y : Real>=0∞} : (x : EReal) != (y : ERea
l) ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `EReal.coe_ennreal_injective`：coe_ennreal_injective : Injective ((↑) : Re
al>=0∞ -> EReal)
-/
theorem coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_ennreal_injective.ne_iff

@[simp, norm_cast]
/-
**EReal.coe_ennreal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_eq_zero {x : Real>=0∞} : (x : EReal) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_ennreal_eq_coe_ennreal_iff`：coe_ennreal_eq_coe_ennreal_iff {x 
y : Real>=0∞} : (x : EReal) = (y : EReal) ↔ x = y
· 使用定理 `EReal.coe_ennreal_zero`：coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : EReal) = 0 ↔ x = 0 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]

@[simp, norm_cast]
/-
**EReal.coe_ennreal_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_eq_one {x : Real>=0∞} : (x : EReal) = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_ennreal_eq_coe_ennreal_iff`：coe_ennreal_eq_coe_ennreal_iff {x 
y : Real>=0∞} : (x : EReal) = (y : EReal) ↔ x = y
· 使用定理 `EReal.coe_ennreal_one`：coe_ennreal_one : ((1 : Real>=0∞) : EReal) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : EReal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]

@[norm_cast]
/-
**EReal.coe_ennreal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_ne_zero {x : Real>=0∞} : (x : EReal) != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EReal.coe_ennreal_eq_zero`：coe_ennreal_eq_zero {x : Real>=0∞} : (x : ERe
al) = 0 ↔ x = 0
-/
theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  coe_ennreal_eq_zero.not

@[norm_cast]
/-
**EReal.coe_ennreal_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_ne_one {x : Real>=0∞} : (x : EReal) != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EReal.coe_ennreal_eq_one`：coe_ennreal_eq_one {x : Real>=0∞} : (x : EReal
) = 1 ↔ x = 1
-/
theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  coe_ennreal_eq_one.not
/-
**EReal.coe_ennreal_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_nonneg (x : Real>=0∞) : (0 : EReal) <= x
参数：x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_ennreal_le_coe_ennreal_iff`：coe_ennreal_le_coe_ennreal_iff {x 
y : Real>=0∞} : (x : EReal) <= (y : EReal) ↔ x <= y
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : EReal) ≤ x :=
  coe_ennreal_le_coe_ennreal_iff.2 zero_le
/-
**EReal.range_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：Set.range ENNReal.toEReal = Set.Ici 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `EReal.coe_ennreal_nonneg`：coe_ennreal_nonneg (x : Real>=0∞) : (0 : EReal
) <= x
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `EReal.bot_lt_zero`：bot_lt_zero : (⊥ : EReal) < 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_nonneg`：∀ {x : ℝ}, 0 ≤ ↑x ↔ 0 ≤ x
-/
@[simp] theorem range_coe_ennreal : range ((↑) : ℝ≥0∞ → EReal) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
    | ⊥ => fun h => absurd h bot_lt_zero.not_ge
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : ℝ) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift EReal ℝ≥0∞ (↑) (0 ≤ ·) := ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]
/-
**EReal.coe_ennreal_pos** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_pos {x : Real>=0∞} : (0 : EReal) < x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_ennreal_zero`：coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0
· 使用定理 `EReal.coe_ennreal_lt_coe_ennreal_iff`：coe_ennreal_lt_coe_ennreal_iff {x 
y : Real>=0∞} : (x : EReal) < (y : EReal) ↔ x < y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]
/-
**EReal.coe_ennreal_pos_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_pos_iff_ne_zero {x : Real>=0∞} : (0 : EReal) < x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.coe_ennreal_pos`：coe_ennreal_pos {x : Real>=0∞} : (0 : EReal) < x 
↔ 0 < x
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_ennreal_pos_iff_ne_zero {x : ℝ≥0∞} : (0 : EReal) < x ↔ x ≠ 0 := by
  rw [coe_ennreal_pos, pos_iff_ne_zero]

@[simp]
/-
**EReal.bot_lt_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：bot_lt_coe_ennreal (x : Real>=0∞) : (⊥ : EReal) < x
参数：x : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `EReal.coe_ennreal_nonneg`：coe_ennreal_nonneg (x : Real>=0∞) : (0 : EReal
) <= x
-/
theorem bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : EReal) < x :=
  (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp]
/-
**EReal.coe_ennreal_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_ne_bot (x : Real>=0∞) : (x : EReal) != ⊥
参数：x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.bot_lt_coe_ennreal`：bot_lt_coe_ennreal (x : Real>=0∞) : (⊥ : EReal
) < x
-/
theorem coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast]
/-
**EReal.coe_ennreal_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_add (x y : ENNReal) : ((x + y : Real>=0∞) : EReal) = x + y
参数：x y : ENNReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_ennreal_add (x y : ENNReal) : ((x + y : ℝ≥0∞) : EReal) = x + y := by
  cases x <;> cases y <;> rfl
/-
**EReal.coe_ennreal_top_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coe_ennreal_top_mul (x : ℝ≥0) : ((⊤ * x : ℝ≥0∞) : EReal) = ⊤ * x := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · simp
  · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
    exact Eq.symm <| if_pos <| NNReal.coe_pos.2 h0.bot_lt

@[simp, norm_cast]
/-
**EReal.coe_ennreal_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x y : ENNReal), ↑(x * y) = ↑x * ↑y
参数：x y : ENNReal；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.EReal.Basic.0.EReal.coe_ennreal_top_mul`：∀ (x : NN
Real), ↑(⊤ * ↑x) = ⊤ * ↑↑x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `EReal.coe_ennreal_top`：coe_ennreal_top : ((⊤ : Real>=0∞) : EReal) = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : EReal) = (x : EReal) * y
  | ⊤, ⊤ => rfl
  | ⊤, (y : ℝ≥0) => coe_ennreal_top_mul y
  | (x : ℝ≥0), ⊤ => by
    rw [mul_comm, coe_ennreal_top_mul, EReal.mul_comm, coe_ennreal_top]
  | (x : ℝ≥0), (y : ℝ≥0) => by
    simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]

@[norm_cast]
/-
**EReal.coe_ennreal_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_nsmul (n : Nat) (x : Real>=0∞) : (↑(n • x) : EReal) = n • (x :
 EReal)
参数：n : Nat；x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `EReal.coe_ennreal_zero`：coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0
· 使用定理 `EReal.coe_ennreal_add`：coe_ennreal_add (x y : ENNReal) : ((x + y : Real>
=0∞) : EReal) = x + y
-/
theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : ℝ≥0∞ →+ EReal) _ _

/-! ### toENNReal -/

/-- `x.toENNReal` returns `x` if it is nonnegative, `0` otherwise. -/
/-
**EReal.toENNReal** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：toENNReal (x : EReal) : Real>=0∞
参数：x : EReal。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x.toENNReal` returns `x` if it is nonnegative, `0` otherwise.
-/
noncomputable def toENNReal (x : EReal) : ℝ≥0∞ :=
  if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal
/-
**EReal.toENNReal_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊤.toENNReal = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

@[simp]
/-
**EReal.toENNReal_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤) : x.toENNReal = ENNReal.ofRe
al x.toReal
参数：hx : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal :=
  if_neg hx

@[simp]
/-
**EReal.toENNReal_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤ := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]
/-
**EReal.toENNReal_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_ne_top_iff {x : EReal} : x.toENNReal != ⊤ ↔ x != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `EReal.toENNReal_eq_top_iff`：toENNReal_eq_top_iff {x : EReal} : x.toENNRe
al = ⊤ ↔ x = ⊤
-/
lemma toENNReal_ne_top_iff {x : EReal} : x.toENNReal ≠ ⊤ ↔ x ≠ ⊤ := toENNReal_eq_top_iff.not

@[simp]
/-
**EReal.toENNReal_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_of_nonpos {x : EReal} (hx : x <= 0) : x.toENNReal = 0
参数：hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.toENNReal.eq_1`：∀ (x : EReal), x.toENNReal = if x = ⊤ then ⊤ else 
ENNReal.ofReal x.toReal
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用引理 `EReal.toReal_nonpos`：toReal_nonpos {x : EReal} (hx : x <= 0) : x.toReal 
<= 0
-/
lemma toENNReal_of_nonpos {x : EReal} (hx : x ≤ 0) : x.toENNReal = 0 := by
  rw [toENNReal, if_neg (fun h ↦ ?_)]
  · exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
  · exact zero_ne_top <| top_le_iff.mp <| h ▸ hx
/-
**EReal.toENNReal_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_bot : (⊥ : EReal).toENNReal = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.toENNReal_of_nonpos`：toENNReal_of_nonpos {x : EReal} (hx : x <= 0)
 : x.toENNReal = 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma toENNReal_bot : (⊥ : EReal).toENNReal = 0 := toENNReal_of_nonpos bot_le
/-
**EReal.toENNReal_zero** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_zero : (0 : EReal).toENNReal = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.toENNReal_of_nonpos`：toENNReal_of_nonpos {x : EReal} (hx : x <= 0)
 : x.toENNReal = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma toENNReal_zero : (0 : EReal).toENNReal = 0 := toENNReal_of_nonpos le_rfl
/-
**EReal.toENNReal_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
lemma toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x ≤ 0 := by
  induction x <;> simp [toENNReal]
/-
**EReal.toENNReal_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_ne_zero_iff {x : EReal} : x.toENNReal != 0 ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `EReal.toENNReal_eq_zero_iff`：toENNReal_eq_zero_iff {x : EReal} : x.toENN
Real = 0 ↔ x <= 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toENNReal_ne_zero_iff {x : EReal} : x.toENNReal ≠ 0 ↔ 0 < x := by
  simp [toENNReal_eq_zero_iff.not]

@[simp]
/-
**EReal.toENNReal_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_pos_iff {x : EReal} : 0 < x.toENNReal ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `EReal.toENNReal_ne_zero_iff`：toENNReal_ne_zero_iff {x : EReal} : x.toENN
Real != 0 ↔ 0 < x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toENNReal_pos_iff {x : EReal} : 0 < x.toENNReal ↔ 0 < x := by
  rw [pos_iff_ne_zero, toENNReal_ne_zero_iff]

@[simp]
/-
**EReal.coe_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_toENNReal {x : EReal} (hx : 0 <= x) : (x.toENNReal : EReal) = x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.toENNReal.eq_1`：∀ (x : EReal), x.toENNReal = if x = ⊤ then ⊤ else 
ENNReal.ofReal x.toReal
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x := by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ ↦ by simp_all only [le_bot_iff, zero_ne_bot]
/-
**EReal.coe_toENNReal_eq_max** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_toENNReal_eq_max {x : EReal} : x.toENNReal = max 0 x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.coe_toENNReal`：coe_toENNReal {x : EReal} (hx : 0 <= x) : (x.toENNR
eal : EReal) = x
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `EReal.toENNReal_of_nonpos`：toENNReal_of_nonpos {x : EReal} (hx : x <= 0)
 : x.toENNReal = 0
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `EReal.coe_ennreal_zero`：coe_ennreal_zero : ((0 : Real>=0∞) : EReal) = 0
-/
lemma coe_toENNReal_eq_max {x : EReal} : x.toENNReal = max 0 x := by
  rcases le_total 0 x with (hx | hx)
  · rw [coe_toENNReal hx, max_eq_right hx]
  · rw [toENNReal_of_nonpos hx, max_eq_left hx, coe_ennreal_zero]

@[simp]
/-
**EReal.toENNReal_coe** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_coe {x : Real>=0∞} : (x : EReal).toENNReal = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.coe_ennreal_top`：coe_ennreal_top : ((⊤ : Real>=0∞) : EReal) = ⊤
· 使用定理 `EReal.toENNReal_top`：⊤.toENNReal = ⊤
· 使用定理 `EReal.toENNReal.eq_1`：∀ (x : EReal), x.toENNReal = if x = ⊤ then ⊤ else 
ENNReal.ofReal x.toReal
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `EReal.toReal_coe_ennreal`：∀ {x : ENNReal}, (↑x).toReal = x.toReal
· 使用定理 `ENNReal.ofReal_toReal_eq_iff`：ofReal_toReal_eq_iff : ENNReal.ofReal a.to
Real = a ↔ a != ⊤
-/
lemma toENNReal_coe {x : ℝ≥0∞} : (x : EReal).toENNReal = x := by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rwa [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  simp [h_top]
/-
**EReal.real_coe_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : ℝ), (↑x).toENNReal = ENNReal.ofReal x
参数：x : ℝ；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma real_coe_toENNReal (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl

@[simp]
/-
**EReal.toReal_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toReal_toENNReal {x : EReal} (hx : 0 <= x) : x.toENNReal.toReal = x.toReal
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `EReal.toReal_nonneg`：toReal_nonneg {x : EReal} (hx : 0 <= x) : 0 <= x.to
Real
-/
lemma toReal_toENNReal {x : EReal} (hx : 0 ≤ x) : x.toENNReal.toReal = x.toReal := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]
/-
**EReal.toENNReal_eq_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_eq_toENNReal {x y : EReal} (hx : 0 <= x) (hy : 0 <= y) : x.toENN
Real = y.toENNReal ↔ x = y
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toENNReal_eq_toENNReal {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x.toENNReal = y.toENNReal ↔ x = y := by
  induction x <;> induction y <;> simp_all
/-
**EReal.toENNReal_le_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_le_toENNReal {x y : EReal} (h : x <= y) : x.toENNReal <= y.toENN
Real
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.toENNReal_of_ne_top`：toENNReal_of_ne_top {x : EReal} (hx : x != ⊤)
 : x.toENNReal = ENNReal.ofReal x.toReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `EReal.toReal_le_toReal`：toReal_le_toReal {x y : EReal} (h : x <= y) (hx 
: x != ⊥) (hy : y != ⊤) : x.toReal <= y.toReal
· 使用定理 `EReal.coe_ne_bot`：coe_ne_bot (x : Real) : (x : EReal) != ⊥
-/
lemma toENNReal_le_toENNReal {x y : EReal} (h : x ≤ y) : x.toENNReal ≤ y.toENNReal := by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp only [toENNReal, coe_ne_top, ↓reduceIte, toReal_coe, hy_top]
    exact ENNReal.ofReal_le_ofReal <| EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all
/-
**EReal.toENNReal_lt_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：toENNReal_lt_toENNReal {x y : EReal} (hx : 0 <= x) (hxy : x < y) : x.toENN
Real < y.toENNReal
参数：hx : 0 <= x；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `EReal.toENNReal_le_toENNReal`：toENNReal_le_toENNReal {x y : EReal} (h : 
x <= y) : x.toENNReal <= y.toENNReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `EReal.toENNReal_eq_toENNReal`：toENNReal_eq_toENNReal {x y : EReal} (hx :
 0 <= x) (hy : 0 <= y) : x.toENNReal = y.toENNReal ↔ x = y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
lemma toENNReal_lt_toENNReal {x y : EReal} (hx : 0 ≤ x) (hxy : x < y) :
    x.toENNReal < y.toENNReal :=
  lt_of_le_of_ne (toENNReal_le_toENNReal hxy.le)
    fun h ↦ hxy.ne <| (toENNReal_eq_toENNReal hx (hx.trans_lt hxy).le).mp h

/-! ### nat coercion -/

/-
**EReal.coe_coe_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n : EReal)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### nat coercion
-/
theorem coe_coe_eq_natCast (n : ℕ) : (n : ℝ) = (n : EReal) := rfl
/-
**EReal.natCast_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_ne_bot (n : Nat) : (n : EReal) != ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_beq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b : α}, 
(a == b) = false → a ≠ b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Std.LawfulBCmp.toTransCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : LT α
} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   Std.T
ransCmp cmp
-/
theorem natCast_ne_bot (n : ℕ) : (n : EReal) ≠ ⊥ := Ne.symm (ne_of_beq_false rfl)
/-
**EReal.natCast_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_beq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b : α}, 
(a == b) = false → a ≠ b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Std.LawfulBCmp.toTransCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : LT α
} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   Std.T
ransCmp cmp
-/
theorem natCast_ne_top (n : ℕ) : (n : EReal) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)

@[norm_cast]
/-
**EReal.natCast_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_eq_iff {m n : Nat} : (m : EReal) = (n : EReal) ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用定理 `EReal.coe_eq_coe_iff`：∀ {x y : ℝ}, ↑x = ↑y ↔ x = y
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_eq_iff {m n : ℕ} : (m : EReal) = (n : EReal) ↔ m = n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_eq_coe_iff, Nat.cast_inj]
/-
**EReal.natCast_ne_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_ne_iff {m n : Nat} : (m : EReal) != (n : EReal) ↔ m != n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `EReal.natCast_eq_iff`：natCast_eq_iff {m n : Nat} : (m : EReal) = (n : ER
eal) ↔ m = n
-/
theorem natCast_ne_iff {m n : ℕ} : (m : EReal) ≠ (n : EReal) ↔ m ≠ n :=
  not_iff_not.2 natCast_eq_iff

@[norm_cast]
/-
**EReal.natCast_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_le_iff {m n : Nat} : (m : EReal) <= (n : EReal) ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_le_iff {m n : ℕ} : (m : EReal) ≤ (n : EReal) ↔ m ≤ n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_le_coe_iff, Nat.cast_le]

@[norm_cast]
/-
**EReal.natCast_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_lt_iff {m n : Nat} : (m : EReal) < (n : EReal) ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natCast_lt_iff {m n : ℕ} : (m : EReal) < (n : EReal) ↔ m < n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_lt_coe_iff, Nat.cast_lt]

@[simp, norm_cast]
/-
**EReal.natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_mul (m n : Nat) : (m * n : Nat) = (m : EReal) * (n : EReal)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
-/
theorem natCast_mul (m n : ℕ) :
    (m * n : ℕ) = (m : EReal) * (n : EReal) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, Nat.cast_mul, EReal.coe_mul]

/-! ### Miscellaneous lemmas -/

/-
**EReal.exists_rat_btwn_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：exists_rat_btwn_of_lt : forall {a b : EReal}, a < b -> exists x : Rat, a <
 (x : Real) ∧ ((x : Real) : EReal) < b | ⊤, _, h => (not_top_lt h).elim | (a : R
eal), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim | (a : Real), (b : Rea
l), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)] | (a : Real), ⊤, _
 => let ⟨b, hab⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用定理 `exists_rat_lt`：exists_rat_lt (x : K) : exists q : Rat, (q : K) < x

--- 原说明 ---
### Miscellaneous lemmas
-/
theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal}, a < b → ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b
  | ⊤, _, h => (not_top_lt h).elim
  | (a : ℝ), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : ℝ), (b : ℝ), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]
  | (a : ℝ), ⊤, _ =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : ℝ), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩
/-
**EReal.lt_iff_exists_rat_btwn** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：lt_iff_exists_rat_btwn {a b : EReal} : a < b ↔ exists x : Rat, a < (x : Re
al) ∧ ((x : Real) : EReal) < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exists_rat_btwn_of_lt`：exists_rat_btwn_of_lt : forall {a b : EReal
}, a < b -> exists x : Rat, a < (x : Real) ∧ ((x : Real) : EReal) < b | ⊤, _, h 
=> (not_top_lt h)…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩
/-
**EReal.lt_iff_exists_real_btwn** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ exists x : Real, a < x ∧ (
x : EReal) < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.exists_rat_btwn_of_lt`：exists_rat_btwn_of_lt : forall {a b : EReal
}, a < b -> exists x : Rat, a < (x : Real) ∧ ((x : Real) : EReal) < b | ⊤, _, h 
=> (not_top_lt h)…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ ∃ x : ℝ, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : ℝ), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

/-- The set of numbers in `EReal` that are not equal to `±∞` is equivalent to `ℝ`. -/
/-
**EReal.neTopBotEquivReal** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ Real where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of numbers in `EReal` that are not equal to `±∞` is equivalent to `ℝ`.
-/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ ℝ where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to ℝ
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: cast from `ℝ` to `EReal`. -/
@[positivity Real.toEReal _]
meta def evalRealToEReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(EReal), ~q(Real.toEReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(EReal.coe_pos.2 $pa))
    | .nonnegative pa => pure (.nonnegative q(EReal.coe_nonneg.2 $pa))
    | .nonzero pa => pure (.nonzero q(EReal.coe_ne_zero.2 $pa))
    | _ => pure .none
  | _, _, _ => throwError "not Real.toEReal"

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `EReal`. -/
@[positivity ENNReal.toEReal _]
meta def evalENNRealToEReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(EReal), ~q(ENNReal.toEReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(EReal.coe_ennreal_pos.2 $pa))
    | .nonzero pa => pure (.positive q(EReal.coe_ennreal_pos_iff_ne_zero.2 $pa))
    | _ => pure (.nonnegative q(EReal.coe_ennreal_nonneg $a))
  | _, _, _ => throwError "not ENNReal.toEReal"

/-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ`.

We prove that `EReal.toReal x` is nonnegative whenever `x` is nonnegative.
Since `EReal.toReal ⊤ = 0`, we cannot prove a stronger statement,
at least without relying on a tactic like `finiteness`. -/
@[positivity EReal.toReal _]
meta def evalERealToReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(EReal.toReal $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) (some q(inferInstance)) a).toNonneg with
    | .some pa => pure (.nonnegative q(EReal.toReal_nonneg $pa))
    | _ => pure .none
  | _, _, _ => throwError "not EReal.toReal"

/-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ≥0∞`.

We show that `EReal.toENNReal x` is positive whenever `x` is positive,
and it is nonnegative otherwise.
We cannot deduce any corollaries from `x ≠ 0`, since `EReal.toENNReal x = 0` for `x < 0`.
-/
@[positivity EReal.toENNReal _]
meta def evalERealToENNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ENNReal), ~q(EReal.toENNReal $a) =>
    assertInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa => pure (.positive q(EReal.toENNReal_pos_iff.2 $pa))
    | _ => pure (.nonnegative q(zero_le (a := $e)))
  | _, _, _ => throwError "not EReal.toENNReal"

end Mathlib.Meta.Positivity

