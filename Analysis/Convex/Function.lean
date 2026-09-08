/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Tactic.NormNum

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `Analysis.Convex.Integral`.

A function `f : E → β` is `ConvexOn` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `ConvexOn 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `ConvexOn 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `ConcaveOn 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `StrictConvexOn 𝕜 s f`: The function `f` is strictly convex on `s` with scalars `𝕜`.
* `StrictConcaveOn 𝕜 s f`: The function `f` is strictly concave on `s` with scalars `𝕜`.
-/

@[expose] public section

open LinearMap Set Convex Pointwise

variable {𝕜 E F α β ι : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 α] [SMul 𝕜 β] (s : Set E) (f : E → β) {g : β → α}

/-- Convexity of functions -/
/-
**ConvexOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConvexOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convexity of functions
-/
def ConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
/-
**ConcaveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConcaveOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concavity of functions
-/
def ConcaveOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

/-- Strict convexity of functions -/
/-
**StrictConvexOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictConvexOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strict convexity of functions
-/
def StrictConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < a • f x + b • f y

/-- Strict concavity of functions -/
/-
**StrictConcaveOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StrictConcaveOn : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strict concavity of functions
-/
def StrictConcaveOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    a • f x + b • f y < f (a • x + b • y)

variable {𝕜 s f}

open OrderDual (toDual ofDual)
/-
**ConvexOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDual ∘ f)
参数：hf : ConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDual ∘ f) := hf
/-
**ConcaveOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (toDual ∘ f)
参数：hf : ConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (toDual ∘ f) := hf
/-
**StrictConvexOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : StrictConcaveOn 𝕜 s (toD
ual ∘ f)
参数：hf : StrictConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : StrictConcaveOn 𝕜 s (toDual ∘ f) := hf
/-
**StrictConcaveOn.dual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) : StrictConvexOn 𝕜 s (to
Dual ∘ f)
参数：hf : StrictConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) : StrictConvexOn 𝕜 s (toDual ∘ f) := hf
/-
**convexOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s _root_.id
参数：hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem convexOn_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩
/-
**concaveOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s _root_.id
参数：hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem concaveOn_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

section congr

variable {g : E → β}

/-
**ConvexOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.congr (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s) : ConvexOn 𝕜 s g
参数：hf : ConvexOn 𝕜 s f；hfg : EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConvexOn.congr (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s) : ConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩
/-
**ConcaveOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s) : ConcaveOn 𝕜 s 
g
参数：hf : ConcaveOn 𝕜 s f；hfg : EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s) : ConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩
/-
**StrictConvexOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.congr (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s) : Stri
ctConvexOn 𝕜 s g
参数：hf : StrictConvexOn 𝕜 s f；hfg : EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StrictConvexOn.congr (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩
/-
**StrictConcaveOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.congr (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s) : St
rictConcaveOn 𝕜 s g
参数：hf : StrictConcaveOn 𝕜 s f；hfg : EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StrictConcaveOn.congr (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

end congr

/-
**ConvexOn.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s subseteq t) (hs
 : Convex 𝕜 s) : ConvexOn 𝕜 s f
参数：hf : ConvexOn 𝕜 t f；hst : s subseteq t；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
/-
**ConcaveOn.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s subseteq t) (
hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f
参数：hf : ConcaveOn 𝕜 t f；hst : s subseteq t；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
/-
**StrictConvexOn.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s sub
seteq t) (hs : Convex 𝕜 s) : StrictConvexOn 𝕜 s f
参数：hf : StrictConvexOn 𝕜 t f；hst : s subseteq t；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
/-
**StrictConcaveOn.subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s s
ubseteq t) (hs : Convex 𝕜 s) : StrictConcaveOn 𝕜 s f
参数：hf : StrictConcaveOn 𝕜 t f；hst : s subseteq t；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩
/-
**ConvexOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f) (hg' : Mo
notoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f)
参数：hg : ConvexOn 𝕜 (f '' s) g；hf : ConvexOn 𝕜 s f；hg' : MonotoneOn g (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha hb hab)
            (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab) <|
          hf.2 hx hy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab⟩
/-
**ConcaveOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f) (hg' :
 MonotoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f)
参数：hg : ConcaveOn 𝕜 (f '' s) g；hf : ConcaveOn 𝕜 s f；hg' : MonotoneOn g (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab).trans <|
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
          (mem_image_of_mem f <| hf.1 hx hy ha hb hab) <|
        hf.2 hx hy ha hb hab⟩
/-
**ConvexOn.comp_concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.comp_concaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f
) (hg' : AntitoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f)
参数：hg : ConvexOn 𝕜 (f '' s) g；hf : ConcaveOn 𝕜 s f；hg' : AntitoneOn g (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.comp`：ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : Conca
veOn 𝕜 s f) (hg' : MonotoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f)
· 使用定理 `ConvexOn.dual`：ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDu
al ∘ f)
-/
theorem ConvexOn.comp_concaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'
/-
**ConcaveOn.comp_convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.comp_convexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f
) (hg' : AntitoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f)
参数：hg : ConcaveOn 𝕜 (f '' s) g；hf : ConvexOn 𝕜 s f；hg' : AntitoneOn g (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.comp`：ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn
 𝕜 s f) (hg' : MonotoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f)
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.comp_convexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'
/-
**StrictConvexOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexO
n 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s 
(g ∘ f)
参数：hg : StrictConvexOn 𝕜 (f '' s) g；hf : StrictConvexOn 𝕜 s f；hg' : StrictMonoOn
 g (f '' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab)
            (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab) <|
          hf.2 hx hy hxy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab⟩
/-
**StrictConcaveOn.comp_strictConvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.comp_strictConvexOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (h
f : StrictConvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) : St
rictConcaveOn 𝕜 s (g ∘ f)
参数：hg : StrictConcaveOn 𝕜 (f '' s) g；hf : StrictConvexOn 𝕜 s f；hg' : StrictAntiO
n g (f '' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.comp`：StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s)
 g) (hf : StrictConvexOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f
) : Stric…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.comp_strictConvexOn (hg : StrictConcaveOn 𝕜 (f '' s) g)
    (hf : StrictConvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'
/-
**StrictConcaveOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConca
veOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 
𝕜 s (g ∘ f)
参数：hg : StrictConcaveOn 𝕜 (f '' s) g；hf : StrictConcaveOn 𝕜 s f；hg' : StrictMono
On g (f '' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConcaveOn.comp_strictConvexOn`：StrictConcaveOn.comp_strictConvexOn
 (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f) (hg' : StrictAn
tiOn g (f '' s)) (hf' : s…
· 使用定理 `StrictMonoOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictMonoOn (⇑Or
derDual…
-/
theorem StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual hf'
/-
**StrictConvexOn.comp_strictConcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.comp_strictConcaveOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf
 : StrictConcaveOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) : St
rictConvexOn 𝕜 s (g ∘ f)
参数：hg : StrictConvexOn 𝕜 (f '' s) g；hf : StrictConcaveOn 𝕜 s f；hg' : StrictAntiO
n g (f '' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConcaveOn.comp`：StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f ''
 s) g) (hf : StrictConcaveOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) (hf' : s.Inj
On f) : St…
· 使用定理 `StrictConvexOn.dual`：StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : S
trictConcaveOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConvexOn.comp_strictConcaveOn (hg : StrictConvexOn 𝕜 (f '' s) g)
    (hf : StrictConcaveOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'
/-
**ConvexOn.comp_strictConvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.comp_strictConvexOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConv
exOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) : StrictConvexOn 𝕜 s (g ∘ f)
参数：hg : ConvexOn 𝕜 (f '' s) g；hf : StrictConvexOn 𝕜 s f；hg' : StrictMonoOn g (f 
'' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConvexOn.comp_strictConvexOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) : StrictConvexOn 𝕜 s (g ∘ f) := by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab ↦ .trans_le (b := g (a • f x + b • f y)) ?_ ?_⟩
  · refine hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab) ?_ <| hf.2 hx hy hxy ha hb hab
    exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab
/-
**ConcaveOn.comp_strictConvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.comp_strictConvexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictCo
nvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) : StrictConcaveOn 𝕜 s (g ∘ f)
参数：hg : ConcaveOn 𝕜 (f '' s) g；hf : StrictConvexOn 𝕜 s f；hg' : StrictAntiOn g (f
 '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.comp_strictConvexOn`：ConvexOn.comp_strictConvexOn (hg : ConvexO
n 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) : St
rictConvexOn 𝕜 s (…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.comp_strictConvexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictAntiOn g (f '' s)) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_strictConvexOn hf hg'
/-
**ConcaveOn.comp_strictConcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.comp_strictConcaveOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictC
oncaveOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)) : StrictConcaveOn 𝕜 s (g ∘ f)
参数：hg : ConcaveOn 𝕜 (f '' s) g；hf : StrictConcaveOn 𝕜 s f；hg' : StrictMonoOn g (
f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.comp_strictConvexOn`：ConcaveOn.comp_strictConvexOn (hg : Conca
veOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) :
 StrictConcaveOn 𝕜 …
· 使用定理 `StrictMonoOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictMonoOn (⇑Or
derDual…
-/
theorem ConcaveOn.comp_strictConcaveOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.comp_strictConvexOn (β := βᵒᵈ) hf hg'.dual
/-
**ConvexOn.comp_strictConcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.comp_strictConcaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictCon
caveOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) : StrictConvexOn 𝕜 s (g ∘ f)
参数：hg : ConvexOn 𝕜 (f '' s) g；hf : StrictConcaveOn 𝕜 s f；hg' : StrictAntiOn g (f
 '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.comp_strictConcaveOn`：ConcaveOn.comp_strictConcaveOn (hg : Con
caveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f) (hg' : StrictMonoOn g (f '' s)
) : StrictConcaveOn …
· 使用定理 `ConvexOn.dual`：ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDu
al ∘ f)
-/
theorem ConvexOn.comp_strictConcaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictAntiOn g (f '' s)) : StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_strictConcaveOn hf hg'
/-
**StrictConvexOn.comp_convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.comp_convexOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : Conv
exOn 𝕜 s f) (hg' : MonotoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s
 (g ∘ f)
参数：hg : StrictConvexOn 𝕜 (f '' s) g；hf : ConvexOn 𝕜 s f；hg' : MonotoneOn g (f ''
 s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem StrictConvexOn.comp_convexOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) := by
  refine ⟨hf.left, fun x hx y hy hxy a b ha hb hab ↦ .trans_le' (b := g (a • f x + b • f y)) ?_ ?_⟩
  · exact hg.right (mem_image_of_mem f hx) (mem_image_of_mem f hy) (hf'.ne hx hy hxy) ha hb hab
  · refine hg' ?_ ?_ <| hf.right hx hy ha.le hb.le hab
    · exact mem_image_of_mem f <| hf.left hx hy ha.le hb.le hab
    · exact hg.left (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab
/-
**StrictConcaveOn.comp_convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.comp_convexOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : Co
nvexOn 𝕜 s f) (hg' : AntitoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 
𝕜 s (g ∘ f)
参数：hg : StrictConcaveOn 𝕜 (f '' s) g；hf : ConvexOn 𝕜 s f；hg' : AntitoneOn g (f '
' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.comp_convexOn`：StrictConvexOn.comp_convexOn (hg : StrictC
onvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f) (hg' : MonotoneOn g (f '' s)) (hf' :
 s.InjOn f) : Stri…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.comp_convexOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_convexOn hf hg' hf'
/-
**StrictConvexOn.comp_concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.comp_concaveOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : Con
caveOn 𝕜 s f) (hg' : AntitoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜
 s (g ∘ f)
参数：hg : StrictConvexOn 𝕜 (f '' s) g；hf : ConcaveOn 𝕜 s f；hg' : AntitoneOn g (f '
' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.comp_convexOn`：StrictConvexOn.comp_convexOn (hg : StrictC
onvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f) (hg' : MonotoneOn g (f '' s)) (hf' :
 s.InjOn f) : Stri…
· 使用定理 `AntitoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn (⇑OrderDua
l.toD…
-/
theorem StrictConvexOn.comp_concaveOn (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.comp_convexOn (β := βᵒᵈ) hf hg'.dual hf'
/-
**StrictConcaveOn.comp_concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.comp_concaveOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : C
oncaveOn 𝕜 s f) (hg' : MonotoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveO
n 𝕜 s (g ∘ f)
参数：hg : StrictConcaveOn 𝕜 (f '' s) g；hf : ConcaveOn 𝕜 s f；hg' : MonotoneOn g (f 
'' s)；hf' : s.InjOn f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.comp_concaveOn`：StrictConvexOn.comp_concaveOn (hg : Stric
tConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f) (hg' : AntitoneOn g (f '' s)) (hf
' : s.InjOn f) : St…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.comp_concaveOn (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp_concaveOn hf hg' hf'

end SMul

section DistribMulAction

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

/-
**ConvexOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f
 + g)
参数：hf : ConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]
      ⟩
/-
**ConcaveOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 
s (f + g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.add`：ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
 ConvexOn 𝕜 s (f + g)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] {s : Set E} {f : E → β}

/-
**convexOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s fun _ : E => c
参数：c : β；hs : Convex 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s fun _ : E => c :=
  ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_self hab c).ge⟩
/-
**concaveOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s fun _ => c
参数：c : β；hs : Convex 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_const`：convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s 
fun _ : E => c
-/
theorem concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s fun _ => c :=
  convexOn_const (β := βᵒᵈ) _ hs
/-
**ConvexOn.add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.add_const [IsOrderedAddMonoid β] (hf : ConvexOn 𝕜 s f) (b : β) : 
ConvexOn 𝕜 s (f + fun _ => b)
参数：hf : ConvexOn 𝕜 s f；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.add`：ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
 ConvexOn 𝕜 s (f + g)
· 使用定理 `convexOn_const`：convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s 
fun _ : E => c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem ConvexOn.add_const [IsOrderedAddMonoid β] (hf : ConvexOn 𝕜 s f) (b : β) :
    ConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add (convexOn_const _ hf.1)
/-
**ConcaveOn.add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.add_const [IsOrderedAddMonoid β] (hf : ConcaveOn 𝕜 s f) (b : β) 
: ConcaveOn 𝕜 s (f + fun _ => b)
参数：hf : ConcaveOn 𝕜 s f；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.add`：ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s 
g) : ConcaveOn 𝕜 s (f + g)
· 使用定理 `concaveOn_const`：concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜
 s fun _ => c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem ConcaveOn.add_const [IsOrderedAddMonoid β] (hf : ConcaveOn 𝕜 s f) (b : β) :
    ConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add (concaveOn_const _ hf.1)
/-
**convexOn_of_convex_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_of_convex_epigraph (h : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <
= p.2 }) : ConvexOn 𝕜 s f
参数：h : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem convexOn_of_convex_epigraph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 }) :
    ConvexOn 𝕜 s f :=
  ⟨fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2⟩
/-
**concaveOn_of_convex_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_of_convex_hypograph (h : Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 <
= f p.1 }) : ConcaveOn 𝕜 s f
参数：h : Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 <= f p.1 }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_of_convex_epigraph`：convexOn_of_convex_epigraph (h : Convex 𝕜 {
 p : E × β | p.1 in s ∧ f p.1 <= p.2 }) : ConvexOn 𝕜 s f
-/
theorem concaveOn_of_convex_hypograph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 }) :
    ConcaveOn 𝕜 s f :=
  convexOn_of_convex_epigraph (β := βᵒᵈ) h

end Module

section PosSMulMono

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β] {s : Set E} {f : E → β}

/-
**ConvexOn.convex_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | f 
x <= r })
参数：hf : ConvexOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  fun x hx y hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ ≤ a • r + b • r := by
        gcongr
        · exact hx.2
        · exact hy.2
      _ = r := Convex.combo_self hab r
      ⟩
/-
**ConcaveOn.convex_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | 
r <= f x })
参数：hf : ConcaveOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.convex_le`：ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : C
onvex 𝕜 ({ x in s | f x <= r })
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  hf.dual.convex_le r
/-
**ConvexOn.convex_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f) : Convex 𝕜 { p : E × β | p.
1 in s ∧ f p.1 <= p.2 }
参数：hf : ConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
theorem ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by gcongr
/-
**ConcaveOn.convex_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.convex_hypograph (hf : ConcaveOn 𝕜 s f) : Convex 𝕜 { p : E × β |
 p.1 in s ∧ p.2 <= f p.1 }
参数：hf : ConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.convex_epigraph`：ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f)
 : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.convex_hypograph (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  hf.dual.convex_epigraph
/-
**convexOn_iff_convex_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_iff_convex_epigraph : ConvexOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1
 in s ∧ f p.1 <= p.2 }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.convex_epigraph`：ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f)
 : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }
· 使用定理 `convexOn_of_convex_epigraph`：convexOn_of_convex_epigraph (h : Convex 𝕜 {
 p : E × β | p.1 in s ∧ f p.1 <= p.2 }) : ConvexOn 𝕜 s f
-/
theorem convexOn_iff_convex_epigraph :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  ⟨ConvexOn.convex_epigraph, convexOn_of_convex_epigraph⟩
/-
**concaveOn_iff_convex_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_iff_convex_hypograph : ConcaveOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | 
p.1 in s ∧ p.2 <= f p.1 }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_iff_convex_epigraph`：convexOn_iff_convex_epigraph : ConvexOn 𝕜 
s f ↔ Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem concaveOn_iff_convex_hypograph :
    ConcaveOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  convexOn_iff_convex_epigraph (β := βᵒᵈ)

end PosSMulMono

section Module

variable [Module 𝕜 E] [SMul 𝕜 β] {s : Set E} {f : E → β}

/-- Right translation preserves convexity. -/
/-
**ConvexOn.translate_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.translate_right (hf : ConvexOn 𝕜 s f) (c : E) : ConvexOn 𝕜 ((fun 
z => c + z) ⁻¹' s) (f ∘ fun z => c + z)
参数：hf : ConvexOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.translate_preimage_right`：Convex.translate_preimage_right (hs : C
onvex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) ⁻¹' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Right translation preserves convexity.
-/
theorem ConvexOn.translate_right (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_comm, Convex.combo_self hab]
      _ ≤ a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

/-- Right translation preserves concavity. -/
/-
**ConcaveOn.translate_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) : ConcaveOn 𝕜 ((f
un z => c + z) ⁻¹' s) (f ∘ fun z => c + z)
参数：hf : ConcaveOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.translate_right`：ConvexOn.translate_right (hf : ConvexOn 𝕜 s f)
 (c : E) : ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z)
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
Right translation preserves concavity.
-/
theorem ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves convexity. -/
/-
**ConvexOn.translate_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (c : E) : ConvexOn 𝕜 ((fun z
 => c + z) ⁻¹' s) (f ∘ fun z => z + c)
参数：hf : ConvexOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ConvexOn.translate_right`：ConvexOn.translate_right (hf : ConvexOn 𝕜 s f)
 (c : E) : ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z)

--- 原说明 ---
Left translation preserves convexity.
-/
theorem ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm c] using hf.translate_right c

/-- Left translation preserves concavity. -/
/-
**ConcaveOn.translate_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) : ConcaveOn 𝕜 ((fu
n z => c + z) ⁻¹' s) (f ∘ fun z => z + c)
参数：hf : ConcaveOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.translate_left`：ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (
c : E) : ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c)
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
Left translation preserves concavity.
-/
theorem ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) :=
  hf.dual.translate_left _

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 β]

/-
**convexOn_iff_forall_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_iff_forall_pos {s : Set E} {f : E -> β} : ConvexOn 𝕜 s f ↔ Convex
 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 
< b -> a + b = 1 -> f (a • x + b • y) <= a • f x + b • f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem convexOn_iff_forall_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
      a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
  refine and_congr_right'
    ⟨fun h x hx y hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    subst b
    simp_rw [zero_smul, zero_add, one_smul, le_rfl]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    subst a
    simp_rw [zero_smul, add_zero, one_smul, le_rfl]
  exact h hx hy ha' hb' hab
/-
**concaveOn_iff_forall_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_iff_forall_pos {s : Set E} {f : E -> β} : ConcaveOn 𝕜 s f ↔ Conv
ex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 
0 < b -> a + b = 1 -> a • f x + b • f y <= f (a • x + b • y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_iff_forall_pos`：convexOn_iff_forall_pos {s : Set E} {f : E -> β
} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> fo
rall ⦃a b : 𝕜…
-/
theorem concaveOn_iff_forall_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
        a • f x + b • f y ≤ f (a • x + b • y) :=
  convexOn_iff_forall_pos (β := βᵒᵈ)
/-
**convexOn_iff_pairwise_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_iff_pairwise_pos {s : Set E} {f : E -> β} : ConvexOn 𝕜 s f ↔ Conv
ex 𝕜 s ∧ s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> 
f (a • x + b • y) <= a • f x + b • f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexOn_iff_forall_pos`：convexOn_iff_forall_pos {s : Set E} {f : E -> β
} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> fo
rall ⦃a b : 𝕜…
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem convexOn_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
  rw [convexOn_iff_forall_pos]
  refine
    and_congr_right'
      ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
  exact h hx hy hxy ha hb hab
/-
**concaveOn_iff_pairwise_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_iff_pairwise_pos {s : Set E} {f : E -> β} : ConcaveOn 𝕜 s f ↔ Co
nvex 𝕜 s ∧ s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -
> a • f x + b • f y <= f (a • x + b • y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_iff_pairwise_pos`：convexOn_iff_pairwise_pos {s : Set E} {f : E 
-> β} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 
< a -> 0 < b ->…
-/
theorem concaveOn_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y) :=
  convexOn_iff_pairwise_pos (β := βᵒᵈ)

/-- A linear map is convex. -/
/-
**LinearMap.convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.convexOn (f : E ->ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : Convex
On 𝕜 s f
参数：f : E ->ₗ[𝕜] β；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A linear map is convex.
-/
theorem LinearMap.convexOn (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- A linear map is concave. -/
/-
**LinearMap.concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.concaveOn (f : E ->ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : Conca
veOn 𝕜 s f
参数：f : E ->ₗ[𝕜] β；hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A linear map is concave.
-/
theorem LinearMap.concaveOn (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩
/-
**StrictConvexOn.convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.convexOn {s : Set E} {f : E -> β} (hf : StrictConvexOn 𝕜 s 
f) : ConvexOn 𝕜 s f
参数：hf : StrictConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convexOn_iff_pairwise_pos`：convexOn_iff_pairwise_pos {s : Set E} {f : E 
-> β} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 
< a -> 0 < b ->…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem StrictConvexOn.convexOn {s : Set E} {f : E → β} (hf : StrictConvexOn 𝕜 s f) :
    ConvexOn 𝕜 s f :=
  convexOn_iff_pairwise_pos.mpr
    ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩
/-
**StrictConcaveOn.concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.concaveOn {s : Set E} {f : E -> β} (hf : StrictConcaveOn 𝕜
 s f) : ConcaveOn 𝕜 s f
参数：hf : StrictConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.concaveOn {s : Set E} {f : E → β} (hf : StrictConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s f :=
  hf.dual.convexOn

section PosSMulMono

variable [IsOrderedAddMonoid β] [PosSMulMono 𝕜 β] {s : Set E} {f : E → β}

/-
**StrictConvexOn.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.convex_lt (hf : StrictConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({
 x in s | f x < r })
参数：hf : StrictConvexOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_pairwise_pos`：convex_iff_pairwise_pos : Convex 𝕜 s ↔ s.Pairwi
se fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in 
s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem StrictConvexOn.convex_lt (hf : StrictConvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ ≤ a • r + b • r := by
          gcongr
          · exact hx.2.le
          · exact hy.2.le
        _ = r := Convex.combo_self hab r
        ⟩
/-
**StrictConcaveOn.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.convex_gt (hf : StrictConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 
({ x in s | r < f x })
参数：hf : StrictConcaveOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.convex_lt`：StrictConvexOn.convex_lt (hf : StrictConvexOn 
𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | f x < r })
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.convex_gt (hf : StrictConcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end PosSMulMono

section LinearOrder

variable [LinearOrder E] {s : Set E} {f : E → β}

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y` and positive `a`,
`b`. The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order.
-/
/-
**LinearOrder.convexOn_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearOrder.convexOn_of_lt (hs : Convex 𝕜 s) (hf : forall ⦃x⦄, x in s -> f
orall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> f
 (a • x + b • y) <= a • f x + b • f y) : ConvexOn 𝕜 s f
参数：hs : Convex 𝕜 s；hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> for
all ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> f (a • x + b • y) <= a • f x + b •
 f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convexOn_iff_pairwise_pos`：convexOn_iff_pairwise_pos {s : Set E} {f : E 
-> β} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 
< a -> 0 < b ->…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
For a function on a convex set in a linearly ordered space (where the order and 
the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, 
it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y` a
nd positive `a`,
`b`. The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with 
lexicographic order.
-/
theorem LinearOrder.convexOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ a • f x + b • f y) :
    ConvexOn 𝕜 s f := by
  refine convexOn_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is concave it suffices to
verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` for `x < y` and positive `a`, `b`. The
main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with lexicographic order. -/
/-
**LinearOrder.concaveOn_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearOrder.concaveOn_of_lt (hs : Convex 𝕜 s) (hf : forall ⦃x⦄, x in s -> 
forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> 
a • f x + b • f y <= f (a • x + b • y)) : ConcaveOn 𝕜 s f
参数：hs : Convex 𝕜 s；hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> for
all ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • f x + b • f y <= f (a • x + b 
• y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.convexOn_of_lt`：LinearOrder.convexOn_of_lt (hs : Convex 𝕜 s)
 (hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 
< a -> 0 < b -> …

--- 原说明 ---
For a function on a convex set in a linearly ordered space (where the order and 
the algebraic
structures aren't necessarily compatible), in order to prove that it is concave 
it suffices to
verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` for `x < y` and po
sitive `a`, `b`. The
main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with lexicogra
phic order.
-/
theorem LinearOrder.concaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      a • f x + b • f y ≤ f (a • x + b • y)) :
    ConcaveOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt (β := βᵒᵈ) hs hf

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly convex, it suffices
to verify the inequality `f (a • x + b • y) < a • f x + b • f y` for `x < y` and positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
/-
**LinearOrder.strictConvexOn_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearOrder.strictConvexOn_of_lt (hs : Convex 𝕜 s) (hf : forall ⦃x⦄, x in 
s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 
1 -> f (a • x + b • y) < a • f x + b • f y) : StrictConvexOn 𝕜 s f
参数：hs : Convex 𝕜 s；hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> for
all ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> f (a • x + b • y) < a • f x + b • 
f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
For a function on a convex set in a linearly ordered space (where the order and 
the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly
 convex, it suffices
to verify the inequality `f (a • x + b • y) < a • f x + b • f y` for `x < y` and
 positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexic
ographic order.
-/
theorem LinearOrder.strictConvexOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) < a • f x + b • f y) :
    StrictConvexOn 𝕜 s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly concave it suffices
to verify the inequality `a • f x + b • f y < f (a • x + b • y)` for `x < y` and positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
/-
**LinearOrder.strictConcaveOn_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearOrder.strictConcaveOn_of_lt (hs : Convex 𝕜 s) (hf : forall ⦃x⦄, x in
 s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b =
 1 -> a • f x + b • f y < f (a • x + b • y)) : StrictConcaveOn 𝕜 s f
参数：hs : Convex 𝕜 s；hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> for
all ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • f x + b • f y < f (a • x + b •
 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.strictConvexOn_of_lt`：LinearOrder.strictConvexOn_of_lt (hs :
 Convex 𝕜 s) (hf : forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x < y -> forall ⦃
a b : 𝕜⦄, 0 < a -> 0 <…

--- 原说明 ---
For a function on a convex set in a linearly ordered space (where the order and 
the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly
 concave it suffices
to verify the inequality `a • f x + b • f y < f (a • x + b • y)` for `x < y` and
 positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexic
ographic order.
-/
theorem LinearOrder.strictConcaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      a • f x + b • f y < f (a • x + b • y)) :
    StrictConcaveOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt (β := βᵒᵈ) hs hf

end LinearOrder

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

/-- If `f` is convex on `s`, so is `(f ∘ g)` on `g ⁻¹' s` for a linear `g`. -/
/-
**ConvexOn.comp_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.comp_linearMap {f : F -> β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g 
: E ->ₗ[𝕜] F) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)
参数：hf : ConvexOn 𝕜 s f；g : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.linear_preimage`：Convex.linear_preimage {s : Set F} (hs : Convex 
𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` is convex on `s`, so is `(f ∘ g)` on `g ⁻¹' s` for a linear `g`.
-/
theorem ConvexOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.linear_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

/-- If `f` is concave on `s`, so is `(g ∘ f)` on `g ⁻¹' s` for a linear `g`. -/
/-
**ConcaveOn.comp_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.comp_linearMap {f : F -> β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (
g : E ->ₗ[𝕜] F) : ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g)
参数：hf : ConcaveOn 𝕜 s f；g : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.comp_linearMap`：ConvexOn.comp_linearMap {f : F -> β} {s : Set F
} (hf : ConvexOn 𝕜 s f) (g : E ->ₗ[𝕜] F) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
If `f` is concave on `s`, so is `(g ∘ f)` on `g ⁻¹' s` for a linear `g`.
-/
theorem ConcaveOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_linearMap g

end Module

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]

section DistribMulAction

variable [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

/-
**StrictConvexOn.add_convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.add_convexOn (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s
 g) : StrictConvexOn 𝕜 s (f + g)
参数：hf : StrictConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
theorem StrictConvexOn.add_convexOn (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩
/-
**ConvexOn.add_strictConvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.add_strictConvexOn (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s
 g) : StrictConvexOn 𝕜 s (f + g)
参数：hf : ConvexOn 𝕜 s f；hg : StrictConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.add_convexOn`：StrictConvexOn.add_convexOn (hf : StrictCon
vexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem ConvexOn.add_strictConvexOn (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  add_comm g f ▸ hg.add_convexOn hf
/-
**StrictConvexOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
 : StrictConvexOn 𝕜 s (f + g)
参数：hf : StrictConvexOn 𝕜 s f；hg : StrictConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
theorem StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩
/-
**StrictConcaveOn.add_concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.add_concaveOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn
 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g)
参数：hf : StrictConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.add_convexOn`：StrictConvexOn.add_convexOn (hf : StrictCon
vexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem StrictConcaveOn.add_concaveOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_convexOn hg.dual
/-
**ConcaveOn.add_strictConcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.add_strictConcaveOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn
 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g)
参数：hf : ConcaveOn 𝕜 s f；hg : StrictConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.add_strictConvexOn`：ConvexOn.add_strictConvexOn (hf : ConvexOn 
𝕜 s f) (hg : StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem ConcaveOn.add_strictConcaveOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_strictConvexOn hg.dual
/-
**StrictConcaveOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s
 g) : StrictConcaveOn 𝕜 s (f + g)
参数：hf : StrictConcaveOn 𝕜 s f；hg : StrictConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.add`：StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg :
 StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg
/-
**StrictConvexOn.add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.add_const {γ : Type*} {f : E -> γ} [AddCommMonoid γ] [Parti
alOrder γ] [IsOrderedCancelAddMonoid γ] [Module 𝕜 γ] (hf : StrictConvexOn 𝕜 s f)
 (b : γ) : StrictConvexOn 𝕜 s (f + fun _ => b)
参数：hf : StrictConvexOn 𝕜 s f；b : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.add_convexOn`：StrictConvexOn.add_convexOn (hf : StrictCon
vexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `convexOn_const`：convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s 
fun _ : E => c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem StrictConvexOn.add_const {γ : Type*} {f : E → γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConvexOn 𝕜 s f) (b : γ) : StrictConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add_convexOn (convexOn_const _ hf.1)
/-
**StrictConcaveOn.add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.add_const {γ : Type*} {f : E -> γ} [AddCommMonoid γ] [Part
ialOrder γ] [IsOrderedCancelAddMonoid γ] [Module 𝕜 γ] (hf : StrictConcaveOn 𝕜 s 
f) (b : γ) : StrictConcaveOn 𝕜 s (f + fun _ => b)
参数：hf : StrictConcaveOn 𝕜 s f；b : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConcaveOn.add_concaveOn`：StrictConcaveOn.add_concaveOn (hf : Stric
tConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g)
· 使用定理 `concaveOn_const`：concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜
 s fun _ => c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem StrictConcaveOn.add_const {γ : Type*} {f : E → γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConcaveOn 𝕜 s f) (b : γ) : StrictConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add_concaveOn (concaveOn_const _ hf.1)

end DistribMulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f : E → β}

/-
**ConvexOn.convex_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | f 
x < r })
参数：hf : ConvexOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_forall_pos`：convex_iff_forall_pos : Convex 𝕜 s ↔ forall ⦃x⦄, 
x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
 a • x + b …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r :=
          (add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hx.2 ha)
            (smul_le_smul_of_nonneg_left hy.2.le hb.le))
        _ = r := Convex.combo_self hab _⟩
/-
**ConcaveOn.convex_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.convex_gt (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x in s | 
r < f x })
参数：hf : ConcaveOn 𝕜 s f；r : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.convex_lt`：ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : C
onvex 𝕜 ({ x in s | f x < r })
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.convex_gt (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r
/-
**ConvexOn.openSegment_subset_strict_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.openSegment_subset_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E
 × β) (hp : p.1 in s ∧ f p.1 < p.2) (hq : q.1 in s ∧ f q.1 <= q.2) : openSegment
 𝕜 p q subseteq { p : E × β | p.1 in s ∧ f p.1 < p.2 }
参数：hf : ConvexOn 𝕜 s f；p q : E × β；hp : p.1 in s ∧ f p.1 < p.2；hq : q.1 in s ∧ f
 q.1 <= q.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
-/
theorem ConvexOn.openSegment_subset_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β)
    (hp : p.1 ∈ s ∧ f p.1 < p.2) (hq : q.1 ∈ s ∧ f q.1 ≤ q.2) :
    openSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, ?_⟩
  calc
    f (a • p.1 + b • q.1) ≤ a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab
    _ < a • p.2 + b • q.2 := add_lt_add_of_lt_of_le
       (smul_lt_smul_of_pos_left hp.2 ha) (smul_le_smul_of_nonneg_left hq.2 hb.le)
/-
**ConcaveOn.openSegment_subset_strict_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.openSegment_subset_strict_hypograph (hf : ConcaveOn 𝕜 s f) (p q 
: E × β) (hp : p.1 in s ∧ p.2 < f p.1) (hq : q.1 in s ∧ q.2 <= f q.1) : openSegm
ent 𝕜 p q subseteq { p : E × β | p.1 in s ∧ p.2 < f p.1 }
参数：hf : ConcaveOn 𝕜 s f；p q : E × β；hp : p.1 in s ∧ p.2 < f p.1；hq : q.1 in s ∧ 
q.2 <= f q.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.openSegment_subset_strict_epigraph`：ConvexOn.openSegment_subset
_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β) (hp : p.1 in s ∧ f p.1 < p.
2) (hq : q.1 in s ∧ f q.1 <= q.2)…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.openSegment_subset_strict_hypograph (hf : ConcaveOn 𝕜 s f) (p q : E × β)
    (hp : p.1 ∈ s ∧ p.2 < f p.1) (hq : q.1 ∈ s ∧ q.2 ≤ f q.1) :
    openSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.openSegment_subset_strict_epigraph p q hp hq
/-
**ConvexOn.convex_strict_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.convex_strict_epigraph [ZeroLEOneClass 𝕜] (hf : ConvexOn 𝕜 s f) :
 Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 < p.2 }
参数：hf : ConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_openSegment_subset`：convex_iff_openSegment_subset [ZeroLEOneC
lass 𝕜] : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> openSegment 𝕜
 x y subseteq s
· 使用定理 `ConvexOn.openSegment_subset_strict_epigraph`：ConvexOn.openSegment_subset
_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β) (hp : p.1 in s ∧ f p.1 < p.
2) (hq : q.1 in s ∧ f q.1 <= q.2)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ConvexOn.convex_strict_epigraph [ZeroLEOneClass 𝕜] (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } :=
  convex_iff_openSegment_subset.mpr fun p hp q hq =>
    hf.openSegment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩
/-
**ConcaveOn.convex_strict_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.convex_strict_hypograph [ZeroLEOneClass 𝕜] (hf : ConcaveOn 𝕜 s f
) : Convex 𝕜 { p : E × β | p.1 in s ∧ p.2 < f p.1 }
参数：hf : ConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.convex_strict_epigraph`：ConvexOn.convex_strict_epigraph [ZeroLE
OneClass 𝕜] (hf : ConvexOn 𝕜 s f) : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 < p.
2 }
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.convex_strict_hypograph [ZeroLEOneClass 𝕜] (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.convex_strict_epigraph

end Module

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E}
  {f g : E → β}

/-- The pointwise maximum of convex functions is convex. -/
/-
**ConvexOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f
 ⊔ g)
参数：hf : ConvexOn 𝕜 s f；hg : ConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
The pointwise maximum of convex functions is convex.
-/
theorem ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f ⊔ g) := by
  refine ⟨hf.left, fun x hx y hy a b ha hb hab => sup_le ?_ ?_⟩
  · calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.right hx hy ha hb hab
      _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left
  · calc
      g (a • x + b • y) ≤ a • g x + b • g y := hg.right hx hy ha hb hab
      _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right

/-- The pointwise minimum of concave functions is concave. -/
/-
**ConcaveOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.inf (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 
s (f ⊓ g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.sup`：ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
 ConvexOn 𝕜 s (f ⊔ g)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
The pointwise minimum of concave functions is concave.
-/
theorem ConcaveOn.inf (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

/-- The pointwise maximum of strictly convex functions is strictly convex. -/
/-
**StrictConvexOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g)
 : StrictConvexOn 𝕜 s (f ⊔ g)
参数：hf : StrictConvexOn 𝕜 s f；hg : StrictConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
The pointwise maximum of strictly convex functions is strictly convex.
-/
theorem StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f ⊔ g) :=
  ⟨hf.left, fun x hx y hy hxy a b ha hb hab =>
    max_lt
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left)
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right)⟩

/-- The pointwise minimum of strictly concave functions is strictly concave. -/
/-
**StrictConcaveOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.inf (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s
 g) : StrictConcaveOn 𝕜 s (f ⊓ g)
参数：hf : StrictConcaveOn 𝕜 s f；hg : StrictConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.sup`：StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg :
 StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f ⊔ g)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
The pointwise minimum of strictly concave functions is strictly concave.
-/
theorem StrictConcaveOn.inf (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
/-
**ConvexOn.le_on_segment'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy 
: y in s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) : f (a • x + b
 • y) <= max (f x) (f y)
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 <= a；hb : 0 <= b；hab : a +
 b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x

--- 原说明 ---
A convex function on a segment is upper-bounded by the max of its endpoints.
-/
theorem ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : f (a • x + b • y) ≤ max (f x) (f y) :=
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
/-
**ConcaveOn.ge_on_segment'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.ge_on_segment' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in s) (h
y : y in s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) : min (f x) 
(f y) <= f (a • x + b • y)
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 <= a；hb : 0 <= b；hab : a 
+ b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_on_segment'`：ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {
x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 <= b) (hab 
: a + b = 1) …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
A concave function on a segment is lower-bounded by the min of its endpoints.
-/
theorem ConcaveOn.ge_on_segment' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) :=
  hf.dual.le_on_segment' hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
/-
**ConvexOn.le_on_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy
 : y in s) (hz : z in [x -[𝕜] y]) : f z <= max (f x) (f y)
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in [x -[𝕜] y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_on_segment'`：ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {
x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 <= a) (hb : 0 <= b) (hab 
: a + b = 1) …

--- 原说明 ---
A convex function on a segment is upper-bounded by the max of its endpoints.
-/
theorem ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : f z ≤ max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
/-
**ConcaveOn.ge_on_segment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.ge_on_segment (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x in s) (
hy : y in s) (hz : z in [x -[𝕜] y]) : min (f x) (f y) <= f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in [x -[𝕜] y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_on_segment`：ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x 
y z : E} (hx : x in s) (hy : y in s) (hz : z in [x -[𝕜] y]) : f z <= max (f x) (
f y)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
A concave function on a segment is lower-bounded by the min of its endpoints.
-/
theorem ConcaveOn.ge_on_segment (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : min (f x) (f y) ≤ f z :=
  hf.dual.le_on_segment hx hy hz

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
/-
**StrictConvexOn.lt_on_open_segment'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn 𝕜 s f) {x y : E} (
hx : x in s) (hy : y in s) (hxy : x != y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (h
ab : a + b = 1) : f (a • x + b • y) < max (f x) (f y)
参数：hf : StrictConvexOn 𝕜 s f；hx : x in s；hy : y in s；hxy : x != y；ha : 0 < a；hb 
: 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x

--- 原说明 ---
A strictly convex function on an open segment is strictly upper-bounded by the m
ax of its
endpoints.
-/
theorem StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    f (a • x + b • y) < max (f x) (f y) :=
  calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
/-
**StrictConcaveOn.lt_on_open_segment'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn 𝕜 s f) {x y : E}
 (hx : x in s) (hy : y in s) (hxy : x != y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) 
(hab : a + b = 1) : min (f x) (f y) < f (a • x + b • y)
参数：hf : StrictConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hxy : x != y；ha : 0 < a；hb
 : 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.lt_on_open_segment'`：StrictConvexOn.lt_on_open_segment' (
hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) (hxy : x != y) 
{a b : 𝕜} (ha : 0 < a) (…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
A strictly concave function on an open segment is strictly lower-bounded by the 
min of its
endpoints.
-/
theorem StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    min (f x) (f y) < f (a • x + b • y) :=
  hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
/-
**StrictConvexOn.lt_on_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.lt_on_openSegment (hf : StrictConvexOn 𝕜 s f) {x y z : E} (
hx : x in s) (hy : y in s) (hxy : x != y) (hz : z in openSegment 𝕜 x y) : f z < 
max (f x) (f y)
参数：hf : StrictConvexOn 𝕜 s f；hx : x in s；hy : y in s；hxy : x != y；hz : z in open
Segment 𝕜 x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.lt_on_open_segment'`：StrictConvexOn.lt_on_open_segment' (
hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) (hxy : x != y) 
{a b : 𝕜} (ha : 0 < a) (…

--- 原说明 ---
A strictly convex function on an open segment is strictly upper-bounded by the m
ax of its
endpoints.
-/
theorem StrictConvexOn.lt_on_openSegment (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ openSegment 𝕜 x y) : f z < max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
/-
**StrictConcaveOn.lt_on_openSegment** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_on_openSegment (hf : StrictConcaveOn 𝕜 s f) {x y z : E}
 (hx : x in s) (hy : y in s) (hxy : x != y) (hz : z in openSegment 𝕜 x y) : min 
(f x) (f y) < f z
参数：hf : StrictConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hxy : x != y；hz : z in ope
nSegment 𝕜 x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.lt_on_openSegment`：StrictConvexOn.lt_on_openSegment (hf :
 StrictConvexOn 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hxy : x != y) (h
z : z in openSegment 𝕜…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
A strictly concave function on an open segment is strictly lower-bounded by the 
min of its
endpoints.
-/
theorem StrictConcaveOn.lt_on_openSegment (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ openSegment 𝕜 x y) : min (f x) (f y) < f z :=
  hf.dual.lt_on_openSegment hx hy hxy hz

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

section PosSMulStrictMono

variable [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f g : E → β}

/-
**ConvexOn.le_left_of_right_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_left_of_right_le' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s
) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) (hfy : f 
y <= f (a • x + b • y)) : f (a • x + b • y) <= f x
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 < a；hb : 0 <= b；hab : a + 
b = 1；hfy : f y <= f (a • x + b • y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
-/
theorem ConvexOn.le_left_of_right_le' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f y ≤ f (a • x + b • y)) :
    f (a • x + b • y) ≤ f x :=
  le_of_not_gt fun h ↦ lt_irrefl (f (a • x + b • y)) <|
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_lt_of_le
          (smul_lt_smul_of_pos_left h ha) (smul_le_smul_of_nonneg_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _
/-
**ConcaveOn.left_le_of_le_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.left_le_of_le_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in
 s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 <= b) (hab : a + b = 1) (hfy : 
f (a • x + b • y) <= f y) : f x <= f (a • x + b • y)
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 < a；hb : 0 <= b；hab : a +
 b = 1；hfy : f (a • x + b • y) <= f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_left_of_right_le'`：ConvexOn.le_left_of_right_le' (hf : Conve
xOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 
<= b) (hab : a + b …
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.left_le_of_le_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f (a • x + b • y) ≤ f y) :
    f x ≤ f (a • x + b • y) :=
  hf.dual.le_left_of_right_le' hx hy ha hb hab hfy
/-
**ConvexOn.le_right_of_left_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_right_of_left_le' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (h
x : x in s) (hy : y in s) (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) (hfx : f 
x <= f (a • x + b • y)) : f (a • x + b • y) <= f y
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 <= a；hb : 0 < b；hab : a + 
b = 1；hfx : f x <= f (a • x + b • y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ConvexOn.le_left_of_right_le'`：ConvexOn.le_left_of_right_le' (hf : Conve
xOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 
<= b) (hab : a + b …
-/
theorem ConvexOn.le_right_of_left_le' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x ≤ f (a • x + b • y)) :
    f (a • x + b • y) ≤ f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx
/-
**ConcaveOn.right_le_of_le_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.right_le_of_le_left' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} 
(hx : x in s) (hy : y in s) (ha : 0 <= a) (hb : 0 < b) (hab : a + b = 1) (hfx : 
f (a • x + b • y) <= f x) : f y <= f (a • x + b • y)
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 <= a；hb : 0 < b；hab : a +
 b = 1；hfx : f (a • x + b • y) <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_right_of_left_le'`：ConvexOn.le_right_of_left_le' (hf : Conve
xOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s) (hy : y in s) (ha : 0 <= a) (hb : 0
 < b) (hab : a + b …
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.right_le_of_le_left' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) ≤ f x) :
    f y ≤ f (a • x + b • y) :=
  hf.dual.le_right_of_left_le' hx hy ha hb hab hfx
/-
**ConvexOn.le_left_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_left_of_right_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in 
s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hyz : f y <= f z) : f z <= f x
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hyz :
 f y <= f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_left_of_right_le'`：ConvexOn.le_left_of_right_le' (hf : Conve
xOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 
<= b) (hab : a + b …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ConvexOn.le_left_of_right_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f y ≤ f z) : f z ≤ f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz
/-
**ConcaveOn.left_le_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.left_le_of_le_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x i
n s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hyz : f z <= f y) : f x <= f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hyz 
: f z <= f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_left_of_right_le`：ConvexOn.le_left_of_right_le (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hyz : f y <= f z) …
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.left_le_of_le_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f z ≤ f y) : f x ≤ f z :=
  hf.dual.le_left_of_right_le hx hy hz hyz
/-
**ConvexOn.le_right_of_left_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_right_of_left_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in 
s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hxz : f x <= f z) : f z <= f y
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hxz :
 f x <= f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_right_of_left_le'`：ConvexOn.le_right_of_left_le' (hf : Conve
xOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s) (hy : y in s) (ha : 0 <= a) (hb : 0
 < b) (hab : a + b …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ConvexOn.le_right_of_left_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f x ≤ f z) : f z ≤ f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz
/-
**ConcaveOn.right_le_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.right_le_of_le_left (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x i
n s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hxz : f z <= f x) : f y <= f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hxz 
: f z <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_right_of_left_le`：ConvexOn.le_right_of_left_le (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hxz : f x <= f z) …
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.right_le_of_le_left (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f z ≤ f x) : f y ≤ f z :=
  hf.dual.le_right_of_left_le hx hy hz hxz

end PosSMulStrictMono

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f g : E → β}

/-! The following lemmas don't require `Module 𝕜 E` if you add the hypothesis `x ≠ y`. At the time
of the writing, we decided the resulting lemmas wouldn't be useful. Feel free to reintroduce them.
-/

/-
**ConvexOn.lt_left_of_right_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.lt_left_of_right_lt' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x in s
) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y
 < f (a • x + b • y)) : f (a • x + b • y) < f x
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 < a；hb : 0 < b；hab : a + b
 = 1；hfy : f y < f (a • x + b • y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x

--- 原说明 ---
The following lemmas don't require `Module 𝕜 E` if you add the hypothesis `x ≠ y
`. At the time
of the writing, we decided the resulting lemmas wouldn't be useful. Feel free to
 reintroduce them.
-/
theorem ConvexOn.lt_left_of_right_lt' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y < f (a • x + b • y)) :
    f (a • x + b • y) < f x :=
  not_le.1 fun h ↦ lt_irrefl (f (a • x + b • y)) <|
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb.le hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_le_of_lt
          (smul_le_smul_of_nonneg_left h ha.le) (smul_lt_smul_of_pos_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _
/-
**ConcaveOn.left_lt_of_lt_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.left_lt_of_lt_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x in
 s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f
 (a • x + b • y) < f y) : f x < f (a • x + b • y)
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 < a；hb : 0 < b；hab : a + 
b = 1；hfy : f (a • x + b • y) < f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.lt_left_of_right_lt'`：ConvexOn.lt_left_of_right_lt' (hf : Conve
xOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 
< b) (hab : a + b =…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.left_lt_of_lt_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f (a • x + b • y) < f y) :
    f x < f (a • x + b • y) :=
  hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy
/-
**ConvexOn.lt_right_of_left_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.lt_right_of_left_lt' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (h
x : x in s) (hy : y in s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x
 < f (a • x + b • y)) : f (a • x + b • y) < f y
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 < a；hb : 0 < b；hab : a + b
 = 1；hfx : f x < f (a • x + b • y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ConvexOn.lt_left_of_right_lt'`：ConvexOn.lt_left_of_right_lt' (hf : Conve
xOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 
< b) (hab : a + b =…
-/
theorem ConvexOn.lt_right_of_left_lt' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x < f (a • x + b • y)) :
    f (a • x + b • y) < f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx
/-
**ConcaveOn.lt_right_of_left_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.lt_right_of_left_lt' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} 
(hx : x in s) (hy : y in s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f
 (a • x + b • y) < f x) : f y < f (a • x + b • y)
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；ha : 0 < a；hb : 0 < b；hab : a + 
b = 1；hfx : f (a • x + b • y) < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.lt_right_of_left_lt'`：ConvexOn.lt_right_of_left_lt' (hf : Conve
xOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s) (hy : y in s) (ha : 0 < a) (hb : 0 
< b) (hab : a + b =…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.lt_right_of_left_lt' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) < f x) :
    f y < f (a • x + b • y) :=
  hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx
/-
**ConvexOn.lt_left_of_right_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.lt_left_of_right_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in 
s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hyz : f y < f z) : f z < f x
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hyz :
 f y < f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.lt_left_of_right_lt'`：ConvexOn.lt_left_of_right_lt' (hf : Conve
xOn 𝕜 s f) {x y : E} (hx : x in s) (hy : y in s) {a b : 𝕜} (ha : 0 < a) (hb : 0 
< b) (hab : a + b =…
-/
theorem ConvexOn.lt_left_of_right_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f y < f z) : f z < f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz
/-
**ConcaveOn.left_lt_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.left_lt_of_lt_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x i
n s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hyz : f z < f y) : f x < f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hyz 
: f z < f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.lt_left_of_right_lt`：ConvexOn.lt_left_of_right_lt (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hyz : f y < f z) :…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.left_lt_of_lt_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f z < f y) : f x < f z :=
  hf.dual.lt_left_of_right_lt hx hy hz hyz
/-
**ConvexOn.lt_right_of_left_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.lt_right_of_left_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x in 
s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hxz : f x < f z) : f z < f y
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hxz :
 f x < f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.lt_right_of_left_lt'`：ConvexOn.lt_right_of_left_lt' (hf : Conve
xOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x in s) (hy : y in s) (ha : 0 < a) (hb : 0 
< b) (hab : a + b =…
-/
theorem ConvexOn.lt_right_of_left_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f x < f z) : f z < f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz
/-
**ConcaveOn.lt_right_of_left_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.lt_right_of_left_lt (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x i
n s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (hxz : f z < f x) : f y < f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in openSegment 𝕜 x y；hxz 
: f z < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.lt_right_of_left_lt`：ConvexOn.lt_right_of_left_lt (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hxz : f x < f z) :…
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.lt_right_of_left_lt (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f z < f x) : f y < f z :=
  hf.dual.lt_right_of_left_lt hx hy hz hxz

end Module

end LinearOrderedCancelAddCommMonoid

section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
  {s : Set E} {f g : E → β}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp]
/-
**neg_convexOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
A function `-f` is convex iff `f` is concave.
-/
theorem neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    simpa [add_comm] using h hx hy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
    rw [← neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy ha hb hab

/-- A function `-f` is concave iff `f` is convex. -/
@[simp]
/-
**neg_concaveOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_concaveOn_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_convexOn_iff`：neg_convexOn_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function `-f` is concave iff `f` is convex.
-/
theorem neg_concaveOn_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f := by
  rw [← neg_convexOn_iff, neg_neg f]

/-- A function `-f` is strictly convex iff `f` is strictly concave. -/
@[simp]
/-
**neg_strictConvexOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_strictConvexOn_iff : StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
A function `-f` is strictly convex iff `f` is strictly concave.
-/
theorem neg_strictConvexOn_iff : StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    simp only [ne_eq, Pi.neg_apply, smul_neg, lt_add_neg_iff_add_lt, add_comm,
      add_neg_lt_iff_lt_add] at h
    exact h hx hy hxy ha hb hab
  · rintro ⟨hconv, h⟩
    refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
    rw [← neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_neg]
    exact h hx hy hxy ha hb hab

/-- A function `-f` is strictly concave iff `f` is strictly convex. -/
@[simp]
/-
**neg_strictConcaveOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_strictConcaveOn_iff : StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_strictConvexOn_iff`：neg_strictConvexOn_iff : StrictConvexOn 𝕜 s (-f)
 ↔ StrictConcaveOn 𝕜 s f
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function `-f` is strictly concave iff `f` is strictly convex.
-/
theorem neg_strictConcaveOn_iff : StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f := by
  rw [← neg_strictConvexOn_iff, neg_neg f]

alias ⟨_, ConcaveOn.neg⟩ := neg_convexOn_iff

alias ⟨_, ConvexOn.neg⟩ := neg_concaveOn_iff

alias ⟨_, StrictConcaveOn.neg⟩ := neg_strictConvexOn_iff

alias ⟨_, StrictConvexOn.neg⟩ := neg_strictConcaveOn_iff
/-
**ConvexOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.sub (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConvexOn 𝕜 s (
f - g)
参数：hf : ConvexOn 𝕜 s f；hg : ConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.add`：ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
 ConvexOn 𝕜 s (f + g)
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem ConvexOn.sub (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg
/-
**ConcaveOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.sub (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConcaveOn 𝕜 s
 (f - g)
参数：hf : ConcaveOn 𝕜 s f；hg : ConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.add`：ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s 
g) : ConcaveOn 𝕜 s (f + g)
· 使用定理 `ConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCom
mG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem ConcaveOn.sub (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg
/-
**StrictConvexOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.sub (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g
) : StrictConvexOn 𝕜 s (f - g)
参数：hf : StrictConvexOn 𝕜 s f；hg : StrictConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.add`：StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg :
 StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem StrictConvexOn.sub (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg
/-
**StrictConcaveOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.sub (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s 
g) : StrictConcaveOn 𝕜 s (f - g)
参数：hf : StrictConcaveOn 𝕜 s f；hg : StrictConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConcaveOn.add`：StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (h
g : StrictConcaveOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g)
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StrictConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst
 : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : 
AddCommG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem StrictConcaveOn.sub (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg
/-
**ConvexOn.sub_strictConcaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.sub_strictConcaveOn (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜
 s g) : StrictConvexOn 𝕜 s (f - g)
参数：hf : ConvexOn 𝕜 s f；hg : StrictConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.add_strictConvexOn`：ConvexOn.add_strictConvexOn (hf : ConvexOn 
𝕜 s f) (hg : StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem ConvexOn.sub_strictConcaveOn (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strictConvexOn hg.neg
/-
**ConcaveOn.sub_strictConvexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.sub_strictConvexOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜
 s g) : StrictConcaveOn 𝕜 s (f - g)
参数：hf : ConcaveOn 𝕜 s f；hg : StrictConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConcaveOn.add_strictConcaveOn`：ConcaveOn.add_strictConcaveOn (hf : Conca
veOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g)
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StrictConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst
 : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : 
AddCommG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem ConcaveOn.sub_strictConvexOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strictConcaveOn hg.neg
/-
**StrictConvexOn.sub_concaveOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.sub_concaveOn (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜
 s g) : StrictConvexOn 𝕜 s (f - g)
参数：hf : StrictConvexOn 𝕜 s f；hg : ConcaveOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.add_convexOn`：StrictConvexOn.add_convexOn (hf : StrictCon
vexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g)
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem StrictConvexOn.sub_concaveOn (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_convexOn hg.neg
/-
**StrictConcaveOn.sub_convexOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.sub_convexOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜
 s g) : StrictConcaveOn 𝕜 s (f - g)
参数：hf : StrictConcaveOn 𝕜 s f；hg : ConvexOn 𝕜 s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConcaveOn.add_concaveOn`：StrictConcaveOn.add_concaveOn (hf : Stric
tConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g)
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `ConvexOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Sem
iring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCom
mG…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem StrictConcaveOn.sub_convexOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_concaveOn hg.neg

end OrderedAddCommGroup

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [AddCommMonoid β] [PartialOrder β] [Module 𝕜 E] [SMul 𝕜 β]
  {s : Set E}
  {f : E → β}

/-- Right translation preserves strict convexity. -/
/-
**StrictConvexOn.translate_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.translate_right (hf : StrictConvexOn 𝕜 s f) (c : E) : Stric
tConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z)
参数：hf : StrictConvexOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.translate_preimage_right`：Convex.translate_preimage_right (hs : C
onvex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) ⁻¹' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G

--- 原说明 ---
Right translation preserves strict convexity.
-/
theorem StrictConvexOn.translate_right (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_comm, Convex.combo_self hab]
      _ < a • f (c + x) + b • f (c + y) := hf.2 hx hy ((add_right_injective c).ne hxy) ha hb hab⟩

/-- Right translation preserves strict concavity. -/
/-
**StrictConcaveOn.translate_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.translate_right (hf : StrictConcaveOn 𝕜 s f) (c : E) : Str
ictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z)
参数：hf : StrictConcaveOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.translate_right`：StrictConvexOn.translate_right (hf : Str
ictConvexOn 𝕜 s f) (c : E) : StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun 
z => c + z)
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
Right translation preserves strict concavity.
-/
theorem StrictConcaveOn.translate_right (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves strict convexity. -/
/-
**StrictConvexOn.translate_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.translate_left (hf : StrictConvexOn 𝕜 s f) (c : E) : Strict
ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c)
参数：hf : StrictConvexOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `StrictConvexOn.translate_right`：StrictConvexOn.translate_right (hf : Str
ictConvexOn 𝕜 s f) (c : E) : StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun 
z => c + z)

--- 原说明 ---
Left translation preserves strict convexity.
-/
theorem StrictConvexOn.translate_left (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm] using hf.translate_right c

/-- Left translation preserves strict concavity. -/
/-
**StrictConcaveOn.translate_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.translate_left (hf : StrictConcaveOn 𝕜 s f) (c : E) : Stri
ctConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c)
参数：hf : StrictConcaveOn 𝕜 s f；c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `StrictConcaveOn.translate_right`：StrictConcaveOn.translate_right (hf : S
trictConcaveOn 𝕜 s f) (c : E) : StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ 
fun z => c + z)

--- 原说明 ---
Left translation preserves strict concavity.
-/
theorem StrictConcaveOn.translate_left (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm] using hf.translate_right c

end AddCancelCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β] {s : Set E} {f : E → β}

/-
**ConvexOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.smul {c : 𝕜} (hc : 0 <= c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
un x => c • f x
参数：hc : 0 <= c；hf : ConvexOn 𝕜 s f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem ConvexOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s fun x => c • f x :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) ≤ c • (a • f x + b • f y) :=
        smul_le_smul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by rw [smul_add, smul_comm c, smul_comm c]⟩
/-
**ConcaveOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.smul {c : 𝕜} (hc : 0 <= c) (hf : ConcaveOn 𝕜 s f) : ConcaveOn 𝕜 
s fun x => c • f x
参数：hc : 0 <= c；hf : ConcaveOn 𝕜 s f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.smul`：ConvexOn.smul {c : 𝕜} (hc : 0 <= c) (hf : ConvexOn 𝕜 s f)
 : ConvexOn 𝕜 s fun x => c • f x
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s fun x => c • f x :=
  hf.dual.smul hc

end Module

end OrderedAddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup E] [AddCommGroup F]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
/-
**ConvexOn.comp_affineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.comp_affineMap {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : Set F} (hf : Co
nvexOn 𝕜 s f) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)
参数：g : E ->ᵃ[𝕜] F；hf : ConvexOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.affine_preimage`：Convex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set
 F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.combo_affine_apply`：Convex.combo_affine_apply {x y : E} {a b : 𝕜}
 {f : E ->ᵃ[𝕜] F} (h : a + b = 1) : f (a • x + b • y) = a • f x + b • f y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function is convex on `s`, it remains convex when precomposed by an affine 
map.
-/
theorem ConvexOn.comp_affineMap {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.affine_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      (f ∘ g) (a • x + b • y) = f (g (a • x + b • y)) := rfl
      _ = f (a • g x + b • g y) := by rw [Convex.combo_affine_apply hab]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
/-
**ConcaveOn.comp_affineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.comp_affineMap {f : F -> β} (g : E ->ᵃ[𝕜] F) {s : Set F} (hf : C
oncaveOn 𝕜 s f) : ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g)
参数：g : E ->ᵃ[𝕜] F；hf : ConcaveOn 𝕜 s f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.comp_affineMap`：ConvexOn.comp_affineMap {f : F -> β} (g : E ->ᵃ
[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g)
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
If a function is concave on `s`, it remains concave when precomposed by an affin
e map.
-/
theorem ConcaveOn.comp_affineMap {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_affineMap g

end Module

end OrderedAddCommMonoid

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E]

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β]

section SMul

variable [SMul 𝕜 E] [SMul 𝕜 β] {s : Set E}

/-
**convexOn_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexOn_iff_div {f : E -> β} : ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, 
x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b 
-> f ((a / (a + b)) • x + (b / (a + b)) • y) <= (a / (a + b)) • f x + (b / (a + 
b)) • f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem convexOn_iff_div {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
        f ((a / (a + b)) • x + (b / (a + b)) • y) ≤ (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl ⟨by
    intro h x hx y hy a b ha hb hab
    apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
    rw [← add_div, div_self hab.ne'], by
    intro h x hx y hy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy ha hb⟩
/-
**concaveOn_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：concaveOn_iff_div {f : E -> β} : ConcaveOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄
, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + 
b -> (a / (a + b)) • f x + (b / (a + b)) • f y <= f ((a / (a + b)) • x + (b / (a
 + b)) • y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexOn_iff_div`：convexOn_iff_div {f : E -> β} : ConvexOn 𝕜 s f ↔ Conve
x 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 
0 <= b…
-/
theorem concaveOn_iff_div {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
        (a / (a + b)) • f x + (b / (a + b)) • f y ≤ f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  convexOn_iff_div (β := βᵒᵈ)
/-
**strictConvexOn_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConvexOn_iff_div {f : E -> β} : StrictConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ 
forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a ->
 0 < b -> f ((a / (a + b)) • x + (b / (a + b)) • y) < (a / (a + b)) • f x + (b /
 (a + b)) • f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem strictConvexOn_iff_div {f : E → β} :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
        f ((a / (a + b)) • x + (b / (a + b)) • y) < (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl ⟨by
    intro h x hx y hy hxy a b ha hb
    have hab := add_pos ha hb
    apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
    rw [← add_div, div_self hab.ne'], by
    intro h x hx y hy hxy a b ha hb hab
    simpa [hab, zero_lt_one] using h hx hy hxy ha hb⟩
/-
**strictConcaveOn_iff_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictConcaveOn_iff_div {f : E -> β} : StrictConcaveOn 𝕜 s f ↔ Convex 𝕜 s 
∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a 
-> 0 < b -> (a / (a + b)) • f x + (b / (a + b)) • f y < f ((a / (a + b)) • x + (
b / (a + b)) • y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictConvexOn_iff_div`：strictConvexOn_iff_div {f : E -> β} : StrictConv
exOn 𝕜 s f ↔ Convex 𝕜 s ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> x != y -> 
forall ⦃a b …
-/
theorem strictConcaveOn_iff_div {f : E → β} :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
        (a / (a + b)) • f x + (b / (a + b)) • f y < f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  strictConvexOn_iff_div (β := βᵒᵈ)

end SMul

end OrderedAddCommMonoid

end LinearOrderedField

section OrderIso

variable [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid α] [PartialOrder α] [SMul 𝕜 α]
  [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

/-
**OrderIso.strictConvexOn_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.strictConvexOn_symm (f : α ≃o β) (hf : StrictConcaveOn 𝕜 univ f) 
: StrictConvexOn 𝕜 univ f.symm
参数：f : α ≃o β；hf : StrictConcaveOn 𝕜 univ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem OrderIso.strictConvexOn_symm (f : α ≃o β) (hf : StrictConcaveOn 𝕜 univ f) :
    StrictConvexOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' ≠ y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) hxy' ha hb hab
/-
**OrderIso.convexOn_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.convexOn_symm (f : α ≃o β) (hf : ConcaveOn 𝕜 univ f) : ConvexOn 𝕜
 univ f.symm
参数：f : α ≃o β；hf : ConcaveOn 𝕜 univ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem OrderIso.convexOn_symm (f : α ≃o β) (hf : ConcaveOn 𝕜 univ f) :
    ConvexOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) ha hb hab
/-
**OrderIso.strictConcaveOn_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.strictConcaveOn_symm (f : α ≃o β) (hf : StrictConvexOn 𝕜 univ f) 
: StrictConcaveOn 𝕜 univ f.symm
参数：f : α ≃o β；hf : StrictConvexOn 𝕜 univ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem OrderIso.strictConcaveOn_symm (f : α ≃o β) (hf : StrictConvexOn 𝕜 univ f) :
    StrictConcaveOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  have hxy' : x' ≠ y' := by rw [← f.injective.ne_iff, ← hx'', ← hy'']; exact hxy
  simp only [hx'', hy'', OrderIso.symm_apply_apply, gt_iff_lt]
  rw [← f.lt_iff_lt, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) hxy' ha hb hab
/-
**OrderIso.concaveOn_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.concaveOn_symm (f : α ≃o β) (hf : ConvexOn 𝕜 univ f) : ConcaveOn 
𝕜 univ f.symm
参数：f : α ≃o β；hf : ConvexOn 𝕜 univ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem OrderIso.concaveOn_symm (f : α ≃o β) (hf : ConvexOn 𝕜 univ f) :
    ConcaveOn 𝕜 univ f.symm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨x', hx''⟩ := f.surjective.exists.mp ⟨x, rfl⟩
  obtain ⟨y', hy''⟩ := f.surjective.exists.mp ⟨y, rfl⟩
  simp only [hx'', hy'', OrderIso.symm_apply_apply]
  rw [← f.le_iff_le, OrderIso.apply_symm_apply]
  exact hf.2 (by simp : x' ∈ univ) (by simp : y' ∈ univ) ha hb hab

end OrderIso


section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section OrderedAddCommMonoid
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  [AddCommMonoid E] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  {f : E → β} {s : Set E} {x y : E}

/-- A strictly convex function admits at most one global minimum. -/
/-
**StrictConvexOn.eq_of_isMinOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvexOn.eq_of_isMinOn (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f 
s x) (hfy : IsMinOn f s y) (hx : x in s) (hy : y in s) : x = y
参数：hf : StrictConvexOn 𝕜 s f；hfx : IsMinOn f s x；hfy : IsMinOn f s y；hx : x in s
；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A strictly convex function admits at most one global minimum.
-/
lemma StrictConvexOn.eq_of_isMinOn (hf : StrictConvexOn 𝕜 s f) (hfx : IsMinOn f s x)
    (hfy : IsMinOn f s y) (hx : x ∈ s) (hy : y ∈ s) : x = y := by
  by_contra hxy
  let z := (2 : 𝕜)⁻¹ • x + (2 : 𝕜)⁻¹ • y
  have hz : z ∈ s := hf.1 hx hy (by simp) (by simp) <| by norm_num
  refine lt_irrefl (f z) ?_
  calc
    f z < _ := hf.2 hx hy hxy (by simp) (by simp) <| by norm_num
    _ ≤ (2 : 𝕜)⁻¹ • f z + (2 : 𝕜)⁻¹ • f z := by gcongr; exacts [hfx hz, hfy hz]
    _ = f z := by rw [← _root_.add_smul]; norm_num

/-- A strictly concave function admits at most one global maximum. -/
/-
**StrictConcaveOn.eq_of_isMaxOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.eq_of_isMaxOn (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn 
f s x) (hfy : IsMaxOn f s y) (hx : x in s) (hy : y in s) : x = y
参数：hf : StrictConcaveOn 𝕜 s f；hfx : IsMaxOn f s x；hfy : IsMaxOn f s y；hx : x in 
s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.eq_of_isMinOn`：StrictConvexOn.eq_of_isMinOn (hf : StrictC
onvexOn 𝕜 s f) (hfx : IsMinOn f s x) (hfy : IsMinOn f s y) (hx : x in s) (hy : y
 in s) : x = y
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
A strictly concave function admits at most one global maximum.
-/
lemma StrictConcaveOn.eq_of_isMaxOn (hf : StrictConcaveOn 𝕜 s f) (hfx : IsMaxOn f s x)
    (hfy : IsMaxOn f s y) (hx : x ∈ s) (hy : y ∈ s) : x = y :=
  hf.dual.eq_of_isMinOn hfx hfy hx hy

end OrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid
variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]
  {x y z : 𝕜} {s : Set 𝕜} {f : 𝕜 → β}

/-
**ConvexOn.le_right_of_left_le''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_right_of_left_le'' (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z
 in s) (hxy : x < y) (hyz : y <= z) (h : f x <= f y) : f y <= f z
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hz : z in s；hxy : x < y；hyz : y <= z；h : f x 
<= f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ConvexOn.le_right_of_left_le`：ConvexOn.le_right_of_left_le (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hxz : f x <= f z) …
· 使用定理 `Ioo_subset_openSegment`：Ioo_subset_openSegment : Ioo x y subseteq openSe
gment 𝕜 x y
-/
theorem ConvexOn.le_right_of_left_le'' (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y)
    (hyz : y ≤ z) (h : f x ≤ f y) : f y ≤ f z :=
  hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h
/-
**ConvexOn.le_left_of_right_le''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_left_of_right_le'' (hf : ConvexOn 𝕜 s f) (hx : x in s) (hz : z
 in s) (hxy : x <= y) (hyz : y < z) (h : f z <= f y) : f y <= f x
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hz : z in s；hxy : x <= y；hyz : y < z；h : f z 
<= f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ConvexOn.le_left_of_right_le`：ConvexOn.le_left_of_right_le (hf : ConvexO
n 𝕜 s f) {x y z : E} (hx : x in s) (hy : y in s) (hz : z in openSegment 𝕜 x y) (
hyz : f y <= f z) …
· 使用定理 `Ioo_subset_openSegment`：Ioo_subset_openSegment : Ioo x y subseteq openSe
gment 𝕜 x y
-/
theorem ConvexOn.le_left_of_right_le'' (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y)
    (hyz : y < z) (h : f z ≤ f y) : f y ≤ f x :=
  hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_openSegment ⟨hxy, hyz⟩) h
/-
**ConcaveOn.right_le_of_le_left''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.right_le_of_le_left'' (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz :
 z in s) (hxy : x < y) (hyz : y <= z) (h : f y <= f x) : f z <= f y
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hz : z in s；hxy : x < y；hyz : y <= z；h : f y
 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_right_of_left_le''`：ConvexOn.le_right_of_left_le'' (hf : Con
vexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x < y) (hyz : y <= z) (h : f x <
= f y) : f y <= f z
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.right_le_of_le_left'' (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y ≤ z) (h : f y ≤ f x) : f z ≤ f y :=
  hf.dual.le_right_of_left_le'' hx hz hxy hyz h
/-
**ConcaveOn.left_le_of_le_right''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.left_le_of_le_right'' (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hz :
 z in s) (hxy : x <= y) (hyz : y < z) (h : f y <= f z) : f x <= f y
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hz : z in s；hxy : x <= y；hyz : y < z；h : f y
 <= f z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_left_of_right_le''`：ConvexOn.le_left_of_right_le'' (hf : Con
vexOn 𝕜 s f) (hx : x in s) (hz : z in s) (hxy : x <= y) (hyz : y < z) (h : f z <
= f y) : f y <= f x
· 使用定理 `OrderDual.isOrderedAddCancelMonoid`：∀ {α : Type u} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], IsOrderedCancelAddMonoid
 αᵒᵈ
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConcaveOn.left_le_of_le_right'' (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x ≤ y) (hyz : y < z) (h : f y ≤ f z) : f x ≤ f y :=
  hf.dual.le_left_of_right_le'' hx hz hxy hyz h

end LinearOrderedCancelAddCommMonoid
end LinearOrderedField

