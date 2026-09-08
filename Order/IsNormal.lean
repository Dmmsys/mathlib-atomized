/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Order.DirSupClosed
public import Mathlib.Order.SuccPred.CompleteLinearOrder
public import Mathlib.Order.SuccPred.InitialSeg

/-!
# Normal functions

A normal function between well-orders is a strictly monotonic continuous function. Normal functions
arise chiefly in the context of cardinal and ordinal-valued functions.

We opt for an equivalent definition that's both simpler and often more convenient: a normal function
is a strictly monotonic function `f` such that at successor limits `a`, `f a` is the least upper
bound of `f b` with `b < a`.

See `Order.isNormal_iff_strictMono_and_continuous` for a proof that these notions are equivalent.
-/

public section

open Set

variable {α β γ : Type*} {a b : α} {f : α → β} {g : β → γ}

namespace Order

/-- A normal function between well-orders is a strictly monotonic continuous function. -/
@[mk_iff isNormal_iff']
/-
**Order.IsNormal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [LinearOrder α] → [LinearOrder β] → (α →
 β) → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normal function between well-orders is a strictly monotonic continuous functio
n.
-/
structure IsNormal [LinearOrder α] [LinearOrder β] (f : α → β) : Prop where
  strictMono : StrictMono f
  /-- This condition is the RHS of the `IsLUB (f '' Iio a) (f a)` predicate, which is sufficient
  since the LHS is implied by monotonicity. -/
  mem_lowerBounds_upperBounds_of_isSuccLimit {a : α} (ha : IsSuccLimit a) :
    f a ∈ lowerBounds (upperBounds (f '' Iio a))
/-
**Order.isNormal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α -> β} : IsNormal f ↔ S
trictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall b < o, f b <= a) -> f
 o <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNormal_iff [LinearOrder α] [LinearOrder β] {f : α → β} :
    IsNormal f ↔ StrictMono f ∧ ∀ o, IsSuccLimit o → ∀ a, (∀ b < o, f b ≤ a) → f o ≤ a := by
  simp [isNormal_iff', mem_lowerBounds, mem_upperBounds]

namespace IsNormal

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-
**Order.IsNormal.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : LinearOrd
er β] {f : α → β},   Order.IsNormal f → Monotone f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
-/
protected theorem monotone {f : α → β} (hf : IsNormal f) : Monotone f :=
  hf.strictMono.monotone
/-
**Order.IsNormal.isLUB_image_Iio_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order
.IsNormal`。
形式化陈述：isLUB_image_Iio_of_isSuccLimit {f : α -> β} (hf : IsNormal f) {a : α} (ha 
: IsSuccLimit a) : IsLUB (f '' Iio a) (f a)
参数：hf : IsNormal f；ha : IsSuccLimit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Order.IsNormal.mem_lowerBounds_upperBounds_of_isSuccLimit`：∀ {α : Type u
_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β}, 
  Order.IsNormal f → ∀ {a : α}, Order.IsSuccLim…
-/
theorem isLUB_image_Iio_of_isSuccLimit {f : α → β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) :
    IsLUB (f '' Iio a) (f a) := by
  refine ⟨?_, hf.2 ha⟩
  rintro - ⟨b, hb, rfl⟩
  exact (hf.1 hb).le
/-
**Order.IsNormal.le_iff_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：le_iff_forall_le (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} : f a <= b
 ↔ forall a' < a, f a' <= b
参数：hf : IsNormal f；ha : IsSuccLimit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `Order.IsNormal.isLUB_image_Iio_of_isSuccLimit`：isLUB_image_Iio_of_isSucc
Limit {f : α -> β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) : IsLUB (f '' 
Iio a) (f a)
-/
theorem le_iff_forall_le (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    f a ≤ b ↔ ∀ a' < a, f a' ≤ b := by
  simpa [mem_upperBounds] using isLUB_le_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)
/-
**Order.IsNormal.lt_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：lt_iff_exists_lt (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} : b < f a 
↔ exists a' < a, b < f a'
参数：hf : IsNormal f；ha : IsSuccLimit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lt_isLUB_iff`：lt_isLUB_iff (h : IsLUB s a) : b < a ↔ exists c in s, b < 
c
· 使用定理 `Order.IsNormal.isLUB_image_Iio_of_isSuccLimit`：isLUB_image_Iio_of_isSucc
Limit {f : α -> β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) : IsLUB (f '' 
Iio a) (f a)
-/
theorem lt_iff_exists_lt (hf : IsNormal f) (ha : IsSuccLimit a) {b : β} :
    b < f a ↔ ∃ a' < a, b < f a' := by
  simpa [mem_upperBounds] using lt_isLUB_iff (hf.isLUB_image_Iio_of_isSuccLimit ha)
/-
**Order.IsNormal.map_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：map_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) : IsSuccLimit (f a)
参数：hf : IsNormal f；ha : IsSuccLimit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isMin_iff`：not_isMin_iff : ¬IsMin a ↔ exists b, b < a
· 使用定理 `Order.IsSuccLimit.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a : α
}, Order.IsSuccLimit a → ¬IsMin a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Order.IsNormal.lt_iff_exists_lt`：lt_iff_exists_lt (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : b < f a ↔ exists a' < a, b < f a'
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `CovBy.ge_of_gt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b ⋖
 a → b < c → a ≤ c
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
-/
theorem map_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) : IsSuccLimit (f a) := by
  refine ⟨?_, fun b hb ↦ ?_⟩
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 ha.not_isMin
    exact not_isMin_iff.2 ⟨_, hf.strictMono hb⟩
  · obtain ⟨c, hc, hc'⟩ := (hf.lt_iff_exists_lt ha).1 hb.lt
    have hc' := hb.ge_of_gt hc'
    rw [hf.strictMono.le_iff_le] at hc'
    exact hc.not_ge hc'
/-
**Order.IsNormal.map_isLUB** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：map_isLUB (hf : IsNormal f) {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty
) : IsLUB (f '' s) (f a)
参数：hf : IsNormal f；hs : IsLUB s a；hs' : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsLUB.isSuccLimit_of_notMem`：∀ {α : Type u_1} {a : α} [inst : LinearOrde
r α] {s : Set α}, IsLUB s a → s.Nonempty → a ∉ s → Order.IsSuccLimit a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.IsNormal.le_iff_forall_le`：le_iff_forall_le (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : f a <= b ↔ forall a' < a, f a' <= b
· 使用定理 `IsLUB.exists_between`：IsLUB.exists_between (h : IsLUB s a) (hb : b < a) 
: exists c in s, b < c ∧ c <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem map_isLUB (hf : IsNormal f) {s : Set α} (hs : IsLUB s a) (hs' : s.Nonempty) :
    IsLUB (f '' s) (f a) := by
  refine ⟨?_, fun b hb ↦ ?_⟩
  · simpa [mem_upperBounds, hf.strictMono.le_iff_le] using hs.1
  · by_cases ha : a ∈ s
    · simp_all [mem_upperBounds]
    · have ha' := hs.isSuccLimit_of_notMem hs' ha
      rw [le_iff_forall_le hf ha']
      intro c hc
      obtain ⟨d, hd, hcd, hda⟩ := hs.exists_between hc
      simp_rw [mem_upperBounds, forall_mem_image] at hb
      exact (hf.strictMono hcd).le.trans (hb hd)
/-
**Order.IsNormal._root_.InitialSeg.isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsN
ormal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.InitialSeg.isNormal (f : α ≤i β) : IsNormal f where
  strictMono := f.strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit ha := by
    rw [f.image_Iio]
    exact (f.map_isSuccLimit ha).isLUB_Iio.2
/-
**Order.IsNormal._root_.PrincipalSeg.isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Order.I
sNormal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PrincipalSeg.isNormal (f : α <i β) : IsNormal f :=
  (f : α ≤i β).isNormal
/-
**Order.IsNormal._root_.OrderIso.isNormal** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNor
mal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.isNormal (f : α ≃o β) : IsNormal f :=
  f.toInitialSeg.isNormal
/-
**Order.IsNormal.id** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α], Order.IsNormal id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isNormal`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α
] [inst_1 : LinearOrder β] (f : α ≃o β), Order.IsNormal ⇑f
-/
protected theorem id : IsNormal (@id α) :=
  (OrderIso.refl _).isNormal
/-
**Order.IsNormal.comp** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f)
参数：hg : IsNormal g；hf : IsNormal f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.IsNormal.le_iff_forall_le`：le_iff_forall_le (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : f a <= b ↔ forall a' < a, f a' <= b
· 使用定理 `Order.IsNormal.map_isSuccLimit`：map_isSuccLimit (hf : IsNormal f) (ha : 
IsSuccLimit a) : IsSuccLimit (f a)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.IsNormal.lt_iff_exists_lt`：lt_iff_exists_lt (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : b < f a ↔ exists a' < a, b < f a'
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
-/
theorem comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) := by
  refine ⟨hg.strictMono.comp hf.strictMono, fun ha b hb ↦ ?_⟩
  simp_rw [Function.comp_apply, mem_upperBounds, forall_mem_image] at hb
  simpa [hg.le_iff_forall_le (hf.map_isSuccLimit ha), hf.lt_iff_exists_lt ha] using
    fun c d hd hc ↦ (hg.strictMono hc).le.trans (hb hd)

/-- Restrict a normal function `α → β` to a normal function `Iio a → Iio (f a)`. -/
/-
**Order.IsNormal.to_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：to_Iio (hf : IsNormal f) (a : α) : IsNormal (β
参数：hf : IsNormal f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `Order.IsNormal.mem_lowerBounds_upperBounds_of_isSuccLimit`：∀ {α : Type u
_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : LinearOrder β] {f : α → β}, 
  Order.IsNormal f → ∀ {a : α}, Order.IsSuccLim…
· 使用定理 `Order.IsSuccLimit.subtypeVal`：∀ {α : Type u_1} [inst : Preorder α] {s : 
Set α}, IsLowerSet s → ∀ {a : ↑s}, Order.IsSuccLimit a → Order.IsSuccLimit ↑a
· 使用定理 `isLowerSet_Iio`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iio a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
Restrict a normal function `α → β` to a normal function `Iio a → Iio (f a)`.
-/
theorem to_Iio (hf : IsNormal f) (a : α) :
    IsNormal (β := Iio (f a)) fun x : Iio a ↦ ⟨f x.1, hf.strictMono x.2⟩ := by
  rw [isNormal_iff]
  refine ⟨fun x y h ↦ hf.strictMono h, fun b hb c hc ↦ hf.2 (hb.subtypeVal (isLowerSet_Iio _)) ?_⟩
  simpa [upperBounds] using! fun d hd ↦ hc ⟨d, hd.trans b.2⟩ hd

end LinearOrder

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLinearOrder β]

/-
**Order.IsNormal.map_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：map_sSup (hf : IsNormal f) {s : Set α} (hs : s.Nonempty) (hs' : BddAbove s
) : f (sSup s) = sSup (f '' s)
参数：hf : IsNormal f；hs : s.Nonempty；hs' : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `Order.IsNormal.map_isLUB`：map_isLUB (hf : IsNormal f) {s : Set α} (hs : 
IsLUB s a) (hs' : s.Nonempty) : IsLUB (f '' s) (f a)
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem map_sSup (hf : IsNormal f) {s : Set α} (hs : s.Nonempty) (hs' : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf.map_isLUB (isLUB_csSup hs hs') hs).csSup_eq (hs.image f)).symm
/-
**Order.IsNormal.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : IsNormal f) (hg : BddAbove (r
ange g)) : f (⨆ i, g i) = ⨆ i, f (g i)
参数：hf : IsNormal f；hg : BddAbove (range g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Order.IsNormal.map_sSup`：map_sSup (hf : IsNormal f) {s : Set α} (hs : s.
Nonempty) (hs' : BddAbove s) : f (sSup s) = sSup (f '' s)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem map_iSup {ι} [Nonempty ι] {g : ι → α} (hf : IsNormal f) (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  unfold iSup
  convert! map_sSup hf (range_nonempty g) hg
  ext
  simp
/-
**Order.IsNormal.iSup_iterate_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `Order.I
sNormal`。
形式化陈述：iSup_iterate_mem_fixedPoints [WellFoundedLT α] {f : α -> α} (a : α) (hf : 
IsNormal f) (hf' : BddAbove (.range fun n => f^[n] a)) : ⨆ n, f^[n] a in f.fixed
Points
参数：a : α；hf : IsNormal f；hf' : BddAbove (.range fun n => f^[n] a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iSup_iterate_mem_fixedPoints [WellFoundedLT α] {f : α → α} (a : α) (hf : IsNormal f)
    (hf' : BddAbove (.range fun n ↦ f^[n] a)) : ⨆ n, f^[n] a ∈ f.fixedPoints := by
  rw [f.mem_fixedPoints_iff, hf.map_iSup hf']
  apply le_antisymm <;> refine ciSup_le fun n ↦ ?_
  · rw [← f.iterate_succ_apply']
    exact le_ciSup hf' _
  · apply hf.strictMono.le_apply.trans
    apply (le_ciSup (hf'.mono _) n)
    simp_rw [← f.iterate_succ_apply']
    grind
/-
**Order.IsNormal.preimage_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：preimage_Iic (hf : IsNormal f) {x : β} (h₁ : (f ⁻¹' Iic x).Nonempty) (h₂ :
 BddAbove (f ⁻¹' Iic x)) : f ⁻¹' Iic x = Iic (sSup (f ⁻¹' Iic x))
参数：hf : IsNormal f；h₁ : (f ⁻¹' Iic x).Nonempty；h₂ : BddAbove (f ⁻¹' Iic x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_csSup_iff`：lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSu
p s ↔ exists b in s, a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Order.IsNormal.map_sSup`：map_sSup (hf : IsNormal f) {s : Set α} (hs : s.
Nonempty) (hs' : BddAbove s) : f (sSup s) = sSup (f '' s)
· 使用定理 `csSup_le_csSup`：csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : 
s subseteq t) : sSup s <= sSup t
· 使用定理 `bddAbove_Iic`：bddAbove_Iic : BddAbove (Iic a)
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `csSup_Iic`：csSup_Iic : sSup (Iic a) = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem preimage_Iic (hf : IsNormal f) {x : β}
    (h₁ : (f ⁻¹' Iic x).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic x)) :
    f ⁻¹' Iic x = Iic (sSup (f ⁻¹' Iic x)) := by
  refine le_antisymm (fun _ ↦ le_csSup h₂) (fun y hy ↦ ?_)
  obtain hy | rfl := hy.lt_or_eq
  · rw [lt_csSup_iff h₂ h₁] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    exact (hf.strictMono hyz).le.trans hz
  · rw [mem_preimage, hf.map_sSup h₁ h₂]
    apply (csSup_le_csSup bddAbove_Iic _ (image_preimage_subset ..)).trans
    · rw [csSup_Iic]
    · simpa
/-
**Order.IsNormal.le_iff_le_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：le_iff_le_sSup (hf : IsNormal f) {x : α} {y : β} (h₁ : (f ⁻¹' Iic y).Nonem
pty) (h₂ : BddAbove (f ⁻¹' Iic y)) : f x <= y ↔ x <= sSup (f ⁻¹' Iic y)
参数：hf : IsNormal f；h₁ : (f ⁻¹' Iic y).Nonempty；h₂ : BddAbove (f ⁻¹' Iic y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Order.IsNormal.preimage_Iic`：preimage_Iic (hf : IsNormal f) {x : β} (h₁ 
: (f ⁻¹' Iic x).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic x)) : f ⁻¹' Iic x = Iic (sSu
p (f ⁻¹' Iic x))
-/
theorem le_iff_le_sSup (hf : IsNormal f) {x : α} {y : β}
    (h₁ : (f ⁻¹' Iic y).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic y)) :
    f x ≤ y ↔ x ≤ sSup (f ⁻¹' Iic y) :=
  Set.ext_iff.1 (preimage_Iic hf h₁ h₂) x

/-- If `f : α → α` in a well-order, we can infer one of the hypotheses in
`Order.IsNormal.le_iff_le_sSup`. -/
/-
**Order.IsNormal.le_iff_le_sSup'** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：le_iff_le_sSup' [WellFoundedLT α] {f : α -> α} (hf : IsNormal f) {x y : α}
 (h : (f ⁻¹' Iic y).Nonempty) : f x <= y ↔ x <= sSup (f ⁻¹' Iic y)
参数：hf : IsNormal f；h : (f ⁻¹' Iic y).Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.le_iff_le_sSup`：le_iff_le_sSup (hf : IsNormal f) {x : α} 
{y : β} (h₁ : (f ⁻¹' Iic y).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic y)) : f x <= y ↔
 x <= sSup (f ⁻¹' I…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f

--- 原说明 ---
If `f : α → α` in a well-order, we can infer one of the hypotheses in
`Order.IsNormal.le_iff_le_sSup`.
-/
theorem le_iff_le_sSup' [WellFoundedLT α] {f : α → α} (hf : IsNormal f) {x y : α}
    (h : (f ⁻¹' Iic y).Nonempty) : f x ≤ y ↔ x ≤ sSup (f ⁻¹' Iic y) :=
  hf.le_iff_le_sSup h ⟨y, fun _ ↦ hf.strictMono.le_apply.trans⟩

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrder β]

/-
**Order.IsNormal.apply_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`
。
形式化陈述：apply_of_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) : f a = ⨆ b : 
Iio a, f b
参数：hf : IsNormal f；ha : IsSuccLimit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsSuccLimit.iSup_Iio`：Order.IsSuccLimit.iSup_Iio (h : IsSuccLimit 
x) : ⨆ a : Iio x, a.1 = x
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem apply_of_isSuccLimit (hf : IsNormal f) (ha : IsSuccLimit a) :
    f a = ⨆ b : Iio a, f b := by
  convert! map_iSup hf _
  · exact ha.iSup_Iio.symm
  · exact ⟨⊥, ha.bot_lt⟩
  · use a
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact hx.le

end ConditionallyCompleteLinearOrderBot

section WellFoundedLT
variable [LinearOrder α] [WellFoundedLT α] [SuccOrder α] [LinearOrder β]

/-
**Order.IsNormal.of_succ_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：of_succ_lt (hs : forall a, f a < f (succ a)) (hl : forall {a}, IsSuccLimit
 a -> IsLUB (f '' Iio a) (f a)) : IsNormal f
参数：hs : forall a, f a < f (succ a)；hl : forall {a}, IsSuccLimit a -> IsLUB (f ''
 Iio a) (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.not_lt`：IsMin.not_lt (h : IsMin a) : ¬b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_succ_iff_eq_or_lt_of_not_isMax`：lt_succ_iff_eq_or_lt_of_not_isM
ax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem of_succ_lt
    (hs : ∀ a, f a < f (succ a)) (hl : ∀ {a}, IsSuccLimit a → IsLUB (f '' Iio a) (f a)) :
    IsNormal f := by
  refine ⟨fun a b ↦ ?_, fun ha ↦ (hl ha).2⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb => exact hb.not_lt.elim
  | succ b hb IH =>
    intro hab
    obtain rfl | h := (lt_succ_iff_eq_or_lt_of_not_isMax hb).1 hab
    · exact hs a
    · exact (IH h).trans (hs b)
  | isSuccLimit b hb IH =>
    intro hab
    have hab' := hb.succ_lt hab
    exact (IH _ hab' (lt_succ_of_not_isMax hab.not_isMax)).trans_le
      ((hl hb).1 (mem_image_of_mem _ hab'))
/-
**Order.IsNormal.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：ext_iff [OrderBot α] {g : α -> β} (hf : IsNormal f) (hg : IsNormal g) : f 
= g ↔ f ⊥ = g ⊥ ∧ forall a, f a = g a -> f (succ a) = g (succ a)
参数：hf : IsNormal f；hg : IsNormal g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `Order.IsNormal.isLUB_image_Iio_of_isSuccLimit`：isLUB_image_Iio_of_isSucc
Limit {f : α -> β} (hf : IsNormal f) {a : α} (ha : IsSuccLimit a) : IsLUB (f '' 
Iio a) (f a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem ext_iff [OrderBot α] {g : α → β} (hf : IsNormal f) (hg : IsNormal g) :
    f = g ↔ f ⊥ = g ⊥ ∧ ∀ a, f a = g a → f (succ a) = g (succ a) := by
  constructor
  · simp_all
  rintro ⟨H₁, H₂⟩
  ext a
  induction a using SuccOrder.limitRecOn with
  | isMin a ha => rw [ha.eq_bot, H₁]
  | succ a ha IH => exact H₂ a IH
  | isSuccLimit a ha IH =>
    apply (hf.isLUB_image_Iio_of_isSuccLimit ha).unique
    convert! hg.isLUB_image_Iio_of_isSuccLimit ha using 1
    aesop

@[deprecated (since := "2026-03-22")] protected alias ext := IsNormal.ext_iff
/-
**Order.IsNormal.exists_map_le_lt_map_succ_of_exists_ge** 是 Mathlib 中的一个定理，位于命名空
间 `Order.IsNormal`。
形式化陈述：exists_map_le_lt_map_succ_of_exists_ge [NoMaxOrder α] [OrderBot α] [WellFo
undedLT β] {f : α -> β} {x : β} (hf : IsNormal f) (hf' : exists y, x <= f y) (hx
 : f ⊥ <= x) : exists a, f a <= x ∧ x < f (succ a)
参数：hf : IsNormal f；hf' : exists y, x <= f y；hx : f ⊥ <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.IsNormal.le_iff_le_sSup`：le_iff_le_sSup (hf : IsNormal f) {x : α} 
{y : β} (h₁ : (f ⁻¹' Iic y).Nonempty) (h₂ : BddAbove (f ⁻¹' Iic y)) : f x <= y ↔
 x <= sSup (f ⁻¹' I…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
-/
theorem exists_map_le_lt_map_succ_of_exists_ge [NoMaxOrder α] [OrderBot α] [WellFoundedLT β]
    {f : α → β} {x : β} (hf : IsNormal f) (hf' : ∃ y, x ≤ f y) (hx : f ⊥ ≤ x) :
    ∃ a, f a ≤ x ∧ x < f (succ a) := by
  have : Nonempty β := ⟨x⟩
  let := WellFoundedLT.toOrderBot β
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot β
  have H : BddAbove (f ⁻¹' Iic x) :=
    have ⟨y, hy⟩ := hf'
    ⟨y, fun z hz ↦ hf.strictMono.le_iff_le.1 <| hz.trans hy⟩
  refine ⟨sSup (f ⁻¹' Set.Iic x), ?_, ?_⟩
  · rw [hf.le_iff_le_sSup ⟨⊥, hx⟩ H]
  · rw [← not_le, hf.le_iff_le_sSup ⟨⊥, hx⟩ H, not_le, lt_succ_iff]

/-- If `f : α → α`, we can infer one of the hypotheses in
`exists_map_le_lt_map_succ_of_exists_ge`. -/
/-
**Order.IsNormal.exists_map_le_lt_map_succ** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNo
rmal`。
形式化陈述：exists_map_le_lt_map_succ [NoMaxOrder α] [OrderBot α] {f : α -> α} {x : α}
 (hf : IsNormal f) (hx : f ⊥ <= x) : exists a, f a <= x ∧ x < f (succ a)
参数：hf : IsNormal f；hx : f ⊥ <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.exists_map_le_lt_map_succ_of_exists_ge`：exists_map_le_lt_
map_succ_of_exists_ge [NoMaxOrder α] [OrderBot α] [WellFoundedLT β] {f : α -> β}
 {x : β} (hf : IsNormal f) (hf' : exists y,…
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f

--- 原说明 ---
If `f : α → α`, we can infer one of the hypotheses in
`exists_map_le_lt_map_succ_of_exists_ge`.
-/
theorem exists_map_le_lt_map_succ [NoMaxOrder α] [OrderBot α] {f : α → α} {x : α}
    (hf : IsNormal f) (hx : f ⊥ ≤ x) : ∃ a, f a ≤ x ∧ x < f (succ a) :=
  exists_map_le_lt_map_succ_of_exists_ge hf ⟨x, hf.strictMono.le_apply⟩ hx

omit [SuccOrder α] in
/-
**Order.IsNormal.dirSupClosed_range** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsNormal`。
形式化陈述：dirSupClosed_range {f : α -> α} (hf : IsNormal f) : DirSupClosed (range f)
参数：hf : IsNormal f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Order.IsNormal.map_isLUB`：map_isLUB (hf : IsNormal f) {s : Set α} (hs : 
IsLUB s a) (hs' : s.Nonempty) : IsLUB (f '' s) (f a)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
theorem dirSupClosed_range {f : α → α} (hf : IsNormal f) : DirSupClosed (range f) := by
  intro s hs hs₀ _ a ha
  have hf' : (f ⁻¹' s).Nonempty := by
    obtain ⟨b, hb⟩ := hs₀
    obtain ⟨c, rfl⟩ := hs hb
    exact ⟨c, hb⟩
  have : Nonempty α := ⟨a⟩
  let := WellFoundedLT.toOrderBot α
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  have hfl : IsLUB (f ⁻¹' s) (sSup (f ⁻¹' s)) :=
    isLUB_csSup hf' ⟨a, fun b hb ↦ hf.strictMono.le_apply.trans (ha.1 hb)⟩
  have ha' := hf.map_isLUB hfl hf'
  rw [image_preimage_eq_of_subset hs] at ha'
  obtain rfl := ha.unique ha'
  exact mem_range_self _

end WellFoundedLT
end IsNormal
end Order

