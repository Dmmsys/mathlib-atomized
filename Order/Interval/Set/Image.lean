/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Directed

/-!
# Monotone functions on intervals

This file shows many variants of the fact that a monotone function `f` sends an interval with
endpoints `a` and `b` to the interval with endpoints `f a` and `f b`.
-/

public section

variable {α β : Type*} {f : α → β}

open Set

section Preorder
variable [Preorder α] [Preorder β] {a b : α}

/-
**MonotoneOn.mapsTo_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.mapsTo_Ici (h : MonotoneOn f (Ici a)) : MapsTo f (Ici a) (Ici (
f a))
参数：h : MonotoneOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma MonotoneOn.mapsTo_Ici (h : MonotoneOn f (Ici a)) : MapsTo f (Ici a) (Ici (f a)) :=
  fun _ _ ↦ by aesop
/-
**MonotoneOn.mapsTo_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.mapsTo_Iic (h : MonotoneOn f (Iic b)) : MapsTo f (Iic b) (Iic (
f b))
参数：h : MonotoneOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma MonotoneOn.mapsTo_Iic (h : MonotoneOn f (Iic b)) : MapsTo f (Iic b) (Iic (f b)) :=
  fun _ _ ↦ by aesop
/-
**MonotoneOn.mapsTo_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.mapsTo_Icc (h : MonotoneOn f (Icc a b)) : MapsTo f (Icc a b) (I
cc (f a) (f b))
参数：h : MonotoneOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
-/
lemma MonotoneOn.mapsTo_Icc (h : MonotoneOn f (Icc a b)) : MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  fun _c hc ↦
    ⟨h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1, h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2⟩
/-
**AntitoneOn.mapsTo_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.mapsTo_Ici (h : AntitoneOn f (Ici a)) : MapsTo f (Ici a) (Iic (
f a))
参数：h : AntitoneOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma AntitoneOn.mapsTo_Ici (h : AntitoneOn f (Ici a)) : MapsTo f (Ici a) (Iic (f a)) :=
  fun _ _ ↦ by aesop
/-
**AntitoneOn.mapsTo_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.mapsTo_Iic (h : AntitoneOn f (Iic b)) : MapsTo f (Iic b) (Ici (
f b))
参数：h : AntitoneOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma AntitoneOn.mapsTo_Iic (h : AntitoneOn f (Iic b)) : MapsTo f (Iic b) (Ici (f b)) :=
  fun _ _ ↦ by aesop
/-
**AntitoneOn.mapsTo_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.mapsTo_Icc (h : AntitoneOn f (Icc a b)) : MapsTo f (Icc a b) (I
cc (f b) (f a))
参数：h : AntitoneOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
lemma AntitoneOn.mapsTo_Icc (h : AntitoneOn f (Icc a b)) : MapsTo f (Icc a b) (Icc (f b) (f a)) :=
  fun _c hc ↦
    ⟨h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2, h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1⟩
/-
**StrictMonoOn.mapsTo_Ioi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mapsTo_Ioi (h : StrictMonoOn f (Ici a)) : MapsTo f (Ioi a) (I
oi (f a))
参数：h : StrictMonoOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma StrictMonoOn.mapsTo_Ioi (h : StrictMonoOn f (Ici a)) : MapsTo f (Ioi a) (Ioi (f a)) :=
  fun _c hc ↦ h le_rfl hc.le hc
/-
**StrictMonoOn.mapsTo_Iio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mapsTo_Iio (h : StrictMonoOn f (Iic b)) : MapsTo f (Iio b) (I
io (f b))
参数：h : StrictMonoOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma StrictMonoOn.mapsTo_Iio (h : StrictMonoOn f (Iic b)) : MapsTo f (Iio b) (Iio (f b)) :=
  fun _c hc ↦ h hc.le le_rfl hc
/-
**StrictMonoOn.mapsTo_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mapsTo_Ioo (h : StrictMonoOn f (Icc a b)) : MapsTo f (Ioo a b
) (Ioo (f a) (f b))
参数：h : StrictMonoOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
-/
lemma StrictMonoOn.mapsTo_Ioo (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  fun _c hc ↦
    ⟨h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1,
     h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2⟩
/-
**StrictAntiOn.mapsTo_Ioi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mapsTo_Ioi (h : StrictAntiOn f (Ici a)) : MapsTo f (Ioi a) (I
io (f a))
参数：h : StrictAntiOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma StrictAntiOn.mapsTo_Ioi (h : StrictAntiOn f (Ici a)) : MapsTo f (Ioi a) (Iio (f a)) :=
  fun _c hc ↦ h le_rfl hc.le hc
/-
**StrictAntiOn.mapsTo_Iio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mapsTo_Iio (h : StrictAntiOn f (Iic b)) : MapsTo f (Iio b) (I
oi (f b))
参数：h : StrictAntiOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma StrictAntiOn.mapsTo_Iio (h : StrictAntiOn f (Iic b)) : MapsTo f (Iio b) (Ioi (f b)) :=
  fun _c hc ↦ h hc.le le_rfl hc
/-
**StrictAntiOn.mapsTo_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mapsTo_Ioo (h : StrictAntiOn f (Icc a b)) : MapsTo f (Ioo a b
) (Ioo (f b) (f a))
参数：h : StrictAntiOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
lemma StrictAntiOn.mapsTo_Ioo (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ioo a b) (Ioo (f b) (f a)) :=
  fun _c hc ↦
    ⟨h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2,
     h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1⟩
/-
**Monotone.mapsTo_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.mapsTo_Ici (h : Monotone f) : MapsTo f (Ici a) (Ici (f a))
参数：h : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.mapsTo_Ici`：MonotoneOn.mapsTo_Ici (h : MonotoneOn f (Ici a)) 
: MapsTo f (Ici a) (Ici (f a))
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
lemma Monotone.mapsTo_Ici (h : Monotone f) : MapsTo f (Ici a) (Ici (f a)) :=
  (h.monotoneOn _).mapsTo_Ici
/-
**Monotone.mapsTo_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.mapsTo_Iic (h : Monotone f) : MapsTo f (Iic b) (Iic (f b))
参数：h : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.mapsTo_Iic`：MonotoneOn.mapsTo_Iic (h : MonotoneOn f (Iic b)) 
: MapsTo f (Iic b) (Iic (f b))
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
lemma Monotone.mapsTo_Iic (h : Monotone f) : MapsTo f (Iic b) (Iic (f b)) :=
  (h.monotoneOn _).mapsTo_Iic
/-
**Monotone.mapsTo_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.mapsTo_Icc (h : Monotone f) : MapsTo f (Icc a b) (Icc (f a) (f b)
)
参数：h : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.mapsTo_Icc`：MonotoneOn.mapsTo_Icc (h : MonotoneOn f (Icc a b)
) : MapsTo f (Icc a b) (Icc (f a) (f b))
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
lemma Monotone.mapsTo_Icc (h : Monotone f) : MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  (h.monotoneOn _).mapsTo_Icc
/-
**Antitone.mapsTo_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.mapsTo_Ici (h : Antitone f) : MapsTo f (Ici a) (Iic (f a))
参数：h : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntitoneOn.mapsTo_Ici`：AntitoneOn.mapsTo_Ici (h : AntitoneOn f (Ici a)) 
: MapsTo f (Ici a) (Iic (f a))
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
lemma Antitone.mapsTo_Ici (h : Antitone f) : MapsTo f (Ici a) (Iic (f a)) :=
  (h.antitoneOn _).mapsTo_Ici
/-
**Antitone.mapsTo_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.mapsTo_Iic (h : Antitone f) : MapsTo f (Iic b) (Ici (f b))
参数：h : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntitoneOn.mapsTo_Iic`：AntitoneOn.mapsTo_Iic (h : AntitoneOn f (Iic b)) 
: MapsTo f (Iic b) (Ici (f b))
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
lemma Antitone.mapsTo_Iic (h : Antitone f) : MapsTo f (Iic b) (Ici (f b)) :=
  (h.antitoneOn _).mapsTo_Iic
/-
**Antitone.mapsTo_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.mapsTo_Icc (h : Antitone f) : MapsTo f (Icc a b) (Icc (f b) (f a)
)
参数：h : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntitoneOn.mapsTo_Icc`：AntitoneOn.mapsTo_Icc (h : AntitoneOn f (Icc a b)
) : MapsTo f (Icc a b) (Icc (f b) (f a))
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
lemma Antitone.mapsTo_Icc (h : Antitone f) : MapsTo f (Icc a b) (Icc (f b) (f a)) :=
  (h.antitoneOn _).mapsTo_Icc
/-
**StrictMono.mapsTo_Ioi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mapsTo_Ioi (h : StrictMono f) : MapsTo f (Ioi a) (Ioi (f a))
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.mapsTo_Ioi`：StrictMonoOn.mapsTo_Ioi (h : StrictMonoOn f (Ic
i a)) : MapsTo f (Ioi a) (Ioi (f a))
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.mapsTo_Ioi (h : StrictMono f) : MapsTo f (Ioi a) (Ioi (f a)) :=
  (h.strictMonoOn _).mapsTo_Ioi
/-
**StrictMono.mapsTo_Iio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mapsTo_Iio (h : StrictMono f) : MapsTo f (Iio b) (Iio (f b))
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.mapsTo_Iio`：StrictMonoOn.mapsTo_Iio (h : StrictMonoOn f (Ii
c b)) : MapsTo f (Iio b) (Iio (f b))
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.mapsTo_Iio (h : StrictMono f) : MapsTo f (Iio b) (Iio (f b)) :=
  (h.strictMonoOn _).mapsTo_Iio
/-
**StrictMono.mapsTo_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mapsTo_Ioo (h : StrictMono f) : MapsTo f (Ioo a b) (Ioo (f a) (
f b))
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.mapsTo_Ioo`：StrictMonoOn.mapsTo_Ioo (h : StrictMonoOn f (Ic
c a b)) : MapsTo f (Ioo a b) (Ioo (f a) (f b))
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.mapsTo_Ioo (h : StrictMono f) : MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ioo
/-
**StrictAnti.mapsTo_Ioi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mapsTo_Ioi (h : StrictAnti f) : MapsTo f (Ioi a) (Iio (f a))
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.mapsTo_Ioi`：StrictAntiOn.mapsTo_Ioi (h : StrictAntiOn f (Ic
i a)) : MapsTo f (Ioi a) (Iio (f a))
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.mapsTo_Ioi (h : StrictAnti f) : MapsTo f (Ioi a) (Iio (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioi
/-
**StrictAnti.mapsTo_Iio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mapsTo_Iio (h : StrictAnti f) : MapsTo f (Iio b) (Ioi (f b))
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.mapsTo_Iio`：StrictAntiOn.mapsTo_Iio (h : StrictAntiOn f (Ii
c b)) : MapsTo f (Iio b) (Ioi (f b))
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.mapsTo_Iio (h : StrictAnti f) : MapsTo f (Iio b) (Ioi (f b)) :=
  (h.strictAntiOn _).mapsTo_Iio
/-
**StrictAnti.mapsTo_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mapsTo_Ioo (h : StrictAnti f) : MapsTo f (Ioo a b) (Ioo (f b) (
f a))
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.mapsTo_Ioo`：StrictAntiOn.mapsTo_Ioo (h : StrictAntiOn f (Ic
c a b)) : MapsTo f (Ioo a b) (Ioo (f b) (f a))
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.mapsTo_Ioo (h : StrictAnti f) : MapsTo f (Ioo a b) (Ioo (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioo
/-
**MonotoneOn.image_Ici_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.image_Ici_subset (h : MonotoneOn f (Ici a)) : f '' Ici a subset
eq Ici (f a)
参数：h : MonotoneOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `MonotoneOn.mapsTo_Ici`：MonotoneOn.mapsTo_Ici (h : MonotoneOn f (Ici a)) 
: MapsTo f (Ici a) (Ici (f a))
-/
lemma MonotoneOn.image_Ici_subset (h : MonotoneOn f (Ici a)) : f '' Ici a ⊆ Ici (f a) :=
  h.mapsTo_Ici.image_subset
/-
**MonotoneOn.image_Iic_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.image_Iic_subset (h : MonotoneOn f (Iic b)) : f '' Iic b subset
eq Iic (f b)
参数：h : MonotoneOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `MonotoneOn.mapsTo_Iic`：MonotoneOn.mapsTo_Iic (h : MonotoneOn f (Iic b)) 
: MapsTo f (Iic b) (Iic (f b))
-/
lemma MonotoneOn.image_Iic_subset (h : MonotoneOn f (Iic b)) : f '' Iic b ⊆ Iic (f b) :=
  h.mapsTo_Iic.image_subset
/-
**MonotoneOn.image_Icc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.image_Icc_subset (h : MonotoneOn f (Icc a b)) : f '' Icc a b su
bseteq Icc (f a) (f b)
参数：h : MonotoneOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `MonotoneOn.mapsTo_Icc`：MonotoneOn.mapsTo_Icc (h : MonotoneOn f (Icc a b)
) : MapsTo f (Icc a b) (Icc (f a) (f b))
-/
lemma MonotoneOn.image_Icc_subset (h : MonotoneOn f (Icc a b)) : f '' Icc a b ⊆ Icc (f a) (f b) :=
  h.mapsTo_Icc.image_subset
/-
**AntitoneOn.image_Ici_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.image_Ici_subset (h : AntitoneOn f (Ici a)) : f '' Ici a subset
eq Iic (f a)
参数：h : AntitoneOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `AntitoneOn.mapsTo_Ici`：AntitoneOn.mapsTo_Ici (h : AntitoneOn f (Ici a)) 
: MapsTo f (Ici a) (Iic (f a))
-/
lemma AntitoneOn.image_Ici_subset (h : AntitoneOn f (Ici a)) : f '' Ici a ⊆ Iic (f a) :=
  h.mapsTo_Ici.image_subset
/-
**AntitoneOn.image_Iic_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.image_Iic_subset (h : AntitoneOn f (Iic b)) : f '' Iic b subset
eq Ici (f b)
参数：h : AntitoneOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `AntitoneOn.mapsTo_Iic`：AntitoneOn.mapsTo_Iic (h : AntitoneOn f (Iic b)) 
: MapsTo f (Iic b) (Ici (f b))
-/
lemma AntitoneOn.image_Iic_subset (h : AntitoneOn f (Iic b)) : f '' Iic b ⊆ Ici (f b) :=
  h.mapsTo_Iic.image_subset
/-
**AntitoneOn.image_Icc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AntitoneOn.image_Icc_subset (h : AntitoneOn f (Icc a b)) : f '' Icc a b su
bseteq Icc (f b) (f a)
参数：h : AntitoneOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `AntitoneOn.mapsTo_Icc`：AntitoneOn.mapsTo_Icc (h : AntitoneOn f (Icc a b)
) : MapsTo f (Icc a b) (Icc (f b) (f a))
-/
lemma AntitoneOn.image_Icc_subset (h : AntitoneOn f (Icc a b)) : f '' Icc a b ⊆ Icc (f b) (f a) :=
  h.mapsTo_Icc.image_subset
/-
**StrictMonoOn.image_Ioi_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.image_Ioi_subset (h : StrictMonoOn f (Ici a)) : f '' Ioi a su
bseteq Ioi (f a)
参数：h : StrictMonoOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictMonoOn.mapsTo_Ioi`：StrictMonoOn.mapsTo_Ioi (h : StrictMonoOn f (Ic
i a)) : MapsTo f (Ioi a) (Ioi (f a))
-/
lemma StrictMonoOn.image_Ioi_subset (h : StrictMonoOn f (Ici a)) : f '' Ioi a ⊆ Ioi (f a) :=
  h.mapsTo_Ioi.image_subset
/-
**StrictMonoOn.image_Iio_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.image_Iio_subset (h : StrictMonoOn f (Iic b)) : f '' Iio b su
bseteq Iio (f b)
参数：h : StrictMonoOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictMonoOn.mapsTo_Iio`：StrictMonoOn.mapsTo_Iio (h : StrictMonoOn f (Ii
c b)) : MapsTo f (Iio b) (Iio (f b))
-/
lemma StrictMonoOn.image_Iio_subset (h : StrictMonoOn f (Iic b)) : f '' Iio b ⊆ Iio (f b) :=
  h.mapsTo_Iio.image_subset
/-
**StrictMonoOn.image_Ioo_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.image_Ioo_subset (h : StrictMonoOn f (Icc a b)) : f '' Ioo a 
b subseteq Ioo (f a) (f b)
参数：h : StrictMonoOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictMonoOn.mapsTo_Ioo`：StrictMonoOn.mapsTo_Ioo (h : StrictMonoOn f (Ic
c a b)) : MapsTo f (Ioo a b) (Ioo (f a) (f b))
-/
lemma StrictMonoOn.image_Ioo_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ioo a b ⊆ Ioo (f a) (f b) := h.mapsTo_Ioo.image_subset
/-
**StrictAntiOn.image_Ioi_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.image_Ioi_subset (h : StrictAntiOn f (Ici a)) : f '' Ioi a su
bseteq Iio (f a)
参数：h : StrictAntiOn f (Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictAntiOn.mapsTo_Ioi`：StrictAntiOn.mapsTo_Ioi (h : StrictAntiOn f (Ic
i a)) : MapsTo f (Ioi a) (Iio (f a))
-/
lemma StrictAntiOn.image_Ioi_subset (h : StrictAntiOn f (Ici a)) : f '' Ioi a ⊆ Iio (f a) :=
  h.mapsTo_Ioi.image_subset
/-
**StrictAntiOn.image_Iio_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.image_Iio_subset (h : StrictAntiOn f (Iic b)) : f '' Iio b su
bseteq Ioi (f b)
参数：h : StrictAntiOn f (Iic b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictAntiOn.mapsTo_Iio`：StrictAntiOn.mapsTo_Iio (h : StrictAntiOn f (Ii
c b)) : MapsTo f (Iio b) (Ioi (f b))
-/
lemma StrictAntiOn.image_Iio_subset (h : StrictAntiOn f (Iic b)) : f '' Iio b ⊆ Ioi (f b) :=
  h.mapsTo_Iio.image_subset
/-
**StrictAntiOn.image_Ioo_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.image_Ioo_subset (h : StrictAntiOn f (Icc a b)) : f '' Ioo a 
b subseteq Ioo (f b) (f a)
参数：h : StrictAntiOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictAntiOn.mapsTo_Ioo`：StrictAntiOn.mapsTo_Ioo (h : StrictAntiOn f (Ic
c a b)) : MapsTo f (Ioo a b) (Ioo (f b) (f a))
-/
lemma StrictAntiOn.image_Ioo_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ioo a b ⊆ Ioo (f b) (f a) := h.mapsTo_Ioo.image_subset
/-
**Monotone.image_Ici_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.image_Ici_subset (h : Monotone f) : f '' Ici a subseteq Ici (f a)
参数：h : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.image_Ici_subset`：MonotoneOn.image_Ici_subset (h : MonotoneOn
 f (Ici a)) : f '' Ici a subseteq Ici (f a)
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
lemma Monotone.image_Ici_subset (h : Monotone f) : f '' Ici a ⊆ Ici (f a) :=
  (h.monotoneOn _).image_Ici_subset
/-
**Monotone.image_Iic_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.image_Iic_subset (h : Monotone f) : f '' Iic b subseteq Iic (f b)
参数：h : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.image_Iic_subset`：MonotoneOn.image_Iic_subset (h : MonotoneOn
 f (Iic b)) : f '' Iic b subseteq Iic (f b)
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
lemma Monotone.image_Iic_subset (h : Monotone f) : f '' Iic b ⊆ Iic (f b) :=
  (h.monotoneOn _).image_Iic_subset
/-
**Monotone.image_Icc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.image_Icc_subset (h : Monotone f) : f '' Icc a b subseteq Icc (f 
a) (f b)
参数：h : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.image_Icc_subset`：MonotoneOn.image_Icc_subset (h : MonotoneOn
 f (Icc a b)) : f '' Icc a b subseteq Icc (f a) (f b)
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
-/
lemma Monotone.image_Icc_subset (h : Monotone f) : f '' Icc a b ⊆ Icc (f a) (f b) :=
  (h.monotoneOn _).image_Icc_subset
/-
**Antitone.image_Ici_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.image_Ici_subset (h : Antitone f) : f '' Ici a subseteq Iic (f a)
参数：h : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntitoneOn.image_Ici_subset`：AntitoneOn.image_Ici_subset (h : AntitoneOn
 f (Ici a)) : f '' Ici a subseteq Iic (f a)
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
lemma Antitone.image_Ici_subset (h : Antitone f) : f '' Ici a ⊆ Iic (f a) :=
  (h.antitoneOn _).image_Ici_subset
/-
**Antitone.image_Iic_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.image_Iic_subset (h : Antitone f) : f '' Iic b subseteq Ici (f b)
参数：h : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntitoneOn.image_Iic_subset`：AntitoneOn.image_Iic_subset (h : AntitoneOn
 f (Iic b)) : f '' Iic b subseteq Ici (f b)
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
lemma Antitone.image_Iic_subset (h : Antitone f) : f '' Iic b ⊆ Ici (f b) :=
  (h.antitoneOn _).image_Iic_subset
/-
**Antitone.image_Icc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.image_Icc_subset (h : Antitone f) : f '' Icc a b subseteq Icc (f 
b) (f a)
参数：h : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntitoneOn.image_Icc_subset`：AntitoneOn.image_Icc_subset (h : AntitoneOn
 f (Icc a b)) : f '' Icc a b subseteq Icc (f b) (f a)
· 使用定理 `Antitone.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → ∀ (s : Set α), AntitoneOn f s
-/
lemma Antitone.image_Icc_subset (h : Antitone f) : f '' Icc a b ⊆ Icc (f b) (f a) :=
  (h.antitoneOn _).image_Icc_subset
/-
**StrictMono.image_Ioi_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.image_Ioi_subset (h : StrictMono f) : f '' Ioi a subseteq Ioi (
f a)
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.image_Ioi_subset`：StrictMonoOn.image_Ioi_subset (h : Strict
MonoOn f (Ici a)) : f '' Ioi a subseteq Ioi (f a)
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.image_Ioi_subset (h : StrictMono f) : f '' Ioi a ⊆ Ioi (f a) :=
  (h.strictMonoOn _).image_Ioi_subset
/-
**StrictMono.image_Iio_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.image_Iio_subset (h : StrictMono f) : f '' Iio b subseteq Iio (
f b)
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.image_Iio_subset`：StrictMonoOn.image_Iio_subset (h : Strict
MonoOn f (Iic b)) : f '' Iio b subseteq Iio (f b)
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.image_Iio_subset (h : StrictMono f) : f '' Iio b ⊆ Iio (f b) :=
  (h.strictMonoOn _).image_Iio_subset
/-
**StrictMono.image_Ioo_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.image_Ioo_subset (h : StrictMono f) : f '' Ioo a b subseteq Ioo
 (f a) (f b)
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.image_Ioo_subset`：StrictMonoOn.image_Ioo_subset (h : Strict
MonoOn f (Icc a b)) : f '' Ioo a b subseteq Ioo (f a) (f b)
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.image_Ioo_subset (h : StrictMono f) : f '' Ioo a b ⊆ Ioo (f a) (f b) :=
  (h.strictMonoOn _).image_Ioo_subset
/-
**StrictAnti.image_Ioi_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.image_Ioi_subset (h : StrictAnti f) : f '' Ioi a subseteq Iio (
f a)
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.image_Ioi_subset`：StrictAntiOn.image_Ioi_subset (h : Strict
AntiOn f (Ici a)) : f '' Ioi a subseteq Iio (f a)
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.image_Ioi_subset (h : StrictAnti f) : f '' Ioi a ⊆ Iio (f a) :=
  (h.strictAntiOn _).image_Ioi_subset
/-
**StrictAnti.image_Iio_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.image_Iio_subset (h : StrictAnti f) : f '' Iio b subseteq Ioi (
f b)
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.image_Iio_subset`：StrictAntiOn.image_Iio_subset (h : Strict
AntiOn f (Iic b)) : f '' Iio b subseteq Ioi (f b)
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.image_Iio_subset (h : StrictAnti f) : f '' Iio b ⊆ Ioi (f b) :=
  (h.strictAntiOn _).image_Iio_subset
/-
**StrictAnti.image_Ioo_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.image_Ioo_subset (h : StrictAnti f) : f '' Ioo a b subseteq Ioo
 (f b) (f a)
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.image_Ioo_subset`：StrictAntiOn.image_Ioo_subset (h : Strict
AntiOn f (Icc a b)) : f '' Ioo a b subseteq Ioo (f b) (f a)
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.image_Ioo_subset (h : StrictAnti f) : f '' Ioo a b ⊆ Ioo (f b) (f a) :=
  (h.strictAntiOn _).image_Ioo_subset

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β] {a b : α}

/-
**StrictMonoOn.mapsTo_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mapsTo_Ico (h : StrictMonoOn f (Icc a b)) : MapsTo f (Ico a b
) (Ico (f a) (f b))
参数：h : StrictMonoOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
-/
lemma StrictMonoOn.mapsTo_Ico (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  fun _c hc ↦ ⟨h.monotoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1,
    h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2⟩
/-
**StrictMonoOn.mapsTo_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.mapsTo_Ioc (h : StrictMonoOn f (Icc a b)) : MapsTo f (Ioc a b
) (Ioc (f a) (f b))
参数：h : StrictMonoOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
-/
lemma StrictMonoOn.mapsTo_Ioc (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  fun _c hc ↦ ⟨h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1,
    h.monotoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2⟩
/-
**StrictAntiOn.mapsTo_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mapsTo_Ico (h : StrictAntiOn f (Icc a b)) : MapsTo f (Ico a b
) (Ioc (f b) (f a))
参数：h : StrictAntiOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `StrictAntiOn.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → Antiton
eOn f s
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
lemma StrictAntiOn.mapsTo_Ico (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ico a b) (Ioc (f b) (f a)) :=
  fun _c hc ↦ ⟨h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2,
    h.antitoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1⟩
/-
**StrictAntiOn.mapsTo_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.mapsTo_Ioc (h : StrictAntiOn f (Icc a b)) : MapsTo f (Ioc a b
) (Ico (f b) (f a))
参数：h : StrictAntiOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → Antiton
eOn f s
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
lemma StrictAntiOn.mapsTo_Ioc (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ioc a b) (Ico (f b) (f a)) :=
  fun _c hc ↦ ⟨h.antitoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2,
    h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1⟩
/-
**StrictMono.mapsTo_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mapsTo_Ico (h : StrictMono f) : MapsTo f (Ico a b) (Ico (f a) (
f b))
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.mapsTo_Ico`：StrictMonoOn.mapsTo_Ico (h : StrictMonoOn f (Ic
c a b)) : MapsTo f (Ico a b) (Ico (f a) (f b))
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.mapsTo_Ico (h : StrictMono f) : MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ico
/-
**StrictMono.mapsTo_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mapsTo_Ioc (h : StrictMono f) : MapsTo f (Ioc a b) (Ioc (f a) (
f b))
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.mapsTo_Ioc`：StrictMonoOn.mapsTo_Ioc (h : StrictMonoOn f (Ic
c a b)) : MapsTo f (Ioc a b) (Ioc (f a) (f b))
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.mapsTo_Ioc (h : StrictMono f) : MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ioc
/-
**StrictAnti.mapsTo_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mapsTo_Ico (h : StrictAnti f) : MapsTo f (Ico a b) (Ioc (f b) (
f a))
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.mapsTo_Ico`：StrictAntiOn.mapsTo_Ico (h : StrictAntiOn f (Ic
c a b)) : MapsTo f (Ico a b) (Ioc (f b) (f a))
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.mapsTo_Ico (h : StrictAnti f) : MapsTo f (Ico a b) (Ioc (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ico
/-
**StrictAnti.mapsTo_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mapsTo_Ioc (h : StrictAnti f) : MapsTo f (Ioc a b) (Ico (f b) (
f a))
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.mapsTo_Ioc`：StrictAntiOn.mapsTo_Ioc (h : StrictAntiOn f (Ic
c a b)) : MapsTo f (Ioc a b) (Ico (f b) (f a))
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.mapsTo_Ioc (h : StrictAnti f) : MapsTo f (Ioc a b) (Ico (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioc
/-
**StrictMonoOn.image_Ico_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.image_Ico_subset (h : StrictMonoOn f (Icc a b)) : f '' Ico a 
b subseteq Ico (f a) (f b)
参数：h : StrictMonoOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictMonoOn.mapsTo_Ico`：StrictMonoOn.mapsTo_Ico (h : StrictMonoOn f (Ic
c a b)) : MapsTo f (Ico a b) (Ico (f a) (f b))
-/
lemma StrictMonoOn.image_Ico_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ico a b ⊆ Ico (f a) (f b) := h.mapsTo_Ico.image_subset
/-
**StrictMonoOn.image_Ioc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMonoOn.image_Ioc_subset (h : StrictMonoOn f (Icc a b)) : f '' Ioc a 
b subseteq Ioc (f a) (f b)
参数：h : StrictMonoOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictMonoOn.mapsTo_Ioc`：StrictMonoOn.mapsTo_Ioc (h : StrictMonoOn f (Ic
c a b)) : MapsTo f (Ioc a b) (Ioc (f a) (f b))
-/
lemma StrictMonoOn.image_Ioc_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ioc a b ⊆ Ioc (f a) (f b) :=
  h.mapsTo_Ioc.image_subset
/-
**StrictAntiOn.image_Ico_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.image_Ico_subset (h : StrictAntiOn f (Icc a b)) : f '' Ico a 
b subseteq Ioc (f b) (f a)
参数：h : StrictAntiOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictAntiOn.mapsTo_Ico`：StrictAntiOn.mapsTo_Ico (h : StrictAntiOn f (Ic
c a b)) : MapsTo f (Ico a b) (Ioc (f b) (f a))
-/
lemma StrictAntiOn.image_Ico_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ico a b ⊆ Ioc (f b) (f a) := h.mapsTo_Ico.image_subset
/-
**StrictAntiOn.image_Ioc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAntiOn.image_Ioc_subset (h : StrictAntiOn f (Icc a b)) : f '' Ioc a 
b subseteq Ico (f b) (f a)
参数：h : StrictAntiOn f (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用引理 `StrictAntiOn.mapsTo_Ioc`：StrictAntiOn.mapsTo_Ioc (h : StrictAntiOn f (Ic
c a b)) : MapsTo f (Ioc a b) (Ico (f b) (f a))
-/
lemma StrictAntiOn.image_Ioc_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ioc a b ⊆ Ico (f b) (f a) := h.mapsTo_Ioc.image_subset
/-
**StrictMono.image_Ico_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.image_Ico_subset (h : StrictMono f) : f '' Ico a b subseteq Ico
 (f a) (f b)
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.image_Ico_subset`：StrictMonoOn.image_Ico_subset (h : Strict
MonoOn f (Icc a b)) : f '' Ico a b subseteq Ico (f a) (f b)
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.image_Ico_subset (h : StrictMono f) : f '' Ico a b ⊆ Ico (f a) (f b) :=
  (h.strictMonoOn _).image_Ico_subset
/-
**StrictMono.image_Ioc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.image_Ioc_subset (h : StrictMono f) : f '' Ioc a b subseteq Ioc
 (f a) (f b)
参数：h : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.image_Ioc_subset`：StrictMonoOn.image_Ioc_subset (h : Strict
MonoOn f (Icc a b)) : f '' Ioc a b subseteq Ioc (f a) (f b)
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
-/
lemma StrictMono.image_Ioc_subset (h : StrictMono f) : f '' Ioc a b ⊆ Ioc (f a) (f b) :=
  (h.strictMonoOn _).image_Ioc_subset
/-
**StrictAnti.image_Ico_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.image_Ico_subset (h : StrictAnti f) : f '' Ico a b subseteq Ioc
 (f b) (f a)
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.image_Ico_subset`：StrictAntiOn.image_Ico_subset (h : Strict
AntiOn f (Icc a b)) : f '' Ico a b subseteq Ioc (f b) (f a)
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.image_Ico_subset (h : StrictAnti f) : f '' Ico a b ⊆ Ioc (f b) (f a) :=
  (h.strictAntiOn _).image_Ico_subset
/-
**StrictAnti.image_Ioc_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.image_Ioc_subset (h : StrictAnti f) : f '' Ioc a b subseteq Ico
 (f b) (f a)
参数：h : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.image_Ioc_subset`：StrictAntiOn.image_Ioc_subset (h : Strict
AntiOn f (Icc a b)) : f '' Ioc a b subseteq Ico (f b) (f a)
· 使用定理 `StrictAnti.strictAntiOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictAnti f → ∀ (s : Set α), StrictAntiOn
 f s
-/
lemma StrictAnti.image_Ioc_subset (h : StrictAnti f) : f '' Ioc a b ⊆ Ico (f b) (f a) :=
  (h.strictAntiOn _).image_Ioc_subset

end PartialOrder

namespace Set

/-
**Set.image_subtype_val_Ixx_Ixi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma image_subtype_val_Ixx_Ixi {p q r : α → α → Prop} {a b : α} (c : {x // p a x ∧ q x b})
    (h : ∀ {x}, r c x → p a x) :
    Subtype.val '' {y : {x // p a x ∧ q x b} | r c.1 y.1} = {y : α | r c.1 y ∧ q y b} :=
  (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r c.1 y}).trans <| by
    ext; simp +contextual [@and_comm (r _ _), h]
/-
**Set.image_subtype_val_Ixx_Iix** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma image_subtype_val_Ixx_Iix {p q r : α → α → Prop} {a b : α} (c : {x // p a x ∧ q x b})
    (h : ∀ {x}, r x c → q x b) :
    Subtype.val '' {y : {x // p a x ∧ q x b} | r y.1 c.1} = {y : α | p a y ∧ r y c.1} :=
  (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r y c.1}).trans <| by
    ext; simp +contextual [h]

variable [Preorder α] {p : α → Prop}
/-
**Set.preimage_subtype_val_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a : { x // p x }), Su
btype.val ⁻¹' Set.Ici ↑a = Set.Ici a
参数：a : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Ici (a : {x // p x}) : (↑) ⁻¹' (Ici a.1) = Ici a := rfl
/-
**Set.preimage_subtype_val_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a : { x // p x }), Su
btype.val ⁻¹' Set.Iic ↑a = Set.Iic a
参数：a : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Iic (a : {x // p x}) : (↑) ⁻¹' (Iic a.1) = Iic a := rfl
/-
**Set.preimage_subtype_val_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a : { x // p x }), Su
btype.val ⁻¹' Set.Ioi ↑a = Set.Ioi a
参数：a : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Ioi (a : {x // p x}) : (↑) ⁻¹' (Ioi a.1) = Ioi a := rfl
/-
**Set.preimage_subtype_val_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a : { x // p x }), Su
btype.val ⁻¹' Set.Iio ↑a = Set.Iio a
参数：a : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Iio (a : {x // p x}) : (↑) ⁻¹' (Iio a.1) = Iio a := rfl
/-
**Set.preimage_subtype_val_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a b : { x // p x }), 
Subtype.val ⁻¹' Set.Icc ↑a ↑b = Set.Icc a b
参数：a b : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Icc (a b : {x // p x}) : (↑) ⁻¹' (Icc a.1 b) = Icc a b := rfl
/-
**Set.preimage_subtype_val_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a b : { x // p x }), 
Subtype.val ⁻¹' Set.Ico ↑a ↑b = Set.Ico a b
参数：a b : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Ico (a b : {x // p x}) : (↑) ⁻¹' (Ico a.1 b) = Ico a b := rfl
/-
**Set.preimage_subtype_val_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a b : { x // p x }), 
Subtype.val ⁻¹' Set.Ioc ↑a ↑b = Set.Ioc a b
参数：a b : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Ioc (a b : {x // p x}) : (↑) ⁻¹' (Ioc a.1 b) = Ioc a b := rfl
/-
**Set.preimage_subtype_val_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {p : α → Prop} (a b : { x // p x }), 
Subtype.val ⁻¹' Set.Ioo ↑a ↑b = Set.Ioo a b
参数：a b : { x // p x }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_subtype_val_Ioo (a b : {x // p x}) : (↑) ⁻¹' (Ioo a.1 b) = Ioo a b := rfl
/-
**Set.image_subtype_val_Icc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Icc_subset (a b : {x // p x}) : Subtype.val '' Icc a b s
ubseteq Icc a.val b.val
参数：a b : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Icc_subset (a b : {x // p x}) :
    Subtype.val '' Icc a b ⊆ Icc a.val b.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Ico_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ico_subset (a b : {x // p x}) : Subtype.val '' Ico a b s
ubseteq Ico a.val b.val
参数：a b : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Ico_subset (a b : {x // p x}) :
    Subtype.val '' Ico a b ⊆ Ico a.val b.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Ioc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioc_subset (a b : {x // p x}) : Subtype.val '' Ioc a b s
ubseteq Ioc a.val b.val
参数：a b : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Ioc_subset (a b : {x // p x}) :
    Subtype.val '' Ioc a b ⊆ Ioc a.val b.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Ioo_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioo_subset (a b : {x // p x}) : Subtype.val '' Ioo a b s
ubseteq Ioo a.val b.val
参数：a b : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Ioo_subset (a b : {x // p x}) :
    Subtype.val '' Ioo a b ⊆ Ioo a.val b.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Iic_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iic_subset (a : {x // p x}) : Subtype.val '' Iic a subse
teq Iic a.val
参数：a : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Iic_subset (a : {x // p x}) :
    Subtype.val '' Iic a ⊆ Iic a.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Iio_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iio_subset (a : {x // p x}) : Subtype.val '' Iio a subse
teq Iio a.val
参数：a : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Iio_subset (a : {x // p x}) :
    Subtype.val '' Iio a ⊆ Iio a.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Ici_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ici_subset (a : {x // p x}) : Subtype.val '' Ici a subse
teq Ici a.val
参数：a : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Ici_subset (a : {x // p x}) :
    Subtype.val '' Ici a ⊆ Ici a.val :=
  image_subset_iff.mpr fun _ m => m
/-
**Set.image_subtype_val_Ioi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioi_subset (a : {x // p x}) : Subtype.val '' Ioi a subse
teq Ioi a.val
参数：a : {x // p x}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem image_subtype_val_Ioi_subset (a : {x // p x}) :
    Subtype.val '' Ioi a ⊆ Ioi a.val :=
  image_subset_iff.mpr fun _ m => m

@[simp]
/-
**Set.image_subtype_val_Ici_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ici_Iic {a : α} (b : Ici a) : Subtype.val '' Iic b = Icc
 a b
参数：b : Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
-/
lemma image_subtype_val_Ici_Iic {a : α} (b : Ici a) : Subtype.val '' Iic b = Icc a b :=
  (Subtype.image_preimage_val (Ici a) (Iic b.1)).trans Ici_inter_Iic

@[simp]
/-
**Set.image_subtype_val_Ici_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ici_Iio {a : α} (b : Ici a) : Subtype.val '' Iio b = Ico
 a b
参数：b : Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
-/
lemma image_subtype_val_Ici_Iio {a : α} (b : Ici a) : Subtype.val '' Iio b = Ico a b :=
  (Subtype.image_preimage_val (Ici a) (Iio b.1)).trans Ici_inter_Iio

@[simp]
/-
**Set.image_subtype_val_Ici_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ici_Ici {a : α} (b : Ici a) : Subtype.val '' Ici b = Ici
 b.1
参数：b : Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ici_Ici {a : α} (b : Ici a) : Subtype.val '' Ici b = Ici b.1 :=
  (Subtype.image_preimage_val (Ici a) (Ici b.1)).trans <| inter_eq_right.2 <| Ici_subset_Ici.2 b.2

@[simp]
/-
**Set.image_subtype_val_Ici_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ici_Ioi {a : α} (b : Ici a) : Subtype.val '' Ioi b = Ioi
 b.1
参数：b : Ici a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.Ioi_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ici b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ici_Ioi {a : α} (b : Ici a) : Subtype.val '' Ioi b = Ioi b.1 :=
  (Subtype.image_preimage_val (Ici a) (Ioi b.1)).trans <| inter_eq_right.2 <| Ioi_subset_Ici b.2

@[simp]
/-
**Set.image_subtype_val_Iic_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iic_Ici {a : α} (b : Iic a) : Subtype.val '' Ici b = Icc
 b.1 a
参数：b : Iic a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
lemma image_subtype_val_Iic_Ici {a : α} (b : Iic a) : Subtype.val '' Ici b = Icc b.1 a :=
  (Subtype.image_preimage_val (Iic a) (Ici b)).trans <| inter_comm _ _

@[simp]
/-
**Set.image_subtype_val_Iic_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iic_Ioi {a : α} (b : Iic a) : Subtype.val '' Ioi b = Ioc
 b.1 a
参数：b : Iic a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
lemma image_subtype_val_Iic_Ioi {a : α} (b : Iic a) : Subtype.val '' Ioi b = Ioc b.1 a :=
  (Subtype.image_preimage_val (Iic a) (Ioi b)).trans <| inter_comm _ _

@[simp]
/-
**Set.image_subtype_val_Iic_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iic_Iic {a : α} (b : Iic a) : Subtype.val '' Iic b = Iic
 b.1
参数：b : Iic a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ici_Ici`：image_subtype_val_Ici_Ici {a : α} (b : Ic
i a) : Subtype.val '' Ici b = Ici b.1
-/
lemma image_subtype_val_Iic_Iic {a : α} (b : Iic a) : Subtype.val '' Iic b = Iic b.1 :=
  image_subtype_val_Ici_Ici (α := αᵒᵈ) _

@[simp]
/-
**Set.image_subtype_val_Iic_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iic_Iio {a : α} (b : Iic a) : Subtype.val '' Iio b = Iio
 b.1
参数：b : Iic a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ici_Ioi`：image_subtype_val_Ici_Ioi {a : α} (b : Ic
i a) : Subtype.val '' Ioi b = Ioi b.1
-/
lemma image_subtype_val_Iic_Iio {a : α} (b : Iic a) : Subtype.val '' Iio b = Iio b.1 :=
  image_subtype_val_Ici_Ioi (α := αᵒᵈ) _

@[simp]
/-
**Set.image_subtype_val_Ioi_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioi_Ici {a : α} (b : Ioi a) : Subtype.val '' Ici b = Ici
 b.1
参数：b : Ioi a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioi_Ici {a : α} (b : Ioi a) : Subtype.val '' Ici b = Ici b.1 :=
  (Subtype.image_preimage_val (Ioi a) (Ici b.1)).trans <| inter_eq_right.2 <| Ici_subset_Ioi.2 b.2

@[simp]
/-
**Set.image_subtype_val_Ioi_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioi_Iic {a : α} (b : Ioi a) : Subtype.val '' Iic b = Ioc
 a b
参数：b : Ioi a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
-/
lemma image_subtype_val_Ioi_Iic {a : α} (b : Ioi a) : Subtype.val '' Iic b = Ioc a b :=
  (Subtype.image_preimage_val (Ioi a) (Iic b.1)).trans Ioi_inter_Iic

@[simp]
/-
**Set.image_subtype_val_Ioi_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioi_Ioi {a : α} (b : Ioi a) : Subtype.val '' Ioi b = Ioi
 b.1
参数：b : Ioi a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioi_Ioi {a : α} (b : Ioi a) : Subtype.val '' Ioi b = Ioi b.1 :=
  (Subtype.image_preimage_val (Ioi a) (Ioi b.1)).trans <| inter_eq_right.2 <| Ioi_subset_Ioi b.2.le

@[simp]
/-
**Set.image_subtype_val_Ioi_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioi_Iio {a : α} (b : Ioi a) : Subtype.val '' Iio b = Ioo
 a b
参数：b : Ioi a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
lemma image_subtype_val_Ioi_Iio {a : α} (b : Ioi a) : Subtype.val '' Iio b = Ioo a b :=
  (Subtype.image_preimage_val (Ioi a) (Iio b.1)).trans Ioi_inter_Iio

@[simp]
/-
**Set.image_subtype_val_Iio_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iio_Ici {a : α} (b : Iio a) : Subtype.val '' Ici b = Ico
 b.1 a
参数：b : Iio a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
lemma image_subtype_val_Iio_Ici {a : α} (b : Iio a) : Subtype.val '' Ici b = Ico b.1 a :=
  (Subtype.image_preimage_val (Iio a) (Ici b)).trans <| inter_comm _ _

@[simp]
/-
**Set.image_subtype_val_Iio_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iio_Iic {a : α} (b : Iio a) : Subtype.val '' Iic b = Iic
 b.1
参数：b : Iio a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ioi_Ici`：image_subtype_val_Ioi_Ici {a : α} (b : Io
i a) : Subtype.val '' Ici b = Ici b.1
-/
lemma image_subtype_val_Iio_Iic {a : α} (b : Iio a) : Subtype.val '' Iic b = Iic b.1 :=
  image_subtype_val_Ioi_Ici (α := αᵒᵈ) _

@[simp]
/-
**Set.image_subtype_val_Iio_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iio_Ioi {a : α} (b : Iio a) : Subtype.val '' Ioi b = Ioo
 b.1 a
参数：b : Iio a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.image_preimage_val`：image_preimage_val (s t : Set α) : (Subtype.
val : s -> α) '' Subtype.val ⁻¹' t = s inter t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
lemma image_subtype_val_Iio_Ioi {a : α} (b : Iio a) : Subtype.val '' Ioi b = Ioo b.1 a :=
  (Subtype.image_preimage_val (Iio a) (Ioi b)).trans <| inter_comm _ _

@[simp]
/-
**Set.image_subtype_val_Iio_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Iio_Iio {a : α} (b : Iio a) : Subtype.val '' Iio b = Iio
 b.1
参数：b : Iio a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ioi_Ioi`：image_subtype_val_Ioi_Ioi {a : α} (b : Io
i a) : Subtype.val '' Ioi b = Ioi b.1
-/
lemma image_subtype_val_Iio_Iio {a : α} (b : Iio a) : Subtype.val '' Iio b = Iio b.1 :=
  image_subtype_val_Ioi_Ioi (α := αᵒᵈ) _

@[simp]
/-
**Set.image_subtype_val_Icc_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Icc_Ici {a b : α} (c : Icc a b) : Subtype.val '' Ici c =
 Icc c.1 b
参数：c : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Icc_Ici {a b : α} (c : Icc a b) : Subtype.val '' Ici c = Icc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/-
**Set.image_subtype_val_Icc_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Icc_Iic {a b : α} (c : Icc a b) : Subtype.val '' Iic c =
 Icc a c
参数：c : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Icc_Iic {a b : α} (c : Icc a b) : Subtype.val '' Iic c = Icc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]
/-
**Set.image_subtype_val_Icc_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Icc_Ioi {a b : α} (c : Icc a b) : Subtype.val '' Ioi c =
 Ioc c.1 b
参数：c : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma image_subtype_val_Icc_Ioi {a b : α} (c : Icc a b) : Subtype.val '' Ioi c = Ioc c.1 b :=
  image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]
/-
**Set.image_subtype_val_Icc_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Icc_Iio {a b : α} (c : Icc a b) : Subtype.val '' Iio c =
 Ico a c
参数：c : Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Icc_Iio {a b : α} (c : Icc a b) : Subtype.val '' Iio c = Ico a c :=
  image_subtype_val_Ixx_Iix c fun h ↦ (le_of_lt h).trans c.2.2

@[simp]
/-
**Set.image_subtype_val_Ico_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ico_Ici {a b : α} (c : Ico a b) : Subtype.val '' Ici c =
 Ico c.1 b
参数：c : Ico a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ico_Ici {a b : α} (c : Ico a b) : Subtype.val '' Ici c = Ico c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/-
**Set.image_subtype_val_Ico_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ico_Iic {a b : α} (c : Ico a b) : Subtype.val '' Iic c =
 Icc a c
参数：c : Ico a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ico_Iic {a b : α} (c : Ico a b) : Subtype.val '' Iic c = Icc a c :=
  image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]
/-
**Set.image_subtype_val_Ico_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ico_Ioi {a b : α} (c : Ico a b) : Subtype.val '' Ioi c =
 Ioo c.1 b
参数：c : Ico a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma image_subtype_val_Ico_Ioi {a b : α} (c : Ico a b) : Subtype.val '' Ioi c = Ioo c.1 b :=
  image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]
/-
**Set.image_subtype_val_Ico_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ico_Iio {a b : α} (c : Ico a b) : Subtype.val '' Iio c =
 Ico a c
参数：c : Ico a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ico_Iio {a b : α} (c : Ico a b) : Subtype.val '' Iio c = Ico a c :=
  image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

@[simp]
/-
**Set.image_subtype_val_Ioc_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioc_Ici {a b : α} (c : Ioc a b) : Subtype.val '' Ici c =
 Icc c.1 b
参数：c : Ioc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioc_Ici {a b : α} (c : Ioc a b) : Subtype.val '' Ici c = Icc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]
/-
**Set.image_subtype_val_Ioc_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioc_Iic {a b : α} (c : Ioc a b) : Subtype.val '' Iic c =
 Ioc a c
参数：c : Ioc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioc_Iic {a b : α} (c : Ioc a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]
/-
**Set.image_subtype_val_Ioc_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioc_Ioi {a b : α} (c : Ioc a b) : Subtype.val '' Ioi c =
 Ioc c.1 b
参数：c : Ioc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioc_Ioi {a b : α} (c : Ioc a b) : Subtype.val '' Ioi c = Ioc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/-
**Set.image_subtype_val_Ioc_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioc_Iio {a b : α} (c : Ioc a b) : Subtype.val '' Iio c =
 Ioo a c
参数：c : Ioc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioc_Iio {a b : α} (c : Ioc a b) : Subtype.val '' Iio c = Ioo a c :=
  image_subtype_val_Ixx_Iix c fun h ↦ (le_of_lt h).trans c.2.2

@[simp]
/-
**Set.image_subtype_val_Ioo_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioo_Ici {a b : α} (c : Ioo a b) : Subtype.val '' Ici c =
 Ico c.1 b
参数：c : Ioo a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioo_Ici {a b : α} (c : Ioo a b) : Subtype.val '' Ici c = Ico c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]
/-
**Set.image_subtype_val_Ioo_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioo_Iic {a b : α} (c : Ioo a b) : Subtype.val '' Iic c =
 Ioc a c
参数：c : Ioo a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioo_Iic {a b : α} (c : Ioo a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]
/-
**Set.image_subtype_val_Ioo_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioo_Ioi {a b : α} (c : Ioo a b) : Subtype.val '' Ioi c =
 Ioo c.1 b
参数：c : Ioo a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ix
i`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r (↑c) x → p a x) → Subtype.val '' {y | r ↑c ↑…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioo_Ioi {a b : α} (c : Ioo a b) : Subtype.val '' Ioi c = Ioo c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/-
**Set.image_subtype_val_Ioo_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_subtype_val_Ioo_Iio {a b : α} (c : Ioo a b) : Subtype.val '' Iio c =
 Ioo a c
参数：c : Ioo a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Order.Interval.Set.Image.0.Set.image_subtype_val_Ixx_Ii
x`：∀ {α : Type u_1} {p q r : α → α → Prop} {a b : α} (c : { x // p a x ∧ q x b }
),   (∀ {x : α}, r x ↑c → q x b) → Subtype.val '' {y | r ↑y ↑c}…
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma image_subtype_val_Ioo_Iio {a b : α} (c : Ioo a b) : Subtype.val '' Iio c = Ioo a c :=
  image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

end Set

section Preorder
variable [Preorder α]

/-
**directedOn_le_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_le_Iic (b : α) : DirectedOn (· <= ·) (Iic b)
参数：b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma directedOn_le_Iic (b : α) : DirectedOn (· ≤ ·) (Iic b) :=
  fun _x hx _y hy ↦ ⟨b, le_rfl, hx, hy⟩
/-
**directedOn_le_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_le_Icc (a b : α) : DirectedOn (· <= ·) (Icc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma directedOn_le_Icc (a b : α) : DirectedOn (· ≤ ·) (Icc a b) :=
  fun _x hx _y hy ↦ ⟨b, right_mem_Icc.2 <| hx.1.trans hx.2, hx.2, hy.2⟩
/-
**directedOn_le_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_le_Ioc (a b : α) : DirectedOn (· <= ·) (Ioc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma directedOn_le_Ioc (a b : α) : DirectedOn (· ≤ ·) (Ioc a b) :=
  fun _x hx _y hy ↦ ⟨b, right_mem_Ioc.2 <| hx.1.trans_le hx.2, hx.2, hy.2⟩
/-
**directedOn_ge_Ici** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_ge_Ici (a : α) : DirectedOn (· >= ·) (Ici a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma directedOn_ge_Ici (a : α) : DirectedOn (· ≥ ·) (Ici a) :=
  fun _x hx _y hy ↦ ⟨a, le_rfl, hx, hy⟩
/-
**directedOn_ge_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_ge_Icc (a b : α) : DirectedOn (· >= ·) (Icc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma directedOn_ge_Icc (a b : α) : DirectedOn (· ≥ ·) (Icc a b) :=
  fun _x hx _y hy ↦ ⟨a, left_mem_Icc.2 <| hx.1.trans hx.2, hx.1, hy.1⟩
/-
**directedOn_ge_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：directedOn_ge_Ico (a b : α) : DirectedOn (· >= ·) (Ico a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma directedOn_ge_Ico (a b : α) : DirectedOn (· ≥ ·) (Ico a b) :=
  fun _x hx _y hy ↦ ⟨a, left_mem_Ico.2 <| hx.1.trans_lt hx.2, hx.1, hy.1⟩

end Preorder

