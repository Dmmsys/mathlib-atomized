/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Monotonicity on intervals

In this file we prove that a function is (strictly) monotone (or antitone) on a linear order `α`
provided that it is (strictly) monotone on `(-∞, a]` and on `[a, +∞)`. This is a special case
of a more general statement where one deduces monotonicity on a union from monotonicity on each
set.
-/

public section


open Set

variable {α β : Type*} [LinearOrder α] [Preorder β] {a : α} {f : α → β}

/-- If `f` is strictly monotone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is strictly monotone on `s ∪ t` -/
/-
**StrictMonoOn.union** 是 Mathlib 中的一个定理，位于命名空间 `StrictMonoOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {f : α → β} {s t : Set α} {c : α},   StrictMonoOn f s → StrictMonoOn f t → Is
Greatest s c → IsLeast t c → StrictMonoOn f (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If `f` is strictly monotone both on `s` and `t`, with `s` to the left of `t` and
 the center
point belonging to both `s` and `t`, then `f` is strictly monotone on `s ∪ t`
-/
protected theorem StrictMonoOn.union {s t : Set α} {c : α} (h₁ : StrictMonoOn f s)
    (h₂ : StrictMonoOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : StrictMonoOn f (s ∪ t) := by
  have A : ∀ x, x ∈ s ∪ t → x ≤ c → x ∈ s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : ∀ x, x ∈ s ∪ t → c ≤ x → x ∈ t := by
    intro x hx hxc
    match hx with
    | Or.inr hx => exact hx
    | Or.inl hx =>
      rcases eq_or_lt_of_le hxc with (rfl | h'x)
      · exact ht.1
      exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim
  intro x hx y hy hxy
  rcases lt_or_ge x c with (hxc | hcx)
  · have xs : x ∈ s := A _ hx hxc.le
    rcases lt_or_ge y c with (hyc | hcy)
    · exact h₁ xs (A _ hy hyc.le) hxy
    · exact (h₁ xs hs.1 hxc).trans_le (h₂.monotoneOn ht.1 (B _ hy hcy) hcy)
  · have xt : x ∈ t := B _ hx hcx
    have yt : y ∈ t := B _ hy (hcx.trans hxy.le)
    exact h₂ xt yt hxy

/-- If `f` is strictly monotone both on `(-∞, a]` and `[a, ∞)`, then it is strictly monotone on the
whole line. -/
/-
**StrictMonoOn.Iic_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `StrictMonoOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {a : α} {f : α → β},   StrictMonoOn f (Set.Iic a) → StrictMonoOn f (Set.Ici a
) → StrictMono f
参数：Set.Iic a；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `strictMonoOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β},   StrictMonoOn f Set.univ ↔ StrictMono f
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `StrictMonoOn.union`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder 
α] [inst_1 : Preorder β] {f : α → β} {s t : Set α} {c : α},   StrictMonoOn f s →
 StrictM…
· 使用定理 `isGreatest_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGreatest
 (Set.Iic a) a
· 使用定理 `isLeast_Ici`：isLeast_Ici : IsLeast (Ici a) a

--- 原说明 ---
If `f` is strictly monotone both on `(-∞, a]` and `[a, ∞)`, then it is strictly 
monotone on the
whole line.
-/
protected theorem StrictMonoOn.Iic_union_Ici (h₁ : StrictMonoOn f (Iic a))
    (h₂ : StrictMonoOn f (Ici a)) : StrictMono f := by
  rw [← strictMonoOn_univ, ← @Iic_union_Ici _ _ a]
  exact StrictMonoOn.union h₁ h₂ isGreatest_Iic isLeast_Ici

/-- If `f` is strictly antitone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is strictly antitone on `s ∪ t` -/
/-
**StrictAntiOn.union** 是 Mathlib 中的一个定理，位于命名空间 `StrictAntiOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {f : α → β} {s t : Set α} {c : α},   StrictAntiOn f s → StrictAntiOn f t → Is
Greatest s c → IsLeast t c → StrictAntiOn f (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → StrictAntiO
n (⇑OrderDual…
· 使用定理 `StrictMonoOn.union`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder 
α] [inst_1 : Preorder β] {f : α → β} {s t : Set α} {c : α},   StrictMonoOn f s →
 StrictM…
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…

--- 原说明 ---
If `f` is strictly antitone both on `s` and `t`, with `s` to the left of `t` and
 the center
point belonging to both `s` and `t`, then `f` is strictly antitone on `s ∪ t`
-/
protected theorem StrictAntiOn.union {s t : Set α} {c : α} (h₁ : StrictAntiOn f s)
    (h₂ : StrictAntiOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : StrictAntiOn f (s ∪ t) :=
  (h₁.dual_right.union h₂.dual_right hs ht).dual_right

/-- If `f` is strictly antitone both on `(-∞, a]` and `[a, ∞)`, then it is strictly antitone on the
whole line. -/
/-
**StrictAntiOn.Iic_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `StrictAntiOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {a : α} {f : α → β},   StrictAntiOn f (Set.Iic a) → StrictAntiOn f (Set.Ici a
) → StrictAnti f
参数：Set.Iic a；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   StrictMono f → StrictAnti (⇑OrderDual.toDual
 ∘ f)
· 使用定理 `StrictMonoOn.Iic_union_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Line
arOrder α] [inst_1 : Preorder β] {a : α} {f : α → β},   StrictMonoOn f (Set.Iic 
a) → StrictMonoO…
· 使用定理 `StrictAntiOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → StrictMonoO
n (⇑OrderDual…

--- 原说明 ---
If `f` is strictly antitone both on `(-∞, a]` and `[a, ∞)`, then it is strictly 
antitone on the
whole line.
-/
protected theorem StrictAntiOn.Iic_union_Ici (h₁ : StrictAntiOn f (Iic a))
    (h₂ : StrictAntiOn f (Ici a)) : StrictAnti f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

/-- If `f` is monotone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is monotone on `s ∪ t` -/
/-
**MonotoneOn.union_right** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {f : α → β} {s t : Set α} {c : α},   MonotoneOn f s → MonotoneOn f t → IsGrea
test s c → IsLeast t c → MonotoneOn f (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If `f` is monotone both on `s` and `t`, with `s` to the left of `t` and the cent
er
point belonging to both `s` and `t`, then `f` is monotone on `s ∪ t`
-/
protected theorem MonotoneOn.union_right {s t : Set α} {c : α} (h₁ : MonotoneOn f s)
    (h₂ : MonotoneOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : MonotoneOn f (s ∪ t) := by
  have A : ∀ x, x ∈ s ∪ t → x ≤ c → x ∈ s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : ∀ x, x ∈ s ∪ t → c ≤ x → x ∈ t := by
    intro x hx hxc
    match hx with
    | Or.inr hx => exact hx
    | Or.inl hx =>
      rcases eq_or_lt_of_le hxc with (rfl | h'x)
      · exact ht.1
      exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim
  intro x hx y hy hxy
  rcases lt_or_ge x c with (hxc | hcx)
  · have xs : x ∈ s := A _ hx hxc.le
    rcases lt_or_ge y c with (hyc | hcy)
    · exact h₁ xs (A _ hy hyc.le) hxy
    · exact (h₁ xs hs.1 hxc.le).trans (h₂ ht.1 (B _ hy hcy) hcy)
  · have xt : x ∈ t := B _ hx hcx
    have yt : y ∈ t := B _ hy (hcx.trans hxy)
    exact h₂ xt yt hxy

/-- If `f` is monotone both on `(-∞, a]` and `[a, ∞)`, then it is monotone on the whole line. -/
/-
**MonotoneOn.Iic_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MonotoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {a : α} {f : α → β},   MonotoneOn f (Set.Iic a) → MonotoneOn f (Set.Ici a) → 
Monotone f
参数：Set.Iic a；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `monotoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, MonotoneOn f Set.univ ↔ Monotone f
· 使用定理 `Set.Iic_union_Ici`：Iic_union_Ici : Iic a union Ici a = univ
· 使用定理 `MonotoneOn.union_right`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOr
der α] [inst_1 : Preorder β] {f : α → β} {s t : Set α} {c : α},   MonotoneOn f s
 → MonotoneO…
· 使用定理 `isGreatest_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsGreatest
 (Set.Iic a) a
· 使用定理 `isLeast_Ici`：isLeast_Ici : IsLeast (Ici a) a

--- 原说明 ---
If `f` is monotone both on `(-∞, a]` and `[a, ∞)`, then it is monotone on the wh
ole line.
-/
protected theorem MonotoneOn.Iic_union_Ici (h₁ : MonotoneOn f (Iic a)) (h₂ : MonotoneOn f (Ici a)) :
    Monotone f := by
  rw [← monotoneOn_univ, ← @Iic_union_Ici _ _ a]
  exact MonotoneOn.union_right h₁ h₂ isGreatest_Iic isLeast_Ici

/-- If `f` is antitone both on `s` and `t`, with `s` to the left of `t` and the center
point belonging to both `s` and `t`, then `f` is antitone on `s ∪ t` -/
/-
**AntitoneOn.union_right** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {f : α → β} {s t : Set α} {c : α},   AntitoneOn f s → AntitoneOn f t → IsGrea
test s c → IsLeast t c → AntitoneOn f (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (⇑Or
derDual.toD…
· 使用定理 `MonotoneOn.union_right`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOr
der α] [inst_1 : Preorder β] {f : α → β} {s t : Set α} {c : α},   MonotoneOn f s
 → MonotoneO…
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
If `f` is antitone both on `s` and `t`, with `s` to the left of `t` and the cent
er
point belonging to both `s` and `t`, then `f` is antitone on `s ∪ t`
-/
protected theorem AntitoneOn.union_right {s t : Set α} {c : α} (h₁ : AntitoneOn f s)
    (h₂ : AntitoneOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : AntitoneOn f (s ∪ t) :=
  (h₁.dual_right.union_right h₂.dual_right hs ht).dual_right

/-- If `f` is antitone both on `(-∞, a]` and `[a, ∞)`, then it is antitone on the whole line. -/
/-
**AntitoneOn.Iic_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `AntitoneOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : Preorder 
β] {a : α} {f : α → β},   AntitoneOn f (Set.Iic a) → AntitoneOn f (Set.Ici a) → 
Antitone f
参数：Set.Iic a；Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → Antitone (⇑OrderDual.toDual ∘ f)
· 使用定理 `MonotoneOn.Iic_union_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Linear
Order α] [inst_1 : Preorder β] {a : α} {f : α → β},   MonotoneOn f (Set.Iic a) →
 MonotoneOn f …
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
If `f` is antitone both on `(-∞, a]` and `[a, ∞)`, then it is antitone on the wh
ole line.
-/
protected theorem AntitoneOn.Iic_union_Ici (h₁ : AntitoneOn f (Iic a)) (h₂ : AntitoneOn f (Ici a)) :
    Antitone f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
