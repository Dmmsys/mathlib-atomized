/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto

/-!
# More basic logic properties

A few more logic lemmas. These are in their own file, rather than `Logic.Basic`, because it is
convenient to be able to use the `tauto` or `split_ifs` tactics.

## Implementation notes
We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/

public section

/-
**iff_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_assoc {a b c : Prop} : ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem iff_assoc {a b c : Prop} : ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c)) := by tauto
/-
**iff_left_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_left_comm {a b c : Prop} : (a ↔ (b ↔ c)) ↔ (b ↔ (a ↔ c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
theorem iff_left_comm {a b c : Prop} : (a ↔ (b ↔ c)) ↔ (b ↔ (a ↔ c)) := by tauto
/-
**iff_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iff_right_comm {a b c : Prop} : ((a ↔ b) ↔ c) ↔ ((a ↔ c) ↔ b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_iff`：∀ {b a : Prop} [Decidable b], ¬(a ↔ b) ↔ (¬a ↔ b)
-/
theorem iff_right_comm {a b c : Prop} : ((a ↔ b) ↔ c) ↔ ((a ↔ c) ↔ b) := by tauto

protected alias ⟨HEq.eq, Eq.heq⟩ := heq_iff_eq

variable {α : Sort*} {p q : Prop} [Decidable p] [Decidable q] {a b c : α}
/-
**dite_dite_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_dite_distrib_left {a : p -> α} {b : ¬p -> q -> α} {c : ¬p -> ¬q -> α}
 : (dite p a fun hp => dite q (b hp) (c hp)) = dite q (fun hq => (dite p a) fun 
hp => b hp hq) fun hq => (dite p a) fun hp => c hp hq
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem dite_dite_distrib_left {a : p → α} {b : ¬p → q → α} {c : ¬p → ¬q → α} :
    (dite p a fun hp ↦ dite q (b hp) (c hp)) =
      dite q (fun hq ↦ (dite p a) fun hp ↦ b hp hq) fun hq ↦ (dite p a) fun hp ↦ c hp hq := by
  split_ifs <;> rfl
/-
**dite_dite_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_dite_distrib_right {a : p -> q -> α} {b : p -> ¬q -> α} {c : ¬p -> α}
 : dite p (fun hp => dite q (a hp) (b hp)) c = dite q (fun hq => dite p (fun hp 
=> a hp hq) c) fun hq => dite p (fun hp => b hp hq) c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem dite_dite_distrib_right {a : p → q → α} {b : p → ¬q → α} {c : ¬p → α} :
    dite p (fun hp ↦ dite q (a hp) (b hp)) c =
      dite q (fun hq ↦ dite p (fun hp ↦ a hp hq) c) fun hq ↦ dite p (fun hp ↦ b hp hq) c := by
  split_ifs <;> rfl
/-
**ite_dite_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_dite_distrib_left {a : α} {b : q -> α} {c : ¬q -> α} : ite p a (dite q
 b c) = dite q (fun hq => ite p a <| b hq) fun hq => ite p a c hq
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_distrib_left`：dite_dite_distrib_left {a : p -> α} {b : ¬p -> q
 -> α} {c : ¬p -> ¬q -> α} : (dite p a fun hp => dite q (b hp) (c hp)) = dite q 
(fun hq => (…
-/
theorem ite_dite_distrib_left {a : α} {b : q → α} {c : ¬q → α} :
    ite p a (dite q b c) = dite q (fun hq ↦ ite p a <| b hq) fun hq ↦ ite p a <| c hq :=
  dite_dite_distrib_left
/-
**ite_dite_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_dite_distrib_right {a : q -> α} {b : ¬q -> α} {c : α} : ite p (dite q 
a b) c = dite q (fun hq => ite p (a hq) c) fun hq => ite p (b hq) c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_distrib_right`：dite_dite_distrib_right {a : p -> q -> α} {b : 
p -> ¬q -> α} {c : ¬p -> α} : dite p (fun hp => dite q (a hp) (b hp)) c = dite q
 (fun hq => d…
-/
theorem ite_dite_distrib_right {a : q → α} {b : ¬q → α} {c : α} :
    ite p (dite q a b) c = dite q (fun hq ↦ ite p (a hq) c) fun hq ↦ ite p (b hq) c :=
  dite_dite_distrib_right
/-
**dite_ite_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_ite_distrib_left {a : p -> α} {b : ¬p -> α} {c : ¬p -> α} : (dite p a
 fun hp => ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_distrib_left`：dite_dite_distrib_left {a : p -> α} {b : ¬p -> q
 -> α} {c : ¬p -> ¬q -> α} : (dite p a fun hp => dite q (b hp) (c hp)) = dite q 
(fun hq => (…
-/
theorem dite_ite_distrib_left {a : p → α} {b : ¬p → α} {c : ¬p → α} :
    (dite p a fun hp ↦ ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
  dite_dite_distrib_left
/-
**dite_ite_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dite_ite_distrib_right {a : p -> α} {b : p -> α} {c : ¬p -> α} : dite p (f
un hp => ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_distrib_right`：dite_dite_distrib_right {a : p -> q -> α} {b : 
p -> ¬q -> α} {c : ¬p -> α} : dite p (fun hp => dite q (a hp) (b hp)) c = dite q
 (fun hq => d…
-/
theorem dite_ite_distrib_right {a : p → α} {b : p → α} {c : ¬p → α} :
    dite p (fun hp ↦ ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
  dite_dite_distrib_right
/-
**ite_ite_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_distrib_left`：dite_dite_distrib_left {a : p -> α} {b : ¬p -> q
 -> α} {c : ¬p -> ¬q -> α} : (dite p a fun hp => dite q (b hp) (c hp)) = dite q 
(fun hq => (…
-/
theorem ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
  dite_dite_distrib_left
/-
**ite_ite_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_dite_distrib_right`：dite_dite_distrib_right {a : p -> q -> α} {b : 
p -> ¬q -> α} {c : ¬p -> α} : dite p (fun hp => dite q (a hp) (b hp)) c = dite q
 (fun hq => d…
-/
theorem ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
  dite_dite_distrib_right
/-
**Prop.forall** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prop.forall {f : Prop -> Prop} : (forall p, f p) ↔ f True ∧ f False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma Prop.forall {f : Prop → Prop} : (∀ p, f p) ↔ f True ∧ f False :=
  ⟨fun h ↦ ⟨h _, h _⟩, by rintro ⟨h₁, h₀⟩ p; by_cases hp : p <;> simp only [hp] <;> assumption⟩
/-
**Prop.exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prop.exists {f : Prop -> Prop} : (exists p, f p) ↔ f True ∨ f False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma Prop.exists {f : Prop → Prop} : (∃ p, f p) ↔ f True ∨ f False :=
  ⟨fun ⟨p, h⟩ ↦ by refine (em p).imp ?_ ?_ <;> intro H <;> convert! h <;> simp [H],
    by rintro (h | h) <;> exact ⟨_, h⟩⟩
