/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/
module

public import Mathlib.Data.List.Lex
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.NormNum

/-!
# Shortlex ordering of lists.

Given a relation `r` on `α`, the shortlex order on `List α` is defined by `L < M` iff
* `L.length < M.length`
* `L.length = M.length` and `L < M` under the lexicographic ordering over `r` on lists

## Main results

We show that if `r` is well-founded, so too is the shortlex order over `r`

## See also

Related files are:
* `Mathlib/Data/List/Lex.lean`: Lexicographic order on `List α`.
* `Mathlib/Data/DFinsupp/WellFounded.lean`: Well-foundedness of lexicographic orders on `DFinsupp`
  and `Pi`.
-/

@[expose] public section

/-! ### shortlex ordering -/

namespace List

/-- Given a relation `r` on `α`, the shortlex order on `List α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `n < k` or `n = k` and `[a0, ..., an] < [b0, ..., bk]`
under the lexicographic order induced by `r`. -/
/-
**List.Shortlex** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：Shortlex {α : Type*} (r : α -> α -> Prop) : List α -> List α -> Prop
参数：r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relation `r` on `α`, the shortlex order on `List α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `n < k` or `n = k` and `[a0, ..., an] < [b0,
 ..., bk]`
under the lexicographic order induced by `r`.
-/
def Shortlex {α : Type*} (r : α → α → Prop) : List α → List α → Prop :=
  InvImage (Prod.Lex (· < ·) (List.Lex r)) fun a ↦ (a.length, a)

variable {α : Type*} {r : α → α → Prop}

/-- If a list `s` is shorter than a list `t`, then `s` is smaller than `t` under any shortlex
order. -/
/-
**List.Shortlex.of_length_lt** 是 Mathlib 中的一个定理，位于命名空间 `List.Shortlex`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : List α}, s.length < t.length → 
List.Shortlex r s t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a list `s` is shorter than a list `t`, then `s` is smaller than `t` under any
 shortlex
order.
-/
theorem Shortlex.of_length_lt {s t : List α} (h : s.length < t.length) : Shortlex r s t :=
  Prod.Lex.left _ _ h

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r`  when `s` is smaller than `t` under the lexicographic order over `r` -/
/-
**List.Shortlex.of_lex** 是 Mathlib 中的一个定理，位于命名空间 `List.Shortlex`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s t : List α}, s.length = t.length → 
List.Lex r s t → List.Shortlex r s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2

--- 原说明 ---
If two lists `s` and `t` have the same length, `s` is smaller than `t` under the
 shortlex order
over a relation `r`  when `s` is smaller than `t` under the lexicographic order 
over `r`
-/
theorem Shortlex.of_lex {s t : List α} (len_eq : s.length = t.length) (h_lex : List.Lex r s t) :
    Shortlex r s t := by
  apply Prod.lex_def.mpr
  right
  exact ⟨len_eq, h_lex⟩
/-
**List.shortlex_def** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：shortlex_def {s t : List α} : Shortlex r s t ↔ s.length < t.length ∨ s.len
gth = t.length ∧ Lex r s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2
-/
theorem shortlex_def {s t : List α} :
    Shortlex r s t ↔ s.length < t.length ∨ s.length = t.length ∧ Lex r s t := Prod.lex_def

/-- If two lists `s` and `t` have the same length, `s` is smaller than `t` under the shortlex order
over a relation `r` exactly when `s` is smaller than `t` under the lexicographic order over `r`. -/
/-
**List.shortlex_iff_lex** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：shortlex_iff_lex {s t : List α} (h : s.length = t.length) : Shortlex r s t
 ↔ List.Lex r s t
参数：h : s.length = t.length。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If two lists `s` and `t` have the same length, `s` is smaller than `t` under the
 shortlex order
over a relation `r` exactly when `s` is smaller than `t` under the lexicographic
 order over `r`.
-/
theorem shortlex_iff_lex {s t : List α} (h : s.length = t.length) :
    Shortlex r s t ↔ List.Lex r s t := by
  simp [shortlex_def, h]
/-
**List.shortlex_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：shortlex_cons_iff [Std.Irrefl r] {a : α} {s t : List α} : Shortlex r (a ::
 s) (a :: t) ↔ Shortlex r s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem shortlex_cons_iff [Std.Irrefl r] {a : α} {s t : List α} :
    Shortlex r (a :: s) (a :: t) ↔ Shortlex r s t := by
  simp only [shortlex_def, length_cons, add_lt_add_iff_right, add_left_inj, List.lex_cons_iff]

alias ⟨Shortlex.of_cons, Shortlex.cons⟩ := shortlex_cons_iff

@[simp]
/-
**List.not_shortlex_nil_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_shortlex_nil_right {s : List α} : ¬ Shortlex r s []
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_shortlex_nil_right {s : List α} : ¬ Shortlex r s [] := by
  simp [shortlex_def]
/-
**List.shortlex_nil_or_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (s : List α), List.Shortlex r [] s ∨ s
 = []
参数：s : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Shortlex.of_length_lt`：∀ {α : Type u_1} {r : α → α → Prop} {s t : L
ist α}, s.length < t.length → List.Shortlex r s t
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem shortlex_nil_or_eq_nil : ∀ s : List α, Shortlex r [] s ∨ s = []
  | [] => .inr rfl
  | _ :: tail => .inl <| .of_length_lt tail.length.succ_pos

@[simp]
/-
**List.shortlex_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：shortlex_singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b
参数：a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem shortlex_singleton_iff (a b : α) : Shortlex r [a] [b] ↔ r a b := by
  simp only [shortlex_def, length_singleton, lt_self_iff_false, lex_singleton_iff, true_and,
    false_or]

namespace Shortlex

/-
**List.Shortlex.trichotomous** 是 Mathlib 中的一个实例，位于命名空间 `List.Shortlex`。
形式化陈述：trichotomous [Std.Trichotomous r] : Std.Trichotomous (Shortlex r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
· 使用定理 `InvImage.trichotomous`：InvImage.trichotomous [Std.Trichotomous r] {f : β
 -> α} (h : Function.Injective f) : Std.Trichotomous (InvImage r f)
· 使用定理 `Nat.instTrichotomousLt`：Std.Trichotomous fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance trichotomous [Std.Trichotomous r] : Std.Trichotomous (Shortlex r) :=
  ⟨(InvImage.trichotomous (by simp [Function.Injective])).trichotomous⟩
/-
**List.Shortlex.asymm** 是 Mathlib 中的一个实例，位于命名空间 `List.Shortlex`。
形式化陈述：asymm [Std.Asymm r] : Std.Asymm (Shortlex r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance asymm [Std.Asymm r] : Std.Asymm (Shortlex r) :=
  inferInstanceAs <| Std.Asymm (InvImage _ _)
/-
**List.Shortlex.append_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Shortlex`。
形式化陈述：append_right {s₁ s₂ : List α} (t : List α) (h : Shortlex r s₁ s₂) : Shortl
ex r s₁ (s₂ ++ t)
参数：t : List α；h : Shortlex r s₁ s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.shortlex_def`：shortlex_def {s t : List α} : Shortlex r s t ↔ s.leng
th < t.length ∨ s.length = t.length ∧ Lex r s t
· 使用定理 `List.Shortlex.of_length_lt`：∀ {α : Type u_1} {r : α → α → Prop} {s t : L
ist α}, s.length < t.length → List.Shortlex r s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
-/
theorem append_right {s₁ s₂ : List α} (t : List α) (h : Shortlex r s₁ s₂) :
    Shortlex r s₁ (s₂ ++ t) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append]
    lia
  cases t with
  | nil =>
    rw [List.append_nil]
    exact h
  | cons head tail =>
    apply of_length_lt
    rw [List.length_append, List.length_cons]
    lia
/-
**List.Shortlex.append_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Shortlex`。
形式化陈述：append_left {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α) : Shortle
x r (s ++ t₁) (s ++ t₂)
参数：h : Shortlex r t₁ t₂；s : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.shortlex_def`：shortlex_def {s t : List α} : Shortlex r s t ↔ s.leng
th < t.length ∨ s.length = t.length ∧ Lex r s t
· 使用定理 `List.Shortlex.of_length_lt`：∀ {α : Type u_1} {r : α → α → Prop} {s t : L
ist α}, s.length < t.length → List.Shortlex r s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Shortlex.of_lex`：∀ {α : Type u_1} {r : α → α → Prop} {s t : List α}
, s.length = t.length → List.Lex r s t → List.Shortlex r s t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.Lex.append_left`：∀ {α : Type u} (R : α → α → Prop) {t₁ t₂ : List α}
, List.Lex R t₁ t₂ → ∀ (s : List α), List.Lex R (s ++ t₁) (s ++ t₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem append_left {t₁ t₂ : List α} (h : Shortlex r t₁ t₂) (s : List α) :
    Shortlex r (s ++ t₁) (s ++ t₂) := by
  rcases shortlex_def.mp h with h1 | h2
  · apply of_length_lt
    rw [List.length_append, List.length_append]
    lia
  cases s with
  | nil =>
    rw [List.nil_append, List.nil_append]
    exact h
  | cons head tail =>
    apply of_lex
    · simp only [List.cons_append, List.length_cons, List.length_append,
      add_left_inj, add_right_inj]
      exact h2.1
    exact List.Lex.append_left r h2.2 (head :: tail)

section WellFounded

variable {h : WellFounded r}

/-
**List.Shortlex._root_.Acc.shortlex** 是 Mathlib 中的一个定理，位于命名空间 `List.Shortlex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem _root_.Acc.shortlex {a : α} {b : List α} (aca : Acc r a)
    (acb : Acc (Shortlex r) b)
    (ih : ∀ s : List α, s.length < (a :: b).length → Acc (Shortlex r) s) :
    Acc (Shortlex r) (a :: b) := by
  induction aca generalizing b with
  | intro xa _ iha =>
    induction acb with
    | intro xb _ ihb =>
      refine Acc.intro (xa :: xb) fun p lt => ?_
      rcases shortlex_def.mp lt with h1 | ⟨h2len, h2lex⟩
      · exact ih _ h1
      · cases h2lex with
        | nil => simp at h2len
        | @cons x xs _ h =>
          simp only [length_cons, add_left_inj] at h2len
          refine ihb _ (of_lex h2len h) fun l hl => ?_
          apply ih
          rw [List.length_cons, ← h2len]
          exact hl
        | @rel x xs _ _ h =>
          simp only [List.length_cons, add_left_inj] at h2len
          refine iha _ h (ih xs (by rw [h2len]; simp)) fun l hl => ?_
          apply ih
          rw [List.length_cons, ← h2len]
          exact hl
/-
**List.Shortlex.wf** 是 Mathlib 中的一个定理，位于命名空间 `List.Shortlex`。
形式化陈述：wf (h : WellFounded r) : WellFounded (Shortlex r)
参数：h : WellFounded r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `List.not_shortlex_nil_right`：not_shortlex_nil_right {s : List α} : ¬ Sho
rtlex r s []
· 使用定理 `List.exists_of_length_succ`：∀ {α : Type u} {n : ℕ} (l : List α), l.lengt
h = n + 1 → ∃ h t, l = h :: t
· 使用定理 `_private.Mathlib.Data.List.Shortlex.0.Acc.shortlex`：∀ {α : Type u_1} {r 
: α → α → Prop} {a : α} {b : List α},   Acc r a →     Acc (List.Shortlex r) b → 
      (∀ (s : List α), s.length < (a :: …
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
-/
theorem wf (h : WellFounded r) : WellFounded (Shortlex r) := .intro fun a => by
  induction len_a : a.length using Nat.caseStrongRecOn generalizing a with
  | zero =>
    rw [List.length_eq_zero_iff] at len_a
    rw [len_a]
    exact Acc.intro _ <| fun _ ylt => (not_shortlex_nil_right ylt).elim
  | ind n ih =>
    obtain ⟨head, tail, rfl⟩ := List.exists_of_length_succ a len_a
    rw [List.length_cons, add_left_inj] at len_a
    apply Acc.shortlex (WellFounded.apply h head) (ih n le_rfl tail len_a)
    intro l ll
    apply ih l.length _ _ rfl
    rw [← len_a]
    exact Nat.le_of_lt_succ ll

end WellFounded

end Shortlex

end List

