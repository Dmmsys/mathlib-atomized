/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Defs
public import Mathlib.Order.BoundedOrder.Basic

/-!
# Definition of `0` and `::ₘ`

This file defines constructors for multisets:

* `Zero (Multiset α)` instance: the empty multiset
* `Multiset.cons`: add one element to a multiset
* `Singleton α (Multiset α)` instance: multiset with one element

It also defines the following predicates on multisets:

* `Multiset.Rel`: `Rel r s t` lifts the relation `r` between two elements to a relation between `s`
  and `t`, s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`.

## Notation

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.

## Main results

* `Multiset.rec`: recursion on adding one element to a multiset at a time.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Empty multiset -/


/-- `0 : Multiset α` is the empty set -/
/-
**Multiset.zero** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → Multiset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`0 : Multiset α` is the empty set
-/
protected def zero : Multiset α :=
  @nil α
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection (Multiset α) :=
  ⟨0⟩
/-
**Multiset.inhabitedMultiset** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：inhabitedMultiset : Inhabited (Multiset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedMultiset : Inhabited (Multiset α) :=
  ⟨0⟩
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (Multiset α) where
  default := 0
  uniq := by rintro ⟨_ | ⟨a, l⟩⟩; exacts [rfl, isEmptyElim a]

@[simp]
/-
**Multiset.coe_nil** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_nil : (@nil α : Multiset α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nil : (@nil α : Multiset α) = 0 :=
  rfl

@[simp]
/-
**Multiset.empty_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：empty_eq_zero : (∅ : Multiset α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_eq_zero : (∅ : Multiset α) = 0 :=
  rfl

@[simp]
/-
**Multiset.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = []
参数：l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `List.perm_nil`：∀ {α : Type u_1} {l₁ : List α}, l₁.Perm [] ↔ l₁ = []
-/
theorem coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = [] :=
  Iff.trans coe_eq_coe perm_nil
/-
**Multiset.coe_eq_zero_iff_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_eq_zero_iff_isEmpty (l : List α) : (l : Multiset α) = 0 ↔ l.isEmpty
参数：l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.coe_eq_zero`：coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ 
l = []
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.isEmpty_iff`：∀ {α : Type u_1} {l : List α}, l.isEmpty = true ↔ l = 
[]
-/
theorem coe_eq_zero_iff_isEmpty (l : List α) : (l : Multiset α) = 0 ↔ l.isEmpty :=
  Iff.trans (coe_eq_zero l) isEmpty_iff.symm

/-! ### `Multiset.cons` -/

/-- `cons a s` is the multiset which contains `s` plus one more instance of `a`. -/
/-
**Multiset.cons** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：cons (a : α) (s : Multiset α) : Multiset α
参数：a : α；s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cons a s` is the multiset which contains `s` plus one more instance of `a`.
-/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (a :: l : Multiset α)) fun _ _ p => Quot.sound (p.cons a)

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Insert α (Multiset α) :=
  ⟨cons⟩

@[simp]
/-
**Multiset.insert_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s :=
  rfl

@[simp]
/-
**Multiset.cons_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α)
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α) :=
  rfl

@[simp]
/-
**Multiset.cons_inj_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b
参数：s : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.singleton_perm_singleton`：∀ {α : Type u_1} {a b : α}, [a].Perm [b] 
↔ a = b
· 使用定理 `List.perm_append_right_iff`：∀ {α : Type u_1} {l₁ l₂ : List α} (l : List 
α), (l₁ ++ l).Perm (l₂ ++ l) ↔ l₁.Perm l₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b :=
  ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
      singleton_perm_singleton.1 <| (perm_append_right_iff _).1 this,
    congr_arg (· ::ₘ _)⟩

@[simp]
/-
**Multiset.cons_inj_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_inj_right (a : α) : forall {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s 
= t
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cons_inj_right (a : α) : ∀ {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t := by
  rintro ⟨l₁⟩ ⟨l₂⟩; simp

@[elab_as_elim]
/-
**Multiset.induction** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀ (a : α) (s : Multiset
 α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
参数：∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)；s : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem induction {p : Multiset α → Prop} (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : ∀ s, p s := by
  rintro ⟨l⟩; induction l with | nil => exact empty | cons _ _ ih => exact cons _ _ ih

@[elab_as_elim]
/-
**Multiset.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Multiset α), p 0 → (∀ (a : α
) (s : Multiset α), p s → p (a ::ₘ s)) → p s
参数：s : Multiset α；∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
-/
protected theorem induction_on {p : Multiset α → Prop} (s : Multiset α) (empty : p 0)
    (cons : ∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) : p s :=
  Multiset.induction empty cons s
/-
**Multiset.cons_swap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s
参数：a b : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
  Quot.inductionOn s fun _ => Quotient.sound <| Perm.swap _ _ _

section Rec

variable {C : Multiset α → Sort*}

/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `Multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected
/-
**Multiset.rec** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：rec (C_0 : C 0) (C_cons : forall a m, C m -> C (a ::ₘ m)) (C_cons_heq : fo
rall a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons
 a m b)) (m : Multiset α) : C m
参数：C_0 : C 0；C_cons : forall a m, C m -> C (a ::ₘ m)；C_cons_heq : forall a a' m 
b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)；m : 
Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rec (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b))
    (m : Multiset α) : C m :=
  Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun _ _ h =>
    h.rec_heq
      (fun hl _ ↦ by congr 1; exact Quot.sound hl)
      (C_cons_heq _ _ ⟦_⟧ _)

/-- Companion to `Multiset.rec` with more convenient argument order. -/
@[elab_as_elim]
protected
/-
**Multiset.recOn** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：recOn (m : Multiset α) (C_0 : C 0) (C_cons : forall a m, C m -> C (a ::ₘ m
)) (C_cons_heq : forall a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a
' (a ::ₘ m) (C_cons a m b)) : C m
参数：m : Multiset α；C_0 : C 0；C_cons : forall a m, C m -> C (a ::ₘ m)；C_cons_heq :
 forall a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_c
ons a m b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def recOn (m : Multiset α) (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq :
      ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)) :
    C m :=
  Multiset.rec C_0 C_cons C_cons_heq m

variable {C_0 : C 0} {C_cons : ∀ a m, C m → C (a ::ₘ m)}
  {C_cons_heq :
    ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)}

@[simp]
/-
**Multiset.recOn_0** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：recOn_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recOn_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0 :=
  rfl

@[simp]
/-
**Multiset.recOn_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：recOn_cons (a : α) (m : Multiset α) : (a ::ₘ m).recOn C_0 C_cons C_cons_he
q = C_cons a m (m.recOn C_0 C_cons C_cons_heq)
参数：a : α；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem recOn_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq) :=
  Quotient.inductionOn m fun _ => rfl

end Rec

section Mem

@[simp, grind =]
/-
**Multiset.mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ a = b ∨ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
-/
theorem mem_cons {a b : α} {s : Multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun _ => List.mem_cons
/-
**Multiset.mem_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_cons_of_mem {a b : α} {s : Multiset α} (h : a in s) : a in b ::ₘ s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
-/
theorem mem_cons_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
  mem_cons.2 <| Or.inr h
/-
**Multiset.mem_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_cons_self (a : α) (s : Multiset α) : a in a ::ₘ s
参数：a : α；s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
-/
theorem mem_cons_self (a : α) (s : Multiset α) : a ∈ a ::ₘ s :=
  mem_cons.2 (Or.inl rfl)
/-
**Multiset.forall_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：forall_mem_cons {p : α -> Prop} {a : α} {s : Multiset α} : (forall x in a 
::ₘ s, p x) ↔ p a ∧ forall x in s, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
-/
theorem forall_mem_cons {p : α → Prop} {a : α} {s : Multiset α} :
    (∀ x ∈ a ::ₘ s, p x) ↔ p a ∧ ∀ x ∈ s, p x :=
  Quotient.inductionOn' s fun _ => List.forall_mem_cons
/-
**Multiset.exists_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：exists_cons_of_mem {s : Multiset α} {a : α} : a in s -> exists t, s = a ::
ₘ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.append_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ s t
, l = s ++ a :: t
· 使用定理 `List.perm_middle`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (l₁ ++ a ::
 l₂).Perm (a :: (l₁ ++ l₂))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_cons_of_mem {s : Multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
  Quot.inductionOn s fun l (h : a ∈ l) =>
    let ⟨l₁, l₂, e⟩ := append_of_mem h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp, grind ←]
/-
**Multiset.notMem_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：notMem_zero (a : α) : a ∉ (0 : Multiset α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
-/
theorem notMem_zero (a : α) : a ∉ (0 : Multiset α) :=
  List.not_mem_nil
/-
**Multiset.eq_zero_of_forall_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_zero_of_forall_notMem {s : Multiset α} : (forall x, x ∉ s) -> s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_nil_iff_forall_not_mem`：∀ {α : Type u_1} {l : List α}, l = [] ↔ 
∀ (a : α), a ∉ l
-/
theorem eq_zero_of_forall_notMem {s : Multiset α} : (∀ x, x ∉ s) → s = 0 :=
  Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl
/-
**Multiset.eq_zero_iff_forall_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_zero_iff_forall_notMem {s : Multiset α} : s = 0 ↔ forall a, a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
-/
theorem eq_zero_iff_forall_notMem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => notMem_zero _, eq_zero_of_forall_notMem⟩
/-
**Multiset.exists_mem_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：exists_mem_of_ne_zero {s : Multiset α} : s != 0 -> exists a : α, a in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem exists_mem_of_ne_zero {s : Multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
  Quot.inductionOn s fun l hl =>
    match l, hl with
    | [], h => False.elim <| h rfl
    | a :: l, _ => ⟨a, by simp⟩
/-
**Multiset.empty_or_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：empty_or_exists_mem (s : Multiset α) : s = 0 ∨ exists a, a in s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
-/
theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]
/-
**Multiset.zero_ne_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_ne_cons {a : α} {m : Multiset α} : 0 != a ::ₘ m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
-/
theorem zero_ne_cons {a : α} {m : Multiset α} : 0 ≠ a ::ₘ m := fun h =>
  have : a ∈ (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  notMem_zero _ this

@[simp]
/-
**Multiset.cons_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Multiset.zero_ne_cons`：zero_ne_cons {a : α} {m : Multiset α} : 0 != a ::
ₘ m
-/
theorem cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m ≠ 0 :=
  zero_ne_cons.symm
/-
**Multiset.cons_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_eq_cons {a b : α} {as bs : Multiset α} : a ::ₘ as = b ::ₘ bs ↔ a = b 
∧ as = bs ∨ a != b ∧ exists cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
-/
theorem cons_eq_cons {a b : α} {as bs : Multiset α} :
    a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a ≠ b ∧ ∃ cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs := by
  have : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases h : a = b
    · subst h
      simp_all
    · have : a ∈ b ::ₘ bs := eq ▸ mem_cons_self _ _
      have : a ∈ bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp only [h, hcs, false_and, ne_eq, not_false_eq_true, cons_inj_right, exists_eq_right',
        true_and, false_or]
      have : a ::ₘ as = b ::ₘ a ::ₘ cs := by simp [eq, hcs]
      have : a ::ₘ as = a ::ₘ b ::ₘ cs := by rwa [cons_swap]
      simpa using this
  · intro h
    rcases h with (⟨eq₁, eq₂⟩ | ⟨_, cs, eq₁, eq₂⟩)
    · simp [*]
    · simp [*, cons_swap a b]

end Mem

/-! ### Singleton -/


/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Singleton
-/
instance : Singleton α (Multiset α) :=
  ⟨fun a => a ::ₘ 0⟩
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulSingleton α (Multiset α) :=
  ⟨fun _ => rfl⟩

@[simp]
/-
**Multiset.cons_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_zero (a : α) : a ::ₘ 0 = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_zero (a : α) : a ::ₘ 0 = {a} :=
  rfl

@[simp, norm_cast]
/-
**Multiset.coe_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_singleton (a : α) : ([a] : Multiset α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_singleton (a : α) : ([a] : Multiset α) = {a} :=
  rfl

@[simp]
/-
**Multiset.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_singleton {a b : α} : b in ({a} : Multiset α) ↔ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_singleton {a b : α} : b ∈ ({a} : Multiset α) ↔ b = a := by
  simp only [← cons_zero, mem_cons, iff_self, or_false, notMem_zero]
/-
**Multiset.mem_singleton_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_singleton_self (a : α) : a in ({a} : Multiset α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_zero`：cons_zero (a : α) : a ::ₘ 0 = {a}
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
-/
theorem mem_singleton_self (a : α) : a ∈ ({a} : Multiset α) := by
  rw [← cons_zero]
  exact mem_cons_self _ _

@[simp]
/-
**Multiset.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.cons_inj_left`：cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ
 s = b ::ₘ s ↔ a = b
-/
theorem singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b := by
  simp_rw [← cons_zero]
  exact cons_inj_left _

@[simp, norm_cast]
/-
**Multiset.coe_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_eq_singleton {l : List α} {a : α} : (l : Multiset α) = {a} ↔ l = [a]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_singleton`：coe_singleton (a : α) : ([a] : Multiset α) = {a}
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `List.perm_singleton`：∀ {α : Type u_1} {a : α} {l : List α}, l.Perm [a] ↔
 l = [a]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_singleton {l : List α} {a : α} : (l : Multiset α) = {a} ↔ l = [a] := by
  rw [← coe_singleton, coe_eq_coe, List.perm_singleton]

@[simp]
/-
**Multiset.singleton_eq_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_eq_cons_iff {a b : α} (m : Multiset α) : {a} = b ::ₘ m ↔ a = b ∧
 m = 0
参数：m : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_zero`：cons_zero (a : α) : a ::ₘ 0 = {a}
· 使用定理 `Multiset.cons_eq_cons`：cons_eq_cons {a b : α} {as bs : Multiset α} : a :
:ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a != b ∧ exists cs, as = b ::ₘ cs ∧ bs = a 
::ₘ cs
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_eq_cons_iff {a b : α} (m : Multiset α) : {a} = b ::ₘ m ↔ a = b ∧ m = 0 := by
  rw [← cons_zero, cons_eq_cons]
  simp [eq_comm]
/-
**Multiset.pair_comm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x}
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
-/
theorem pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x} :=
  cons_swap x y 0

/-! ### `Multiset.Subset` -/


section Subset
variable {s : Multiset α} {a : α}

@[simp]
/-
**Multiset.zero_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_subset (s : Multiset α) : 0 subseteq s
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
-/
theorem zero_subset (s : Multiset α) : 0 ⊆ s := fun _ => not_mem_nil.elim
/-
**Multiset.subset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_cons (s : Multiset α) (a : α) : s subseteq a ::ₘ s
参数：s : Multiset α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem subset_cons (s : Multiset α) (a : α) : s ⊆ a ::ₘ s := fun _ => mem_cons_of_mem
/-
**Multiset.ssubset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s
参数：ha : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_cons`：subset_cons (s : Multiset α) (a : α) : s subseteq 
a ::ₘ s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
-/
theorem ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s :=
  ⟨subset_cons _ _, fun h => ha <| h <| mem_cons_self _ _⟩

@[simp]
/-
**Multiset.cons_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_subset {a : α} {s t : Multiset α} : a ::ₘ s subseteq t ↔ a in t ∧ s s
ubseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cons_subset {a : α} {s t : Multiset α} : a ::ₘ s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp [subset_iff, or_imp, forall_and]
/-
**Multiset.cons_subset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_subset_cons {a : α} {s t : Multiset α} : s subseteq t -> a ::ₘ s subs
eteq a ::ₘ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.cons_subset_cons`：∀ {α : Type u_1} {l₁ l₂ : List α} (a : α), l₁ ⊆ l
₂ → a :: l₁ ⊆ a :: l₂
-/
theorem cons_subset_cons {a : α} {s t : Multiset α} : s ⊆ t → a ::ₘ s ⊆ a ::ₘ t :=
  Quotient.inductionOn₂ s t fun _ _ => List.cons_subset_cons _
/-
**Multiset.eq_zero_of_subset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_zero_of_subset_zero {s : Multiset α} (h : s subseteq 0) : s = 0
参数：h : s subseteq 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
-/
theorem eq_zero_of_subset_zero {s : Multiset α} (h : s ⊆ 0) : s = 0 :=
  eq_zero_of_forall_notMem fun _ hx ↦ notMem_zero _ (h hx)
/-
**Multiset.subset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α}, s ⊆ 0 ↔ s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_zero_of_subset_zero`：eq_zero_of_subset_zero {s : Multiset α}
 (h : s subseteq 0) : s = 0
· 使用定理 `Multiset.Subset.refl`：∀ {α : Type u_1} (s : Multiset α), s ⊆ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma subset_zero : s ⊆ 0 ↔ s = 0 :=
  ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩
/-
**Multiset.zero_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α}, 0 ⊂ s ↔ s ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_iff_left_not_left`：right_iff_left_not_left {r s : α -> α -> Prop} 
[IsNonstrictStrictOrder α r s] {a b : α} : s a b ↔ r a b ∧ ¬r b a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma zero_ssubset : 0 ⊂ s ↔ s ≠ 0 := by
  simp [(right_iff_left_not_left : 0 ⊂ s ↔ 0 ⊆ s ∧ ¬s ⊆ 0)]
/-
**Multiset.singleton_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, {a} ⊆ s ↔ a ∈ s
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma singleton_subset : {a} ⊆ s ↔ a ∈ s := by simp [subset_iff]
/-
**Multiset.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：induction_on' {p : Multiset α -> Prop} (S : Multiset α) (h₁ : p 0) (h₂ : f
orall {a s}, a in S -> s subseteq S -> p s -> p (insert a s)) : p S
参数：S : Multiset α；h₁ : p 0；h₂ : forall {a s}, a in S -> s subseteq S -> p s -> p
 (insert a s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.cons_subset`：cons_subset {a : α} {s t : Multiset α} : a ::ₘ s s
ubseteq t ↔ a in t ∧ s subseteq t
· 使用定理 `Multiset.Subset.refl`：∀ {α : Type u_1} (s : Multiset α), s ⊆ s
-/
theorem induction_on' {p : Multiset α → Prop} (S : Multiset α) (h₁ : p 0)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
  @Multiset.induction_on α (fun T => T ⊆ S → p T) S (fun _ => h₁)
    (fun _ _ hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

end Subset

/-! ### Partial order on `Multiset`s -/

section

variable {s t : Multiset α} {a : α}

/-
**Multiset.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_le (s : Multiset α) : 0 <= s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.nil_sublist`：∀ {α : Type u_1} (l : List α), [].Sublist l
-/
theorem zero_le (s : Multiset α) : 0 ≤ s :=
  Quot.inductionOn s fun l => (nil_sublist l).subperm
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Multiset α) where
  bot := 0
  bot_le := zero_le

/-- This is a `rfl` and `simp` version of `bot_eq_zero`. -/
@[simp]
/-
**Multiset.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bot_eq_zero : (⊥ : Multiset α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a `rfl` and `simp` version of `bot_eq_zero`.
-/
theorem bot_eq_zero : (⊥ : Multiset α) = 0 :=
  rfl
/-
**Multiset.le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_zero : s <= 0 ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem le_zero : s ≤ 0 ↔ s = 0 :=
  le_bot_iff
/-
**Multiset.lt_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s
参数：s : Multiset α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.sublist_cons_self`：∀ {α : Type u_1} (a : α) (l : List α), l.Sublist
 (a :: l)
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s :=
  Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons_self _ _).subperm,
      fun p => _root_.ne_of_lt (lt_succ_self (length l)) p.length_eq⟩
/-
**Multiset.le_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_cons_self (s : Multiset α) (a : α) : s <= a ::ₘ s
参数：s : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
-/
theorem le_cons_self (s : Multiset α) (a : α) : s ≤ a ::ₘ s :=
  le_of_lt <| lt_cons_self _ _
/-
**Multiset.cons_le_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s t : Multiset α} (a : α), a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.subperm_cons`：∀ {α : Type u_1} (a : α) {l₁ l₂ : List α}, (a :: l₁).
Subperm (a :: l₂) ↔ l₁.Subperm l₂
-/
@[simp] theorem cons_le_cons_iff (a : α) : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t fun _ _ => subperm_cons a
/-
**Multiset.cons_le_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ t
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
-/
theorem cons_le_cons (a : α) : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
  (cons_le_cons_iff a).2
/-
**Multiset.cons_lt_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s t : Multiset α} {a : α}, a ::ₘ s < a ::ₘ t ↔ s < t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
-/
@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)
/-
**Multiset.cons_lt_cons** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t
参数：a : α；h : s < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.cons_lt_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} {a : α}, 
a ::ₘ s < a ::ₘ t ↔ s < t
-/
lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h
/-
**Multiset.le_cons_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_cons_of_notMem (m : a ∉ s) : s <= a ::ₘ t ↔ s <= t
参数：m : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.append_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ s t
, l = s ++ a :: t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.subperm_left`：∀ {α : Type u_1} {l l₁ l₂ : List α}, l₁.Perm l₂ 
→ (l.Subperm l₁ ↔ l.Subperm l₂)
· 使用定理 `List.perm_middle`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (l₁ ++ a ::
 l₂).Perm (a :: (l₁ ++ l₂))
· 使用定理 `List.subperm_cons`：∀ {α : Type u_1} (a : α) {l₁ l₂ : List α}, (a :: l₁).
Subperm (a :: l₂) ↔ l₁.Subperm l₂
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `List.sublist_or_mem_of_sublist`：∀ {α : Type u_1} {l l₁ : List α} {a : α}
 {l₂ : List α}, l.Sublist (l₁ ++ a :: l₂) → l.Sublist (l₁ ++ l₂) ∨ a ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.le_cons_self`：le_cons_self (s : Multiset α) (a : α) : s <= a ::
ₘ s
-/
theorem le_cons_of_notMem (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t := by
  refine ⟨?_, fun h => le_trans h <| le_cons_self _ _⟩
  suffices ∀ {t'}, s ≤ t' → a ∈ t' → a ::ₘ s ≤ t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine leInductionOn h ?_
  introv s m₁ m₂
  rcases append_of_mem m₂ with ⟨r₁, r₂, rfl⟩
  exact
    perm_middle.subperm_left.2
      ((subperm_cons _).2 <| ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)
/-
**Multiset.cons_le_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_le_of_notMem (hs : a ∉ s) : a ::ₘ s <= t ↔ a in t ∧ s <= t
参数：hs : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.le_cons_self`：le_cons_self (s : Multiset α) (a : α) : s <= a ::
ₘ s
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Multiset.cons_le_cons`：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ
 t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_cons_of_notMem`：le_cons_of_notMem (m : a ∉ s) : s <= a ::ₘ t
 ↔ s <= t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_le_of_notMem (hs : a ∉ s) : a ::ₘ s ≤ t ↔ a ∈ t ∧ s ≤ t := by
  apply Iff.intro (fun h ↦ ⟨subset_of_le h (mem_cons_self a s), le_trans (le_cons_self s a) h⟩)
  rintro ⟨h₁, h₂⟩; rcases exists_cons_of_mem h₁ with ⟨_, rfl⟩
  exact cons_le_cons _ ((le_cons_of_notMem hs).mp h₂)

@[simp]
/-
**Multiset.singleton_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_ne_zero (a : α) : ({a} : Multiset α) != 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
-/
theorem singleton_ne_zero (a : α) : ({a} : Multiset α) ≠ 0 :=
  ne_of_gt (lt_cons_self _ _)

@[simp]
/-
**Multiset.zero_ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (a : α), 0 ≠ {a}
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Multiset.singleton_ne_zero`：singleton_ne_zero (a : α) : ({a} : Multiset 
α) != 0
-/
theorem zero_ne_singleton (a : α) : 0 ≠ ({a} : Multiset α) := singleton_ne_zero _ |>.symm

@[simp]
/-
**Multiset.singleton_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_le {a : α} {s : Multiset α} : {a} <= s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Mu
ltiset α)
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Multiset.cons_le_cons`：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ
 t
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem singleton_le {a : α} {s : Multiset α} : {a} ≤ s ↔ a ∈ s :=
  ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨_t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩
/-
**Multiset.le_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, s ≤ {a} ↔ s = 0 ∨ s = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma le_singleton : s ≤ {a} ↔ s = 0 ∨ s = {a} :=
  Quot.induction_on s fun l ↦ by simp only [← coe_singleton, quot_mk_to_coe'', coe_le,
    coe_eq_zero, coe_eq_coe, perm_singleton, subperm_singleton_iff]
/-
**Multiset.lt_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, s < {a} ↔ s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Multiset.singleton_ne_zero`：singleton_ne_zero (a : α) : ({a} : Multiset 
α) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma lt_singleton : s < {a} ↔ s = 0 := by
  simp only [lt_iff_le_and_ne, le_singleton, or_and_right, Ne, and_not_self, or_false,
    and_iff_left_iff_imp]
  rintro rfl
  exact (singleton_ne_zero _).symm
/-
**Multiset.ssubset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, s ⊂ {a} ↔ s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_zero_of_subset_zero`：eq_zero_of_subset_zero {s : Multiset α}
 (h : s subseteq 0) : s = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.singleton_subset`：∀ {α : Type u_1} {s : Multiset α} {a : α}, {a
} ⊆ s ↔ a ∈ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma ssubset_singleton_iff : s ⊂ {a} ↔ s = 0 := by
  refine ⟨fun hs ↦ eq_zero_of_subset_zero fun b hb ↦ (hs.2 ?_).elim, ?_⟩
  · obtain rfl := mem_singleton.1 (hs.1 hb)
    rwa [singleton_subset]
  · rintro rfl
    simp

end

/-! ### Cardinality -/

@[simp]
/-
**Multiset.card_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_zero : @card α 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Cardinality
-/
theorem card_zero : @card α 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.card_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
theorem card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1 :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/-
**Multiset.card_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_singleton (a : α) : card ({a} : Multiset α) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_singleton (a : α) : card ({a} : Multiset α) = 1 := by
  simp only [← cons_zero, card_zero, card_cons]
/-
**Multiset.card_pair** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_pair (a b : α) : card {a, b} = 2
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.insert_eq_cons`：insert_eq_cons (a : α) (s : Multiset α) : inser
t a s = a ::ₘ s
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
-/
theorem card_pair (a b : α) : card {a, b} = 2 := by
  rw [insert_eq_cons, card_cons, card_singleton]
/-
**Multiset.card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_one {s : Multiset α} : card s = 1 ↔ exists a, s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_one_iff`：∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ 
a, l = [a]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_eq_one {s : Multiset α} : card s = 1 ↔ ∃ a, s = {a} :=
  ⟨Quot.inductionOn s fun _l h => (List.length_eq_one_iff.1 h).imp fun _a => congr_arg _,
    fun ⟨_a, e⟩ => e.symm ▸ rfl⟩
/-
**Multiset.lt_iff_cons_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lt_iff_cons_le {s t : Multiset α} : s < t ↔ exists a, a ::ₘ s <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.Subperm.exists_of_length_lt`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.
Subperm l₂ → l₁.length < l₂.length → ∃ a, (a :: l₁).Subperm l₂
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Multiset.card_lt_card`：card_lt_card {s t : Multiset α} (h : s < t) : car
d s < card t
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
-/
theorem lt_iff_cons_le {s t : Multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
  ⟨Quotient.inductionOn₂ s t fun _l₁ _l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_card h),
    fun ⟨_a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp]
/-
**Multiset.card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0 :=
  ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩
/-
**Multiset.card_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_pos {s : Multiset α} : 0 < card s ↔ s != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
-/
theorem card_pos {s : Multiset α} : 0 < card s ↔ s ≠ 0 :=
  Nat.pos_iff_ne_zero.trans <| not_congr card_eq_zero
/-
**Multiset.card_pos_iff_exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ exists a, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_pos_iff_exists_mem`：∀ {α : Type u_1} {l : List α}, 0 < l.len
gth ↔ ∃ a, a ∈ l
-/
theorem card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
  Quot.inductionOn s fun _l => length_pos_iff_exists_mem
/-
**Multiset.card_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_two {s : Multiset α} : card s = 2 ↔ exists x y, s = {x, y}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_two`：length_eq_two {l : List α} : l.length = 2 ↔ exists a
 b, l = [a, b]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_eq_two {s : Multiset α} : card s = 2 ↔ ∃ x y, s = {x, y} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_two.mp h).imp fun _a => Exists.imp fun _b => congr_arg _,
    fun ⟨_a, _b, e⟩ => e.symm ▸ rfl⟩
/-
**Multiset.card_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_three {s : Multiset α} : card s = 3 ↔ exists x y z, s = {x, y, z}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_three`：length_eq_three {l : List α} : l.length = 3 ↔ exis
ts a b c, l = [a, b, c]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_eq_three {s : Multiset α} : card s = 3 ↔ ∃ x y z, s = {x, y, z} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_three.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => congr_arg _,
    fun ⟨_a, _b, _c, e⟩ => e.symm ▸ rfl⟩
/-
**Multiset.card_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_four {s : Multiset α} : card s = 4 ↔ exists x y z w, s = {x, y, z,
 w}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_four`：length_eq_four {l : List α} : l.length = 4 ↔ exists
 a b c d, l = [a, b, c, d]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_eq_four {s : Multiset α} : card s = 4 ↔ ∃ x y z w, s = {x, y, z, w} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_four.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => Exists.imp fun _d => congr_arg _,
    fun ⟨_a, _b, _c, _d, e⟩ => e.symm ▸ rfl⟩
/-
**Multiset.card_eq_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_succ_iff {s : Multiset α} {n : Nat} : card s = n + 1 ↔ exists a t,
 a ::ₘ t = s ∧ card t = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_succ_iff {s : Multiset α} {n : ℕ} :
    card s = n + 1 ↔ ∃ a t, a ::ₘ t = s ∧ card t = n := by
  refine ⟨?_, by aesop⟩
  induction s using Multiset.induction generalizing n with aesop

/-! ### Map for partial functions -/

@[simp]
/-
**Multiset.pmap_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pmap_zero {p : α -> Prop} (f : forall a, p a -> β) (h : forall a in (0 : M
ultiset α), p a) : pmap f 0 h = 0
参数：f : forall a, p a -> β；h : forall a in (0 : Multiset α), p a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Map for partial functions
-/
theorem pmap_zero {p : α → Prop} (f : ∀ a, p a → β) (h : ∀ a ∈ (0 : Multiset α), p a) :
    pmap f 0 h = 0 :=
  rfl

@[simp]
/-
**Multiset.pmap_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pmap_cons {p : α -> Prop} (f : forall a, p a -> β) (a : α) (m : Multiset α
) : forall h : forall b in a ::ₘ m, p b, pmap f (a ::ₘ m) h = f a (h a (mem_cons
_self a m)) ::ₘ pmap f m fun a ha => h a mem_cons_of_mem ha
参数：f : forall a, p a -> β；a : α；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem pmap_cons {p : α → Prop} (f : ∀ a, p a → β) (a : α) (m : Multiset α) :
    ∀ h : ∀ b ∈ a ::ₘ m, p b,
      pmap f (a ::ₘ m) h =
        f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun a ha => h a <| mem_cons_of_mem ha :=
  Quotient.inductionOn m fun _l _h => rfl

@[simp]
/-
**Multiset.attach_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：attach_zero : (0 : Multiset α).attach = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem attach_zero : (0 : Multiset α).attach = 0 :=
  rfl

/-! ### Lift a relation to `Multiset`s -/

section Rel

/-- `Rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`. -/
@[mk_iff]
/-
**Multiset.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `Multiset`。
形式化陈述：Rel (r : α -> β -> Prop) : Multiset α -> Multiset β -> Prop | zero : Rel r
 0 0 | cons {a b as bs} : r a b -> Rel r as bs -> Rel r (a ::ₘ as) (b ::ₘ bs)  v
ariable {δ : Type*} {r : α -> β -> Prop} {p : γ -> δ -> Prop}  private theorem r
el_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s
参数：r : α -> β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Rel r s t` -- lift the relation `r` between two elements to a relation between 
`s` and `t`,
s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`
.
-/
inductive Rel (r : α → β → Prop) : Multiset α → Multiset β → Prop
  | zero : Rel r 0 0
  | cons {a b as bs} : r a b → Rel r as bs → Rel r (a ::ₘ as) (b ::ₘ bs)

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}
/-
**Multiset.rel_flip_aux** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem rel_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s :=
  Rel.recOn h Rel.zero fun h₀ _h₁ ih => Rel.cons h₀ ih
/-
**Multiset.rel_flip** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.Multiset.ZeroCons.0.Multiset.rel_flip_aux`：∀ {α : 
Type u_1} {β : Type v} {r : α → β → Prop} {s : Multiset α} {t : Multiset β},   M
ultiset.Rel r s t → Multiset.Rel (flip r) t s
-/
theorem rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s :=
  ⟨rel_flip_aux, rel_flip_aux⟩
/-
**Multiset.rel_refl_of_refl_on** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_refl_of_refl_on {m : Multiset α} {r : α -> α -> Prop} : (forall x in m
, r x x) -> Rel r m m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem rel_refl_of_refl_on {m : Multiset α} {r : α → α → Prop} : (∀ x ∈ m, r x x) → Rel r m m := by
  refine m.induction_on ?_ ?_
  · intros
    apply Rel.zero
  · intro a m ih h
    exact Rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))
/-
**Multiset.rel_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_eq_refl {s : Multiset α} : Rel (· = ·) s s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.rel_refl_of_refl_on`：rel_refl_of_refl_on {m : Multiset α} {r : 
α -> α -> Prop} : (forall x in m, r x x) -> Rel r m m
-/
theorem rel_eq_refl {s : Multiset α} : Rel (· = ·) s s :=
  rel_refl_of_refl_on fun _x _hx => rfl
/-
**Multiset.rel_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.rel_eq_refl`：rel_eq_refl {s : Multiset α} : Rel (· = ·) s s
-/
theorem rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t := by
  constructor
  · intro h
    induction h <;> simp [*]
  · rintro rfl
    exact rel_eq_refl
/-
**Multiset.Rel.mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Rel`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {r p : α → β → Prop} {s : Multiset α} {t : M
ultiset β},   Multiset.Rel r s t → (∀ a ∈ s, ∀ b ∈ t, r a b → p a b) → Multiset.
Rel p s t
参数：∀ a ∈ s, ∀ b ∈ t, r a b → p a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem Rel.mono {r p : α → β → Prop} {s t} (hst : Rel r s t)
    (h : ∀ a ∈ s, ∀ b ∈ t, r a b → p a b) : Rel p s t := by
  induction hst with
  | zero => exact Rel.zero
  | @cons a b s t hab _hst ih =>
    apply Rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'
/-
**Multiset.rel_flip_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.rel_flip`：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
· 使用定理 `Multiset.rel_eq`：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t :=
  show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]

@[simp]
/-
**Multiset.rel_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.rel_iff`：∀ {α : Type u_1} {β : Type v} (r : α → β → Prop) (a : 
Multiset α) (a_1 : Multiset β),   Multiset.Rel r a a_1 ↔     a = 0 ∧ a_1 = 0 ∨ ∃
 a_2 b…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0 := by rw [rel_iff]; simp

@[simp]
/-
**Multiset.rel_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.rel_iff`：∀ {α : Type u_1} {β : Type v} (r : α → β → Prop) (a : 
Multiset α) (a_1 : Multiset β),   Multiset.Rel r a a_1 ↔     a = 0 ∧ a_1 = 0 ∨ ∃
 a_2 b…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0 := by rw [rel_iff]; simp
/-
**Multiset.rel_cons_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_cons_left {a as bs} : Rel r (a ::ₘ as) bs ↔ exists b bs', r a b ∧ Rel 
r as bs' ∧ bs = b ::ₘ bs'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.cons_eq_cons`：cons_eq_cons {a b : α} {as bs : Multiset α} : a :
:ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a != b ∧ exists cs, as = b ::ₘ cs ∧ bs = a 
::ₘ cs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
-/
theorem rel_cons_left {a as bs} :
    Rel r (a ::ₘ as) bs ↔ ∃ b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs' := by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as with
    | zero => simp at hm
    | @cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨rfl, rfl⟩ | ⟨_h, cs, eq₁, eq₂⟩)
      · exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ Rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩
  · exact fun ⟨b, bs', hab, h, Eq⟩ => Eq.symm ▸ Rel.cons hab h
/-
**Multiset.rel_cons_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_cons_right {as b bs} : Rel r as (b ::ₘ bs) ↔ exists a as', r a b ∧ Rel
 r as' bs ∧ as = a ::ₘ as'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_flip`：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
· 使用定理 `Multiset.rel_cons_left`：rel_cons_left {a as bs} : Rel r (a ::ₘ as) bs ↔ 
exists b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs'
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `flip.eq_1`：∀ {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) (b :
 β) (a : α), flip f b a = f a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_cons_right {as b bs} :
    Rel r as (b ::ₘ bs) ↔ ∃ a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as' := by
  rw [← rel_flip, rel_cons_left]
  refine exists₂_congr fun a as' => ?_
  rw [rel_flip, flip]
/-
**Multiset.card_eq_card_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_card_of_rel {r : α -> β -> Prop} {s : Multiset α} {t : Multiset β}
 (h : Rel r s t) : card s = card t
参数：h : Rel r s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem card_eq_card_of_rel {r : α → β → Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) :
    card s = card t := by induction h <;> simp [*]
/-
**Multiset.exists_mem_of_rel_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：exists_mem_of_rel_of_mem {r : α -> β -> Prop} {s : Multiset α} {t : Multis
et β} (h : Rel r s t) : forall {a : α}, a in s -> exists b in t, r a b
参数：h : Rel r s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem exists_mem_of_rel_of_mem {r : α → β → Prop} {s : Multiset α} {t : Multiset β}
    (h : Rel r s t) : ∀ {a : α}, a ∈ s → ∃ b ∈ t, r a b := by
  induction h with
  | zero => simp
  | @cons x y s t hxy _ ih =>
    intro a ha
    rcases mem_cons.1 ha with ha | ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩
/-
**Multiset.rel_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_of_forall {m1 m2 : Multiset α} {r : α -> α -> Prop} (h : forall a b, a
 in m1 -> b in m2 -> r a b) (hc : card m1 = card m2) : m1.Rel r m2
参数：h : forall a b, a in m1 -> b in m2 -> r a b；hc : card m1 = card m2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.rel_zero_right`：rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Multiset.card_zero`：card_zero : @card α 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_pos_iff_exists_mem`：card_pos_iff_exists_mem {s : Multiset 
α} : 0 < card s ↔ exists a, a in s
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.rel_cons_right`：rel_cons_right {as b bs} : Rel r as (b ::ₘ bs) 
↔ exists a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as'
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem rel_of_forall {m1 m2 : Multiset α} {r : α → α → Prop} (h : ∀ a b, a ∈ m1 → b ∈ m2 → r a b)
    (hc : card m1 = card m2) : m1.Rel r m2 := by
  revert m1
  refine @(m2.induction_on ?_ ?_)
  · intro m _h hc
    rw [rel_zero_right, ← card_eq_zero, hc, card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb
    refine rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih ?_ ?_, rfl⟩
    · exact fun _ _ ha hb => h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb)
    · simpa using hc

protected nonrec
/-
**Multiset.Rel.trans** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Rel`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α},   
Multiset.Rel r s t → Multiset.Rel r t u → Multiset.Rel r s u
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.rel_zero_right`：rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a
 = 0
· 使用定理 `Multiset.rel_zero_left`：rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b =
 0
· 使用定理 `Multiset.rel_cons_right`：rel_cons_right {as b bs} : Rel r as (b ::ₘ bs) 
↔ exists a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as'
· 使用定理 `Multiset.rel_cons_left`：rel_cons_left {a as bs} : Rel r (a ::ₘ as) bs ↔ 
exists b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs'
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Rel.trans (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
    (r2 : Rel r t u) : Rel r s u := by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  | cons x t ih =>
    obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.cons (_root_.trans ha1 hb1) (ih ha2 hb2)

end Rel

@[simp]
/-
**Multiset.pairwise_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pairwise_zero (r : α -> α -> Prop) : Multiset.Pairwise r 0
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pairwise_zero (r : α → α → Prop) : Multiset.Pairwise r 0 :=
  ⟨[], rfl, List.Pairwise.nil⟩

section Nodup

variable {s : Multiset α} {a : α}

@[simp]
/-
**Multiset.nodup_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_zero : @Nodup α 0
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodup_zero : @Nodup α 0 :=
  Pairwise.nil

@[simp]
/-
**Multiset.nodup_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
-/
theorem nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_cons
/-
**Multiset.Nodup.cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, a ∉ s → s.Nodup → (a ::ₘ s).Nod
up
参数：a ::ₘ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
-/
theorem Nodup.cons (m : a ∉ s) (n : Nodup s) : Nodup (a ::ₘ s) :=
  nodup_cons.2 ⟨m, n⟩
/-
**Multiset.Nodup.of_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, (a ::ₘ s).Nodup → s.Nodup
参数：a ::ₘ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
-/
theorem Nodup.of_cons (h : Nodup (a ::ₘ s)) : Nodup s :=
  (nodup_cons.1 h).2
/-
**Multiset.Nodup.notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {a : α}, (a ::ₘ s).Nodup → a ∉ s
参数：a ::ₘ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
-/
theorem Nodup.notMem (h : Nodup (a ::ₘ s)) : a ∉ s :=
  (nodup_cons.1 h).1

end Nodup

end Multiset

