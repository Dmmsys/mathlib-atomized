/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.List.Sym

/-! # Unordered tuples of elements of a multiset

Defines `Multiset.sym` and the specialized `Multiset.sym2` for computing multisets of all
unordered n-tuples from a given multiset. These are multiset versions of `Nat.multichoose`.

## Main declarations

* `Multiset.sym2`: `xs.sym2` is the multiset of all unordered pairs of elements from `xs`,
  with multiplicity. The multiset's values are in `Sym2 α`.

## TODO

* Once `List.Perm.sym` is defined, define
  ```lean
  protected def sym (n : Nat) (m : Multiset α) : Multiset (Sym α n) :=
    m.liftOn (fun xs => xs.sym n) (List.perm.sym n)
  ```
  and then use this to remove the `DecidableEq` assumption from `Finset.sym`.

* `theorem injective_sym2 : Function.Injective (Multiset.sym2 : Multiset α → _)`

* `theorem strictMono_sym2 : StrictMono (Multiset.sym2 : Multiset α → _)`

-/

@[expose] public section

namespace Multiset

variable {α β : Type*}

section Sym2

/-- `m.sym2` is the multiset of all unordered pairs of elements from `m`, with multiplicity.
If `m` has no duplicates then neither does `m.sym2`. -/
/-
**Multiset.sym2** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → Multiset α → Multiset (Sym2 α)
参数：Sym2 α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`m.sym2` is the multiset of all unordered pairs of elements from `m`, with multi
plicity.
If `m` has no duplicates then neither does `m.sym2`.
-/
protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2
/-
**Multiset.sym2_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (xs : List α), (↑xs).sym2 = ↑xs.sym2
参数：xs : List α；↑xs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sym2_coe (xs : List α) : (xs : Multiset α).sym2 = xs.sym2 := rfl

@[simp]
/-
**Multiset.sym2_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sym2_eq_zero_iff {m : Multiset α} : m.sym2 = 0 ↔ m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sym2_eq_zero_iff {m : Multiset α} : m.sym2 = 0 ↔ m = 0 :=
  m.inductionOn fun xs => by simp

@[simp]
/-
**Multiset.sym2_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sym2_zero : (0 : Multiset α).sym2 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym2_zero : (0 : Multiset α).sym2 = 0 := rfl
/-
**Multiset.sym2_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sym2_cons (a : α) (m : Multiset α) : (m.cons a).sym2 = ((m.cons a).map <| 
fun b => s(a, b)) + m.sym2
参数：a : α；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem sym2_cons (a : α) (m : Multiset α) :
    (m.cons a).sym2 = ((m.cons a).map <| fun b => s(a, b)) + m.sym2 :=
  m.inductionOn fun _ => rfl
/-
**Multiset.sym2_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sym2_map (f : α -> β) (m : Multiset α) : (m.map f).sym2 = m.sym2.map (Sym2
.map f)
参数：f : α -> β；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sym2_map`：sym2_map (f : α -> β) (xs : List α) : (xs.map f).sym2 = x
s.sym2.map (Sym2.map f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sym2_map (f : α → β) (m : Multiset α) :
    (m.map f).sym2 = m.sym2.map (Sym2.map f) :=
  m.inductionOn fun xs => by simp [List.sym2_map]
/-
**Multiset.mk_mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mk_mem_sym2_iff {m : Multiset α} {a b : α} : s(a, b) in m.sym2 ↔ a in m ∧ 
b in m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_mem_sym2_iff {m : Multiset α} {a b : α} :
    s(a, b) ∈ m.sym2 ↔ a ∈ m ∧ b ∈ m :=
  m.inductionOn fun xs => by simp [List.mk_mem_sym2_iff]
/-
**Multiset.mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_sym2_iff {m : Multiset α} {z : Sym2 α} : z in m.sym2 ↔ forall y in z, 
y in m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sym2_iff {m : Multiset α} {z : Sym2 α} :
    z ∈ m.sym2 ↔ ∀ y ∈ z, y ∈ m :=
  m.inductionOn fun xs => by simp [List.mem_sym2_iff]
/-
**Multiset.setOfPred_mem_sym2** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：setOfPred_mem_sym2 {m : Multiset α} : {z : Sym2 α | z in m.sym2} = {x : α 
| x in m}.sym2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma setOfPred_mem_sym2 {m : Multiset α} :
    {z : Sym2 α | z ∈ m.sym2} = {x : α | x ∈ m}.sym2 :=
  Set.ext fun z ↦ z.ind fun a b => by simp [mk_mem_sym2_iff]

@[deprecated (since := "2026-07-09")] alias setOf_mem_sym2 := setOfPred_mem_sym2
/-
**Multiset.Nodup.sym2** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {m : Multiset α}, m.Nodup → m.sym2.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.Nodup.sym2`：∀ {α : Type u_1} {xs : List α}, xs.Nodup → xs.sym2.Nodu
p
-/
protected theorem Nodup.sym2 {m : Multiset α} (h : m.Nodup) : m.sym2.Nodup :=
  m.inductionOn (fun _ h => List.Nodup.sym2 h) h

open scoped List in
@[simp, mono]
/-
**Multiset.sym2_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sym2_mono {m m' : Multiset α} (h : m <= m') : m.sym2 <= m'.sym2
参数：h : m <= m'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.Subperm.sym2`：∀ {α : Type u_1} {xs ys : List α}, xs.Subperm ys → xs
.sym2.Subperm ys.sym2
-/
theorem sym2_mono {m m' : Multiset α} (h : m ≤ m') : m.sym2 ≤ m'.sym2 := by
  induction m, m' using Quotient.inductionOn₂ with | _ xs ys
  suffices xs <+~ ys from this.sym2
  simpa only [quot_mk_to_coe, coe_le, sym2_coe] using h
/-
**Multiset.monotone_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：monotone_sym2 : Monotone (Multiset.sym2 : Multiset α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sym2_mono`：sym2_mono {m m' : Multiset α} (h : m <= m') : m.sym2
 <= m'.sym2
-/
theorem monotone_sym2 : Monotone (Multiset.sym2 : Multiset α → _) := fun _ _ => sym2_mono
/-
**Multiset.card_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_sym2 {m : Multiset α} : Multiset.card m.sym2 = Nat.choose (Multiset.c
ard m + 1) 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_sym2`：length_sym2 {xs : List α} : xs.sym2.length = Nat.choos
e (xs.length + 1) 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_sym2 {m : Multiset α} :
    Multiset.card m.sym2 = Nat.choose (Multiset.card m + 1) 2 := by
  refine m.inductionOn fun xs => ?_
  simp [List.length_sym2]
/-
**Multiset.dedup_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_sym2 [DecidableEq α] (m : Multiset α) : m.sym2.dedup = m.dedup.sym2
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_sym2`：dedup_sym2 [DecidableEq α] (xs : List α) : xs.sym2.dedu
p = xs.dedup.sym2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dedup_sym2 [DecidableEq α] (m : Multiset α) : m.sym2.dedup = m.dedup.sym2 :=
  m.inductionOn fun xs => by simp [List.dedup_sym2]

end Sym2

end Multiset

