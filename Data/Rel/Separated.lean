/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.Rel

/-!
# Uniform separation

This file defines a notion of separation of a set relative to a relation.

For a relation `R`, an `R`-separated set `s` is a set such that every pair of elements of `s` is
`R`-unrelated.

The concept of uniformly separated sets is used to define two further notions of separation:
* Metric separation: `Metric.IsSeparated`, defined using the small distance relation.
* Dynamical nets: `Dynamics.IsDynNetIn`, defined using the dynamical relation.

## TODO

* Actually use `SetRel.IsSeparated` to define the above two notions.
* Link to the notion of separation given by pairwise disjoint balls.
-/

@[expose] public section

open Set

namespace SetRel
variable {X : Type*} {R S : SetRel X X} {s t : Set X} {x : X}

/-- Given a relation `R`, a set `s` is `R`-separated if its elements are pairwise `R`-unrelated from
each other. -/
/-
**SetRel.IsSeparated** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：IsSeparated (R : SetRel X X) (s : Set X) : Prop
参数：R : SetRel X X；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relation `R`, a set `s` is `R`-separated if its elements are pairwise `R
`-unrelated from
each other.
-/
def IsSeparated (R : SetRel X X) (s : Set X) : Prop := s.Pairwise fun x y ↦ ¬ x ~[R] y
/-
**SetRel.IsSeparated.empty** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSeparated`。
形式化陈述：∀ {X : Type u_1} {R : SetRel X X}, R.IsSeparated ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_empty`：pairwise_empty (r : α -> α -> Prop) : (∅ : Set α).Pa
irwise r
-/
protected lemma IsSeparated.empty : IsSeparated R (∅ : Set X) := pairwise_empty _
/-
**SetRel.IsSeparated.singleton** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSeparated`。
形式化陈述：∀ {X : Type u_1} {R : SetRel X X} {x : X}, R.IsSeparated {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_singleton`：pairwise_singleton (a : α) (r : α -> α -> Prop) 
: Set.Pairwise {a} r
-/
protected lemma IsSeparated.singleton : IsSeparated R {x} := pairwise_singleton ..
/-
**SetRel.IsSeparated.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSeparat
ed`。
形式化陈述：∀ {X : Type u_1} {R : SetRel X X} {s : Set X}, s.Subsingleton → R.IsSepara
ted s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
@[simp] lemma IsSeparated.of_subsingleton (hs : s.Subsingleton) : IsSeparated R s := hs.pairwise _

alias _root_.Set.Subsingleton.relIsSeparated := IsSeparated.of_subsingleton

nonrec lemma IsSeparated.mono_left (hUV : R ⊆ S) (hs : IsSeparated S s) : IsSeparated R s :=
  hs.mono' fun _x _y hxy h ↦ hxy <| hUV h
/-
**SetRel.IsSeparated.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSeparated`。
形式化陈述：∀ {X : Type u_1} {R : SetRel X X} {s t : Set X}, s ⊆ t → R.IsSeparated t →
 R.IsSeparated s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
lemma IsSeparated.mono_right (hst : s ⊆ t) (ht : IsSeparated R t) : IsSeparated R s := ht.mono hst
/-
**SetRel.isSeparated_insert'** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：isSeparated_insert' : IsSeparated R (insert x s) ↔ IsSeparated R s ∧ (fora
ll y in s, x ~[R] y -> x = y) ∧ forall y in s, y ~[R] x -> x = y
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isSeparated_insert' :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ (∀ y ∈ s, x ~[R] y → x = y) ∧
        ∀ y ∈ s, y ~[R] x → x = y := by
  simp [IsSeparated, pairwise_insert, not_imp_comm (a := _ = _), -not_and, forall_and]
/-
**SetRel.isSeparated_insert** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：isSeparated_insert [R.IsSymm] : IsSeparated R (insert x s) ↔ IsSeparated R
 s ∧ forall y in s, x ~[R] y -> x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
-/
lemma isSeparated_insert [R.IsSymm] :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ ∀ y ∈ s, x ~[R] y → x = y := by
  have : Std.Symm fun x y ↦ ¬(x, y) ∈ R := { symm _ _ := mt R.symm }
  simpa [not_imp_not, IsSeparated] using pairwise_insert_of_symm (r := fun x y ↦ ¬(x, y) ∈ R)
/-
**SetRel.isSeparated_insert_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `SetRel`。
形式化陈述：isSeparated_insert_of_notMem [R.IsSymm] (hx : x ∉ s) : IsSeparated R (inse
rt x s) ↔ IsSeparated R s ∧ forall y in s, ¬ x ~[R] y
参数：hx : x ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `Set.pairwise_insert_of_symm_of_notMem`：pairwise_insert_of_symm_of_notMem
 [Std.Symm r] (ha : a ∉ s) : (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b i
n s, r a b
-/
lemma isSeparated_insert_of_notMem [R.IsSymm] (hx : x ∉ s) :
    IsSeparated R (insert x s) ↔ IsSeparated R s ∧ ∀ y ∈ s, ¬ x ~[R] y :=
  have : Std.Symm fun x y ↦ ¬(x, y) ∈ R := { symm _ _ := mt R.symm }
  pairwise_insert_of_symm_of_notMem hx
/-
**SetRel.IsSeparated.insert'** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSeparated`。
形式化陈述：∀ {X : Type u_1} {R : SetRel X X} {s : Set X} {x : X},   R.IsSeparated s →
 (∀ y ∈ s, (x, y) ∈ R → x = y) → (∀ y ∈ s, (y, x) ∈ R → x = y) → R.IsSeparated (
insert x s)
参数：∀ y ∈ s, (x, y) ∈ R → x = y；∀ y ∈ s, (y, x) ∈ R → x = y；insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SetRel.isSeparated_insert'`：isSeparated_insert' : IsSeparated R (insert 
x s) ↔ IsSeparated R s ∧ (forall y in s, x ~[R] y -> x = y) ∧ forall y in s, y ~
[R] x -> x = y
-/
protected lemma IsSeparated.insert' (hs : IsSeparated R s) (h : ∀ y ∈ s, x ~[R] y → x = y)
    (h' : ∀ y ∈ s, y ~[R] x → x = y) : IsSeparated R (insert x s) :=
  isSeparated_insert'.2 ⟨hs, h, h'⟩
/-
**SetRel.IsSeparated.insert** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsSeparated`。
形式化陈述：∀ {X : Type u_1} {R : SetRel X X} {s : Set X} {x : X} [R.IsSymm],   R.IsSe
parated s → (∀ y ∈ s, (x, y) ∈ R → x = y) → R.IsSeparated (insert x s)
参数：∀ y ∈ s, (x, y) ∈ R → x = y；insert x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SetRel.isSeparated_insert`：isSeparated_insert [R.IsSymm] : IsSeparated R
 (insert x s) ↔ IsSeparated R s ∧ forall y in s, x ~[R] y -> x = y
-/
protected lemma IsSeparated.insert [R.IsSymm] (hs : IsSeparated R s)
    (h : ∀ y ∈ s, x ~[R] y → x = y) : IsSeparated R (insert x s) :=
  isSeparated_insert.2 ⟨hs, h⟩

end SetRel

