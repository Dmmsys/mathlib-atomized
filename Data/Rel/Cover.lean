/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Separated

/-!
# Covers in a uniform space

This file defines covers, aka nets, which are a quantitative notion of compactness given an
entourage.

A `U`-cover of a set `s` is a set `N` such that every element of `s` is `U`-close to some element of
`N`.

The concept of uniform covers is used to define two further notions of covering:
* Metric covers: `Metric.IsCover`, defined using the distance entourage.
* Dynamical covers: `Dynamics.IsDynCoverOf`, defined using the dynamical entourage.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

@[expose] public section

open Set

namespace SetRel
variable {X : Type*} {U V : SetRel X X} {s t N N₁ N₂ : Set X} {x : X}

/-- For an entourage `U`, a set `N` is a *`U`-cover* of a set `s` if every point of `s` is `U`-close
to some point of `N`.

This is also called a *`U`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
/-
**SetRel.IsCover** 是 Mathlib 中的一个定义，位于命名空间 `SetRel`。
形式化陈述：IsCover (U : SetRel X X) (s N : Set X) : Prop
参数：U : SetRel X X；s N : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an entourage `U`, a set `N` is a *`U`-cover* of a set `s` if every point of 
`s` is `U`-close
to some point of `N`.

This is also called a *`U`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1.
-/
def IsCover (U : SetRel X X) (s N : Set X) : Prop := ∀ ⦃x⦄, x ∈ s → ∃ y ∈ N, x ~[U] y
/-
**SetRel.IsCover.empty** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} {N : Set X}, U.IsCover ∅ N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma IsCover.empty : IsCover U ∅ N := by simp [IsCover]
/-
**SetRel.isCover_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} {s : Set X}, U.IsCover s ∅ ↔ s = ∅
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isCover_empty_right : IsCover U s ∅ ↔ s = ∅ := by
  simp [IsCover, eq_empty_iff_forall_notMem]

protected nonrec lemma IsCover.nonempty (hsN : IsCover U s N) (hs : s.Nonempty) : N.Nonempty :=
  let ⟨_x, hx⟩ := hs; let ⟨y, hy, _⟩ := hsN hx; ⟨y, hy⟩
/-
**SetRel.IsCover.refl** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} (U : SetRel X X) [U.IsRefl] (s : Set X), U.IsCover s s
参数：U : SetRel X X；s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
-/
@[simp] lemma IsCover.refl (U : SetRel X X) [U.IsRefl] (s : Set X) : IsCover U s s :=
  fun a ha ↦ ⟨a, ha, U.rfl⟩
/-
**SetRel.IsCover.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} [U.IsRefl] {s : Set X}, U.IsCover s s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.refl`：∀ {X : Type u_1} (U : SetRel X X) [U.IsRefl] (s : S
et X), U.IsCover s s
-/
lemma IsCover.rfl {U : SetRel X X} [U.IsRefl] {s : Set X} : IsCover U s s := refl U s
/-
**SetRel.isCover_univ** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {X : Type u_1} {s N : Set X}, SetRel.IsCover Set.univ s N ↔ s.Nonempty →
 N.Nonempty
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] protected lemma isCover_univ : IsCover univ s N ↔ (s.Nonempty → N.Nonempty) := by
  simp [IsCover, Set.Nonempty]
/-
**SetRel.IsCover.mono** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} {s N₁ N₂ : Set X}, N₁ ⊆ N₂ → U.IsCover s
 N₁ → U.IsCover s N₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCover.mono (hN : N₁ ⊆ N₂) (h₁ : IsCover U s N₁) : IsCover U s N₂ :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩
/-
**SetRel.IsCover.anti** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} {s t N : Set X}, s ⊆ t → U.IsCover t N →
 U.IsCover s N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCover.anti (hst : s ⊆ t) (ht : IsCover U t N) : IsCover U s N := fun _x hx ↦ ht <| hst hx
/-
**SetRel.IsCover.mono_entourage** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} {U V : SetRel X X} {s N : Set X}, U ⊆ V → U.IsCover s N →
 V.IsCover s N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCover.mono_entourage (hUV : U ⊆ V) (hU : IsCover U s N) : IsCover V s N :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := hU hx; ⟨y, hy, hUV hxy⟩
/-
**SetRel.IsCover.union** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCover`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} {s t N₁ N₂ : Set X}, U.IsCover s N₁ → U.
IsCover t N₂ → U.IsCover (s ∪ t) (N₁ ∪ N₂)
参数：s ∪ t；N₁ ∪ N₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCover.union (hs : IsCover U s N₁) (ht : IsCover U t N₂) : IsCover U (s ∪ t) (N₁ ∪ N₂) := fun
  | _x, .inl hx => let ⟨y, hy, hxy⟩ := hs hx; ⟨y, .inl hy, hxy⟩
  | _x, .inr hx => let ⟨y, hy, hxy⟩ := ht hx; ⟨y, .inr hy, hxy⟩

/-- A maximal `U`-separated subset of a set `s` is a `U`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
/-
**SetRel.IsCover.of_maximal_isSeparated** 是 Mathlib 中的一个定理，位于命名空间 `SetRel.IsCove
r`。
形式化陈述：∀ {X : Type u_1} {U : SetRel X X} {s N : Set X} [U.IsRefl] [U.IsSymm],   M
aximal (fun N => N ⊆ s ∧ U.IsSeparated N) N → U.IsCover s N
参数：fun N => N ⊆ s ∧ U.IsSeparated N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SetRel.rfl`：∀ {α : Type u_1} (R : SetRel α α) {a : α} [R.IsRefl], (a, a)
 ∈ R
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `SetRel.IsSeparated.insert`：∀ {X : Type u_1} {R : SetRel X X} {s : Set X}
 {x : X} [R.IsSymm],   R.IsSeparated s → (∀ y ∈ s, (x, y) ∈ R → x = y) → R.IsSep
arated (insert …
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
A maximal `U`-separated subset of a set `s` is a `U`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6.
-/
lemma IsCover.of_maximal_isSeparated [U.IsRefl] [U.IsSymm]
    (hN : Maximal (fun N ↦ N ⊆ s ∧ IsSeparated U N) N) : IsCover U s N := by
  rintro x hx
  by_contra! h
  simpa [U.rfl] using h _ <| hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert fun y hy hxy ↦ (h y hy hxy).elim⟩ (subset_insert _ _) (mem_insert _ _)
/-
**SetRel.isCover_id** 是 Mathlib 中的一个定理，位于命名空间 `SetRel`。
形式化陈述：∀ {X : Type u_1} {s N : Set X}, SetRel.id.IsCover s N ↔ s ⊆ N
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
@[simp] lemma isCover_id : IsCover .id s N ↔ s ⊆ N := by simp [IsCover, subset_def]

end SetRel

