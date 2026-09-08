/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# A construction by Gabriel and Zisman

In this file, we construct a cosimplicial object `SimplexCategory.II`
in `SimplexCategoryᵒᵖ`, i.e. a functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ`.
If we identify `SimplexCategory` with the category of finite nonempty
linearly ordered types, this functor could be interpreted as the
contravariant functor which sends a finite nonempty linearly ordered type `T`
to `T →o Fin 2` (with `f ≤ g ↔ ∀ i, g i ≤ f i`, which turns out to
be a linear order); in particular, it sends `Fin (n + 1)` to a linearly
ordered type which is isomorphic to `Fin (n + 2)`. As a result, we define
`SimplexCategory.II` as a functor which sends `⦋n⦌` to `⦋n + 1⦌`: on morphisms,
it sends faces to degeneracies and vice versa. This construction appeared
in *Calculus of fractions and homotopy theory*, chapter III, paragraph 1.1,
by Gabriel and Zisman.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

@[expose] public section

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

namespace II

variable {n m : ℕ}

/-- Auxiliary definition for `map'`. Given `f : Fin (n + 1) →o Fin (m + 1)` and
`x : Fin (m + 2)`, `map' f x` shall be the smallest element in
this `finset f x : Finset (Fin (n + 2))`. -/
/-
**SimplexCategory.II.finset** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.II`。
形式化陈述：finset (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) : Finset (Fin (
n + 2))
参数：f : Fin (n + 1) ->o Fin (m + 1)；x : Fin (m + 2)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `map'`. Given `f : Fin (n + 1) →o Fin (m + 1)` and
`x : Fin (m + 2)`, `map' f x` shall be the smallest element in
this `finset f x : Finset (Fin (n + 2))`.
-/
def finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i ↦ i = Fin.last _ ∨
    ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc)
/-
**SimplexCategory.II.mem_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.I
I`。
形式化陈述：mem_finset_iff (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) (i : Fi
n (n + 2)) : i in finset f x ↔ i = Fin.last _ ∨ exists (h : i != Fin.last _), x 
<= (f (i.castPred h)).castSucc
参数：f : Fin (n + 1) ->o Fin (m + 1)；x : Fin (m + 2)；i : Fin (n + 2)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_finset_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 2)) :
    i ∈ finset f x ↔ i = Fin.last _ ∨
      ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc := by
  simp [finset]

@[simp]
/-
**SimplexCategory.II.last_mem_finset** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.
II`。
形式化陈述：last_mem_finset (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) : Fin.
last _ in finset f x
参数：f : Fin (n + 1) ->o Fin (m + 1)；x : Fin (m + 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma last_mem_finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    Fin.last _ ∈ finset f x := by
  simp [mem_finset_iff]

@[simp]
/-
**SimplexCategory.II.castSucc_mem_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimplexC
ategory.II`。
形式化陈述：castSucc_mem_finset_iff (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)
) (i : Fin (n + 1)) : i.castSucc in finset f x ↔ x <= (f i).castSucc
参数：f : Fin (n + 1) ->o Fin (m + 1)；x : Fin (m + 2)；i : Fin (n + 1)。
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
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma castSucc_mem_finset_iff
    (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 1)) :
    i.castSucc ∈ finset f x ↔ x ≤ (f i).castSucc := by
  simp [mem_finset_iff, Fin.castPred_castSucc]
/-
**SimplexCategory.II.nonempty_finset** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.
II`。
形式化陈述：nonempty_finset (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) : (fin
set f x).Nonempty
参数：f : Fin (n + 1) ->o Fin (m + 1)；x : Fin (m + 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma nonempty_finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    (finset f x).Nonempty :=
  ⟨Fin.last _, by simp [mem_finset_iff]⟩

/-- Auxiliary definition for the definition of the action of the
functor `SimplexCategory.II` on morphisms. -/
/-
**SimplexCategory.II.map'** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory.II`。
形式化陈述：map' (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) : Fin (n + 2)
参数：f : Fin (n + 1) ->o Fin (m + 1)；x : Fin (m + 2)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `SimplexCategory.II.nonempty_finset`：nonempty_finset (f : Fin (n + 1) ->o
 Fin (m + 1)) (x : Fin (m + 2)) : (finset f x).Nonempty

--- 原说明 ---
Auxiliary definition for the definition of the action of the
functor `SimplexCategory.II` on morphisms.
-/
def map' (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Fin (n + 2) :=
  (finset f x).min' (nonempty_finset f x)
/-
**SimplexCategory.II.map'_eq_last_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory
.II`。
形式化陈述：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)),   SimplexC
ategory.II.map' f x = Fin.last (n + 1) ↔ ∀ (i : Fin (n + 1)), (f i).castSucc < x
参数：f : Fin (n + 1) →o Fin (m + 1)；x : Fin (m + 2)；n + 1；i : Fin (n + 1)；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `SimplexCategory.II.nonempty_finset`：nonempty_finset (f : Fin (n + 1) ->o
 Fin (m + 1)) (x : Fin (m + 2)) : (finset f x).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Fin.castSucc_ne_last`：castSucc_ne_last {n : Nat} (i : Fin n) : i.castSuc
c != .last n
· 使用定理 `Fin.eq_castSucc_of_ne_last`：eq_castSucc_of_ne_last {x : Fin (n + 1)} (h 
: x != (last _)) : exists y, Fin.castSucc y = x
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
lemma map'_eq_last_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) :
    map' f x = Fin.last _ ↔ ∀ (i : Fin (n + 1)), (f i).castSucc < x := by
  simp only [map', Finset.min'_eq_iff, last_mem_finset, Fin.last_le_iff, true_and]
  constructor
  · intro h i
    by_contra!
    exact i.castSucc_ne_last (h i.castSucc (by simpa))
  · intro h i hi
    by_contra!
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last this
    simp only [castSucc_mem_finset_iff] at hi
    exact hi.not_gt (h i)
/-
**SimplexCategory.II.map'_eq_castSucc_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCate
gory.II`。
形式化陈述：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n
 + 1)),   SimplexCategory.II.map' f x = y.castSucc ↔ x ≤ (f y).castSucc ∧ ∀ i < 
y, (f i).castSucc < x
参数：f : Fin (n + 1) →o Fin (m + 1)；x : Fin (m + 2)；y : Fin (n + 1)；f y；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用引理 `SimplexCategory.II.nonempty_finset`：nonempty_finset (f : Fin (n + 1) ->o
 Fin (m + 1)) (x : Fin (m + 2)) : (finset f x).Nonempty
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
-/
lemma map'_eq_castSucc_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)) :
    map' f x = y.castSucc ↔ x ≤ (f y).castSucc ∧
      ∀ (i : Fin (n + 1)) (_ : i < y), (f i).castSucc < x := by
  simp only [map', Finset.min'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_ge (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_ge (by simpa using hi)
    · apply Fin.le_last

@[simp]
/-
**SimplexCategory.II.map'_last** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.II`。
形式化陈述：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)), SimplexCategory.II.map' f (F
in.last (m + 1)) = Fin.last (n + 1)
参数：f : Fin (n + 1) →o Fin (m + 1)；Fin.last (m + 1)；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma map'_last (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f (Fin.last _) = Fin.last _ := by
  simp [map'_eq_last_iff]

@[simp]
/-
**SimplexCategory.II.map'_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.II`。
形式化陈述：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)), SimplexCategory.II.map' f 0 
= 0
参数：f : Fin (n + 1) →o Fin (m + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma map'_zero (f : Fin (n + 1) →o Fin (m + 1)) :
    map' f 0 = 0 := by
  simp [← Fin.castSucc_zero, -Fin.castSucc_zero', map'_eq_castSucc_iff]

@[simp]
/-
**SimplexCategory.II.map'_id** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.II`。
形式化陈述：∀ {n : ℕ} (x : Fin (n + 2)), SimplexCategory.II.map' OrderHom.id x = x
参数：x : Fin (n + 2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimplexCategory.II.map'_eq_castSucc_iff`：∀ {n m : ℕ} (f : Fin (n + 1) →o
 Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)),   SimplexCategory.II.map' f x
 = y.castSucc ↔ x ≤ (f y).cas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimplexCategory.II.map'_last`：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1
)), SimplexCategory.II.map' f (Fin.last (m + 1)) = Fin.last (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map'_id (x : Fin (n + 2)) : map' OrderHom.id x = x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · rw [map'_eq_castSucc_iff]
    simp
  · simp
/-
**SimplexCategory.II.map'_map'** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.II`。
形式化陈述：∀ {n m p : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) (g : Fin (m + 1) →o Fin (p 
+ 1)) (x : Fin (p + 2)),   SimplexCategory.II.map' f (SimplexCategory.II.map' g 
x) = SimplexCategory.II.map' (g.comp f) x
参数：f : Fin (n + 1) →o Fin (m + 1)；g : Fin (m + 1) →o Fin (p + 1)；x : Fin (p + 2)
；SimplexCategory.II.map' g x；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `SimplexCategory.II.map'_eq_castSucc_iff`：∀ {n m : ℕ} (f : Fin (n + 1) →o
 Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)),   SimplexCategory.II.map' f x
 = y.castSucc ↔ x ≤ (f y).cas…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimplexCategory.II.map'_eq_last_iff`：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin
 (m + 1)) (x : Fin (m + 2)),   SimplexCategory.II.map' f x = Fin.last (n + 1) ↔ 
∀ (i : Fin (n + 1)), (f i…
· 使用定理 `SimplexCategory.II.map'_last`：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1
)), SimplexCategory.II.map' f (Fin.last (m + 1)) = Fin.last (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map'_map' {p : ℕ} (f : Fin (n + 1) →o Fin (m + 1))
    (g : Fin (m + 1) →o Fin (p + 1)) (x : Fin (p + 2)) :
    map' f (map' g x) = map' (g.comp f) x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' g x.castSucc)
    · rw [hy]
      rw [map'_eq_castSucc_iff] at hy
      obtain ⟨z, hz⟩ | hz := Fin.eq_castSucc_or_eq_last (map' f y.castSucc)
      · rw [hz, Eq.comm]
        rw [map'_eq_castSucc_iff] at hz ⊢
        constructor
        · refine hy.1.trans ?_
          simp only [OrderHom.comp_coe, Function.comp_apply, Fin.castSucc_le_castSucc_iff]
          exact g.monotone (by simpa using hz.1)
        · intro i hi
          exact hy.2 (f i) (by simpa using hz.2 i hi)
      · rw [hz, Eq.comm]
        rw [map'_eq_last_iff] at hz ⊢
        intro i
        exact hy.2 (f i) (by simpa using hz i)
    · rw [Eq.comm, hx, map'_last]
      rw [map'_eq_last_iff] at hx ⊢
      intro i
      apply hx
  · simp

@[simp]
/-
**SimplexCategory.II.map'_succAboveOrderEmb** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCa
tegory.II`。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 3)), SimplexCategory.II.map' i.s
uccAboveOrderEmb.toOrderHom x = i.predAbove x
参数：i : Fin (n + 2)；x : Fin (n + 3)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Fin.castPred_castSucc`：castPred_castSucc {i : Fin n} (h'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderEmbedding.toOrderHom_coe`：∀ {X : Type u_6} {Y : Type u_7} [inst : P
reorder X] [inst_1 : Preorder Y] (f : X ↪o Y), ⇑f.toOrderHom = ⇑f
· 使用定理 `Fin.succAboveOrderEmb_apply`：∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.
succAboveOrderEmb i = p.succAbove i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Fin.succAbove_castSucc_self`：∀ {n : ℕ} (j : Fin n), j.castSucc.succAbove
 j = j.succ
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.succAbove_last`：∀ {n : ℕ}, (Fin.last n).succAbove = Fin.castSucc
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 50 条，此处仅展示前 30 条）
-/
lemma map'_succAboveOrderEmb {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 3)) :
    map' i.succAboveOrderEmb.toOrderHom x = i.predAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hx : x ≤ i
    · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
      obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
      · simp only [map'_eq_castSucc_iff, OrderEmbedding.toOrderHom_coe,
          Fin.succAboveOrderEmb_apply, Fin.castSucc_le_castSucc_iff,
          Fin.castSucc_lt_castSucc_iff]
        constructor
        · obtain hx | rfl := hx.lt_or_eq
          · rwa [Fin.succAbove_of_castSucc_lt]
          · simpa only [Fin.succAbove_castSucc_self] using Fin.castSucc_le_succ x
        · intro j hj
          rwa [Fin.succAbove_of_castSucc_lt _ _ (lt_of_lt_of_le (by simpa) hx),
            Fin.castSucc_lt_castSucc_iff]
      · obtain rfl : i = Fin.last _ := Fin.last_le_iff.1 hx
        simp [map'_eq_last_iff]
    · obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff]),
        Fin.pred_castSucc_succ, map'_eq_castSucc_iff]
      simp only [Fin.succAbove_of_lt_succ _ _ hx,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
        le_refl, Fin.castSucc_lt_castSucc_iff, true_and]
      intro j hj
      by_cases! h : j.castSucc < i
      · simpa [Fin.succAbove_of_castSucc_lt _ _ h] using hj.le
      · rwa [Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_lt_succ_iff]
  · simp

@[simp]
/-
**SimplexCategory.II.map'_predAbove** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCategory.I
I`。
形式化陈述：∀ {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 2)),   SimplexCategory.II.map' {
 toFun := i.predAbove, monotone' := ⋯ } x = i.succ.castSucc.succAbove x
参数：i : Fin (n + 1)；x : Fin (n + 2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.predAbove_right_monotone`：predAbove_right_monotone (p : Fin n) : Mon
otone p.predAbove
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.succ_castSucc`：∀ {n : ℕ} (i : Fin n), i.castSucc.succ = i.succ.castS
ucc
· 使用定理 `SimplexCategory.II.map'_eq_castSucc_iff`：∀ {n m : ℕ} (f : Fin (n + 1) →o
 Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)),   SimplexCategory.II.map' f x
 = y.castSucc ↔ x ≤ (f y).cas…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `Fin.pred_succ`：∀ {n : ℕ} (i : Fin n) {h : i.succ ≠ 0}, i.succ.pred h = i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.succ_lt_succ_iff`：∀ {n : ℕ} {a b : Fin n}, a.succ < b.succ ↔ a < b
· 使用定理 `Fin.succ_pred`：∀ {n : ℕ} (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ 
= i
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `Fin.castSucc_lt_castSucc_iff`：∀ {n : ℕ} {a b : Fin n}, a.castSucc < b.ca
stSucc ↔ a < b
· 使用定理 `Fin.castSucc_castPred`：castSucc_castPred (i : Fin (n + 1)) (h : i != las
t n) : castSucc (i.castPred h) = i
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Fin.castSucc_lt_succ`：∀ {n : ℕ} {i : Fin n}, i.castSucc < i.succ
· 使用定理 `SimplexCategory.II.map'_last`：∀ {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1
)), SimplexCategory.II.map' f (Fin.last (m + 1)) = Fin.last (n + 1)
（共 33 条，此处仅展示前 30 条）
-/
lemma map'_predAbove {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 2)) :
    map' { toFun := i.predAbove, monotone' := Fin.predAbove_right_monotone i } x =
      i.succ.castSucc.succAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hi : i < x
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc, map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · rw [Fin.predAbove_of_castSucc_lt _ _
          (by simpa only [Fin.castSucc_lt_succ_iff] using hi.le), Fin.pred_succ]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rwa [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff,
            Fin.succ_pred]
        · rw [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
          exact lt_of_le_of_lt h hi
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa), map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · simp only [i.predAbove_of_le_castSucc x.castSucc (by simpa),
          Fin.castPred_castSucc, le_refl]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rw [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
          exact hj.trans x.castSucc_lt_succ
        · rwa [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
  · simp [map'_last]
/-
**SimplexCategory.II.monotone_map'** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.II
`。
形式化陈述：monotone_map' (f : Fin (n + 1) ->o Fin (m + 1)) : Monotone (map' f)
参数：f : Fin (n + 1) ->o Fin (m + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.min'_subset`：∀ {α : Type u_2} [inst : LinearOrder α] {s t : Finse
t α} (H : s.Nonempty) (hst : s ⊆ t), t.min' ⋯ ≤ s.min' H
· 使用引理 `SimplexCategory.II.nonempty_finset`：nonempty_finset (f : Fin (n + 1) ->o
 Fin (m + 1)) (x : Fin (m + 2)) : (finset f x).Nonempty
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma monotone_map' (f : Fin (n + 1) →o Fin (m + 1)) :
    Monotone (map' f) := by
  intro x y hxy
  exact Finset.min'_subset _ (fun z hz ↦ by
    obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
    · simp only [castSucc_mem_finset_iff] at hz ⊢
      exact hxy.trans hz
    · simp)

end II

/-- The functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ` (i.e. a cosimplicial
object in `SimplexCategoryᵒᵖ`) which sends `⦋n⦌` to the object in `SimplexCategoryᵒᵖ`
that is associated to the linearly ordered type `⦋n + 1⦌` (which could be
identified to the ordered type `⦋n⦌ →o ⦋1⦌`). -/
@[simps obj]
/-
**SimplexCategory.II** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategory`。
形式化陈述：II : CosimplicialObject SimplexCategoryᵒᵖ where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ` (i.e. a cosimplicial
object in `SimplexCategoryᵒᵖ`) which sends `⦋n⦌` to the object in `SimplexCatego
ryᵒᵖ`
that is associated to the linearly ordered type `⦋n + 1⦌` (which could be
identified to the ordered type `⦋n⦌ →o ⦋1⦌`).
-/
def II : CosimplicialObject SimplexCategoryᵒᵖ where
  obj n := op ⦋n.len + 1⦌
  map f := op (Hom.mk
    { toFun := II.map' f.toOrderHom
      monotone' := II.monotone_map' _ })
  map_id n := Quiver.Hom.unop_inj (by
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

@[simp]
/-
**SimplexCategory.II_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma II_δ {n : ℕ} (i : Fin (n + 2)) :
    II.δ i = (σ i).op :=
  Quiver.Hom.unop_inj (by ext : 3; apply II.map'_succAboveOrderEmb)

@[simp]
/-
**SimplexCategory.II_** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma II_σ {n : ℕ} (i : Fin (n + 1)) :
    II.σ i = (δ i.succ.castSucc).op :=
  Quiver.Hom.unop_inj (by ext x : 3; apply II.map'_predAbove)

end SimplexCategory

