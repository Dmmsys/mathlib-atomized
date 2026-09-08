/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Split a box along one or more hyperplanes

## Main definitions

A hyperplane `{x : ι → ℝ | x i = a}` splits a rectangular box `I : BoxIntegral.Box ι` into two
smaller boxes. If `a ∉ Ioo (I.lower i, I.upper i)`, then one of these boxes is empty, so it is not a
box in the sense of `BoxIntegral.Box`.

We introduce the following definitions.

* `BoxIntegral.Box.splitLower I i a` and `BoxIntegral.Box.splitUpper I i a` are these boxes (as
  `WithBot (BoxIntegral.Box ι)`);
* `BoxIntegral.Prepartition.split I i a` is the partition of `I` made of these two boxes (or of one
  box `I` if one of these boxes is empty);
* `BoxIntegral.Prepartition.splitMany I s`, where `s : Finset (ι × ℝ)` is a finite set of
  hyperplanes `{x : ι → ℝ | x i = a}` encoded as pairs `(i, a)`, is the partition of `I` made by
  cutting it along all the hyperplanes in `s`.

## Main results

The main result `BoxIntegral.Prepartition.exists_iUnion_eq_sdiff` says that any prepartition `π` of
`I` admits a prepartition `π'` of `I` that covers exactly `I \ π.iUnion`. One of these prepartitions
is available as `BoxIntegral.Prepartition.compl`.

## Tags

rectangular box, partition, hyperplane
-/

@[expose] public section

noncomputable section

open Function Set Filter

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

namespace Box

variable {I : Box ι} {i : ι} {x : ℝ} {y : ι → ℝ}

open scoped Classical in
/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `BoxIntegral.Box.splitLower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). As usual, we represent a box that may be empty as
`WithBot (BoxIntegral.Box ι)`. -/
/-
**BoxIntegral.Box.splitLower** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitLower (I : Box ι) (i : ι) (x : Real) : WithBot (Box ι)
参数：I : Box ι；i : ι；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y
 i = x}` splits
`I` into two boxes. `BoxIntegral.Box.splitLower I i x` is the box `I ∩ {y | y i 
≤ x}`
(if it is nonempty). As usual, we represent a box that may be empty as
`WithBot (BoxIntegral.Box ι)`.
-/
def splitLower (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' I.lower (update I.upper i (min x (I.upper i)))

@[simp]
/-
**BoxIntegral.Box.coe_splitLower** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_splitLower : (splitLower I i x : Set (ι -> Real)) = ↑I inter { y | y i
 <= x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.splitLower.eq_1`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι
) (i : ι) (x : ℝ),   I.splitLower i x = BoxIntegral.Box.mk' I.lower (Function.up
date I.upper i (min x…
· 使用定理 `BoxIntegral.Box.coe_mk'`：coe_mk' (l u : ι -> Real) : (mk' l u : Set (ι -
> Real)) = pi univ fun i => Ioc (l i) (u i)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_forall_ne`：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔
 forall b, p b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_splitLower : (splitLower I i x : Set (ι → ℝ)) = ↑I ∩ { y | y i ≤ x } := by
  rw [splitLower, coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and, ← Pi.le_def,
    le_update_iff, le_min_iff, and_assoc, and_forall_ne (p := fun j => y j ≤ upper I j) i, mem_def]
  rw [and_comm (a := y i ≤ x)]
/-
**BoxIntegral.Box.splitLower_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitLower_le : I.splitLower i x <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.withBotCoe_subset_iff`：withBotCoe_subset_iff {I J : With
Bot (Box ι)} : (I : Set (ι -> Real)) subseteq J ↔ I <= J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.coe_splitLower`：coe_splitLower : (splitLower I i x : Set
 (ι -> Real)) = ↑I inter { y | y i <= x }
-/
theorem splitLower_le : I.splitLower i x ≤ I :=
  withBotCoe_subset_iff.1 <| by simp

@[simp]
/-
**BoxIntegral.Box.splitLower_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitLower_eq_bot {i x} : I.splitLower i x = ⊥ ↔ x <= I.lower i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.splitLower.eq_1`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι
) (i : ι) (x : ℝ),   I.splitLower i x = BoxIntegral.Box.mk' I.lower (Function.up
date I.upper i (min x…
· 使用定理 `BoxIntegral.Box.mk'_eq_bot`：∀ {ι : Type u_1} {l u : ι → ℝ}, BoxIntegral.
Box.mk' l u = ⊥ ↔ ∃ i, u i ≤ l i
· 使用定理 `Function.exists_update_iff`：exists_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (exists x, p x (update f a b x)) ↔ p a
 b ∨ exists x !=…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem splitLower_eq_bot {i x} : I.splitLower i x = ⊥ ↔ x ≤ I.lower i := by
  classical
  rw [splitLower, mk'_eq_bot, exists_update_iff I.upper fun j y => y ≤ I.lower j]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]
/-
**BoxIntegral.Box.splitLower_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`
。
形式化陈述：splitLower_eq_self : I.splitLower i x = I ↔ I.upper i <= x
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem splitLower_eq_self : I.splitLower i x = I ↔ I.upper i ≤ x := by
  simp [splitLower]
/-
**BoxIntegral.Box.splitLower_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitLower_def [DecidableEq ι] {i x} (h : x in Ioo (I.lower i) (I.upper i)
) (h' : forall j, I.lower j < update I.upper i x j
参数：h : x in Ioo (I.lower i) (I.upper i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.Box.mk.congr_simp`：∀ {ι : Type u_2} (lower lower_1 : ι → ℝ) 
(e_lower : lower = lower_1) (upper upper_1 : ι → ℝ) (e_upper : upper = upper_1) 
  (lower_lt_upper :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem splitLower_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, I.lower j < update I.upper i x j :=
      (forall_update_iff I.upper fun j y => I.lower j < y).2
        ⟨h.1, fun _ _ => I.lower_lt_upper _⟩) :
    I.splitLower i x = (⟨I.lower, update I.upper i x, h'⟩ : Box ι) := by
  simp +unfoldPartialApp only [splitLower, mk'_eq_coe, min_eq_left h.2.le,
    update, and_self]

open scoped Classical in
/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `BoxIntegral.Box.splitUpper I i x` is the box `I ∩ {y | x < y i}`
(if it is nonempty). As usual, we represent a box that may be empty as
`WithBot (BoxIntegral.Box ι)`. -/
/-
**BoxIntegral.Box.splitUpper** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitUpper (I : Box ι) (i : ι) (x : Real) : WithBot (Box ι)
参数：I : Box ι；i : ι；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y
 i = x}` splits
`I` into two boxes. `BoxIntegral.Box.splitUpper I i x` is the box `I ∩ {y | x < 
y i}`
(if it is nonempty). As usual, we represent a box that may be empty as
`WithBot (BoxIntegral.Box ι)`.
-/
def splitUpper (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' (update I.lower i (max x (I.lower i))) I.upper

@[simp]
/-
**BoxIntegral.Box.coe_splitUpper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：coe_splitUpper : (splitUpper I i x : Set (ι -> Real)) = ↑I inter { y | x <
 y i }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.splitUpper.eq_1`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι
) (i : ι) (x : ℝ),   I.splitUpper i x = BoxIntegral.Box.mk' (Function.update I.l
ower i (max x (I.lowe…
· 使用定理 `BoxIntegral.Box.coe_mk'`：coe_mk' (l u : ι -> Real) : (mk' l u : Set (ι -
> Real)) = pi univ fun i => Ioc (l i) (u i)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Function.forall_update_iff`：forall_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (forall x, p x (update f a b x)) ↔ p a
 b ∧ forall x, x…
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_forall_ne`：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔
 forall b, p b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem coe_splitUpper : (splitUpper I i x : Set (ι → ℝ)) = ↑I ∩ { y | x < y i } := by
  classical
  rw [splitUpper, coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and,
    forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc (a := x < y i),
    and_forall_ne (p := fun j => lower I j < y j) i, mem_def]
  exact and_comm
/-
**BoxIntegral.Box.splitUpper_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitUpper_le : I.splitUpper i x <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.withBotCoe_subset_iff`：withBotCoe_subset_iff {I J : With
Bot (Box ι)} : (I : Set (ι -> Real)) subseteq J ↔ I <= J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.coe_splitUpper`：coe_splitUpper : (splitUpper I i x : Set
 (ι -> Real)) = ↑I inter { y | x < y i }
-/
theorem splitUpper_le : I.splitUpper i x ≤ I :=
  withBotCoe_subset_iff.1 <| by simp

@[simp]
/-
**BoxIntegral.Box.splitUpper_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitUpper_eq_bot {i x} : I.splitUpper i x = ⊥ ↔ I.upper i <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Box.splitUpper.eq_1`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι
) (i : ι) (x : ℝ),   I.splitUpper i x = BoxIntegral.Box.mk' (Function.update I.l
ower i (max x (I.lowe…
· 使用定理 `BoxIntegral.Box.mk'_eq_bot`：∀ {ι : Type u_1} {l u : ι → ℝ}, BoxIntegral.
Box.mk' l u = ⊥ ↔ ∃ i, u i ≤ l i
· 使用定理 `Function.exists_update_iff`：exists_update_iff (f : forall a, β a) {a : α
} {b : β a} (p : forall a, β a -> Prop) : (exists x, p x (update f a b x)) ↔ p a
 b ∨ exists x !=…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `BoxIntegral.Box.lower_lt_upper`：∀ {ι : Type u_2} (self : BoxIntegral.Box
 ι) (i : ι), self.lower i < self.upper i
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem splitUpper_eq_bot {i x} : I.splitUpper i x = ⊥ ↔ I.upper i ≤ x := by
  classical
  rw [splitUpper, mk'_eq_bot, exists_update_iff I.lower fun j y => I.upper j ≤ y]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]
/-
**BoxIntegral.Box.splitUpper_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`
。
形式化陈述：splitUpper_eq_self : I.splitUpper i x = I ↔ x <= I.lower i
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
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem splitUpper_eq_self : I.splitUpper i x = I ↔ x ≤ I.lower i := by
  simp [splitUpper]
/-
**BoxIntegral.Box.splitUpper_def** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Box`。
形式化陈述：splitUpper_def [DecidableEq ι] {i x} (h : x in Ioo (I.lower i) (I.upper i)
) (h' : forall j, update I.lower i x j < I.upper j
参数：h : x in Ioo (I.lower i) (I.upper i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Box.mk.congr_simp`：∀ {ι : Type u_2} (lower lower_1 : ι → ℝ) 
(e_lower : lower = lower_1) (upper upper_1 : ι → ℝ) (e_upper : upper = upper_1) 
  (lower_lt_upper :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem splitUpper_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, update I.lower i x j < I.upper j :=
      (forall_update_iff I.lower fun j y => y < I.upper j).2
        ⟨h.2, fun _ _ => I.lower_lt_upper _⟩) :
    I.splitUpper i x = (⟨update I.lower i x, I.upper, h'⟩ : Box ι) := by
  simp +unfoldPartialApp only [splitUpper, mk'_eq_coe, max_eq_left h.1.le,
    update, and_self]
/-
**BoxIntegral.Box.disjoint_splitLower_splitUpper** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.Box`。
形式化陈述：disjoint_splitLower_splitUpper (I : Box ι) (i : ι) (x : Real) : Disjoint (
I.splitLower i x) (I.splitUpper i x)
参数：I : Box ι；i : ι；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Box.disjoint_withBotCoe`：disjoint_withBotCoe {I J : WithBot 
(Box ι)} : Disjoint (I : Set (ι -> Real)) J ↔ Disjoint I J
· 使用定理 `BoxIntegral.Box.coe_splitLower`：coe_splitLower : (splitLower I i x : Set
 (ι -> Real)) = ↑I inter { y | y i <= x }
· 使用定理 `BoxIntegral.Box.coe_splitUpper`：coe_splitUpper : (splitUpper I i x : Set
 (ι -> Real)) = ↑I inter { y | x < y i }
· 使用定理 `Disjoint.inf_right'`：Disjoint.inf_right' (h : Disjoint a b) : Disjoint a
 (c ⊓ b)
· 使用定理 `Disjoint.inf_left'`：Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c 
⊓ a) b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem disjoint_splitLower_splitUpper (I : Box ι) (i : ι) (x : ℝ) :
    Disjoint (I.splitLower i x) (I.splitUpper i x) := by
  rw [← disjoint_withBotCoe, coe_splitLower, coe_splitUpper]
  refine (Disjoint.inf_left' _ ?_).inf_right' _
  rw [Set.disjoint_left]
  exact fun y (hle : y i ≤ x) hlt => not_lt_of_ge hle hlt
/-
**BoxIntegral.Box.splitLower_ne_splitUpper** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Box`。
形式化陈述：splitLower_ne_splitUpper (I : Box ι) (i : ι) (x : Real) : I.splitLower i x
 != I.splitUpper i x
参数：I : Box ι；i : ι；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Box.splitUpper_eq_self`：splitUpper_eq_self : I.splitUpper i 
x = I ↔ x <= I.lower i
· 使用定理 `BoxIntegral.Box.splitLower_eq_bot`：splitLower_eq_bot {i x} : I.splitLowe
r i x = ⊥ ↔ x <= I.lower i
· 使用定理 `WithBot.bot_ne_coe`：bot_ne_coe : ⊥ != (a : WithBot α)
· 使用定理 `Disjoint.ne`：Disjoint.ne (ha : a != ⊥) (hab : Disjoint a b) : a != b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `BoxIntegral.Box.disjoint_splitLower_splitUpper`：disjoint_splitLower_spli
tUpper (I : Box ι) (i : ι) (x : Real) : Disjoint (I.splitLower i x) (I.splitUppe
r i x)
-/
theorem splitLower_ne_splitUpper (I : Box ι) (i : ι) (x : ℝ) :
    I.splitLower i x ≠ I.splitUpper i x := by
  rcases le_or_gt x (I.lower i) with h | _
  · rw [splitUpper_eq_self.2 h, splitLower_eq_bot.2 h]
    exact WithBot.bot_ne_coe
  · refine (disjoint_splitLower_splitUpper I i x).ne ?_
    rwa [Ne, splitLower_eq_bot, not_le]

end Box

namespace Prepartition

variable {I J : Box ι} {i : ι} {x : ℝ}

open scoped Classical in
/-- The partition of `I : Box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
/-
**BoxIntegral.Prepartition.split** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Preparti
tion`。
形式化陈述：split (I : Box ι) (i : ι) (x : Real) : Prepartition I
参数：I : Box ι；i : ι；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partition of `I : Box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x 
i < y}`.
One of these boxes can be empty, then this partition is just the single-box part
ition `⊤`.
-/
def split (I : Box ι) (i : ι) (x : ℝ) : Prepartition I :=
  ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts [Box.splitLower_le, Box.splitUpper_le])
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and, Set.mem_singleton_iff,
        pairwise_insert_of_symm, pairwise_singleton]
      rintro J rfl -
      exact I.disjoint_splitLower_splitUpper i x)

@[simp]
/-
**BoxIntegral.Prepartition.mem_split_iff** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：mem_split_iff : J in split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpp
er i x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_split_iff : J ∈ split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x := by
  simp [split]
/-
**BoxIntegral.Prepartition.mem_split_iff'** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：mem_split_iff' : J in split I i x ↔ (J : Set (ι -> Real)) = ↑I inter { y |
 y i <= x } ∨ (J : Set (ι -> Real)) = ↑I inter { y | x < y i }
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
· 使用定理 `BoxIntegral.Box.coe_splitLower`：coe_splitLower : (splitLower I i x : Set
 (ι -> Real)) = ↑I inter { y | y i <= x }
· 使用定理 `BoxIntegral.Box.coe_splitUpper`：coe_splitUpper : (splitUpper I i x : Set
 (ι -> Real)) = ↑I inter { y | x < y i }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_split_iff' : J ∈ split I i x ↔
    (J : Set (ι → ℝ)) = ↑I ∩ { y | y i ≤ x } ∨ (J : Set (ι → ℝ)) = ↑I ∩ { y | x < y i } := by
  simp [mem_split_iff, ← Box.withBotCoe_inj]

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_split** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：iUnion_split (I : Box ι) (i : ι) (x : Real) : (split I i x).iUnion = I
参数：I : Box ι；i : ι；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_ofWithBot`：iUnion_ofWithBot (boxes : Fin
set (WithBot (Box ι))) (le_of_mem : forall J in boxes, (J : WithBot (Box ι)) <= 
I) (pairwise_disjoint : Set.Pai…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.Box.coe_splitLower`：coe_splitLower : (splitLower I i x : Set
 (ι -> Real)) = ↑I inter { y | y i <= x }
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `BoxIntegral.Box.coe_splitUpper`：coe_splitUpper : (splitUpper I i x : Set
 (ι -> Real)) = ↑I inter { y | x < y i }
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_split (I : Box ι) (i : ι) (x : ℝ) : (split I i x).iUnion = I := by
  simp [split, ← inter_union_distrib_left, ← ofPred_or, le_or_gt]
/-
**BoxIntegral.Prepartition.isPartitionSplit** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：isPartitionSplit (I : Box ι) (i : ι) (x : Real) : IsPartition (split I i x
)
参数：I : Box ι；i : ι；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.isPartition_iff_iUnion_eq`：isPartition_iff_iUni
on_eq {π : Prepartition I} : π.IsPartition ↔ π.iUnion = I
· 使用定理 `BoxIntegral.Prepartition.iUnion_split`：iUnion_split (I : Box ι) (i : ι) 
(x : Real) : (split I i x).iUnion = I
-/
theorem isPartitionSplit (I : Box ι) (i : ι) (x : ℝ) : IsPartition (split I i x) :=
  isPartition_iff_iUnion_eq.2 <| iUnion_split I i x

set_option backward.isDefEq.respectTransparency false in
/-
**BoxIntegral.Prepartition.sum_split_boxes** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：sum_split_boxes {M : Type*} [AddCommMonoid M] (I : Box ι) (i : ι) (x : Rea
l) (f : Box ι -> M) : (∑ J in (split I i x).boxes, f J) = (I.splitLower i x).eli
m' 0 f + (I.splitUpper i x).elim' 0 f
参数：I : Box ι；i : ι；x : Real；f : Box ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.split.eq_1`：∀ {ι : Type u_1} (I : BoxIntegral.B
ox ι) (i : ι) (x : ℝ),   BoxIntegral.Prepartition.split I i x = BoxIntegral.Prep
artition.ofWithBot {I.spl…
· 使用定理 `BoxIntegral.Prepartition.sum_ofWithBot`：sum_ofWithBot {M : Type*} [AddCo
mmMonoid M] (boxes : Finset (WithBot (Box ι))) (le_of_mem : forall J in boxes, (
J : WithBot (Box ι)) <= I) (…
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `BoxIntegral.Box.splitLower_ne_splitUpper`：splitLower_ne_splitUpper (I : 
Box ι) (i : ι) (x : Real) : I.splitLower i x != I.splitUpper i x
-/
theorem sum_split_boxes {M : Type*} [AddCommMonoid M] (I : Box ι) (i : ι) (x : ℝ) (f : Box ι → M) :
    (∑ J ∈ (split I i x).boxes, f J) =
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f := by
  classical
  rw [split, sum_ofWithBot, Finset.sum_pair (I.splitLower_ne_splitUpper i x)]

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
/-
**BoxIntegral.Prepartition.split_of_notMem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `BoxInt
egral.Prepartition`。
形式化陈述：split_of_notMem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = 
⊤
参数：h : x ∉ Ioo (I.lower i) (I.upper i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.IsPartition.eq_of_boxes_subset`：eq_of_boxes_sub
set (h₁ : π₁.IsPartition) (h₂ : π₁.boxes subseteq π₂.boxes) : π₁ = π₂
· 使用定理 `BoxIntegral.Prepartition.isPartitionTop`：isPartitionTop (I : Box ι) : Is
Partition (⊤ : Prepartition I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.mem_boxes`：mem_boxes : J in π.boxes ↔ J in π
· 使用定理 `BoxIntegral.Prepartition.mem_split_iff`：mem_split_iff : J in split I i x
 ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `BoxIntegral.Box.splitUpper_eq_self`：splitUpper_eq_self : I.splitUpper i 
x = I ↔ x <= I.lower i
· 使用定理 `BoxIntegral.Box.splitLower_eq_self`：splitLower_eq_self : I.splitLower i 
x = I ↔ I.upper i <= x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_top`：mem_top : J in (⊤ : Prepartition I) ↔ 
J = I

--- 原说明 ---
If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not sp
lit `I`.
-/
theorem split_of_notMem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ := by
  refine ((isPartitionTop I).eq_of_boxes_subset fun J hJ => ?_).symm
  rcases mem_top.1 hJ with rfl; clear hJ
  rw [mem_boxes, mem_split_iff]
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  cases h <;> [right; left]
  · rwa [eq_comm, Box.splitUpper_eq_self]
  · rwa [eq_comm, Box.splitLower_eq_self]
/-
**BoxIntegral.Prepartition.coe_eq_of_mem_split_of_mem_le** 是 Mathlib 中的一个定理，位于命名
空间 `BoxIntegral.Prepartition`。
形式化陈述：coe_eq_of_mem_split_of_mem_le {y : ι -> Real} (h₁ : J in split I i x) (h₂ 
: y in J) (h₃ : y i <= x) : (J : Set (ι -> Real)) = ↑I inter { y | y i <= x }
参数：h₁ : J in split I i x；h₂ : y in J；h₃ : y i <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_split_iff'`：mem_split_iff' : J in split I i
 x ↔ (J : Set (ι -> Real)) = ↑I inter { y | y i <= x } ∨ (J : Set (ι -> Real)) =
 ↑I inter { y | x < y i }
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Box.mem_coe`：mem_coe : x in (I : Set (ι -> Real)) ↔ x in I
-/
theorem coe_eq_of_mem_split_of_mem_le {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J)
    (h₃ : y i ≤ x) : (J : Set (ι → ℝ)) = ↑I ∩ { y | y i ≤ x } := by
  refine (mem_split_iff'.1 h₁).resolve_right fun H => ?_
  rw [← Box.mem_coe, H] at h₂
  exact h₃.not_gt h₂.2
/-
**BoxIntegral.Prepartition.coe_eq_of_mem_split_of_lt_mem** 是 Mathlib 中的一个定理，位于命名
空间 `BoxIntegral.Prepartition`。
形式化陈述：coe_eq_of_mem_split_of_lt_mem {y : ι -> Real} (h₁ : J in split I i x) (h₂ 
: y in J) (h₃ : x < y i) : (J : Set (ι -> Real)) = ↑I inter { y | x < y i }
参数：h₁ : J in split I i x；h₂ : y in J；h₃ : x < y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Prepartition.mem_split_iff'`：mem_split_iff' : J in split I i
 x ↔ (J : Set (ι -> Real)) = ↑I inter { y | y i <= x } ∨ (J : Set (ι -> Real)) =
 ↑I inter { y | x < y i }
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Box.mem_coe`：mem_coe : x in (I : Set (ι -> Real)) ↔ x in I
-/
theorem coe_eq_of_mem_split_of_lt_mem {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J)
    (h₃ : x < y i) : (J : Set (ι → ℝ)) = ↑I ∩ { y | x < y i } := by
  refine (mem_split_iff'.1 h₁).resolve_left fun H => ?_
  rw [← Box.mem_coe, H] at h₂
  exact h₃.not_ge h₂.2

@[simp]
/-
**BoxIntegral.Prepartition.restrict_split** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral
.Prepartition`。
形式化陈述：restrict_split (h : I <= J) (i : ι) (x : Real) : (split J i x).restrict I 
= split I i x
参数：h : I <= J；i : ι；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.eq_of_boxes_subset`：eq_of_boxes_sub
set (h₁ : π₁.IsPartition) (h₂ : π₁.boxes subseteq π₂.boxes) : π₁ = π₂
· 使用定理 `BoxIntegral.Prepartition.IsPartition.restrict`：∀ {ι : Type u_1} {I J : B
oxIntegral.Box ι} {π : BoxIntegral.Prepartition I},   π.IsPartition → J ≤ I → (π
.restrict J).IsPartition
· 使用定理 `BoxIntegral.Prepartition.isPartitionSplit`：isPartitionSplit (I : Box ι) 
(i : ι) (x : Real) : IsPartition (split I i x)
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.inter_left_comm`：inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ i
nter s₃) = s₂ inter (s₁ inter s₃)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem restrict_split (h : I ≤ J) (i : ι) (x : ℝ) : (split J i x).restrict I = split I i x := by
  refine ((isPartitionSplit J i x).restrict h).eq_of_boxes_subset ?_
  simp only [Finset.subset_iff, mem_boxes, mem_restrict', mem_split_iff']
  have : ∀ s, (I ∩ s : Set (ι → ℝ)) ⊆ J := fun s => inter_subset_left.trans h
  rintro J₁ ⟨J₂, H₂ | H₂, H₁⟩ <;> [left; right] <;>
    simp [H₁, H₂, inter_left_comm (I : Set (ι → ℝ)), this]
/-
**BoxIntegral.Prepartition.inf_split** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：inf_split (π : Prepartition I) (i : ι) (x : Real) : π ⊓ split I i x = π.bi
Union fun J => split J i x
参数：π : Prepartition I；i : ι；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.biUnion_congr_of_le`：biUnion_congr_of_le (h : π
₁ = π₂) (hi : forall J <= I, πi₁ J = πi₂ J) : π₁.biUnion πi₁ = π₂.biUnion πi₂
· 使用定理 `BoxIntegral.Prepartition.restrict_split`：restrict_split (h : I <= J) (i 
: ι) (x : Real) : (split J i x).restrict I = split I i x
-/
theorem inf_split (π : Prepartition I) (i : ι) (x : ℝ) :
    π ⊓ split I i x = π.biUnion fun J => split J i x :=
  biUnion_congr_of_le rfl fun _ hJ => restrict_split hJ i x

/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
/-
**BoxIntegral.Prepartition.splitMany** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：splitMany (I : Box ι) (s : Finset (ι × Real)) : Prepartition I
参数：I : Box ι；s : Finset (ι × Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by 
the pair
`(i x)`.
-/
def splitMany (I : Box ι) (s : Finset (ι × ℝ)) : Prepartition I :=
  s.inf fun p => split I p.1 p.2

@[simp]
/-
**BoxIntegral.Prepartition.splitMany_empty** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.Prepartition`。
形式化陈述：splitMany_empty (I : Box ι) : splitMany I ∅ = ⊤
参数：I : Box ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem splitMany_empty (I : Box ι) : splitMany I ∅ = ⊤ :=
  rfl

open scoped Classical in
@[simp]
/-
**BoxIntegral.Prepartition.splitMany_insert** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：splitMany_insert (I : Box ι) (s : Finset (ι × Real)) (p : ι × Real) : spli
tMany I (insert p s) = splitMany I s ⊓ split I p.1 p.2
参数：I : Box ι；s : Finset (ι × Real)；p : ι × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.splitMany.eq_1`：∀ {ι : Type u_1} (I : BoxIntegr
al.Box ι) (s : Finset (ι × ℝ)),   BoxIntegral.Prepartition.splitMany I s = s.inf
 fun p => BoxIntegral.Prepart…
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem splitMany_insert (I : Box ι) (s : Finset (ι × ℝ)) (p : ι × ℝ) :
    splitMany I (insert p s) = splitMany I s ⊓ split I p.1 p.2 := by
  rw [splitMany, Finset.inf_insert, inf_comm, splitMany]
/-
**BoxIntegral.Prepartition.splitMany_le_split** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.Prepartition`。
形式化陈述：splitMany_le_split (I : Box ι) {s : Finset (ι × Real)} {p : ι × Real} (hp 
: p in s) : splitMany I s <= split I p.1 p.2
参数：I : Box ι；ι × Real；hp : p in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
-/
theorem splitMany_le_split (I : Box ι) {s : Finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
    splitMany I s ≤ split I p.1 p.2 :=
  Finset.inf_le hp
/-
**BoxIntegral.Prepartition.isPartition_splitMany** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.Prepartition`。
形式化陈述：isPartition_splitMany (I : Box ι) (s : Finset (ι × Real)) : IsPartition (s
plitMany I s)
参数：I : Box ι；s : Finset (ι × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.splitMany_insert`：splitMany_insert (I : Box ι) 
(s : Finset (ι × Real)) (p : ι × Real) : splitMany I (insert p s) = splitMany I 
s ⊓ split I p.1 p.2
· 使用定理 `BoxIntegral.Prepartition.inf_split`：inf_split (π : Prepartition I) (i : 
ι) (x : Real) : π ⊓ split I i x = π.biUnion fun J => split J i x
· 使用定理 `BoxIntegral.Prepartition.IsPartition.biUnion`：∀ {ι : Type u_1} {I : BoxI
ntegral.Box ι} {π : BoxIntegral.Prepartition I}   {πi : (J : BoxIntegral.Box ι) 
→ BoxIntegral.Prepartition J},   π…
· 使用定理 `BoxIntegral.Prepartition.isPartitionSplit`：isPartitionSplit (I : Box ι) 
(i : ι) (x : Real) : IsPartition (split I i x)
-/
theorem isPartition_splitMany (I : Box ι) (s : Finset (ι × ℝ)) : IsPartition (splitMany I s) := by
  classical
  exact Finset.induction_on s (by simp only [splitMany_empty, isPartitionTop]) fun a s _ hs => by
    simpa only [splitMany_insert, inf_split] using hs.biUnion fun J _ => isPartitionSplit _ _ _

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_splitMany** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegr
al.Prepartition`。
形式化陈述：iUnion_splitMany (I : Box ι) (s : Finset (ι × Real)) : (splitMany I s).iUn
ion = I
参数：I : Box ι；s : Finset (ι × Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
· 使用定理 `BoxIntegral.Prepartition.isPartition_splitMany`：isPartition_splitMany (I
 : Box ι) (s : Finset (ι × Real)) : IsPartition (splitMany I s)
-/
theorem iUnion_splitMany (I : Box ι) (s : Finset (ι × ℝ)) : (splitMany I s).iUnion = I :=
  (isPartition_splitMany I s).iUnion_eq
/-
**BoxIntegral.Prepartition.inf_splitMany** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.
Prepartition`。
形式化陈述：inf_splitMany {I : Box ι} (π : Prepartition I) (s : Finset (ι × Real)) : π
 ⊓ splitMany I s = π.biUnion fun J => splitMany J s
参数：π : Prepartition I；s : Finset (ι × Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `BoxIntegral.Prepartition.biUnion_top`：biUnion_top : (π.biUnion fun _ => 
⊤) = π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BoxIntegral.Prepartition.splitMany_insert`：splitMany_insert (I : Box ι) 
(s : Finset (ι × Real)) (p : ι × Real) : splitMany I (insert p s) = splitMany I 
s ⊓ split I p.1 p.2
· 使用定理 `BoxIntegral.Prepartition.biUnion_congr`：biUnion_congr (h : π₁ = π₂) (hi 
: forall J in π₁, πi₁ J = πi₂ J) : π₁.biUnion πi₁ = π₂.biUnion πi₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.inf_split`：inf_split (π : Prepartition I) (i : 
ι) (x : Real) : π ⊓ split I i x = π.biUnion fun J => split J i x
· 使用定理 `BoxIntegral.Prepartition.biUnion_assoc`：biUnion_assoc (πi : forall J, Pr
epartition J) (πi' : Box ι -> forall J : Box ι, Prepartition J) : (π.biUnion fun
 J => (πi J).biUnion (πi' J)…
-/
theorem inf_splitMany {I : Box ι} (π : Prepartition I) (s : Finset (ι × ℝ)) :
    π ⊓ splitMany I s = π.biUnion fun J => splitMany J s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s _ ihp => simp_rw [splitMany_insert, ← inf_assoc, ihp, inf_split, biUnion_assoc]

open scoped Classical in
/-- Let `s : Finset (ι × ℝ)` be a set of hyperplanes `{x : ι → ℝ | x i = r}` in `ι → ℝ` encoded as
pairs `(i, r)`. Suppose that this set contains all faces of a box `J`. The hyperplanes of `s` split
a box `I` into subboxes. Let `Js` be one of them. If `J` and `Js` have nonempty intersection, then
`Js` is a subbox of `J`. -/
/-
**BoxIntegral.Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitMany** 是 Ma
thlib 中的一个定理，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：not_disjoint_imp_le_of_subset_of_mem_splitMany {I J Js : Box ι} {s : Finse
t (ι × Real)} (H : forall i, {(i, J.lower i), (i, J.upper i)} subseteq s) (HJs :
 Js in splitMany I s) (Hn : ¬Disjoint (J : WithBot (Box ι)) Js) : Js <= J
参数：ι × Real；H : forall i, {(i, J.lower i), (i, J.upper i)} subseteq s；HJs : Js i
n splitMany I s；Hn : ¬Disjoint (J : WithBot (Box ι)) Js。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.Box.not_disjoint_coe_iff_nonempty_inter`：not_disjoint_coe_if
f_nonempty_inter : ¬Disjoint (I : WithBot (Box ι)) J ↔ (I inter J : Set (ι -> Re
al)).Nonempty
· 使用定理 `BoxIntegral.Prepartition.splitMany_le_split`：splitMany_le_split (I : Box
 ι) {s : Finset (ι × Real)} {p : ι × Real} (hp : p in s) : splitMany I s <= spli
t I p.1 p.2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.Prepartition.coe_eq_of_mem_split_of_lt_mem`：coe_eq_of_mem_sp
lit_of_lt_mem {y : ι -> Real} (h₁ : J in split I i x) (h₂ : y in J) (h₃ : x < y 
i) : (J : Set (ι -> Real)) = ↑I inter { y | …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Box.coe_subset_coe`：coe_subset_coe : (I : Set (ι -> Real)) s
ubseteq J ↔ I <= J
· 使用定理 `BoxIntegral.Prepartition.coe_eq_of_mem_split_of_mem_le`：coe_eq_of_mem_sp
lit_of_mem_le {y : ι -> Real} (h₁ : J in split I i x) (h₂ : y in J) (h₃ : y i <=
 x) : (J : Set (ι -> Real)) = ↑I inter { y |…

--- 原说明 ---
Let `s : Finset (ι × ℝ)` be a set of hyperplanes `{x : ι → ℝ | x i = r}` in `ι →
 ℝ` encoded as
pairs `(i, r)`. Suppose that this set contains all faces of a box `J`. The hyper
planes of `s` split
a box `I` into subboxes. Let `Js` be one of them. If `J` and `Js` have nonempty 
intersection, then
`Js` is a subbox of `J`.
-/
theorem not_disjoint_imp_le_of_subset_of_mem_splitMany {I J Js : Box ι} {s : Finset (ι × ℝ)}
    (H : ∀ i, {(i, J.lower i), (i, J.upper i)} ⊆ s) (HJs : Js ∈ splitMany I s)
    (Hn : ¬Disjoint (J : WithBot (Box ι)) Js) : Js ≤ J := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at H
  rcases Box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩
  refine fun y hy i => ⟨?_, ?_⟩
  · rcases splitMany_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.lower i), Hle⟩
    have := Hle hxs
    rw [← Box.coe_subset_coe, coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1] at Hle
    exact (Hle hy).2
  · rcases splitMany_le_split I (H i).2 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.upper i), Hle⟩
    have := Hle hxs
    rw [← Box.coe_subset_coe, coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2] at Hle
    exact (Hle hy).2

section Finite

variable [Finite ι]

/-- Let `s` be a finite set of boxes in `ℝⁿ = ι → ℝ`. Then there exists a finite set `t₀` of
hyperplanes (namely, the set of all hyperfaces of boxes in `s`) such that for any `t ⊇ t₀`
and any box `I` in `ℝⁿ` the following holds. The hyperplanes from `t` split `I` into subboxes.
Let `J'` be one of them, and let `J` be one of the boxes in `s`. If these boxes have a nonempty
intersection, then `J' ≤ J`. -/
/-
**BoxIntegral.Prepartition.eventually_not_disjoint_imp_le_of_mem_splitMany** 是 M
athlib 中的一个定理，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：eventually_not_disjoint_imp_le_of_mem_splitMany (s : Finset (Box ι)) : for
allᶠ t : Finset (ι × Real) in atTop, forall (I : Box ι), forall J in s, forall J
' in splitMany I t, ¬Disjoint (J : WithBot (Box ι)) J' -> J' <= J
参数：s : Finset (Box ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `BoxIntegral.Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitMany`
：not_disjoint_imp_le_of_subset_of_mem_splitMany {I J Js : Box ι} {s : Finset (ι 
× Real)} (H : forall i, {(i, J.lower i), (i, J.upper i)} subs…
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Let `s` be a finite set of boxes in `ℝⁿ = ι → ℝ`. Then there exists a finite set
 `t₀` of
hyperplanes (namely, the set of all hyperfaces of boxes in `s`) such that for an
y `t ⊇ t₀`
and any box `I` in `ℝⁿ` the following holds. The hyperplanes from `t` split `I` 
into subboxes.
Let `J'` be one of them, and let `J` be one of the boxes in `s`. If these boxes 
have a nonempty
intersection, then `J' ≤ J`.
-/
theorem eventually_not_disjoint_imp_le_of_mem_splitMany (s : Finset (Box ι)) :
    ∀ᶠ t : Finset (ι × ℝ) in atTop, ∀ (I : Box ι), ∀ J ∈ s, ∀ J' ∈ splitMany I t,
      ¬Disjoint (J : WithBot (Box ι)) J' → J' ≤ J := by
  classical
  cases nonempty_fintype ι
  refine eventually_atTop.2
    ⟨s.biUnion fun J => Finset.univ.biUnion fun i => {(i, J.lower i), (i, J.upper i)},
      fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_splitMany (fun i => ?_) hJ'⟩
  exact fun p hp =>
    ht (Finset.mem_biUnion.2 ⟨J, hJ, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hp⟩⟩)
/-
**BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter** 是 Mathlib 中的一个定理
，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：eventually_splitMany_inf_eq_filter (π : Prepartition I) : forallᶠ t : Fins
et (ι × Real) in atTop, π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J s
ubseteq π.iUnion
参数：π : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `BoxIntegral.Prepartition.eventually_not_disjoint_imp_le_of_mem_splitMany
`：eventually_not_disjoint_imp_le_of_mem_splitMany (s : Finset (Box ι)) : forallᶠ
 t : Finset (ι × Real) in atTop, forall (I : Box ι), forall J …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.Prepartition.biUnion_le_iff`：biUnion_le_iff {πi : forall J, 
Prepartition J} {π' : Prepartition I} : π.biUnion πi <= π' ↔ forall J in π, πi J
 <= π'.restrict J
· 使用定理 `BoxIntegral.Prepartition.ofWithBot_mono`：ofWithBot_mono {boxes₁ : Finset
 (WithBot (Box ι))} {le_of_mem₁ : forall J in boxes₁, (J : WithBot (Box ι)) <= I
} {pairwise_disjoint₁ : Set.P…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `BoxIntegral.Prepartition.subset_iUnion`：subset_iUnion (h : J in π) : ↑J 
subseteq π.iUnion
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.Prepartition.mem_filter`：mem_filter {p : Box ι -> Prop} : J 
in π.filter p ↔ J in π ∧ p J
· 使用定理 `BoxIntegral.Box.upper_mem`：upper_mem : I.upper in I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Box.not_disjoint_coe_iff_nonempty_inter`：not_disjoint_coe_if
f_nonempty_inter : ¬Disjoint (I : WithBot (Box ι)) J ↔ (I inter J : Set (ι -> Re
al)).Nonempty
· 使用定理 `BoxIntegral.Prepartition.filter_le`：filter_le (π : Prepartition I) (p : 
Box ι -> Prop) : π.filter p <= π
-/
theorem eventually_splitMany_inf_eq_filter (π : Prepartition I) :
    ∀ᶠ t : Finset (ι × ℝ) in atTop,
      π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J ⊆ π.iUnion := by
  refine (eventually_not_disjoint_imp_le_of_mem_splitMany π.boxes).mono fun t ht => ?_
  refine le_antisymm ((biUnion_le_iff _).2 fun J hJ => ?_) (le_inf (fun J hJ => ?_) (filter_le _ _))
  · refine ofWithBot_mono ?_
    simp only [Finset.mem_image, mem_boxes, mem_filter]
    rintro _ ⟨J₁, h₁, rfl⟩ hne
    refine ⟨_, ⟨J₁, ⟨h₁, Subset.trans ?_ (π.subset_iUnion hJ)⟩, rfl⟩, le_rfl⟩
    exact ht I J hJ J₁ h₁ (mt disjoint_iff.1 hne)
  · rw [mem_filter] at hJ
    rcases Set.mem_iUnion₂.1 (hJ.2 J.upper_mem) with ⟨J', hJ', hmem⟩
    refine ⟨J', hJ', ht I _ hJ' _ hJ.1 <| Box.not_disjoint_coe_iff_nonempty_inter.2 ?_⟩
    exact ⟨J.upper, hmem, J.upper_mem⟩
/-
**BoxIntegral.Prepartition.exists_splitMany_inf_eq_filter_of_finite** 是 Mathlib 
中的一个定理，位于命名空间 `BoxIntegral.Prepartition`。
形式化陈述：exists_splitMany_inf_eq_filter_of_finite (s : Set (Prepartition I)) (hs : 
s.Finite) : exists t : Finset (ι × Real), forall π in s, π ⊓ splitMany I t = (sp
litMany I t).filter fun J => ↑J subseteq π.iUnion
参数：s : Set (Prepartition I)；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter`：eventually_
splitMany_inf_eq_filter (π : Prepartition I) : forallᶠ t : Finset (ι × Real) in 
atTop, π ⊓ splitMany I t = (splitMany I t).filter…
-/
theorem exists_splitMany_inf_eq_filter_of_finite (s : Set (Prepartition I)) (hs : s.Finite) :
    ∃ t : Finset (ι × ℝ),
      ∀ π ∈ s, π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J ⊆ π.iUnion :=
  haveI := fun π (_ : π ∈ s) => eventually_splitMany_inf_eq_filter π
  (hs.eventually_all.2 this).exists

/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`splitMany I s ≤ π`. -/
/-
**BoxIntegral.Prepartition.IsPartition.exists_splitMany_le** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} [Finite ι] {I : BoxIntegral.Box ι} {π : BoxIntegral.Prepa
rtition I},   π.IsPartition → ∃ s, BoxIntegral.Prepartition.splitMany I s ≤ π
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `BoxIntegral.Prepartition.filter_of_true`：filter_of_true {p : Box ι -> Pr
op} (hp : forall J in π, p J) : π.filter p = π
· 使用定理 `BoxIntegral.Prepartition.le_of_mem`：le_of_mem (hJ : J in π) : J <= I
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter`：eventually_
splitMany_inf_eq_filter (π : Prepartition I) : forallᶠ t : Finset (ι × Real) in 
atTop, π ⊓ splitMany I t = (splitMany I t).filter…

--- 原说明 ---
If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes 
such that
`splitMany I s ≤ π`.
-/
theorem IsPartition.exists_splitMany_le {I : Box ι} {π : Prepartition I} (h : IsPartition π) :
    ∃ s, splitMany I s ≤ π := by
  refine (eventually_splitMany_inf_eq_filter π).exists.imp fun s hs => ?_
  rwa [h.iUnion_eq, filter_of_true, inf_eq_right] at hs
  exact fun J hJ => le_of_mem _ hJ

/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.iUnion`. -/
/-
**BoxIntegral.Prepartition.exists_iUnion_eq_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.Prepartition`。
形式化陈述：exists_iUnion_eq_sdiff (π : Prepartition I) : exists π' : Prepartition I, 
π'.iUnion = ↑I \ π.iUnion
参数：π : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter`：eventually_
splitMany_inf_eq_filter (π : Prepartition I) : forallᶠ t : Finset (ι × Real) in 
atTop, π ⊓ splitMany I t = (splitMany I t).filter…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_filter_not`：iUnion_filter_not (π : Prepa
rtition I) (p : Box ι -> Prop) : (π.filter fun J => ¬p J).iUnion = π.iUnion \ (π
.filter p).iUnion
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_splitMany`：iUnion_splitMany (I : Box ι) 
(s : Finset (ι × Real)) : (splitMany I s).iUnion = I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.iUnion_inf`：iUnion_inf (π₁ π₂ : Prepartition I)
 : (π₁ ⊓ π₂).iUnion = π₁.iUnion inter π₂.iUnion
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For every prepartition `π` of `I` there exists a prepartition that covers exactl
y
`I \ π.iUnion`.
-/
theorem exists_iUnion_eq_sdiff (π : Prepartition I) :
    ∃ π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion := by
  rcases π.eventually_splitMany_inf_eq_filter.exists with ⟨s, hs⟩
  use (splitMany I s).filter fun J => ¬(J : Set (ι → ℝ)) ⊆ π.iUnion
  simp [← hs]

@[deprecated (since := "2026-06-03")] alias exists_iUnion_eq_diff := exists_iUnion_eq_sdiff

/-- If `π` is a prepartition of `I`, then `π.compl` is a prepartition of `I`
such that `π.compl.iUnion = I \ π.iUnion`. -/
/-
**BoxIntegral.Prepartition.compl** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Preparti
tion`。
形式化陈述：compl (π : Prepartition I) : Prepartition I
参数：π : Prepartition I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.exists_iUnion_eq_sdiff`：exists_iUnion_eq_sdiff 
(π : Prepartition I) : exists π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion

--- 原说明 ---
If `π` is a prepartition of `I`, then `π.compl` is a prepartition of `I`
such that `π.compl.iUnion = I \ π.iUnion`.
-/
def compl (π : Prepartition I) : Prepartition I :=
  π.exists_iUnion_eq_sdiff.choose

@[simp]
/-
**BoxIntegral.Prepartition.iUnion_compl** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.P
repartition`。
形式化陈述：iUnion_compl (π : Prepartition I) : π.compl.iUnion = ↑I \ π.iUnion
参数：π : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `BoxIntegral.Prepartition.exists_iUnion_eq_sdiff`：exists_iUnion_eq_sdiff 
(π : Prepartition I) : exists π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion
-/
theorem iUnion_compl (π : Prepartition I) : π.compl.iUnion = ↑I \ π.iUnion :=
  π.exists_iUnion_eq_sdiff.choose_spec

/-- Since the definition of `BoxIntegral.Prepartition.compl` uses `Exists.choose`,
the result depends only on `π.iUnion`. -/
/-
**BoxIntegral.Prepartition.compl_congr** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Pr
epartition`。
形式化陈述：compl_congr {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π₂.iUnion) : π₁.comp
l = π₂.compl
参数：h : π₁.iUnion = π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.exists_iUnion_eq_sdiff`：exists_iUnion_eq_sdiff 
(π : Prepartition I) : exists π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion

--- 原说明 ---
Since the definition of `BoxIntegral.Prepartition.compl` uses `Exists.choose`,
the result depends only on `π.iUnion`.
-/
theorem compl_congr {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π₂.iUnion) : π₁.compl = π₂.compl := by
  dsimp only [compl]
  congr 1
  rw [h]
/-
**BoxIntegral.Prepartition.IsPartition.compl_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.Prepartition.IsPartition`。
形式化陈述：∀ {ι : Type u_1} {I : BoxIntegral.Box ι} [inst : Finite ι] {π : BoxIntegra
l.Prepartition I}, π.IsPartition → π.compl = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.iUnion_eq_empty`：iUnion_eq_empty : π₁.iUnion = 
∅ ↔ π₁ = ⊥
· 使用定理 `BoxIntegral.Prepartition.iUnion_compl`：iUnion_compl (π : Prepartition I)
 : π.compl.iUnion = ↑I \ π.iUnion
· 使用定理 `BoxIntegral.Prepartition.IsPartition.iUnion_eq`：iUnion_eq (h : π.IsParti
tion) : π.iUnion = I
· 使用定理 `Set.sdiff_self`：sdiff_self {s : Set α} : s \ s = ∅
-/
theorem IsPartition.compl_eq_bot {π : Prepartition I} (h : IsPartition π) : π.compl = ⊥ := by
  rw [← iUnion_eq_empty, iUnion_compl, h.iUnion_eq, sdiff_self]

@[simp]
/-
**BoxIntegral.Prepartition.compl_top** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Prep
artition`。
形式化陈述：compl_top : (⊤ : Prepartition I).compl = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.Prepartition.IsPartition.compl_eq_bot`：∀ {ι : Type u_1} {I :
 BoxIntegral.Box ι} [inst : Finite ι] {π : BoxIntegral.Prepartition I}, π.IsPart
ition → π.compl = ⊥
· 使用定理 `BoxIntegral.Prepartition.isPartitionTop`：isPartitionTop (I : Box ι) : Is
Partition (⊤ : Prepartition I)
-/
theorem compl_top : (⊤ : Prepartition I).compl = ⊥ :=
  (isPartitionTop I).compl_eq_bot

end Finite

end Prepartition

end BoxIntegral

