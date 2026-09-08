/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Ray
public import Mathlib.Topology.Order.LocalExtr

/-!
# (Local) maximums in a normed space

In this file we prove the following lemma, see `IsMaxFilter.norm_add_sameRay`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a maximum along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `IsMaxFilter`:
`IsMaxOn`, `IsLocalMaxOn`, and `IsLocalMax`.

## Tags

local maximum, normed space
-/

public section


variable {α X E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

section

variable {f : α → E} {l : Filter α} {s : Set α} {c : α} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has
a maximum along `l` at `c`. -/
/-
**IsMaxFilter.norm_add_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.norm_add_sameRay (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRa
y Real (f c) y) : IsMaxFilter (fun x => ‖f x + y‖) l c
参数：h : IsMaxFilter (norm ∘ f) l c；hy : SameRay Real (f c) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.norm_add`：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `
l` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `fun x => ‖f
 x + y‖` has
a maximum along `l` at `c`.
-/
theorem IsMaxFilter.norm_add_sameRay (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay ℝ (f c) y) :
    IsMaxFilter (fun x => ‖f x + y‖) l c :=
  h.mono fun x hx => by dsimp at hx ⊢; grw [hy.norm_add, norm_add_le, hx]

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c`, then the function `fun x => ‖f x + f c‖` has a maximum along `l` at `c`. -/
/-
**IsMaxFilter.norm_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) : IsMaxFilter (
fun x => ‖f x + f c‖) l c
参数：h : IsMaxFilter (norm ∘ f) l c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_sameRay`：IsMaxFilter.norm_add_sameRay (h : IsMaxFil
ter (norm ∘ f) l c) (hy : SameRay Real (f c) y) : IsMaxFilter (fun x => ‖f x + y
‖) l c
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `
l` at a point
`c`, then the function `fun x => ‖f x + f c‖` has a maximum along `l` at `c`.
-/
theorem IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) :
    IsMaxFilter (fun x => ‖f x + f c‖) l c :=
  IsMaxFilter.norm_add_sameRay h SameRay.rfl

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c` and
`y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a maximum
on `s` at `c`. -/
/-
**IsMaxOn.norm_add_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.norm_add_sameRay (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay Real (
f c) y) : IsMaxOn (fun x => ‖f x + y‖) s c
参数：h : IsMaxOn (norm ∘ f) s c；hy : SameRay Real (f c) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_sameRay`：IsMaxFilter.norm_add_sameRay (h : IsMaxFil
ter (norm ∘ f) l c) (hy : SameRay Real (f c) y) : IsMaxFilter (fun x => ‖f x + y
‖) l c

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at 
a point `c` and
`y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖`
 has a maximum
on `s` at `c`.
-/
theorem IsMaxOn.norm_add_sameRay (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c`,
then the function `fun x => ‖f x + f c‖` has a maximum on `s` at `c`. -/
/-
**IsMaxOn.norm_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ‖f 
x + f c‖) s c
参数：h : IsMaxOn (norm ∘ f) s c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_self`：IsMaxFilter.norm_add_self (h : IsMaxFilter (n
orm ∘ f) l c) : IsMaxFilter (fun x => ‖f x + f c‖) l c

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at 
a point `c`,
then the function `fun x => ‖f x + f c‖` has a maximum on `s` at `c`.
-/
theorem IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h

end

variable {f : X → E} {s : Set X} {c : X} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a local
maximum on `s` at `c`. -/
/-
**IsLocalMaxOn.norm_add_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.norm_add_sameRay (h : IsLocalMaxOn (norm ∘ f) s c) (hy : Same
Ray Real (f c) y) : IsLocalMaxOn (fun x => ‖f x + y‖) s c
参数：h : IsLocalMaxOn (norm ∘ f) s c；hy : SameRay Real (f c) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_sameRay`：IsMaxFilter.norm_add_sameRay (h : IsMaxFil
ter (norm ∘ f) l c) (hy : SameRay Real (f c) y) : IsMaxFilter (fun x => ‖f x + y
‖) l c

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `
s` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `fun x => ‖f
 x + y‖` has a local
maximum on `s` at `c`.
-/
theorem IsLocalMaxOn.norm_add_sameRay (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsLocalMaxOn (fun x => ‖f x + y‖) s c :=
  IsMaxFilter.norm_add_sameRay h hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c`, then the function `fun x => ‖f x + f c‖` has a local maximum on `s` at `c`. -/
/-
**IsLocalMaxOn.norm_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) : IsLocalMaxO
n (fun x => ‖f x + f c‖) s c
参数：h : IsLocalMaxOn (norm ∘ f) s c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_self`：IsMaxFilter.norm_add_self (h : IsMaxFilter (n
orm ∘ f) l c) : IsMaxFilter (fun x => ‖f x + f c‖) l c

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `
s` at a point
`c`, then the function `fun x => ‖f x + f c‖` has a local maximum on `s` at `c`.
-/
theorem IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) :
    IsLocalMaxOn (fun x => ‖f x + f c‖) s c :=
  IsMaxFilter.norm_add_self h

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c` and `y` is
a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a local maximum
at `c`. -/
/-
**IsLocalMax.norm_add_sameRay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.norm_add_sameRay (h : IsLocalMax (norm ∘ f) c) (hy : SameRay Re
al (f c) y) : IsLocalMax (fun x => ‖f x + y‖) c
参数：h : IsLocalMax (norm ∘ f) c；hy : SameRay Real (f c) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_sameRay`：IsMaxFilter.norm_add_sameRay (h : IsMaxFil
ter (norm ∘ f) l c) (hy : SameRay Real (f c) y) : IsMaxFilter (fun x => ‖f x + y
‖) l c

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point
 `c` and `y` is
a vector on the same ray as `f c`, then the function `fun x => ‖f x + y‖` has a 
local maximum
at `c`.
-/
theorem IsLocalMax.norm_add_sameRay (h : IsLocalMax (norm ∘ f) c) (hy : SameRay ℝ (f c) y) :
    IsLocalMax (fun x => ‖f x + y‖) c :=
  IsMaxFilter.norm_add_sameRay h hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c`, then the
function `fun x => ‖f x + f c‖` has a local maximum at `c`. -/
/-
**IsLocalMax.norm_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) : IsLocalMax (fun x
 => ‖f x + f c‖) c
参数：h : IsLocalMax (norm ∘ f) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxFilter.norm_add_self`：IsMaxFilter.norm_add_self (h : IsMaxFilter (n
orm ∘ f) l c) : IsMaxFilter (fun x => ‖f x + f c‖) l c

--- 原说明 ---
If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point
 `c`, then the
function `fun x => ‖f x + f c‖` has a local maximum at `c`.
-/
theorem IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) :
    IsLocalMax (fun x => ‖f x + f c‖) c :=
  IsMaxFilter.norm_add_self h
