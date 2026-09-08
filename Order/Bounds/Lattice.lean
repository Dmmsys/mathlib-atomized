/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Set.Lattice.Image

/-!
# Unions and intersections of bounds

Some results about upper and lower bounds over collections of sets.

## Implementation notes

In a separate file as we need to import `Mathlib/Data/Set/Lattice.lean`.

-/

public section

variable {α : Type*} [Preorder α] {ι : Sort*} {s : ι → Set α}

open Set

@[to_dual]
/-
**gc_upperBounds_lowerBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_upperBounds_lowerBounds : GaloisConnection (OrderDual.toDual ∘ upperBou
nds : Set α -> (Set α)ᵒᵈ) (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
theorem gc_upperBounds_lowerBounds : GaloisConnection
    (OrderDual.toDual ∘ upperBounds : Set α → (Set α)ᵒᵈ)
    (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ → Set α) := by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T ↦ forall₂_comm

@[to_dual (attr := simp)]
/-
**upperBounds_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperBounds_iUnion : upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `gc_upperBounds_lowerBounds`：gc_upperBounds_lowerBounds : GaloisConnectio
n (OrderDual.toDual ∘ upperBounds : Set α -> (Set α)ᵒᵈ) (lowerBounds ∘ OrderDual
.ofDual : (Set α…
-/
theorem upperBounds_iUnion :
    upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i) :=
  gc_upperBounds_lowerBounds.l_iSup

@[to_dual]
/-
**isLUB_iUnion_iff_of_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_iUnion_iff_of_isLUB {u : ι -> α} (hs : forall i, IsLUB (s i) (u i)) 
(c : α) : IsLUB (Set.range u) c ↔ IsLUB (⋃ i, s i) c
参数：hs : forall i, IsLUB (s i) (u i)；c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_congr`：isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a
 ↔ IsLUB t a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_iUnion`：range_eq_iUnion {ι} (f : ι -> α) : range f = ⋃ i, {
f i}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `upperBounds_iUnion`：upperBounds_iUnion : upperBounds (⋃ i, s i) = ⋂ i, u
pperBounds (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `upperBounds_singleton`：upperBounds_singleton : upperBounds {a} = Ici a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLUB.upperBounds_eq`：IsLUB.upperBounds_eq (h : IsLUB s a) : upperBounds
 s = Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isLUB_iUnion_iff_of_isLUB {u : ι → α} (hs : ∀ i, IsLUB (s i) (u i)) (c : α) :
    IsLUB (Set.range u) c ↔ IsLUB (⋃ i, s i) c := by
  refine isLUB_congr ?_
  simp_rw [range_eq_iUnion, upperBounds_iUnion, upperBounds_singleton, (hs _).upperBounds_eq]

@[deprecated isGLB_iUnion_iff_of_isGLB (since := "2026-06-04")]
/-
**isGLB_iUnion_iff_of_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_iUnion_iff_of_isLUB {u : ι -> α} (hs : forall i, IsGLB (s i) (u i)) 
(c : α) : IsGLB (Set.range u) c ↔ IsGLB (⋃ i, s i) c
参数：hs : forall i, IsGLB (s i) (u i)；c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_congr`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α} {a : α},
 lowerBounds s = lowerBounds t → (IsGLB s a ↔ IsGLB t a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_iUnion`：range_eq_iUnion {ι} (f : ι -> α) : range f = ⋃ i, {
f i}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `lowerBounds_iUnion`：∀ {α : Type u_1} [inst : Preorder α] {ι : Sort u_2} 
{s : ι → Set α}, lowerBounds (⋃ i, s i) = ⋂ i, lowerBounds (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lowerBounds_singleton`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, low
erBounds {a} = Set.Iic a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsGLB.lowerBounds_eq`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {
a : α}, IsGLB s a → lowerBounds s = Set.Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isGLB_iUnion_iff_of_isLUB {u : ι → α} (hs : ∀ i, IsGLB (s i) (u i)) (c : α) :
    IsGLB (Set.range u) c ↔ IsGLB (⋃ i, s i) c := by
  refine isGLB_congr ?_
  simp_rw [range_eq_iUnion, lowerBounds_iUnion, lowerBounds_singleton, (hs _).lowerBounds_eq]
