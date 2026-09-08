/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Order.Group.Nat

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Linear and semilinear sets

This file defines linear and semilinear sets. In an `AddCommMonoid`, a linear set is a coset of a
finitely generated additive submonoid, and a semilinear set is a finite union of linear sets.

We prove that semilinear sets are closed under union, projection, set addition and additive closure.
We also prove that any semilinear set can be decomposed into a finite union of proper linear sets,
which are linear sets with linearly independent submonoid generators (periods).

## Main Definitions

- `IsLinearSet`: a set is linear if it is a coset of a finitely generated additive submonoid.
- `IsSemilinearSet`: a set is semilinear if it is a finite union of linear sets.
- `IsProperLinearSet`: a linear set is proper if its submonoid generators (periods) are linearly
  independent.
- `IsProperSemilinearSet`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `IsSemilinearSet` is closed under union, projection, set addition and additive closure.
- `IsSemilinearSet.isProperSemilinearSet`: every semilinear set is a finite union of proper linear
  sets.
- `Nat.isSemilinearSet_iff_ultimately_periodic`: A set of `ℕ` is semilinear if and only if it is
  ultimately periodic, i.e. periodic after some number `k`.

## Naming convention

`IsSemilinearSet.proj` projects a semilinear set of `ι ⊕ κ → M` to `ι → M` by taking `Sum.inl` on
the index. It is a special case of `IsSemilinearSet.image`, and is useful in proving semilinearity
of sets in form `{ x | ∃ y, p x y }`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

@[expose] public section

variable {M N ι κ F : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [FunLike F M N] [AddMonoidHomClass F M N] {a : M} {s s₁ s₂ : Set M}

open Set Pointwise AddSubmonoid

/-- A set is linear if it is a coset of a finitely generated additive submonoid. -/
/-
**IsLinearSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLinearSet (s : Set M) : Prop
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is linear if it is a coset of a finitely generated additive submonoid.
-/
def IsLinearSet (s : Set M) : Prop :=
  ∃ (a : M) (t : Set M), t.Finite ∧ s = a +ᵥ (closure t : Set M)

/-- An equivalent expression of `IsLinearSet` in terms of `Finset` instead of `Set.Finite`. -/
/-
**isLinearSet_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLinearSet_iff : IsLinearSet s ↔ exists (a : M) (t : Finset M), s = a +ᵥ 
(closure (t : Set M) : Set M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An equivalent expression of `IsLinearSet` in terms of `Finset` instead of `Set.F
inite`.
-/
theorem isLinearSet_iff :
    IsLinearSet s ↔ ∃ (a : M) (t : Finset M), s = a +ᵥ (closure (t : Set M) : Set M) := by
  simp [IsLinearSet, Finset.exists]

@[simp]
/-
**IsLinearSet.singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.singleton (a : M) : IsLinearSet {a}
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoid.closure_empty`：∀ {M : Type u_1} [inst : AddZeroClass M], Ad
dSubmonoid.closure ∅ = ⊥
· 使用定理 `Set.vadd_set_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β
] {a : α} {b : β}, a +ᵥ {b} = {a +ᵥ b}
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsLinearSet.singleton (a : M) : IsLinearSet {a} :=
  ⟨a, ∅, by simp⟩
/-
**IsLinearSet.closure_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.closure_finset (s : Finset M) : IsLinearSet (closure (s : Set 
M) : Set M)
参数：s : Finset M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsLinearSet.closure_finset (s : Finset M) : IsLinearSet (closure (s : Set M) : Set M) :=
  ⟨0, s, by simp⟩
/-
**IsLinearSet.closure_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.closure_of_finite (hs : s.Finite) : IsLinearSet (closure s : S
et M)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLinearSet.closure_of_finite (hs : s.Finite) :
    IsLinearSet (closure s : Set M) :=
  ⟨0, s, hs, by simp⟩
/-
**isLinearSet_iff_exists_fg_eq_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLinearSet_iff_exists_fg_eq_vadd : IsLinearSet s ↔ exists (a : M) (P : Ad
dSubmonoid M), P.FG ∧ s = a +ᵥ (P : Set M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLinearSet_iff`：isLinearSet_iff : IsLinearSet s ↔ exists (a : M) (t : F
inset M), s = a +ᵥ (closure (t : Set M) : Set M)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isLinearSet_iff_exists_fg_eq_vadd :
    IsLinearSet s ↔ ∃ (a : M) (P : AddSubmonoid M), P.FG ∧ s = a +ᵥ (P : Set M) :=
  isLinearSet_iff.trans (exists_congr fun a =>
    ⟨fun ⟨t, hs⟩ => ⟨_, ⟨t, rfl⟩, hs⟩, fun ⟨P, ⟨t, hP⟩, hs⟩ => ⟨t, by rwa [hP]⟩⟩)
/-
**IsLinearSet.of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : IsLinearSet (P : Set 
M)
参数：hP : P.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLinearSet_iff_exists_fg_eq_vadd`：isLinearSet_iff_exists_fg_eq_vadd : I
sLinearSet s ↔ exists (a : M) (P : AddSubmonoid M), P.FG ∧ s = a +ᵥ (P : Set M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : IsLinearSet (P : Set M) := by
  rw [isLinearSet_iff_exists_fg_eq_vadd]
  exact ⟨0, P, hP, by simp⟩

@[simp]
/-
**IsLinearSet.univ** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearSet`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] [AddMonoid.FG M], IsLinearSet Se
t.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearSet.of_fg`：IsLinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : 
IsLinearSet (P : Set M)
· 使用定理 `AddMonoid.FG.fg_top`：∀ {M : Type u_3} {inst : AddMonoid M} [self : AddMo
noid.FG M], ⊤.FG
-/
protected theorem IsLinearSet.univ [AddMonoid.FG M] : IsLinearSet (univ : Set M) :=
  of_fg AddMonoid.FG.fg_top
/-
**IsLinearSet.vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.vadd (a : M) (hs : IsLinearSet s) : IsLinearSet (a +ᵥ s)
参数：a : M；hs : IsLinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLinearSet.vadd (a : M) (hs : IsLinearSet s) : IsLinearSet (a +ᵥ s) := by
  rcases hs with ⟨b, t, ht, rfl⟩
  exact ⟨a + b, t, ht, by rw [vadd_vadd]⟩
/-
**IsLinearSet.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsLinearSe
t (s₁ + s₂)
参数：hs₁ : IsLinearSet s₁；hs₂ : IsLinearSet s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_add_vadd`：∀ {α : Type u_5} {β : Type u_6} [inst : Add α] [inst_1 : 
Add β] [inst_2 : VAdd α β] [VAddAssocClass α β β]   [VAddAssocClass α α β] [VAdd
Com…
· 使用定理 `Set.vaddAssocClass'`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [ins
t : VAdd α β] [inst_1 : VAdd α γ] [inst_2 : VAdd β γ]   [VAddAssocClass α β γ], 
VAddAssoc…
· 使用定理 `VAddAssocClass.left`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M
] [inst_1 : AddAction M α], VAddAssocClass M M α
· 使用定理 `Set.vaddAssocClass`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst
 : VAdd α β] [inst_1 : VAdd α γ] [inst_2 : VAdd β γ]   [VAddAssocClass α β γ], V
AddAssoc…
· 使用定理 `Set.vaddCommClass_set'`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [
inst : VAdd α γ] [inst_1 : VAdd β γ] [VAddCommClass α β γ],   VAddCommClass α (S
et β) (Set γ…
· 使用定理 `instVAddCommClassOfVAddAssocClass`：∀ {R : Type u_9} {M : Type u_10} [ins
t : AddCommMonoid M] [inst_1 : VAdd R M] [VAddAssocClass R M M],   VAddCommClass
 R M M
· 使用定理 `AddSubmonoid.closure_union`：∀ {M : Type u_1} [inst : AddZeroClass M] (s 
t : Set M),   AddSubmonoid.closure (s ∪ t) = AddSubmonoid.closure s ⊔ AddSubmono
id.closure t
· 使用定理 `AddSubmonoid.coe_sup`：∀ {N : Type u_7} [inst : AddCommMonoid N] (H K : A
ddSubmonoid N), ↑(H ⊔ K) = ↑H + ↑K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsLinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨a, t₁, ht₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, ht₂, rfl⟩
  exact ⟨a + b, t₁ ∪ t₂, ht₁.union ht₂, by simp [vadd_add_vadd, closure_union, coe_sup]⟩
/-
**IsLinearSet.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.image (hs : IsLinearSet s) (f : F) : IsLinearSet (f '' s)
参数：hs : IsLinearSet s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_vadd_distrib`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Add α] [inst_1 : Add β] [inst_2 : FunLike F α β]   [AddHomClass F α β] (f
 : F) (a : α…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLinearSet.image (hs : IsLinearSet s) (f : F) : IsLinearSet (f '' s) := by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨f a, f '' t, ht.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

/-- A set is semilinear if it is a finite union of linear sets. -/
/-
**IsSemilinearSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSemilinearSet (s : Set M) : Prop
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is semilinear if it is a finite union of linear sets.
-/
def IsSemilinearSet (s : Set M) : Prop :=
  ∃ (S : Set (Set M)), S.Finite ∧ (∀ t ∈ S, IsLinearSet t) ∧ s = ⋃₀ S

/-- An equivalent expression of `IsSemilinearSet` in terms of `Finset` instead of `Set.Finite`. -/
/-
**isSemilinearSet_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSemilinearSet_iff : IsSemilinearSet s ↔ exists (S : Finset (Set M)), (fo
rall t in S, IsLinearSet t) ∧ s = ⋃₀ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_finite_iff_finset`：exists_finite_iff_finset {p : Set α -> Pro
p} : (exists s : Set α, s.Finite ∧ p s) ↔ exists s : Finset α, p ↑s

--- 原说明 ---
An equivalent expression of `IsSemilinearSet` in terms of `Finset` instead of `S
et.Finite`.
-/
theorem isSemilinearSet_iff :
    IsSemilinearSet s ↔ ∃ (S : Finset (Set M)), (∀ t ∈ S, IsLinearSet t) ∧ s = ⋃₀ S :=
  Set.exists_finite_iff_finset
/-
**IsLinearSet.isSemilinearSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearSet.isSemilinearSet (h : IsLinearSet s) : IsSemilinearSet s
参数：h : IsLinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem IsLinearSet.isSemilinearSet (h : IsLinearSet s) : IsSemilinearSet s :=
  ⟨{s}, by simpa⟩

@[simp]
/-
**IsSemilinearSet.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.empty : IsSemilinearSet (∅ : Set M)
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsSemilinearSet.empty : IsSemilinearSet (∅ : Set M) :=
  ⟨∅, by simp⟩

@[simp]
/-
**IsSemilinearSet.singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.singleton (a : M) : IsSemilinearSet {a}
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.singleton`：IsLinearSet.singleton (a : M) : IsLinearSet {a}
-/
theorem IsSemilinearSet.singleton (a : M) : IsSemilinearSet {a} :=
  (IsLinearSet.singleton a).isSemilinearSet
/-
**IsSemilinearSet.closure_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.closure_finset (s : Finset M) : IsSemilinearSet (closure (
s : Set M) : Set M)
参数：s : Finset M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.closure_finset`：IsLinearSet.closure_finset (s : Finset M) : 
IsLinearSet (closure (s : Set M) : Set M)
-/
theorem IsSemilinearSet.closure_finset (s : Finset M) :
    IsSemilinearSet (closure (s : Set M) : Set M) :=
  (IsLinearSet.closure_finset s).isSemilinearSet
/-
**IsSemilinearSet.closure_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.closure_of_finite (hs : s.Finite) : IsSemilinearSet (closu
re s : Set M)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.closure_of_finite`：IsLinearSet.closure_of_finite (hs : s.Fin
ite) : IsLinearSet (closure s : Set M)
-/
theorem IsSemilinearSet.closure_of_finite (hs : s.Finite) :
    IsSemilinearSet (closure s : Set M) :=
  (IsLinearSet.closure_of_finite hs).isSemilinearSet
/-
**IsSemilinearSet.of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : IsSemilinearSet (
P : Set M)
参数：hP : P.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.of_fg`：IsLinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : 
IsLinearSet (P : Set M)
-/
theorem IsSemilinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) :
    IsSemilinearSet (P : Set M) :=
  (IsLinearSet.of_fg hP).isSemilinearSet

@[simp]
/-
**IsSemilinearSet.univ** 是 Mathlib 中的一个定理，位于命名空间 `IsSemilinearSet`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] [AddMonoid.FG M], IsSemilinearSe
t Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.univ`：∀ {M : Type u_1} [inst : AddCommMonoid M] [AddMonoid.F
G M], IsLinearSet Set.univ
-/
protected theorem IsSemilinearSet.univ [AddMonoid.FG M] : IsSemilinearSet (univ : Set M) :=
  IsLinearSet.univ.isSemilinearSet

/-- Semilinear sets are closed under union. -/
/-
**IsSemilinearSet.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂
) : IsSemilinearSet (s₁ union s₂)
参数：hs₁ : IsSemilinearSet s₁；hs₂ : IsSemilinearSet s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_union`：sUnion_union (S T : Set (Set α)) : ⋃₀ (S union T) = ⋃₀
 S union ⋃₀ T
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b

--- 原说明 ---
Semilinear sets are closed under union.
-/
theorem IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ ∪ s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ ∪ S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)
/-
**IsSemilinearSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite) (hS' : forall s i
n S, IsSemilinearSet s) : IsSemilinearSet (⋃₀ S)
参数：Set M；hS : S.Finite；hS' : forall s in S, IsSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `IsSemilinearSet.union`：IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) 
(hs₂ : IsSemilinearSet s₂) : IsSemilinearSet (s₁ union s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsSemilinearSet s) : IsSemilinearSet (⋃₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)
/-
**IsSemilinearSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.iUnion [Finite ι] {s : ι -> Set M} (hs : forall i, IsSemil
inearSet (s i)) : IsSemilinearSet (⋃ i, s i)
参数：hs : forall i, IsSemilinearSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `IsSemilinearSet.sUnion`：IsSemilinearSet.sUnion {S : Set (Set M)} (hS : S
.Finite) (hS' : forall s in S, IsSemilinearSet s) : IsSemilinearSet (⋃₀ S)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem IsSemilinearSet.iUnion [Finite ι] {s : ι → Set M} (hs : ∀ i, IsSemilinearSet (s i)) :
    IsSemilinearSet (⋃ i, s i) := by
  rw [← sUnion_range]
  apply sUnion (finite_range s)
  simpa
/-
**IsSemilinearSet.biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.biUnion {s : Set ι} {t : ι -> Set M} (hs : s.Finite) (ht :
 forall i in s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i in s, t i)
参数：hs : s.Finite；ht : forall i in s, IsSemilinearSet (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `IsSemilinearSet.sUnion`：IsSemilinearSet.sUnion {S : Set (Set M)} (hS : S
.Finite) (hS' : forall s in S, IsSemilinearSet s) : IsSemilinearSet (⋃₀ S)
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem IsSemilinearSet.biUnion {s : Set ι} {t : ι → Set M} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i ∈ s, t i) := by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa
/-
**IsSemilinearSet.biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.biUnion_finset {s : Finset ι} {t : ι -> Set M} (ht : foral
l i in s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i in s, t i)
参数：ht : forall i in s, IsSemilinearSet (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemilinearSet.biUnion`：IsSemilinearSet.biUnion {s : Set ι} {t : ι -> S
et M} (hs : s.Finite) (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinear
Set (⋃ i in s…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem IsSemilinearSet.biUnion_finset {s : Finset ι} {t : ι → Set M}
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i ∈ s, t i) :=
  biUnion s.finite_toSet ht
/-
**IsSemilinearSet.of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.of_finite (hs : s.Finite) : IsSemilinearSet s
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `IsSemilinearSet.biUnion`：IsSemilinearSet.biUnion {s : Set ι} {t : ι -> S
et M} (hs : s.Finite) (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinear
Set (⋃ i in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsSemilinearSet.of_finite (hs : s.Finite) : IsSemilinearSet s := by
  rw [← biUnion_of_singleton s]
  apply biUnion hs
  simp
/-
**IsSemilinearSet.vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.vadd (a : M) (hs : IsSemilinearSet s) : IsSemilinearSet (a
 +ᵥ s)
参数：a : M；hs : IsSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.vadd_set_sUnion`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] (
a : α) (S : Set (Set β)), a +ᵥ ⋃₀ S = ⋃ s ∈ S, a +ᵥ s
· 使用定理 `IsSemilinearSet.biUnion`：IsSemilinearSet.biUnion {s : Set ι} {t : ι -> S
et M} (hs : s.Finite) (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinear
Set (⋃ i in s…
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.vadd`：IsLinearSet.vadd (a : M) (hs : IsLinearSet s) : IsLine
arSet (a +ᵥ s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsSemilinearSet.vadd (a : M) (hs : IsSemilinearSet s) : IsSemilinearSet (a +ᵥ s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  rw [vadd_set_sUnion]
  exact biUnion hS fun s hs => ((hS' s hs).vadd a).isSemilinearSet

/-- Semilinear sets are closed under set addition. -/
/-
**IsSemilinearSet.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) 
: IsSemilinearSet (s₁ + s₂)
参数：hs₁ : IsSemilinearSet s₁；hs₂ : IsSemilinearSet s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_add`：∀ {α : Type u_2} [inst : Add α] (S : Set (Set α)) (t : S
et α), ⋃₀ S + t = ⋃ s ∈ S, s + t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.add_sUnion`：∀ {α : Type u_2} [inst : Add α] (s : Set α) (T : Set (Se
t α)), s + ⋃₀ T = ⋃ t ∈ T, s + t
· 使用定理 `IsSemilinearSet.biUnion`：IsSemilinearSet.biUnion {s : Set ι} {t : ι -> S
et M} (hs : s.Finite) (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinear
Set (⋃ i in s…
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.add`：IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearS
et s₂) : IsLinearSet (s₁ + s₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Semilinear sets are closed under set addition.
-/
theorem IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  simp_rw [sUnion_add, add_sUnion]
  exact biUnion hS₁ fun s₁ hs₁ => biUnion hS₂ fun s₂ hs₂ =>
    ((hS₁' s₁ hs₁).add (hS₂' s₂ hs₂)).isSemilinearSet

/-- The image of a semilinear set under a homomorphism is semilinear. -/
/-
**IsSemilinearSet.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.image (hs : IsSemilinearSet s) (f : F) : IsSemilinearSet (
f '' s)
参数：hs : IsSemilinearSet s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSemilinearSet.biUnion`：IsSemilinearSet.biUnion {s : Set ι} {t : ι -> S
et M} (hs : s.Finite) (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinear
Set (⋃ i in s…
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
· 使用定理 `IsLinearSet.image`：IsLinearSet.image (hs : IsLinearSet s) (f : F) : IsLi
nearSet (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The image of a semilinear set under a homomorphism is semilinear.
-/
theorem IsSemilinearSet.image (hs : IsSemilinearSet s) (f : F) : IsSemilinearSet (f '' s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, image_iUnion]
  exact biUnion hS fun s hs => ((hS' s hs).image f).isSemilinearSet
/-
**isSemilinearSet_image_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSemilinearSet_image_iff {F : Type*} [EquivLike F M N] [AddEquivClass F M
 N] (f : F) : IsSemilinearSet (f '' s) ↔ IsSemilinearSet s
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AddEquivClass.coe_symm_apply_apply`：∀ {α : Type u_9} {β : Type u_10} [in
st : Add α] [inst_1 : Add β] {F : Type u_11} [inst_2 : EquivLike F α β]   [inst_
3 : AddEquivClass F α β]…
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsSemilinearSet.image`：IsSemilinearSet.image (hs : IsSemilinearSet s) (f
 : F) : IsSemilinearSet (f '' s)
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem isSemilinearSet_image_iff {F : Type*} [EquivLike F M N] [AddEquivClass F M N] (f : F) :
    IsSemilinearSet (f '' s) ↔ IsSemilinearSet s := by
  constructor <;> intro h
  · convert! h.image (f : M ≃+ N).symm
    simp [image_image]
  · exact h.image f

set_option backward.isDefEq.respectTransparency false in
/-- Semilinear sets are closed under projection (from `ι ⊕ κ → M` to `ι → M` by taking `Sum.inl` on
the index). It is a special case of `IsSemilinearSet.image`. -/
/-
**IsSemilinearSet.proj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.proj {s : Set (ι oplus κ -> M)} (hs : IsSemilinearSet s) :
 IsSemilinearSet { x | exists y, Sum.elim x y in s }
参数：ι oplus κ -> M；hs : IsSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sum.elim_comp_inl_inr`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f
 : α ⊕ β → γ), Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) = f
· 使用定理 `IsSemilinearSet.image`：IsSemilinearSet.image (hs : IsSemilinearSet s) (f
 : F) : IsSemilinearSet (f '' s)
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
Semilinear sets are closed under projection (from `ι ⊕ κ → M` to `ι → M` by taki
ng `Sum.inl` on
the index). It is a special case of `IsSemilinearSet.image`.
-/
theorem IsSemilinearSet.proj {s : Set (ι ⊕ κ → M)} (hs : IsSemilinearSet s) :
    IsSemilinearSet { x | ∃ y, Sum.elim x y ∈ s } := by
  convert! hs.image (LinearMap.funLeft ℕ M Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

/-- A variant of `IsSemilinearSet.proj` for backward reasoning. -/
/-
**IsSemilinearSet.proj'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.proj' {p : (ι -> M) -> (κ -> M) -> Prop} : IsSemilinearSet
 { x | p (x ∘ Sum.inl) (x ∘ Sum.inr) } -> IsSemilinearSet { x | exists y, p x y 
}
参数：ι -> M；κ -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemilinearSet.proj`：IsSemilinearSet.proj {s : Set (ι oplus κ -> M)} (h
s : IsSemilinearSet s) : IsSemilinearSet { x | exists y, Sum.elim x y in s }

--- 原说明 ---
A variant of `IsSemilinearSet.proj` for backward reasoning.
-/
theorem IsSemilinearSet.proj' {p : (ι → M) → (κ → M) → Prop} :
    IsSemilinearSet { x | p (x ∘ Sum.inl) (x ∘ Sum.inr) } → IsSemilinearSet { x | ∃ y, p x y } :=
  proj
/-
**IsLinearSet.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsLinearSet`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {s : Set M}, IsLinearSet s → IsS
emilinearSet ↑(AddSubmonoid.closure s)
参数：AddSubmonoid.closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `AddSubmonoid.closure_mono`：∀ {M : Type u_1} [inst : AddZeroClass M] ⦃s t
 : Set M⦄, s ⊆ t → AddSubmonoid.closure s ≤ AddSubmonoid.closure t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `AddSubmonoid.mem_closure_of_mem`：∀ {M : Type u_1} [inst : AddZeroClass M
] {s : Set M} {x : M}, x ∈ s → x ∈ AddSubmonoid.closure s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.closure_union`：∀ {M : Type u_1} [inst : AddZeroClass M] (s 
t : Set M),   AddSubmonoid.closure (s ∪ t) = AddSubmonoid.closure s ⊔ AddSubmono
id.closure t
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `Set.vadd_mem_vadd_set`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a +ᵥ b ∈ a +ᵥ s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `IsSemilinearSet.union`：IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) 
(hs₂ : IsSemilinearSet s₂) : IsSemilinearSet (s₁ union s₂)
· 使用定理 `IsSemilinearSet.singleton`：IsSemilinearSet.singleton (a : M) : IsSemilin
earSet {a}
· 使用定理 `IsLinearSet.isSemilinearSet`：IsLinearSet.isSemilinearSet (h : IsLinearSe
t s) : IsSemilinearSet s
（共 31 条，此处仅展示前 30 条）
-/
protected lemma IsLinearSet.closure (hs : IsLinearSet s) : IsSemilinearSet (closure s : Set M) := by
  rcases hs with ⟨a, t, ht, rfl⟩
  convert! (IsSemilinearSet.singleton 0).union (isSemilinearSet ⟨a, { a } ∪ t, by simp [ht], rfl⟩)
  ext x
  simp only [SetLike.mem_coe, singleton_union, mem_insert_iff, mem_vadd_set, vadd_eq_add]
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with ⟨x, hx, rfl⟩
      exact Or.inr ⟨x, closure_mono (subset_insert _ _) hx, rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨x, hx, rfl⟩
      · simpa
      · rcases ih₂ with rfl | ⟨y, hy, rfl⟩
        · exact Or.inr ⟨x, hx, by simp⟩
        · refine Or.inr ⟨_, add_mem (mem_closure_of_mem (mem_insert _ _)) (add_mem hx hy), ?_⟩
          simp_rw [← add_assoc, add_right_comm a a x]
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · simp
    · simp_rw [insert_eq, closure_union, mem_sup, mem_closure_singleton] at hx
      rcases hx with ⟨_, ⟨n, rfl⟩, ⟨x, hx, rfl⟩⟩
      rw [add_left_comm]
      refine add_mem (nsmul_mem (mem_closure_of_mem ?_) _)
        (mem_closure_of_mem (vadd_mem_vadd_set hx))
      nth_rw 2 [← add_zero a]
      exact vadd_mem_vadd_set (zero_mem _)

/-- Semilinear sets are closed under additive closure. -/
/-
**IsSemilinearSet.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsSemilinearSet`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] {s : Set M}, IsSemilinearSet s →
 IsSemilinearSet ↑(AddSubmonoid.closure s)
参数：AddSubmonoid.closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `AddSubmonoid.closure_empty`：∀ {M : Type u_1} [inst : AddZeroClass M], Ad
dSubmonoid.closure ∅ = ⊥
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `AddSubmonoid.closure_union`：∀ {M : Type u_1} [inst : AddZeroClass M] (s 
t : Set M),   AddSubmonoid.closure (s ∪ t) = AddSubmonoid.closure s ⊔ AddSubmono
id.closure t
· 使用定理 `AddSubmonoid.coe_sup`：∀ {N : Type u_7} [inst : AddCommMonoid N] (H K : A
ddSubmonoid N), ↑(H ⊔ K) = ↑H + ↑K
· 使用定理 `IsSemilinearSet.add`：IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂
 : IsSemilinearSet s₂) : IsSemilinearSet (s₁ + s₂)
· 使用定理 `IsLinearSet.closure`：∀ {M : Type u_1} [inst : AddCommMonoid M] {s : Set 
M}, IsLinearSet s → IsSemilinearSet ↑(AddSubmonoid.closure s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Semilinear sets are closed under additive closure.
-/
protected theorem IsSemilinearSet.closure (hs : IsSemilinearSet s) :
    IsSemilinearSet (closure s : Set M) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa [closure_union, coe_sup] using hS'.1.closure.add (ih hS'.2)

/-- A linear set is proper if its submonoid generators (periods) are linearly independent. -/
/-
**IsProperLinearSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsProperLinearSet (s : Set M) : Prop
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear set is proper if its submonoid generators (periods) are linearly indepe
ndent.
-/
def IsProperLinearSet (s : Set M) : Prop :=
  ∃ (a : M) (t : Set M), t.Finite ∧ LinearIndepOn ℕ id t ∧ s = a +ᵥ (closure t : Set M)

/-- An equivalent expression of `IsProperLinearSet` in terms of `Finset` instead of `Set.Finite`. -/
/-
**isProperLinearSet_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperLinearSet_iff : IsProperLinearSet s ↔ exists (a : M) (t : Finset M
), LinearIndepOn Nat id (t : Set M) ∧ s = a +ᵥ (closure (t : Set M) : Set M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
An equivalent expression of `IsProperLinearSet` in terms of `Finset` instead of 
`Set.Finite`.
-/
theorem isProperLinearSet_iff :
    IsProperLinearSet s ↔ ∃ (a : M) (t : Finset M),
      LinearIndepOn ℕ id (t : Set M) ∧ s = a +ᵥ (closure (t : Set M) : Set M) :=
  exists_congr fun a =>
    ⟨fun ⟨t, ht, hs⟩ => ⟨ht.toFinset, by simpa⟩, fun ⟨t, hs⟩ => ⟨t, t.finite_toSet, hs⟩⟩
/-
**IsProperLinearSet.isLinearSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperLinearSet.isLinearSet (hs : IsProperLinearSet s) : IsLinearSet s
参数：hs : IsProperLinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsProperLinearSet.isLinearSet (hs : IsProperLinearSet s) : IsLinearSet s := by
  rcases hs with ⟨a, t, ht, _, rfl⟩
  exact ⟨a, t, ht, rfl⟩

@[simp]
/-
**IsProperLinearSet.singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperLinearSet.singleton (a : M) : IsProperLinearSet {a}
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoid.closure_empty`：∀ {M : Type u_1} [inst : AddZeroClass M], Ad
dSubmonoid.closure ∅ = ⊥
· 使用定理 `Set.vadd_set_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β
] {a : α} {b : β}, a +ᵥ {b} = {a +ᵥ b}
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsProperLinearSet.singleton (a : M) : IsProperLinearSet {a} :=
  ⟨a, ∅, by simp⟩

/-- A semilinear set is proper if it is a finite union of proper linear sets. -/
/-
**IsProperSemilinearSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet (s : Set M) : Prop
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semilinear set is proper if it is a finite union of proper linear sets.
-/
def IsProperSemilinearSet (s : Set M) : Prop :=
  ∃ (S : Set (Set M)), S.Finite ∧ (∀ t ∈ S, IsProperLinearSet t) ∧ s = ⋃₀ S

/-- An equivalent expression of `IsProperSemilinearSet` in terms of `Finset` instead of
`Set.Finite`. -/
/-
**isProperSemilinearSet_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isProperSemilinearSet_iff : IsProperSemilinearSet s ↔ exists (S : Finset (
Set M)), (forall t in S, IsProperLinearSet t) ∧ s = ⋃₀ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_finite_iff_finset`：exists_finite_iff_finset {p : Set α -> Pro
p} : (exists s : Set α, s.Finite ∧ p s) ↔ exists s : Finset α, p ↑s

--- 原说明 ---
An equivalent expression of `IsProperSemilinearSet` in terms of `Finset` instead
 of
`Set.Finite`.
-/
theorem isProperSemilinearSet_iff :
    IsProperSemilinearSet s ↔ ∃ (S : Finset (Set M)), (∀ t ∈ S, IsProperLinearSet t) ∧ s = ⋃₀ S :=
  Set.exists_finite_iff_finset
/-
**IsProperSemilinearSet.isSemilinearSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet.isSemilinearSet (hs : IsProperSemilinearSet s) : IsS
emilinearSet s
参数：hs : IsProperSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsProperLinearSet.isLinearSet`：IsProperLinearSet.isLinearSet (hs : IsPro
perLinearSet s) : IsLinearSet s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsProperSemilinearSet.isSemilinearSet (hs : IsProperSemilinearSet s) :
    IsSemilinearSet s := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  exact ⟨S, hS, fun s hs => (hS' s hs).isLinearSet, rfl⟩
/-
**IsProperLinearSet.isProperSemilinearSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperLinearSet.isProperSemilinearSet (hs : IsProperLinearSet s) : IsPro
perSemilinearSet s
参数：hs : IsProperLinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem IsProperLinearSet.isProperSemilinearSet (hs : IsProperLinearSet s) :
    IsProperSemilinearSet s :=
  ⟨{s}, by simpa⟩

@[simp]
/-
**IsProperSemilinearSet.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet.empty : IsProperSemilinearSet (∅ : Set M)
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsProperSemilinearSet.empty : IsProperSemilinearSet (∅ : Set M) :=
  ⟨∅, by simp⟩
/-
**IsProperSemilinearSet.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet.union (hs₁ : IsProperSemilinearSet s₁) (hs₂ : IsProp
erSemilinearSet s₂) : IsProperSemilinearSet (s₁ union s₂)
参数：hs₁ : IsProperSemilinearSet s₁；hs₂ : IsProperSemilinearSet s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_union`：sUnion_union (S T : Set (Set α)) : ⋃₀ (S union T) = ⋃₀
 S union ⋃₀ T
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
-/
theorem IsProperSemilinearSet.union (hs₁ : IsProperSemilinearSet s₁)
    (hs₂ : IsProperSemilinearSet s₂) : IsProperSemilinearSet (s₁ ∪ s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ ∪ S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)
/-
**IsProperSemilinearSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite) (hS' : fora
ll s in S, IsProperSemilinearSet s) : IsProperSemilinearSet (⋃₀ S)
参数：Set M；hS : S.Finite；hS' : forall s in S, IsProperSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `Set.sUnion_insert`：sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀ inse
rt s T = s union ⋃₀ T
· 使用定理 `IsProperSemilinearSet.union`：IsProperSemilinearSet.union (hs₁ : IsProper
SemilinearSet s₁) (hs₂ : IsProperSemilinearSet s₂) : IsProperSemilinearSet (s₁ u
nion s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsProperSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsProperSemilinearSet s) : IsProperSemilinearSet (⋃₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)
/-
**IsProperSemilinearSet.biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet.biUnion {s : Set ι} {t : ι -> Set M} (hs : s.Finite)
 (ht : forall i in s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i 
in s, t i)
参数：hs : s.Finite；ht : forall i in s, IsProperSemilinearSet (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `IsProperSemilinearSet.sUnion`：IsProperSemilinearSet.sUnion {S : Set (Set
 M)} (hS : S.Finite) (hS' : forall s in S, IsProperSemilinearSet s) : IsProperSe
milinearSet (⋃₀ S)
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem IsProperSemilinearSet.biUnion {s : Set ι} {t : ι → Set M} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i ∈ s, t i) := by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa
/-
**IsProperSemilinearSet.biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsProperSemilinearSet.biUnion_finset {s : Finset ι} {t : ι -> Set M} (ht :
 forall i in s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i in s, 
t i)
参数：ht : forall i in s, IsProperSemilinearSet (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsProperSemilinearSet.biUnion`：IsProperSemilinearSet.biUnion {s : Set ι}
 {t : ι -> Set M} (hs : s.Finite) (ht : forall i in s, IsProperSemilinearSet (t 
i)) : IsProperSemil…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem IsProperSemilinearSet.biUnion_finset {s : Finset ι} {t : ι → Set M}
    (ht : ∀ i ∈ s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i ∈ s, t i) :=
  biUnion s.finite_toSet ht
/-
**IsLinearSet.isProperSemilinearSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsLinearSet s) : I
sProperSemilinearSet s
参数：hs : IsLinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLinearSet_iff`：isLinearSet_iff : IsLinearSet s ↔ exists (a : M) (t : F
inset M), s = a +ᵥ (closure (t : Set M) : Set M)
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `IsProperLinearSet.isProperSemilinearSet`：IsProperLinearSet.isProperSemil
inearSet (hs : IsProperLinearSet s) : IsProperSemilinearSet s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `not_linearIndepOn_finset_iffₒₛ`：not_linearIndepOn_finset_iffₒₛ [Decidabl
eEq ι] {s : Finset ι} : ¬LinearIndepOn R v s ↔ exists t subseteq s, exists (f : 
ι -> R), ∑ i in t, f…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddSubmonoid.mem_closure_finset`：∀ {M : Type u_1} [inst : AddCommMonoid 
M] {x : M} {s : Finset M},   x ∈ AddSubmonoid.closure ↑s ↔ ∃ f, Function.support
 f ⊆ ↑s ∧ ∑ a ∈ s, f …
· 使用定理 `Finset.union_sdiff_of_subset`：union_sdiff_of_subset (h : s subseteq t) :
 s union t \ s = t
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
（共 61 条，此处仅展示前 30 条）
-/
lemma IsLinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsLinearSet s) :
    IsProperSemilinearSet s := by
  classical
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn ℕ id (t : Set M)
  · exact IsProperLinearSet.isProperSemilinearSet ⟨a, t, by simpa⟩
  rw [not_linearIndepOn_finset_iffₒₛ] at hindep
  rcases hindep with ⟨t', ht', f, heq, i, hi, hfi⟩
  simp only [Function.id_def] at heq
  convert_to IsProperSemilinearSet (⋃ j ∈ t', ⋃ k ∈ Finset.range (f j),
    (a + k • j) +ᵥ (closure (t.erase j : Set M) : Set M))
  · ext x
    simp only [mem_vadd_set, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closure_finset] at hy
      rcases hy with ⟨g, -, rfl⟩
      induction hn : g i using Nat.strong_induction_on generalizing g with | _ n ih'
      subst hn
      by_cases! hfg : ∀ j ∈ t', f j ≤ g j
      · convert!
        ih' (g i - f i) (Nat.sub_lt_self hfi (hfg i hi))
          (fun j => if j ∈ t' then g j - f j else g j + f j) (by simp [hi]) using 1
        conv_lhs => rw [← Finset.union_sdiff_of_subset ht']
        simp_rw [vadd_eq_add, add_left_cancel_iff, Finset.sum_union Finset.sdiff_disjoint.symm,
          ite_smul, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht',
          Finset.filter_notMem_eq_sdiff, add_smul, Finset.sum_add_distrib, ← heq, ← add_assoc,
          add_right_comm, ← Finset.sum_add_distrib]
        congr! 2 with j hj
        rw [← add_smul, tsub_add_cancel_of_le (hfg j hj)]
      · rcases hfg with ⟨j, hj, hgj⟩
        simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
        refine ⟨j, hj, g j, hgj, ∑ k ∈ t.erase j, g k • k,
          sum_mem fun x hx => (nsmul_mem (mem_closure_of_mem hx) _), ?_⟩
        rw [← Finset.sum_erase_add _ _ (ht' hj), ← add_assoc, add_right_comm]
    · simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
      rintro ⟨j, hj, k, hk, y, hy, rfl⟩
      refine ⟨k • j + y,
        add_mem (nsmul_mem (mem_closure_of_mem (ht' hj)) _)
          ((closure_mono (t.erase_subset j)) hy), ?_⟩
      rw [add_assoc]
  · exact .biUnion_finset fun j hj => .biUnion_finset fun k hk =>
      ih _ (Finset.card_lt_card (Finset.erase_ssubset (ht' hj))) _ _ rfl

/-- The **proper decomposition** of semilinear sets: every semilinear set is a finite union of
proper linear sets. -/
/-
**IsSemilinearSet.isProperSemilinearSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSemilinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsSemilinearSe
t s) : IsProperSemilinearSet s
参数：hs : IsSemilinearSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `IsProperSemilinearSet.biUnion`：IsProperSemilinearSet.biUnion {s : Set ι}
 {t : ι -> Set M} (hs : s.Finite) (ht : forall i in s, IsProperSemilinearSet (t 
i)) : IsProperSemil…
· 使用引理 `IsLinearSet.isProperSemilinearSet`：IsLinearSet.isProperSemilinearSet [Is
CancelAdd M] (hs : IsLinearSet s) : IsProperSemilinearSet s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The **proper decomposition** of semilinear sets: every semilinear set is a finit
e union of
proper linear sets.
-/
theorem IsSemilinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsSemilinearSet s) :
    IsProperSemilinearSet s := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion]
  exact IsProperSemilinearSet.biUnion hS fun s hs => (hS' s hs).isProperSemilinearSet



/-- A set of `ℕ` is semilinear if and only if it is ultimately periodic, i.e. periodic after some
number `k`. -/
/-
**Nat.isSemilinearSet_iff_ultimately_periodic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.isSemilinearSet_iff_ultimately_periodic {s : Set Nat} : IsSemilinearSe
t s ↔ exists k, exists p > 0, forall x >= k, x in s ↔ x + p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isProperSemilinearSet_iff`：isProperSemilinearSet_iff : IsProperSemilinea
rSet s ↔ exists (S : Finset (Set M)), (forall t in S, IsProperLinearSet t) ∧ s =
 ⋃₀ S
· 使用定理 `IsSemilinearSet.isProperSemilinearSet`：IsSemilinearSet.isProperSemilinea
rSet [IsCancelAdd M] (hs : IsSemilinearSet s) : IsProperSemilinearSet s
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `isProperLinearSet_iff`：isProperLinearSet_iff : IsProperLinearSet s ↔ exi
sts (a : M) (t : Finset M), LinearIndepOn Nat id (t : Set M) ∧ s = a +ᵥ (closure
 (t : Set M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `CommSemiring.rank_self`：CommSemiring.rank_self (R) [CommSemiring R] : Mo
dule.rank R R = 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `AddSubmonoid.closure_empty`：∀ {M : Type u_1} [inst : AddZeroClass M], Ad
dSubmonoid.closure ∅ = ⊥
· 使用定理 `Set.vadd_set_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β
] {a : α} {b : β}, a +ᵥ {b} = {a +ᵥ b}
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `LinearIndepOn.zero_notMem_image`：LinearIndepOn.zero_notMem_image [Nontri
vial R] (hs : LinearIndepOn R v s) : 0 ∉ v '' s
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
A set of `ℕ` is semilinear if and only if it is ultimately periodic, i.e. period
ic after some
number `k`.
-/
theorem Nat.isSemilinearSet_iff_ultimately_periodic {s : Set ℕ} :
    IsSemilinearSet s ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ s ↔ x + p ∈ s := by
  constructor
  · intro hs
    apply IsSemilinearSet.isProperSemilinearSet at hs
    rw [isProperSemilinearSet_iff] at hs
    rcases hs with ⟨S, hS, rfl⟩
    replace hS : ∀ t ∈ S, ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ t ↔ x + p ∈ t := by
      intro t ht
      apply hS at ht
      rw [isProperLinearSet_iff] at ht
      rcases ht with ⟨a, t, ht, rfl⟩
      have hcard : t.card ≤ 1 := by simpa [CommSemiring.rank_self] using ht.cardinal_le_rank
      simp_rw [Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff] at hcard
      rcases hcard with ⟨b, (rfl | rfl)⟩
      · refine ⟨a + 1, 1, zero_lt_one, fun x hx => ?_⟩
        simp [(by grind : x ≠ a), (by grind : x + 1 ≠ a)]
      · have hb : b ≠ 0 := by simpa [ne_comm] using ht.zero_notMem_image
        rw [Nat.ne_zero_iff_zero_lt] at hb
        refine ⟨a, b, hb, fun x hx => ?_⟩
        simp only [Finset.coe_singleton, mem_vadd_set, SetLike.mem_coe,
          AddSubmonoid.mem_closure_singleton, smul_eq_mul, vadd_eq_add, exists_exists_eq_and]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x + 1, by grind⟩
        · rintro ⟨y, heq⟩
          cases y with
          | zero => exact ⟨0, by grind⟩
          | succ y => exact ⟨y, by grind⟩
    choose! k p hS hS' using hS
    refine ⟨S.sup k, S.lcm p, ?_, fun x hx => ?_⟩
    · grind [Finset.lcm_eq_zero_iff]
    · simp only [mem_sUnion, SetLike.mem_coe]
      refine exists_congr fun t => and_congr_right fun ht => ?_
      have hpt : p t ∣ S.lcm p := Finset.dvd_lcm ht
      rw [dvd_iff_exists_eq_mul_left] at hpt
      rcases hpt with ⟨m, hpt⟩
      rw [hpt]
      clear hpt
      induction m with grind [Finset.sup_le_iff]
  · intro ⟨k, p, hp, hs⟩
    have h₁ : {x ∈ s | x < k}.Finite := (Set.finite_lt_nat k).subset (sep_subset_ofPred _ _)
    have h₂ : {x ∈ s | k ≤ x ∧ x < k + p}.Finite :=
      (Set.finite_Ico k (k + p)).subset (sep_subset_ofPred _ _)
    convert! (IsSemilinearSet.of_finite h₁).union (.add (.of_finite h₂) (.closure_finset { p }))
    ext x
    simp only [sep_and, Finset.coe_singleton, mem_union, mem_ofPred_eq, mem_add, mem_inter_iff,
      SetLike.mem_coe, AddSubmonoid.mem_closure_singleton, smul_eq_mul, exists_exists_eq_and]
    constructor
    · intro hx
      by_cases hx' : x < k
      · exact Or.inl ⟨hx, hx'⟩
      · rw [not_lt] at hx'
        refine Or.inr ⟨k + (x - k) % p, ⟨⟨?_1, ?_2⟩, ?_1, ?_3⟩, (x - k) / p, ?_4⟩
        · rw [← add_tsub_cancel_of_le hx', ← Nat.mod_add_div' (x - k) p, ← add_assoc] at hx
          generalize (x - k) / p = m at hx
          induction m with grind
        · grind
        · exact Nat.add_lt_add_left (Nat.mod_lt _ hp) _
        · rw [add_assoc, Nat.mod_add_div', add_tsub_cancel_of_le hx']
    · rintro (⟨hx, hx'⟩ | ⟨x, ⟨⟨hx, hx'⟩, _⟩, m, rfl⟩)
      · exact hx
      · induction m with grind
