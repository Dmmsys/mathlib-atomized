/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Equivalence of real-valued absolute values

Two absolute values `v₁, v₂ : AbsoluteValue R ℝ` are *equivalent* if there exists a
positive real number `c` such that `v₁ x ^ c = v₂ x` for all `x : R`.
-/

@[expose] public section

namespace AbsoluteValue

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S]
  (v w : AbsoluteValue R S)

/-- Two absolute values `v` and `w` are *equivalent* if `v x ≤ v y` precisely when
`w x ≤ w y`.

Note that for real absolute values this condition is equivalent to the existence of a positive
real number `c` such that `v x ^ c = w x` for all `x`. See
`AbsoluteValue.isEquiv_iff_exists_rpow_eq`. -/
/-
**AbsoluteValue.IsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：IsEquiv : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two absolute values `v` and `w` are *equivalent* if `v x ≤ v y` precisely when
`w x ≤ w y`.

Note that for real absolute values this condition is equivalent to the existence
 of a positive
real number `c` such that `v x ^ c = w x` for all `x`. See
`AbsoluteValue.isEquiv_iff_exists_rpow_eq`.
-/
def IsEquiv : Prop := ∀ x y, v x ≤ v y ↔ w x ≤ w y
/-
**AbsoluteValue.IsEquiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (v : AbsoluteValue R S), v.IsEquiv v
参数：v : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsEquiv.refl : v.IsEquiv v := fun _ _ ↦ .rfl

variable {v w}
/-
**AbsoluteValue.IsEquiv.rfl** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v : AbsoluteValue R S}, v.IsEquiv v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsEquiv.rfl : v.IsEquiv v := fun _ _ ↦ .rfl
/-
**AbsoluteValue.IsEquiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S}, v.IsEquiv w → w.IsEquiv v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem IsEquiv.symm (h : v.IsEquiv w) : w.IsEquiv v := fun _ _ ↦ (h _ _).symm
/-
**AbsoluteValue.IsEquiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w u : AbsoluteValue R S}, v.IsEquiv w → w.IsEquiv
 u → v.IsEquiv u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
theorem IsEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsEquiv w)
    (h₂ : w.IsEquiv u) : v.IsEquiv u := fun _ _ ↦ (h₁ _ _).trans (h₂ _ _)
/-
**AbsoluteValue.** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Setoid (AbsoluteValue R S) where
  r := IsEquiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }
/-
**AbsoluteValue.IsEquiv.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEqu
iv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S}, v.IsEquiv w → ∀ {x y : R}
, v x ≤ v y ↔ w x ≤ w y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsEquiv.le_iff_le (h : v.IsEquiv w) {x y : R} : v x ≤ v y ↔ w x ≤ w y := h ..
/-
**AbsoluteValue.IsEquiv.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEqu
iv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S}, v.IsEquiv w → ∀ {x y : R}
, v x < v y ↔ w x < w y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
-/
theorem IsEquiv.lt_iff_lt (h : v.IsEquiv w) {x y : R} : v x < v y ↔ w x < w y :=
  lt_iff_lt_of_le_iff_le' (h y x) (h x y)
/-
**AbsoluteValue.IsEquiv.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEqu
iv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S}, v.IsEquiv w → ∀ {x y : R}
, v x = v y ↔ w x = w y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsEquiv.eq_iff_eq (h : v.IsEquiv w) {x y : R} : v x = v y ↔ w x = w y := by
  simp [le_antisymm_iff, h x y, h y x]

variable [IsDomain S] [Nontrivial R]
/-
**AbsoluteValue.IsEquiv.lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEq
uiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S} [IsDomain S] [Nontrivial R
], v.IsEquiv w → ∀ {x : R}, v x < 1 ↔ w x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `AbsoluteValue.IsEquiv.lt_iff_lt`：∀ {R : Type u_1} [inst : Semiring R] {S
 : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteVa
lue R S}, v.IsEquiv w…
-/
theorem IsEquiv.lt_one_iff (h : v.IsEquiv w) {x : R} :
    v x < 1 ↔ w x < 1 := by
  simpa only [map_one] using h.lt_iff_lt (y := 1)
/-
**AbsoluteValue.IsEquiv.one_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEq
uiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S} [IsDomain S] [Nontrivial R
], v.IsEquiv w → ∀ {x : R}, 1 < v x ↔ 1 < w x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `AbsoluteValue.IsEquiv.lt_iff_lt`：∀ {R : Type u_1} [inst : Semiring R] {S
 : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteVa
lue R S}, v.IsEquiv w…
-/
theorem IsEquiv.one_lt_iff (h : v.IsEquiv w) {x : R} :
    1 < v x ↔ 1 < w x := by
  simpa only [map_one] using h.lt_iff_lt (x := 1)
/-
**AbsoluteValue.IsEquiv.le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEq
uiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S} [IsDomain S] [Nontrivial R
], v.IsEquiv w → ∀ {x : R}, v x ≤ 1 ↔ w x ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem IsEquiv.le_one_iff (h : v.IsEquiv w) {x : R} :
    v x ≤ 1 ↔ w x ≤ 1 := by
  simpa only [map_one] using h x 1
/-
**AbsoluteValue.IsEquiv.one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEq
uiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S} [IsDomain S] [Nontrivial R
], v.IsEquiv w → ∀ {x : R}, 1 ≤ v x ↔ 1 ≤ w x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem IsEquiv.one_le_iff (h : v.IsEquiv w) {x : R} :
    1 ≤ v x ↔ 1 ≤ w x := by
  simpa only [map_one] using h 1 x
/-
**AbsoluteValue.IsEquiv.eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue.IsEq
uiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v w : AbsoluteValue R S} [IsDomain S] [Nontrivial R
], v.IsEquiv w → ∀ {x : R}, v x = 1 ↔ w x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `AbsoluteValue.IsEquiv.eq_iff_eq`：∀ {R : Type u_1} [inst : Semiring R] {S
 : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteVa
lue R S}, v.IsEquiv w…
-/
theorem IsEquiv.eq_one_iff (h : v.IsEquiv w) {x : R} : v x = 1 ↔ w x = 1 := by
  simpa only [map_one] using h.eq_iff_eq (x := x) (y := 1)
/-
**AbsoluteValue.IsEquiv.isNontrivial_congr** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteVa
lue.IsEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {S : Type u_2} [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   {v : AbsoluteValue R S} [IsDomain S] [Nontrivial R] 
{w : AbsoluteValue R S},   v.IsEquiv w → (v.IsNontrivial ↔ w.IsNontrivial)
参数：v.IsNontrivial ↔ w.IsNontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `AbsoluteValue.IsEquiv.eq_one_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsEquiv.isNontrivial_congr {w : AbsoluteValue R S} (h : v.IsEquiv w) :
    v.IsNontrivial ↔ w.IsNontrivial :=
  not_iff_not.1 <| by aesop (add simp [not_isNontrivial_iff, h.eq_one_iff])

alias ⟨IsEquiv.isNontrivial, _⟩ := IsEquiv.isNontrivial_congr

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
/-
**AbsoluteValue.isEquiv_trivial_iff_eq_trivial** 是 Mathlib 中的一个引理，位于命名空间 `Absolu
teValue`。
形式化陈述：isEquiv_trivial_iff_eq_trivial [DecidablePred fun x : R => x = 0] [NoZeroD
ivisors R] [IsStrictOrderedRing S] {f : AbsoluteValue R S} : f.IsEquiv .trivial 
↔ f = .trivial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `AbsoluteValue.ext`：ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x)
 -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AbsoluteValue.IsEquiv.eq_one_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsoluteValue.IsEquiv.rfl`：∀ {R : Type u_1} [inst : Semiring R] {S : Typ
e u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v : AbsoluteValue R S}
, v.IsEquiv v

--- 原说明 ---
An absolute value is equivalent to the trivial iff it is trivial itself.
-/
lemma isEquiv_trivial_iff_eq_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [IsStrictOrderedRing S] {f : AbsoluteValue R S} :
    f.IsEquiv .trivial ↔ f = .trivial :=
  ⟨fun h ↦ by aesop (add simp [h.eq_one_iff, AbsoluteValue.trivial]), fun h ↦ h ▸ .rfl⟩

variable [IsStrictOrderedRing S]
/-
**AbsoluteValue.isEquiv_iff_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`
。
形式化陈述：isEquiv_iff_lt_one_iff : v.IsEquiv w ↔ forall x, v x < 1 ↔ w x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.IsEquiv.lt_one_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_inv_lt_iff₀`：mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
theorem isEquiv_iff_lt_one_iff :
    v.IsEquiv w ↔ ∀ x, v x < 1 ↔ w x < 1 := by
  refine ⟨fun h _ ↦ h.lt_one_iff, fun h x y ↦ ?_⟩
  rcases eq_or_ne (v x) 0 with (_ | hy₀)
  · simp_all
  rw [le_iff_le_iff_lt_iff_lt, ← one_mul (v x), ← mul_inv_lt_iff₀ (by simp_all), ← one_mul (w x),
    ← mul_inv_lt_iff₀ (by simp_all), ← map_inv₀, ← map_mul, ← map_inv₀, ← map_mul]
  exact h _

variable [Archimedean S] [ExistsAddOfLE S]
/-
**AbsoluteValue.isEquiv_of_lt_one_imp** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：isEquiv_of_lt_one_imp (hv : v.IsNontrivial) (h : forall x, v x < 1 -> w x 
< 1) : v.IsEquiv w
参数：hv : v.IsNontrivial；h : forall x, v x < 1 -> w x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.isEquiv_iff_lt_one_iff`：isEquiv_iff_lt_one_iff : v.IsEquiv
 w ↔ forall x, v x < 1 ↔ w x < 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsoluteValue.IsNontrivial.exists_abv_lt_one`：∀ {R : Type u_3} {S : Type
 u_4} [inst : Field R] [inst_1 : Semifield S] [inst_2 : LinearOrder S] [IsStrict
OrderedRing S]   [ExistsAddOfLE S]…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_inv_lt_iff₀`：mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
（共 42 条，此处仅展示前 30 条）
-/
theorem isEquiv_of_lt_one_imp (hv : v.IsNontrivial) (h : ∀ x, v x < 1 → w x < 1) : v.IsEquiv w := by
  refine isEquiv_iff_lt_one_iff.2 fun a ↦ ?_
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · simp
  refine ⟨h a, fun hw ↦ ?_⟩
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  have hpow (n : ℕ) (hv : 1 ≤ v a) : w x₀ < w a ^ n := by
    rw [← one_mul (_ ^ _), ← mul_inv_lt_iff₀ (pow_pos (by simp_all) _),
      ← map_pow, ← map_inv₀, ← map_mul]
    apply h
    rw [map_mul, map_inv₀, map_pow, mul_inv_lt_iff₀ (pow_pos (by simp [ha₀]) _), one_mul]
    exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (w.pos hx₀.1) hw
  exact not_le.1 <| mt (hpow n) <| not_lt.2 hn.le

/--
If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we can find an `a : R`
such that `v a < 1` while `1 ≤ w a`.
-/
/-
**AbsoluteValue.exists_lt_one_one_le_of_not_isEquiv** 是 Mathlib 中的一个定理，位于命名空间 `A
bsoluteValue`。
形式化陈述：exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNo
ntrivial) (h : ¬v.IsEquiv w) : exists a : R, v a < 1 ∧ 1 <= w a
参数：hv : v.IsNontrivial；h : ¬v.IsEquiv w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `AbsoluteValue.isEquiv_of_lt_one_imp`：isEquiv_of_lt_one_imp (hv : v.IsNon
trivial) (h : forall x, v x < 1 -> w x < 1) : v.IsEquiv w

--- 原说明 ---
If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we 
can find an `a : R`
such that `v a < 1` while `1 ≤ w a`.
-/
theorem exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial)
    (h : ¬v.IsEquiv w) : ∃ a : R, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_of_lt_one_imp hv h

/--
If `v` and `w` are two non-trivial and inequivalent absolute values then we can find an `a : R`
such that `1 < v a` while `w a < 1`.
-/
/-
**AbsoluteValue.exists_one_lt_lt_one_of_not_isEquiv** 是 Mathlib 中的一个定理，位于命名空间 `A
bsoluteValue`。
形式化陈述：exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNo
ntrivial) (hw : w.IsNontrivial) (h : ¬v.IsEquiv w) : exists a : R, 1 < v a ∧ w a
 < 1
参数：hv : v.IsNontrivial；hw : w.IsNontrivial；h : ¬v.IsEquiv w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.exists_lt_one_one_le_of_not_isEquiv`：exists_lt_one_one_le_
of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial) (h : ¬v.IsEquiv w
) : exists a : R, v a < 1 ∧ 1 <= w a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AbsoluteValue.IsEquiv.symm`：∀ {R : Type u_1} [inst : Semiring R] {S : Ty
pe u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteValue R
 S}, v.IsEquiv w…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AbsoluteValue.pos_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, 0 <…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `lt_of_le_of_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `v` and `w` are two non-trivial and inequivalent absolute values then we can 
find an `a : R`
such that `1 < v a` while `w a < 1`.
-/
theorem exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬v.IsEquiv w) :
    ∃ a : R, 1 < v a ∧ w a < 1 := by
  let ⟨a, hva, hwa⟩ := exists_lt_one_one_le_of_not_isEquiv hv h
  let ⟨b, hwb, hvb⟩ := exists_lt_one_one_le_of_not_isEquiv hw (mt .symm h)
  exact ⟨b / a, by simp [w.pos_iff.1 (lt_of_lt_of_le zero_lt_one hwa), one_lt_div, div_lt_one,
    lt_of_le_of_lt' hvb hva, lt_of_le_of_lt' hwa hwb]⟩

end LinearOrderedSemifield

section LinearOrderedField

open Filter
open scoped Topology

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [OrderTopology S]
  {ι : Type*} [Finite ι] {v : ι → AbsoluteValue R S} {w : AbsoluteValue R S}
  {a b : R} {i : ι}

/--
Suppose that
- `v i` and `w` are absolute values on a field `R`.
- `v i` is inequivalent to `v j` for all `j ≠ i` via the divergent point `a : R`.
- `v i` is inequivalent to `w` via the divergent point `b : R`.
- `w a = 1`.

Then there is a common divergent point `k` causing both `v i` and `w` to be inequivalent to
each `v j` for `j ≠ i`.
-/
/-
**AbsoluteValue.exists_one_lt_lt_one_pi_of_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Abs
oluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose that
- `v i` and `w` are absolute values on a field `R`.
- `v i` is inequivalent to `v j` for all `j ≠ i` via the divergent point `a : R`
.
- `v i` is inequivalent to `w` via the divergent point `b : R`.
- `w a = 1`.

Then there is a common divergent point `k` causing both `v i` and `w` to be ineq
uivalent to
each `v j` for `j ≠ i`.
-/
private theorem exists_one_lt_lt_one_pi_of_eq_one (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1)
    (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : R, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  classical
  let c : ℕ → R := fun n ↦ a ^ n * b
  have hcᵢ : Tendsto (fun n ↦ (v i) (c n)) atTop atTop := by
    simpa [c] using Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt ha)
  have hcⱼ (j : ι) (hj : j ≠ i) : Tendsto (fun n ↦ (v j) (c n)) atTop (𝓝 0) := by
    simpa [c] using (tendsto_pow_atTop_nhds_zero_of_lt_one ((v j).nonneg _) (haj j hj)).mul_const _
  simp_rw +instances [OrderTopology.topology_eq_generate_intervals,
    TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_atTop_sets, Set.mem_preimage] at hcⱼ
  choose r₁ hr₁ using tendsto_atTop_atTop.1 hcᵢ 2
  choose rₙ hrₙ using fun j hj ↦ hcⱼ j hj (.Iio 1) (by simpa using ⟨1, .inr rfl⟩) (by simp)
  have := Fintype.ofFinite ι
  let r := Finset.univ.sup fun j ↦ if h : j = i then r₁ else rₙ j h
  refine ⟨c r, lt_of_lt_of_le (by linarith) (hr₁ r ?_), fun j hj ↦ ?_, by simpa [c, haw]⟩
  · exact Finset.le_sup_dite_pos (p := fun j ↦ j = i) (f := fun _ _ ↦ r₁) (Finset.mem_univ _) rfl
  · simpa using hrₙ j hj _ <| Finset.le_sup_dite_neg (fun j ↦ j = i) (Finset.mem_univ j) _

/--
Suppose that
- `v i` and `w` are absolute values on a field `R`.
- `v i` is inequivalent to `v j` for all `j ≠ i` via the divergent point `a : R`.
- `v i` is inequivalent to `w` via the divergent point `b : R`.
- `1 < w a`.

Then there is a common divergent point `k : R` causing both `v i` and `w` to be inequivalent to
each `v j` for `j ≠ i`.
-/
/-
**AbsoluteValue.exists_one_lt_lt_one_pi_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Abs
oluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose that
- `v i` and `w` are absolute values on a field `R`.
- `v i` is inequivalent to `v j` for all `j ≠ i` via the divergent point `a : R`
.
- `v i` is inequivalent to `w` via the divergent point `b : R`.
- `1 < w a`.

Then there is a common divergent point `k : R` causing both `v i` and `w` to be 
inequivalent to
each `v j` for `j ≠ i`.
-/
private theorem exists_one_lt_lt_one_pi_of_one_lt (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1)
    (haw : 1 < w a) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : R, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  classical
  let c : ℕ → R := fun n ↦ 1 / (1 + a⁻¹ ^ n) * b
  have hcᵢ : Tendsto (fun n ↦ v i (c n)) atTop (𝓝 (v i b)) := by
    have : v i a⁻¹ < 1 := map_inv₀ (v i) a ▸ inv_lt_one_of_one_lt₀ ha
    simpa [c] using (tendsto_div_one_add_pow_nhds_one this).mul_const (v i b)
  have hcⱼ (j : ι) (hj : j ≠ i) : atTop.Tendsto (fun n ↦ v j (c n)) (𝓝 0) := by
    have : 1 < v j a⁻¹ := map_inv₀ (v j) _ ▸
      (one_lt_inv₀ <| (v j).pos fun h ↦ by linarith [map_zero (v _) ▸ h ▸ ha]).2 (haj j hj)
    simpa [c] using (tendsto_div_one_add_pow_nhds_zero this).mul_const _
  have hcₙ : atTop.Tendsto (fun n ↦ w (c n)) (𝓝 (w b)) := by
    have : w a⁻¹ < 1 := map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ haw
    simpa [c] using (tendsto_div_one_add_pow_nhds_one this).mul_const (w b)
  simp_rw +instances [OrderTopology.topology_eq_generate_intervals,
    TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_atTop_sets, Set.mem_preimage] at hcⱼ
  choose r₁ hr₁ using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_const_lt hb hcᵢ
  choose rₙ hrₙ using fun j hj ↦ hcⱼ j hj (.Iio 1) (by simpa using ⟨1, .inr rfl⟩) (by simp)
  choose rN hrN using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_lt_const hbw hcₙ
  have := Fintype.ofFinite ι
  let r := max (Finset.univ.sup fun j ↦ if h : j = i then r₁ else rₙ j h) rN
  refine ⟨c r, hr₁ r ?_, fun j hj ↦ ?_, ?_⟩
  · exact le_max_iff.2 <| .inl <|
      Finset.le_sup_dite_pos (p := fun j ↦ j = i) (f := fun _ _ ↦ r₁) (Finset.mem_univ _) rfl
  · exact hrₙ j hj _ <| le_max_iff.2 <| .inl <|
      Finset.le_sup_dite_neg (fun j ↦ j = i) (Finset.mem_univ j) _
  · exact hrN _ <| le_max_iff.2 (.inr le_rfl)

open Fintype Subtype in
/--
If `v : ι → AbsoluteValue R S` is a finite collection of non-trivial and pairwise inequivalent
absolute values, then for any `i` there is some `a : R` such that `1 < v i a` and
`v j a < 1` for all `j ≠ i`.
-/
/-
**AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv** 是 Mathlib 中的一个定理，位于命名空间
 `AbsoluteValue`。
形式化陈述：exists_one_lt_lt_one_pi_of_not_isEquiv (h : forall i, (v i).IsNontrivial) 
(hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) : forall i, exists (a : R), 1 < 
v i a ∧ forall j != i, v j a < 1
参数：h : forall i, (v i).IsNontrivial；hv : Pairwise fun i j => ¬(v i).IsEquiv (v j
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.induction_subsingleton_or_nontrivial`：Fintype.induction_subsingl
eton_or_nontrivial {P : forall (α) [Fintype α], Prop} (α : Type*) [Fintype α] (h
base : forall (α) [Fintype α] [Sub…
· 使用定理 `AbsoluteValue.IsNontrivial.exists_abv_gt_one`：∀ {R : Type u_3} {S : Type
 u_4} [inst : Field R] [inst_1 : Semifield S] [inst_2 : LinearOrder S] [IsStrict
OrderedRing S]   [ExistsAddOfLE S]…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.card_eq_two_iff'`：card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ exists
! y, y != x
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `AbsoluteValue.exists_one_lt_lt_one_of_not_isEquiv`：exists_one_lt_lt_one_
of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial) (hw : w.IsNontriv
ial) (h : ¬v.IsEquiv w) : exists a : R,…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_of_le_of_ne`：∀ {n m : ℕ}, n ≤ m → ¬n = m → n < m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用引理 `Fintype.card_subtype_lt`：Fintype.card_subtype_lt [Fintype α] {p : α -> P
rop} [Fintype {a // p a}] {x : α} (hx : ¬p x) : Fintype.card { x // p x } < Fint
ype.card α
· 使用引理 `Pairwise.comp_of_injective`：Pairwise.comp_of_injective (hr : Pairwise r)
 {f : β -> α} (hf : Injective f) : Pairwise (r on f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
If `v : ι → AbsoluteValue R S` is a finite collection of non-trivial and pairwis
e inequivalent
absolute values, then for any `i` there is some `a : R` such that `1 < v i a` an
d
`v j a < 1` for all `j ≠ i`.
-/
theorem exists_one_lt_lt_one_pi_of_not_isEquiv (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) :
    ∀ i, ∃ (a : R), 1 < v i a ∧ ∀ j ≠ i, v j a < 1 := by
  classical
  have := Fintype.ofFinite ι
  let P (ι : Type _) [Fintype ι] : Prop :=
    ∀ v : ι → AbsoluteValue R S, (∀ i, (v i).IsNontrivial) →
      (Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) → ∀ i, ∃ (a : R), 1 < v i a ∧ ∀ j ≠ i, v j a < 1
  -- Use strong induction on the index.
  revert hv h; refine induction_subsingleton_or_nontrivial (P := P) ι (fun ι _ _ v h hv i ↦ ?_)
    (fun ι _ _ ih v h hv i ↦ ?_) v
  · -- If `ι` is trivial this follows immediately from `(v i).IsNontrivial`.
    let ⟨a, ha⟩ := (h i).exists_abv_gt_one
    exact ⟨a, ha, fun j hij ↦ absurd (Subsingleton.elim i j) hij.symm⟩
  · rcases eq_or_ne (card ι) 2 with (hc | hc)
    · -- If `ι` has two elements this is `exists_one_lt_lt_one_of_not_isEquiv`.
      let ⟨j, hj⟩ := (Nat.card_eq_two_iff' i).1 <| card_eq_nat_card ▸ hc
      let ⟨a, ha⟩ := (v i).exists_one_lt_lt_one_of_not_isEquiv (h i) (h j) (hv hj.1.symm)
      exact ⟨a, ha.1, fun _ h ↦ hj.2 _ h ▸ ha.2⟩
    have hlt : 2 < card ι := Nat.lt_of_le_of_ne (one_lt_card_iff_nontrivial.2 ‹_›) hc.symm
    -- Otherwise, choose another distinguished index `j ≠ i`.
    let ⟨j, hj⟩ := exists_ne i
    -- Apply induction first on the subcollection `v i` for `i ≠ j` to get `a : K`
    let ⟨a, ha⟩ := ih {k : ι // k ≠ j} (card_subtype_lt fun a ↦ a rfl) (restrict _ v)
      (fun i ↦ h _) (hv.comp_of_injective val_injective) ⟨i, hj.symm⟩
    -- Then apply induction next to the subcollection `{v i, v j}` to get `b : K`.
    let ⟨b, hb⟩ := ih {k : ι // k = i ∨ k = j} (by linarith [card_subtype_eq_or_eq_of_ne hj.symm])
      (restrict _ v) (fun _ ↦ h _) (hv.comp_of_injective val_injective) ⟨i, .inl rfl⟩
    rcases eq_or_ne (v j a) 1 with (ha₁ | ha₁)
    · -- If `v j a = 1` then take a large enough value from the sequence `a ^ n * b`.
      let ⟨c, hc⟩ := exists_one_lt_lt_one_pi_of_eq_one ha.1 ha.2 ha₁ hb.1 (hb.2 ⟨j, .inr rfl⟩
        (by grind))
      refine ⟨c, hc.1, fun k hk ↦ ?_⟩
      rcases eq_or_ne k j with (rfl | h); try exact hc.2.2; exact hc.2.1 ⟨k, h⟩ (by grind)
    rcases ha₁.lt_or_gt with (ha_lt | ha_gt)
    · -- If `v j a < 1` then `a` works as the divergent point.
      refine ⟨a, ha.1, fun k hk ↦ ?_⟩
      rcases eq_or_ne k j with (rfl | h); try exact ha_lt; exact ha.2 ⟨k, h⟩ (by grind)
    · -- If `1 < v j a` then take a large enough value from the sequence `b / (1 + a ^ (-n))`.
      let ⟨c, hc⟩ := exists_one_lt_lt_one_pi_of_one_lt ha.1 ha.2 ha_gt hb.1 (hb.2 ⟨j, .inr rfl⟩
        (by grind))
      refine ⟨c, hc.1, fun k hk ↦ ?_⟩
      rcases eq_or_ne k j with (rfl | h); try exact hc.2.2; exact hc.2.1 ⟨k, h⟩ (by grind)

end LinearOrderedField

section Real

open Real Topology

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

/-
**AbsoluteValue.IsEquiv.log_div_log_pos** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue
.IsEquiv`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {v w : AbsoluteValue F ℝ},   v.IsEquiv w
 → ∀ {a : F}, a ≠ 0 → w a ≠ 1 → 0 < Real.log (w a) / Real.log (v a)
参数：w a；v a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `neg_pos_of_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, a < 0 → 0 < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_neg`：log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.IsEquiv.lt_one_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `AbsoluteValue.IsEquiv.one_lt_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
-/
theorem IsEquiv.log_div_log_pos (h : v.IsEquiv w) {a : F} (ha₀ : a ≠ 0) (ha₁ : w a ≠ 1) :
    0 < (w a).log / (v a).log := by
  rcases ha₁.lt_or_gt with hwa | hwa
  · simpa using div_pos (neg_pos_of_neg <| log_neg (w.pos ha₀) (hwa))
      (neg_pos_of_neg <| log_neg (v.pos ha₀) (h.lt_one_iff.2 hwa))
  · exact div_pos (log_pos <| hwa) (log_pos (h.one_lt_iff.2 hwa))

/--
If $v$ and $w$ are two real absolute values on a field $F$, equivalent in the sense that
$v(x) \leq v(y)$ if and only if $w(x) \leq w(y)$, then $\frac{\log (v(a))}{\log (w(a))}$ is
constant for all $0 \neq a\in F$ with $v(a) \neq 1$.
-/
/-
**AbsoluteValue.IsEquiv.log_div_log_eq_log_div_log** 是 Mathlib 中的一个定理，位于命名空间 `Ab
soluteValue.IsEquiv`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {v w : AbsoluteValue F ℝ},   v.IsEquiv w
 →     ∀ {a : F},       a ≠ 0 → v a ≠ 1 → ∀ {b : F}, b ≠ 0 → v b ≠ 1 → Real.log 
(v b) / Real.log (w b) = Real.log (v a) / Real.log (w a)
参数：v b；w b；v a；w a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AbsoluteValue.IsEquiv.one_lt_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_div_iff₀`：div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c /
 d ↔ a * d < c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `AbsoluteValue.IsEquiv.lt_one_iff`：∀ {R : Type u_1} [inst : Semiring R] {
S : Type u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteV
alue R S} [IsDomain S]…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
If $v$ and $w$ are two real absolute values on a field $F$, equivalent in the se
nse that
$v(x) \leq v(y)$ if and only if $w(x) \leq w(y)$, then $\frac{\log (v(a))}{\log 
(w(a))}$ is
constant for all $0 \neq a\in F$ with $v(a) \neq 1$.
-/
theorem IsEquiv.log_div_log_eq_log_div_log (h : v.IsEquiv w)
    {a : F} (ha₀ : a ≠ 0) (ha₁ : v a ≠ 1) {b : F} (hb₀ : b ≠ 0) (hb₁ : v b ≠ 1) :
    (v b).log / (w b).log = (v a).log / (w a).log := by
  by_contra! h_ne
  wlog! ha : 1 < v a generalizing a b
  · apply this (inv_ne_zero ha₀) (by simpa) hb₀ hb₁ (by simpa)
    simpa using one_lt_inv_iff₀.2 ⟨v.pos ha₀, ha₁.lt_of_le ha⟩
  wlog! hb : 1 < v b generalizing a b
  · apply this ha₀ ha₁ (inv_ne_zero hb₀) (by simpa) (by simpa) ha
    simpa using one_lt_inv_iff₀.2 ⟨v.pos hb₀, hb₁.lt_of_le hb⟩
  wlog! h_lt : (v b).log / (w b).log < (v a).log / (w a).log generalizing a b
  · exact this hb₀ hb₁ ha₀ ha₁ h_ne.symm hb ha <| lt_of_le_of_ne h_lt h_ne.symm
  have hwa := h.one_lt_iff.1 ha
  have hwb := h.one_lt_iff.1 hb
  rw [div_lt_div_iff₀ (log_pos hwb) (log_pos hwa), mul_comm (v a).log,
    ← div_lt_div_iff₀ (log_pos ha) (log_pos hwa)] at h_lt
  let ⟨q, ⟨hq₁, hq₂⟩⟩ := exists_rat_btwn h_lt
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hq₁ hq₂
  rw [div_lt_div_iff₀ (log_pos ha) (by simp [q.den_pos]), mul_comm, ← log_pow, ← log_zpow,
    log_lt_log_iff (pow_pos (by linarith) _) (zpow_pos (by linarith) _),
    ← div_lt_one (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at hq₁
  rw [div_lt_div_iff₀ (by simp [q.den_pos]) (log_pos hwa), mul_comm (w _).log,
    ← log_pow, ← log_zpow, log_lt_log_iff (zpow_pos (by linarith) _) (pow_pos (by linarith) _),
    ← one_lt_div (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at hq₂
  exact not_lt_of_gt (h.lt_one_iff.1 hq₁) hq₂

/--
If `v` and `w` are two real absolute values on a field `F`, then `v` and `w` are equivalent if
and only if there exists a positive real constant `c` such that for all `x : R`, `(f x)^c = g x`.
-/
/-
**AbsoluteValue.isEquiv_iff_exists_rpow_eq** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteVa
lue`。
形式化陈述：isEquiv_iff_exists_rpow_eq {v w : AbsoluteValue F Real} : v.IsEquiv w ↔ ex
ists c : Real, 0 < c ∧ (v · ^ c) = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.IsEquiv.log_div_log_pos`：∀ {F : Type u_1} [inst : Field F]
 {v w : AbsoluteValue F ℝ},   v.IsEquiv w → ∀ {a : F}, a ≠ 0 → w a ≠ 1 → 0 < Rea
l.log (w a) / Real.log (v a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
If `v` and `w` are two real absolute values on a field `F`, then `v` and `w` are
 equivalent if
and only if there exists a positive real constant `c` such that for all `x : R`,
 `(f x)^c = g x`.
-/
theorem isEquiv_iff_exists_rpow_eq {v w : AbsoluteValue F ℝ} :
    v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, h⟩ ↦ isEquiv_iff_lt_one_iff.2
    fun x ↦ h ▸ (rpow_lt_one_iff' (v.nonneg x) ht).symm⟩
  by_cases hw : w.IsNontrivial
  · let ⟨a, ha₀, ha₁⟩ := hw
    refine ⟨(w a).log / (v a).log, h.log_div_log_pos ha₀ ha₁, funext fun b ↦ ?_⟩
    rcases eq_or_ne b 0 with rfl | hb₀; · simp [zero_rpow (by linarith [h.log_div_log_pos ha₀ ha₁])]
    rcases eq_or_ne (w b) 1 with hb₁ | hb₁; · simp [hb₁, h.eq_one_iff.2 hb₁]
    rw [← h.symm.log_div_log_eq_log_div_log ha₀ ha₁ hb₀ hb₁, div_eq_inv_mul, rpow_mul (v.nonneg _),
      rpow_inv_log (v.pos hb₀) (h.eq_one_iff.not.2 hb₁), exp_one_rpow, exp_log (w.pos hb₀)]
  · exact ⟨1, zero_lt_one,
      funext fun x ↦ by
        rcases eq_or_ne x 0 with rfl | h₀ <;>
        aesop (add simp [h.isNontrivial_congr])⟩
/-
**AbsoluteValue.IsEquiv.equivWithAbs_image_mem_nhds_zero** 是 Mathlib 中的一个定理，位于命名
空间 `AbsoluteValue.IsEquiv`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {v w : AbsoluteValue F ℝ},   v.IsEquiv w
 → ∀ {U : Set (WithAbs v)}, U ∈ nhds 0 → ⇑(WithAbs.congr v w (RingEquiv.refl F))
 '' U ∈ nhds 0
参数：WithAbs v；WithAbs.congr v w (RingEquiv.refl F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AbsoluteValue.isEquiv_iff_exists_rpow_eq`：isEquiv_iff_exists_rpow_eq {v 
w : AbsoluteValue F Real} : v.IsEquiv w ↔ exists c : Real, 0 < c ∧ (v · ^ c) = w
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Real.rpow_lt_rpow_iff`：rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z < y ^ z ↔ x < y
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用引理 `WithAbs.norm_eq_apply_ofAbs`：norm_eq_apply_ofAbs (v : AbsoluteValue R Re
al) (x : WithAbs v) : ‖x‖ = v x.ofAbs
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
-/
theorem IsEquiv.equivWithAbs_image_mem_nhds_zero (h : v.IsEquiv w) {U : Set (WithAbs v)}
    (hU : U ∈ 𝓝 0) : WithAbs.congr v w (.refl F) '' U ∈ 𝓝 0 := by
  rw [Metric.mem_nhds_iff] at hU ⊢
  obtain ⟨ε, hε, hU⟩ := hU
  obtain ⟨c, hc, hvw⟩ := isEquiv_iff_exists_rpow_eq.1 h
  refine ⟨ε ^ c, rpow_pos_of_pos hε _, fun x hx ↦ ?_⟩
  rw [← RingEquiv.apply_symm_apply (WithAbs.congr v w (.refl F)) x]
  refine Set.mem_image_of_mem _ (hU ?_)
  rw [Metric.mem_ball, dist_zero_right, WithAbs.norm_eq_apply_ofAbs, ← funext_iff.1 hvw,
    rpow_lt_rpow_iff (v.nonneg _) hε.le hc] at hx
  simpa [WithAbs.norm_eq_apply_ofAbs]

open Topology IsTopologicalAddGroup in
/-
**AbsoluteValue.IsEquiv.isEmbedding_equivWithAbs** 是 Mathlib 中的一个定理，位于命名空间 `Abso
luteValue.IsEquiv`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] {v w : AbsoluteValue F ℝ},   v.IsEquiv w
 → Topology.IsEmbedding ⇑(WithAbs.congr v w (RingEquiv.refl F))
参数：WithAbs.congr v w (RingEquiv.refl F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space X] {f : X → Y},   To
pology.IsInducing f →…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsTopologicalAddGroup.isInducing_iff_nhds_zero`：∀ {G : Type w} [inst : T
opologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {H : Type u_1
}   [inst_3 : AddGroup H] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `AbsoluteValue.IsEquiv.equivWithAbs_image_mem_nhds_zero`：∀ {F : Type u_1}
 [inst : Field F] {v w : AbsoluteValue F ℝ},   v.IsEquiv w → ∀ {U : Set (WithAbs
 v)}, U ∈ nhds 0 → ⇑(WithAbs.congr v w (Ring…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingEquiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : R ≃+* S) (
s : Set R) : e '' s = e.symm ⁻¹' s
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map_iff_exists_image`：mem_map_iff_exists_image : t in map m f
 ↔ exists s in f, m '' s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_equiv_symm`：map_equiv_symm (e : α ≃ β) (f : Filter β) : map e
.symm f = comap e f
· 使用定理 `RingEquiv.coe_toEquiv`：coe_toEquiv (f : R ≃+* S) : ⇑(f : R ≃ S) = f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `AbsoluteValue.IsEquiv.symm`：∀ {R : Type u_1} [inst : Semiring R] {S : Ty
pe u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v w : AbsoluteValue R
 S}, v.IsEquiv w…
（共 32 条，此处仅展示前 30 条）
-/
theorem IsEquiv.isEmbedding_equivWithAbs (h : v.IsEquiv w) :
    IsEmbedding (WithAbs.congr v w (.refl F)) := by
  refine IsInducing.isEmbedding <| isInducing_iff_nhds_zero.2 <| Filter.ext fun U ↦
    ⟨fun hU ↦ ?_, fun hU ↦ ?_⟩
  · exact ⟨WithAbs.congr v w (.refl F)'' U, h.equivWithAbs_image_mem_nhds_zero hU,
      by
        #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
        (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
        goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
        the new canonicalizer; a minimization would help. The original proof was:
        `grind [RingEquiv.image_eq_preimage_symm, Set.preimage_preimage]` -/
        rw [RingEquiv.image_eq_preimage_symm, Set.preimage_preimage]; simp⟩
  · rw [← RingEquiv.coe_toEquiv, ← Filter.map_equiv_symm] at hU
    obtain ⟨s, hs, hss⟩ := Filter.mem_map_iff_exists_image.1 hU
    rw [← RingEquiv.coe_toEquiv_symm, WithAbs.congr_symm] at hss
    exact Filter.mem_of_superset (h.symm.equivWithAbs_image_mem_nhds_zero hs) hss
/-
**AbsoluteValue.isEquiv_iff_isHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValu
e`。
形式化陈述：isEquiv_iff_isHomeomorph (v w : AbsoluteValue F Real) : v.IsEquiv w ↔ IsHo
meomorph (WithAbs.congr v w (.refl F))
参数：v w : AbsoluteValue F Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isHomeomorph_iff_isEmbedding_surjective`：isHomeomorph_iff_isEmbedding_su
rjective : IsHomeomorph f ↔ IsEmbedding f ∧ Surjective f where mp hf
· 使用定理 `AbsoluteValue.IsEquiv.isEmbedding_equivWithAbs`：∀ {F : Type u_1} [inst :
 Field F] {v w : AbsoluteValue F ℝ},   v.IsEquiv w → Topology.IsEmbedding ⇑(With
Abs.congr v w (RingEquiv.refl F))
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.isEquiv_iff_lt_one_iff`：isEquiv_iff_lt_one_iff : v.IsEquiv
 w ↔ forall x, v x < 1 ↔ w x < 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithAbs.ofAbs_toAbs`：ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x
· 使用引理 `WithAbs.norm_eq_apply_ofAbs`：norm_eq_apply_ofAbs (v : AbsoluteValue R Re
al) (x : WithAbs v) : ‖x‖ = v x.ofAbs
· 使用引理 `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one`：tendsto_pow_atTop_nhds_zero
_iff_norm_lt_one {R : Type*} [SeminormedRing R] [NormMulClass R] {x : R} : Tends
to (fun n : Nat => x ^ n) atTop (…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem isEquiv_iff_isHomeomorph (v w : AbsoluteValue F ℝ) :
    v.IsEquiv w ↔ IsHomeomorph (WithAbs.congr v w (.refl F)) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  refine ⟨fun h ↦ ⟨h.isEmbedding_equivWithAbs, RingEquiv.surjective _⟩, fun ⟨hi, _⟩ ↦ ?_⟩
  refine isEquiv_iff_lt_one_iff.2 fun x ↦ ?_
  conv_lhs => rw [← WithAbs.ofAbs_toAbs v x]
  conv_rhs => rw [← WithAbs.ofAbs_toAbs w x]
  rw [← WithAbs.norm_eq_apply_ofAbs, ← WithAbs.norm_eq_apply_ofAbs,
    ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  exact ⟨fun h ↦ by simpa [Function.comp_def] using (hi.continuous.tendsto 0).comp h, fun h ↦ by
    simpa [Function.comp_def] using (hi.continuous_iff (f := (WithAbs.congr v w (.refl F)).symm)).2
      continuous_id |>.tendsto 0 |>.comp h ⟩

end Real

section WeakApproximation

open Filter
open scoped Topology

variable {F : Type*} [Field F]

/--
If `v : ι → AbsoluteValue F ℝ` is a finite family of nontrivial, pairwise inequivalent
real absolute values on a field `F`, then the diagonal embedding
`algebraMap F ((i : ι) → WithAbs (v i))` has dense range.

This is the abstract weak approximation theorem; see
`NumberField.InfinitePlace.denseRange_algebraMap_pi` for the number-field special case.
-/
/-
**AbsoluteValue.denseRange_algebraMap_pi** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValu
e`。
形式化陈述：denseRange_algebraMap_pi {ι : Type*} [Finite ι] {v : ι -> AbsoluteValue F 
Real} (h : forall i, (v i).IsNontrivial) (hv : Pairwise fun i j => ¬(v i).IsEqui
v (v j)) : DenseRange algebraMap F ((i : ι) -> WithAbs (v i))
参数：h : forall i, (v i).IsNontrivial；hv : Pairwise fun i j => ¬(v i).IsEquiv (v j
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.denseRange_iff`：denseRange_iff {f : β -> α} : DenseRange f ↔ fora
ll x, forall r > 0, exists y, dist x (f y) < r
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_pi_single`：∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : Dec
idableEq ι] {M : ι → Type u_6} [inst_2 : (i : ι) → AddCommMonoid (M i)]   (i : ι
) (f : (i :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `tendsto_finsetSum`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : AddCommMonoid M] [ContinuousAdd M]   {f : ι → α 
→ M} {x…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
If `v : ι → AbsoluteValue F ℝ` is a finite family of nontrivial, pairwise inequi
valent
real absolute values on a field `F`, then the diagonal embedding
`algebraMap F ((i : ι) → WithAbs (v i))` has dense range.

This is the abstract weak approximation theorem; see
`NumberField.InfinitePlace.denseRange_algebraMap_pi` for the number-field specia
l case.
-/
theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] {v : ι → AbsoluteValue F ℝ}
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) :
    DenseRange <| algebraMap F ((i : ι) → WithAbs (v i)) := by
  classical
  have := Fintype.ofFinite ι
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using exists_one_lt_lt_one_pi_of_not_isEquiv h hv
  let y := fun n : ℕ ↦ ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (v i) (z i)
  have htend : atTop.Tendsto (fun n i ↦ (WithAbs.equiv (v i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have hlt : (v u) (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using Or.inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one hlt).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (v i)) hw (z w)]
      have hgt : 1 < (v u) (a w)⁻¹ := by
        rw [map_inv₀]
        refine one_lt_inv_iff₀.mpr ⟨(v u).pos_iff.mpr fun ha ↦ ?_, (hx w).2 u hw⟩
        linarith [map_zero (v w) ▸ ha ▸ (hx w).1]
      have := (v u).tendsto_div_one_add_pow_nhds_zero hgt
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (v u)).symm _)
  let ⟨N, hN⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap F _ (y N)) ▸ hN N le_rfl⟩

end WeakApproximation

end AbsoluteValue

