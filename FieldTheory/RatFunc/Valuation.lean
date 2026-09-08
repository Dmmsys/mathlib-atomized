/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Valuations on F(t)

This file defines the valuation at infinity on the field of rational functions `F(t)`.

## Main definitions

- `RatFunc.inftyValuation` : The place at infinity on `F(t)` is the nonarchimedean
  valuation on `F(t)` with uniformizer `1/t`.
- `RatFunc.CompletionAtInfty` : The completion `F((t⁻¹))` of `F(t)` with respect to the
  valuation at infinity.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/

@[expose] public section


public noncomputable section

namespace RatFunc

variable (F K : Type*) [Field F] [Field K]

/-! ### The place at infinity on F(t) -/

section InftyValuation

open Multiplicative WithZero Polynomial

variable [DecidableEq (RatFunc F)]

/-- The valuation at infinity is the nonarchimedean valuation on `F(t)` with uniformizer `1/t`.
Explicitly, if `f/g ∈ F(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`exp (degree(f) - degree(g))`. -/
/-
**RatFunc.inftyValuationDef** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：inftyValuationDef (r : RatFunc F) : Intᵐ⁰
参数：r : RatFunc F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation at infinity is the nonarchimedean valuation on `F(t)` with uniform
izer `1/t`.
Explicitly, if `f/g ∈ F(t)` is a nonzero quotient of polynomials, its valuation 
at infinity is
`exp (degree(f) - degree(g))`.
-/
def inftyValuationDef (r : RatFunc F) : ℤᵐ⁰ :=
  if r = 0 then 0 else exp r.intDegree
/-
**RatFunc.InftyValuation.map_zero'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.InftyValua
tion`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)], RatF
unc.inftyValuationDef F 0 = 0
参数：F : Type u_1；RatFunc F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem InftyValuation.map_zero' : inftyValuationDef F 0 = 0 :=
  if_pos rfl
/-
**RatFunc.InftyValuation.map_one'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.InftyValuat
ion`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)], RatF
unc.inftyValuationDef F 1 = 1
参数：F : Type u_1；RatFunc F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.intDegree_one`：intDegree_one : intDegree (1 : K⟮X⟯) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem InftyValuation.map_one' : inftyValuationDef F 1 = 1 :=
  (if_neg one_ne_zero).trans <| by simp
/-
**RatFunc.InftyValuation.map_mul'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.InftyValuat
ion`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] (x y 
: RatFunc F),   RatFunc.inftyValuationDef F (x * y) = RatFunc.inftyValuationDef 
F x * RatFunc.inftyValuationDef F y
参数：F : Type u_1；RatFunc F；x y : RatFunc F；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.inftyValuationDef.eq_1`：∀ (F : Type u_1) [inst : Field F] [inst_
1 : DecidableEq (RatFunc F)] (r : RatFunc F),   RatFunc.inftyValuationDef F r = 
if r = 0 then 0 else…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `RatFunc.intDegree_mul`：intDegree_mul {x y : K⟮X⟯} (hx : x != 0) (hy : y 
!= 0) : intDegree (x * y) = intDegree x + intDegree y
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem InftyValuation.map_mul' (x y : RatFunc F) :
    inftyValuationDef F (x * y) = inftyValuationDef F x * inftyValuationDef F y := by
  rw [inftyValuationDef, inftyValuationDef, inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · simp_all [RatFunc.intDegree_mul]
/-
**RatFunc.InftyValuation.map_add_le_max'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.Inft
yValuation`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] (x y 
: RatFunc F),   RatFunc.inftyValuationDef F (x + y) ≤ max (RatFunc.inftyValuatio
nDef F x) (RatFunc.inftyValuationDef F y)
参数：F : Type u_1；RatFunc F；x y : RatFunc F；x + y；RatFunc.inftyValuationDef F x；Ra
tFunc.inftyValuationDef F y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.intDegree_add_le`：intDegree_add_le {x y : K⟮X⟯} (hy : y != 0) (h
xy : x + y != 0) : intDegree (x + y) <= max (intDegree x) (intDegree y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem InftyValuation.map_add_le_max' (x y : RatFunc F) :
    inftyValuationDef F (x + y) ≤ max (inftyValuationDef F x) (inftyValuationDef F y) := by
  unfold inftyValuationDef
  have := @RatFunc.intDegree_add_le F
  aesop

@[simp]
/-
**RatFunc.inftyValuation_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：inftyValuation_of_nonzero {x : RatFunc F} (hx : x != 0) : inftyValuationDe
f F x = exp x.intDegree
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.inftyValuationDef.eq_1`：∀ (F : Type u_1) [inst : Field F] [inst_
1 : DecidableEq (RatFunc F)] (r : RatFunc F),   RatFunc.inftyValuationDef F r = 
if r = 0 then 0 else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem inftyValuation_of_nonzero {x : RatFunc F} (hx : x ≠ 0) :
    inftyValuationDef F x = exp x.intDegree := by
  rw [inftyValuationDef, if_neg hx]

/-- The valuation at infinity on `F(t)`. -/
/-
**RatFunc.inftyValuation** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：inftyValuation : Valuation (RatFunc F) Intᵐ⁰ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.InftyValuation.map_zero'`：∀ (F : Type u_1) [inst : Field F] [ins
t_1 : DecidableEq (RatFunc F)], RatFunc.inftyValuationDef F 0 = 0
· 使用定理 `RatFunc.InftyValuation.map_one'`：∀ (F : Type u_1) [inst : Field F] [inst
_1 : DecidableEq (RatFunc F)], RatFunc.inftyValuationDef F 1 = 1
· 使用定理 `RatFunc.InftyValuation.map_mul'`：∀ (F : Type u_1) [inst : Field F] [inst
_1 : DecidableEq (RatFunc F)] (x y : RatFunc F),   RatFunc.inftyValuationDef F (
x * y) = RatFunc.inft…
· 使用定理 `RatFunc.InftyValuation.map_add_le_max'`：∀ (F : Type u_1) [inst : Field F
] [inst_1 : DecidableEq (RatFunc F)] (x y : RatFunc F),   RatFunc.inftyValuation
Def F (x + y) ≤ max (RatFunc…

--- 原说明 ---
The valuation at infinity on `F(t)`.
-/
def inftyValuation : Valuation (RatFunc F) ℤᵐ⁰ where
  toFun := inftyValuationDef F
  map_zero' := InftyValuation.map_zero' F
  map_one' := InftyValuation.map_one' F
  map_mul' := InftyValuation.map_mul' F
  map_add_le_max' := InftyValuation.map_add_le_max' F
/-
**RatFunc.inftyValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：inftyValuation_apply {x : RatFunc F} : inftyValuation F x = inftyValuation
Def F x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem inftyValuation_apply {x : RatFunc F} : inftyValuation F x = inftyValuationDef F x :=
  rfl

@[simp]
/-
**RatFunc.inftyValuation.C** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.inftyValuation`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] {k : 
F},   k ≠ 0 → (RatFunc.inftyValuation F) (RatFunc.C k) = 1
参数：F : Type u_1；RatFunc F；RatFunc.inftyValuation F；RatFunc.C k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.inftyValuation_of_nonzero`：inftyValuation_of_nonzero {x : RatFun
c F} (hx : x != 0) : inftyValuationDef F x = exp x.intDegree
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RatFunc.intDegree_C`：intDegree_C (k : K) : intDegree (C k) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inftyValuation.C {k : F} (hk : k ≠ 0) :
    inftyValuation F (RatFunc.C k) = 1 := by
  simp [inftyValuation_apply, hk]

@[simp]
/-
**RatFunc.inftyValuation.X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.inftyValuation`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)],   (R
atFunc.inftyValuation F) RatFunc.X = WithZero.exp 1
参数：F : Type u_1；RatFunc F；RatFunc.inftyValuation F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RatFunc.intDegree_X`：intDegree_X : intDegree (X : K⟮X⟯) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `RatFunc.X_ne_zero`：X_ne_zero : (X : K⟮X⟯) != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inftyValuation.X : inftyValuation F RatFunc.X = exp 1 := by
  simp [inftyValuation_apply, inftyValuationDef, if_neg RatFunc.X_ne_zero, RatFunc.intDegree_X]
/-
**RatFunc.inftyValuation.X_zpow** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.inftyValuatio
n`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] (m : 
ℤ),   (RatFunc.inftyValuation F) (RatFunc.X ^ m) = WithZero.exp m
参数：F : Type u_1；RatFunc F；m : ℤ；RatFunc.inftyValuation F；RatFunc.X ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `RatFunc.inftyValuation.X`：∀ (F : Type u_1) [inst : Field F] [inst_1 : De
cidableEq (RatFunc F)],   (RatFunc.inftyValuation F) RatFunc.X = WithZero.exp 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inftyValuation.X_zpow (m : ℤ) : inftyValuation F (RatFunc.X ^ m) = exp m := by simp
/-
**RatFunc.inftyValuation.X_inv** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.inftyValuation
`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)],   (R
atFunc.inftyValuation F) (1 / RatFunc.X) = WithZero.exp (-1)
参数：F : Type u_1；RatFunc F；RatFunc.inftyValuation F；1 / RatFunc.X；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
· 使用定理 `RatFunc.inftyValuation.X_zpow`：∀ (F : Type u_1) [inst : Field F] [inst_1
 : DecidableEq (RatFunc F)] (m : ℤ),   (RatFunc.inftyValuation F) (RatFunc.X ^ m
) = WithZero.exp m
-/
theorem inftyValuation.X_inv : inftyValuation F (1 / RatFunc.X) = exp (-1) := by
  rw [one_div, ← zpow_neg_one, inftyValuation.X_zpow]

-- Dropped attribute `@[simp]` due to issue described here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60synthInstance.2EmaxHeartbeats.60.20error.20but.20only.20in.20.60simpNF.60
/-
**RatFunc.inftyValuation.polynomial** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.inftyValu
ation`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] {p : 
Polynomial F},   p ≠ 0 → RatFunc.inftyValuationDef F ((algebraMap (Polynomial F)
 (RatFunc F)) p) = WithZero.exp ↑p.natDegree
参数：F : Type u_1；RatFunc F；(algebraMap (Polynomial F) (RatFunc F)) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.inftyValuationDef.eq_1`：∀ (F : Type u_1) [inst : Field F] [inst_
1 : DecidableEq (RatFunc F)] (r : RatFunc F),   RatFunc.inftyValuationDef F r = 
if r = 0 then 0 else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `Polynomial.instIsCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : Semi
ring R] [IsCancelAdd R] [IsCancelMulZero R], IsCancelMulZero (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `RatFunc.instIsFractionRingPolynomial`：∀ (K : Type u) [inst : CommRing K]
 [inst_1 : IsDomain K], IsFractionRing (Polynomial K) (RatFunc K)
· 使用定理 `RatFunc.intDegree_polynomial`：intDegree_polynomial {p : K[X]} : intDegre
e (algebraMap K[X] K⟮X⟯ p) = natDegree p
-/
theorem inftyValuation.polynomial {p : F[X]} (hp : p ≠ 0) :
    inftyValuationDef F (algebraMap F[X] (RatFunc F) p) = exp (p.natDegree : ℤ) := by
  rw [inftyValuationDef, if_neg (by simpa), RatFunc.intDegree_polynomial]
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Valuation.IsNontrivial (inftyValuation F) := ⟨RatFunc.X, by simp⟩
/-
**RatFunc.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Valuation.IsTrivialOn F (inftyValuation F) :=
  ⟨fun _ hx ↦ by simp [inftyValuation.C _ hx]⟩

/-- The valued field `F(t)` with the valuation at infinity. -/
@[instance_reducible]
/-
**RatFunc.inftyValued** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc`。
形式化陈述：inftyValued : Valued (RatFunc F) Intᵐ⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valued field `F(t)` with the valuation at infinity.
-/
def inftyValued : Valued (RatFunc F) ℤᵐ⁰ :=
  Valued.mk' <| inftyValuation F
/-
**RatFunc.inftyValued.def** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.inftyValued`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] {x : 
RatFunc F},   Valued.v x = RatFunc.inftyValuationDef F x
参数：F : Type u_1；RatFunc F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem inftyValued.def {x : RatFunc F} :
    (inftyValued F).v x = inftyValuationDef F x :=
  rfl

namespace CompletionAtInfty

/- We temporarily disable the existing valued instance coming from the ideal `X` to avoid diamonds
with the uniform space structure coming from the valuation at infinity. -/
attribute [-instance] RatFunc.valuedRatFunc

/- Locally add the uniform space structure coming from the valuation at infinity. This instance
is scoped in the `CompletionAtInfty` namescape in case it is needed in the future. -/
/-- The uniform space structure on `RatFunc F` coming from the valuation at infinity. -/
/-
**RatFunc.CompletionAtInfty.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc.CompletionAtInft
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform space structure on `RatFunc F` coming from the valuation at infinity
.
-/
scoped instance : UniformSpace (RatFunc F) := (inftyValued F).toUniformSpace

/-- The completion `F((t⁻¹))` of `F(t)` with respect to the valuation at infinity. -/
/-
**RatFunc.CompletionAtInfty._root_.RatFunc.CompletionAtInfty** 是 Mathlib 中的一个定义，
位于命名空间 `RatFunc.CompletionAtInfty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion `F((t⁻¹))` of `F(t)` with respect to the valuation at infinity.
-/
def _root_.RatFunc.CompletionAtInfty := UniformSpace.Completion (RatFunc F)
deriving Field, Algebra (RatFunc F), Coe (RatFunc F), Inhabited

/-- The valuation at infinity on `k(t)` extends to a valuation on `CompletionAtInfty`. -/
/-
**RatFunc.CompletionAtInfty.** 是 Mathlib 中的一个实例，位于命名空间 `RatFunc.CompletionAtInft
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation at infinity on `k(t)` extends to a valuation on `CompletionAtInfty
`.
-/
instance : Valued (CompletionAtInfty F) ℤᵐ⁰ :=
  inferInstanceAs <| Valued (UniformSpace.Completion (RatFunc F)) ℤᵐ⁰

end CompletionAtInfty

/-
**RatFunc.valuedCompletionAtInfty.def** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.valuedC
ompletionAtInfty`。
形式化陈述：∀ (F : Type u_1) [inst : Field F] [inst_1 : DecidableEq (RatFunc F)] {x : 
RatFunc.CompletionAtInfty F},   Valued.v x = Valued.extensionValuation x
参数：F : Type u_1；RatFunc F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valuedCompletionAtInfty.def {x : CompletionAtInfty F} :
  Valued.v x = (inftyValued F).extensionValuation x := rfl

end InftyValuation

end RatFunc

