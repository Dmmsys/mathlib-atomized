/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Archimedean
public import Mathlib.Algebra.Ring.Subring.Order
public import Mathlib.Order.Quotient
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Standard part function

Given a finite element in a non-archimedean field, the standard part function rounds it to the
unique closest real number. That is, it chops off any infinitesimals.

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

Given a finite element of the field, the `ArchimedeanClass.stdPart` function returns the real number
corresponding to this unique embedding. This function generalizes, among other things, the standard
part function on `Hyperreal`.

## References

* https://en.wikipedia.org/wiki/Standard_part_function
-/

@[expose] public noncomputable section

namespace ArchimedeanClass
variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsStrictOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in
/-- The valuation subring of elements in non-negative Archimedean classes, i.e. elements bounded by
some natural number. -/
/-
**ArchimedeanClass.FiniteElement** 是 Mathlib 中的一个定义，位于命名空间 `ArchimedeanClass`。
形式化陈述：FiniteElement : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation subring of elements in non-negative Archimedean classes, i.e. elem
ents bounded by
some natural number.
-/
def FiniteElement : Type _ :=
  (addValuation K).toValuation.valuationSubring
deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

namespace FiniteElement

/-
**ArchimedeanClass.FiniteElement.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean
Class.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K], ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem val_zero : (0 : FiniteElement K).1 = 0 := rfl
/-
**ArchimedeanClass.FiniteElement.val_one** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem val_one : (1 : FiniteElement K).1 = 1 := rfl
/-
**ArchimedeanClass.FiniteElement.val_add** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K]   (x y : ArchimedeanClass.FiniteElement K), ↑(x + y) = ↑x + ↑y
参数：x y : ArchimedeanClass.FiniteElement K；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem val_add (x y : FiniteElement K) : (x + y).1 = x.1 + y.1 := rfl
/-
**ArchimedeanClass.FiniteElement.val_sub** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K]   (x y : ArchimedeanClass.FiniteElement K), ↑(x - y) = ↑x - ↑y
参数：x y : ArchimedeanClass.FiniteElement K；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem val_sub (x y : FiniteElement K) : (x - y).1 = x.1 - y.1 := rfl
/-
**ArchimedeanClass.FiniteElement.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K]   (x y : ArchimedeanClass.FiniteElement K), ↑(x * y) = ↑x * ↑y
参数：x y : ArchimedeanClass.FiniteElement K；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem val_mul (x y : FiniteElement K) : (x * y).1 = x.1 * y.1 := rfl
/-
**ArchimedeanClass.FiniteElement.ext** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass
.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K]   {x y : ArchimedeanClass.FiniteElement K}, ↑x = ↑y → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
@[ext] theorem ext {x y : FiniteElement K} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- The constructor for `FiniteElement`. -/
/-
**ArchimedeanClass.FiniteElement.mk** 是 Mathlib 中的一个定义，位于命名空间 `ArchimedeanClass.
FiniteElement`。
形式化陈述：{K : Type u_1} →   [inst : LinearOrder K] →     [inst_1 : Field K] →      
 [inst_2 : IsOrderedRing K] → (x : K) → 0 ≤ ArchimedeanClass.mk x → ArchimedeanC
lass.FiniteElement K
参数：x : K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructor for `FiniteElement`.
-/
protected def mk (x : K) (h : 0 ≤ mk x) : FiniteElement K := ⟨x, h⟩
/-
**ArchimedeanClass.FiniteElement.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K],   ArchimedeanClass.FiniteElement.mk 0 ⋯ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mk_zero : FiniteElement.mk (0 : K) (by simp) = 0 := rfl
/-
**ArchimedeanClass.FiniteElement.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCl
ass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K],   ArchimedeanClass.FiniteElement.mk 1 ⋯ = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mk_one : FiniteElement.mk (1 : K) (by simp) = 1 := rfl
/-
**ArchimedeanClass.FiniteElement.mk_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Archimede
anClass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K] (n : ℕ),   ArchimedeanClass.FiniteElement.mk ↑n ⋯ = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_natCast_nonneg`：mk_natCast_nonneg (n : Nat) : 0 <= m
k (n : S)
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
@[simp] theorem mk_natCast (n : ℕ) : FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n := rfl
/-
**ArchimedeanClass.FiniteElement.mk_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Archimede
anClass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K] (n : ℤ),   ArchimedeanClass.FiniteElement.mk ↑n ⋯ = ↑n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_intCast_nonneg`：mk_intCast_nonneg (n : Int) : 0 <= m
k (n : S)
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
@[simp] theorem mk_intCast (n : ℤ) : FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n := rfl

@[simp]
/-
**ArchimedeanClass.FiniteElement.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCl
ass.FiniteElement`。
形式化陈述：neg_mk {x : K} (h : 0 <= mk x) : -FiniteElement.mk x h = FiniteElement.mk 
(-x) (by rwa [mk_neg])
参数：h : 0 <= mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem neg_mk {x : K} (h : 0 ≤ mk x) :
    -FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg]) :=
  rfl

@[simp]
/-
**ArchimedeanClass.FiniteElement.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archimedea
nClass.FiniteElement`。
形式化陈述：mk_add_mk (x y : K) (hx hy) : .mk x hx + .mk y hy = FiniteElement.mk (x + 
y) ((le_min hx hy).trans <| min_le_mk_add ..)
参数：x y : K；hx hy。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem mk_add_mk (x y : K) (hx hy) :
    .mk x hx + .mk y hy = FiniteElement.mk (x + y) ((le_min hx hy).trans <| min_le_mk_add ..) :=
  rfl

@[simp]
/-
**ArchimedeanClass.FiniteElement.mk_sub_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archimedea
nClass.FiniteElement`。
形式化陈述：mk_sub_mk (x y : K) (hx hy) : .mk x hx - .mk y hy = FiniteElement.mk (x - 
y) ((le_min hx hy).trans <| min_le_mk_sub ..)
参数：x y : K；hx hy。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem mk_sub_mk (x y : K) (hx hy) :
    .mk x hx - .mk y hy = FiniteElement.mk (x - y) ((le_min hx hy).trans <| min_le_mk_sub ..) :=
  rfl

@[simp]
/-
**ArchimedeanClass.FiniteElement.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archimedea
nClass.FiniteElement`。
形式化陈述：mk_mul_mk (x y : K) (hx hy) : .mk x hx * .mk y hy = FiniteElement.mk (x * 
y) (add_nonneg hx hy)
参数：x y : K；hx hy。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
theorem mk_mul_mk (x y : K) (hx hy) :
    .mk x hx * .mk y hy = FiniteElement.mk (x * y) (add_nonneg hx hy) :=
  rfl

@[simp]
/-
**ArchimedeanClass.FiniteElement.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean
Class.FiniteElement`。
形式化陈述：mk_le_mk (x y : K) (hx hy) : FiniteElement.mk x hx <= .mk y hy ↔ x <= y
参数：x y : K；hx hy。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk (x y : K) (hx hy) : FiniteElement.mk x hx ≤ .mk y hy ↔ x ≤ y :=
  .rfl

@[simp]
/-
**ArchimedeanClass.FiniteElement.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean
Class.FiniteElement`。
形式化陈述：mk_lt_mk (x y : K) (hx hy) : FiniteElement.mk x hx < .mk y hy ↔ x < y
参数：x y : K；hx hy。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk (x y : K) (hx hy) : FiniteElement.mk x hx < .mk y hy ↔ x < y :=
  .rfl
/-
**ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos** 是 Mathlib 中的一个定理，位于命名空间
 `ArchimedeanClass.FiniteElement`。
形式化陈述：not_isUnit_iff_mk_pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integer.not_isUnit_iff_valuation_lt_one`：∀ {F : Type u} {Γ₀ : 
Type v} [inst : Field F] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valua
tion F Γ₀}   {x : ↥v.integer}, ¬IsUnit …
-/
theorem not_isUnit_iff_mk_pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one
/-
**ArchimedeanClass.FiniteElement.isUnit_iff_mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间
 `ArchimedeanClass.FiniteElement`。
形式化陈述：isUnit_iff_mk_eq_zero {x : FiniteElement K} : IsUnit x ↔ mk x.1 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos`：not_isUnit_iff_mk_
pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_mk_eq_zero {x : FiniteElement K} : IsUnit x ↔ mk x.1 = 0 := by
  rw [← not_iff_not, not_isUnit_iff_mk_pos, lt_iff_not_ge, x.2.ge_iff_eq']
/-
**ArchimedeanClass.FiniteElement.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass.Fi
niteElement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RatCast (FiniteElement K) where
  ratCast q := .mk q (mk_ratCast_nonneg q)
/-
**ArchimedeanClass.FiniteElement.mk_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Archimede
anClass.FiniteElement`。
形式化陈述：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrd
eredRing K] (q : ℚ),   ArchimedeanClass.FiniteElement.mk ↑q ⋯ = ↑q
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_ratCast_nonneg`：mk_ratCast_nonneg (q : Rat) : 0 <= m
k (q : R)
-/
@[simp] theorem mk_ratCast (q : ℚ) : FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q := rfl

@[no_expose]
/-
**ArchimedeanClass.FiniteElement.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanClass.Fi
niteElement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FloorRing (FiniteElement K) :=
  .ofBounded _ fun x ↦ by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, (le_abs_self x).trans ?_⟩
    simpa using! hn

end FiniteElement

set_option backward.isDefEq.respectTransparency.types false in
variable (K) in
/-- The residue field of `FiniteElement`. This quotient inherits an order from `K`,
which makes it into a linearly ordered Archimedean field. -/
/-
**ArchimedeanClass.FiniteResidueField** 是 Mathlib 中的一个定义，位于命名空间 `ArchimedeanClas
s`。
形式化陈述：FiniteResidueField : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue field of `FiniteElement`. This quotient inherits an order from `K`,
which makes it into a linearly ordered Archimedean field.
-/
def FiniteResidueField : Type _ :=
  IsLocalRing.ResidueField (FiniteElement K)
deriving Field

namespace FiniteResidueField

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.ordConnected_preimage_mk'** 是 Mathlib 中的一个
实例，位于命名空间 `ArchimedeanClass.FiniteResidueField`。
形式化陈述：ordConnected_preimage_mk' : forall x, Set.OrdConnected Quotient.mk (Submod
ule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))) ⁻¹' {x}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ArchimedeanClass.instValuationRingFiniteElement`：∀ (K : Type u_1) [inst 
: LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   ValuationRing 
(ArchimedeanClass.FiniteElement K)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Submodule.quotientRel_def`：quotientRel_def {x y : M} : p.quotientRel x y
 ↔ x - y in p
· 使用定理 `IsLocalRing.mem_maximalIdeal`：mem_maximalIdeal (x) : x in maximalIdeal R
 ↔ x in nonunits R
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos`：not_isUnit_iff_mk_
pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ArchimedeanClass.mk_antitoneOn`：∀ {M : Type u_1} [inst : AddCommGroup M]
 [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M],   AntitoneOn Archimed
eanClass.mk (Set.Ici…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
instance ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanCla
ss.FiniteResidueField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder (FiniteResidueField K) :=
  haveI := Classical.decRel fun x y : FiniteElement K ↦
    letI := Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))
    x ≈ y
  inferInstanceAs <| LinearOrder (Quotient _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient map from finite elements on the field to the associated residue field. -/
/-
**ArchimedeanClass.FiniteResidueField.mk** 是 Mathlib 中的一个定义，位于命名空间 `ArchimedeanC
lass.FiniteResidueField`。
形式化陈述：mk : FiniteElement K ->+*o FiniteResidueField K where monotone' _ _ h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map from finite elements on the field to the associated residue fie
ld.
-/
def mk : FiniteElement K →+*o FiniteResidueField K where
  monotone' _ _ h := Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

set_option backward.isDefEq.respectTransparency.types false in
@[induction_eliminator]
/-
**ArchimedeanClass.FiniteResidueField.ind** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean
Class.FiniteResidueField`。
形式化陈述：ind {motive : FiniteResidueField K -> Prop} (mk : forall x, motive (mk x))
 : forall x, motive x
参数：mk : forall x, motive (mk x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
-/
theorem ind {motive : FiniteResidueField K → Prop} (mk : ∀ x, motive (mk x)) : ∀ x, motive x :=
  Quotient.ind mk

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.ordConnected_preimage_mk** 是 Mathlib 中的一个实
例，位于命名空间 `ArchimedeanClass.FiniteResidueField`。
形式化陈述：ordConnected_preimage_mk : forall x, Set.OrdConnected (mk ⁻¹' ({x} : Set (
FiniteResidueField K)))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ordConnected_preimage_mk :
    ∀ x, Set.OrdConnected (mk ⁻¹' ({x} : Set (FiniteResidueField K))) :=
  ordConnected_preimage_mk'

set_option backward.isDefEq.respectTransparency false in
/-
**ArchimedeanClass.FiniteResidueField.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archim
edeanClass.FiniteResidueField`。
形式化陈述：mk_eq_mk {x y : FiniteElement K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (
x.1 - y.1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.quotientRel_def`：quotientRel_def {x y : M} : p.quotientRel x y
 ↔ x - y in p
· 使用定理 `IsLocalRing.mem_maximalIdeal`：mem_maximalIdeal (x) : x in maximalIdeal R
 ↔ x in nonunits R
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `ArchimedeanClass.FiniteElement.not_isUnit_iff_mk_pos`：not_isUnit_iff_mk_
pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `AddSubgroupClass.coe_sub`：∀ {G : Type u_1} [inst : AddGroup G] {S : Type
 u_4} {H : S} [inst_1 : SetLike S G] [inst_2 : AddSubgroupClass S G]   (x y : ↥H
), ↑(x - y) = …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_mk {x y : FiniteElement K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    FiniteElement.not_isUnit_iff_mk_pos, AddSubgroupClass.coe_sub]
/-
**ArchimedeanClass.FiniteResidueField.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Arch
imedeanClass.FiniteResidueField`。
形式化陈述：mk_eq_zero {x : FiniteElement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_eq_mk`：mk_eq_mk {x y : FiniteElem
ent K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_eq_zero {x : FiniteElement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1 := by
  apply mk_eq_mk.trans
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.mk_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Arch
imedeanClass.FiniteResidueField`。
形式化陈述：mk_ne_zero {x : FiniteElement K} : mk x != 0 ↔ ArchimedeanClass.mk x.1 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_eq_zero`：mk_eq_zero {x : FiniteEl
ement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_ne_zero {x : FiniteElement K} : mk x ≠ 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq, mk_eq_zero, not_lt, x.2.ge_iff_eq']

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archim
edeanClass.FiniteResidueField`。
形式化陈述：mk_le_mk {x y : FiniteElement K} : mk x <= mk y ↔ x <= y ∨ mk x = mk y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ArchimedeanClass.instValuationRingFiniteElement`：∀ (K : Type u_1) [inst 
: LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   ValuationRing 
(ArchimedeanClass.FiniteElement K)
· 使用定理 `Quotient.mk_le_mk`：mk_le_mk {x y : α} : Quotient.mk s x <= Quotient.mk s
 y ↔ x <= y ∨ x ≈ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.eq_iff_equiv`：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : 
Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {x y : FiniteElement K} : mk x ≤ mk y ↔ x ≤ y ∨ mk x = mk y := by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Archim
edeanClass.FiniteResidueField`。
形式化陈述：mk_lt_mk {x y : FiniteElement K} : mk x < mk y ↔ x < y ∧ mk x != mk y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `ArchimedeanClass.instValuationRingFiniteElement`：∀ (K : Type u_1) [inst 
: LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   ValuationRing 
(ArchimedeanClass.FiniteElement K)
· 使用定理 `Quotient.mk_lt_mk`：mk_lt_mk {x y : α} : Quotient.mk s x < Quotient.mk s 
y ↔ x < y ∧ ¬ x ≈ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.eq_iff_equiv`：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : 
Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk {x y : FiniteElement K} : mk x < mk y ↔ x < y ∧ mk x ≠ mk y := by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.lt_of_mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `
ArchimedeanClass.FiniteResidueField`。
形式化陈述：lt_of_mk_lt_mk {x y : FiniteElement K} (h : mk x < mk y) : x < y
参数：h : mk x < mk y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_lt_mk`：mk_lt_mk {x y : FiniteElem
ent K} : mk x < mk y ↔ x < y ∧ mk x != mk y
-/
theorem lt_of_mk_lt_mk {x y : FiniteElement K} (h : mk x < mk y) : x < y :=
  (mk_lt_mk.1 h).1

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.mul_le_mul_of_nonneg_left'** 是 Mathlib 中的一
个定理，位于命名空间 `ArchimedeanClass.FiniteResidueField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
    z * x ≤ z * y := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul, ← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanCla
ss.FiniteResidueField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedRing (FiniteResidueField K) where
  zero_le_one := mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
    · exact mk.monotone' <| add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h hx
  mul_le_mul_of_nonneg_right x hx y z h := by
    simp_rw [mul_comm _ x]
    exact mul_le_mul_of_nonneg_left' h hx

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.FiniteResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `ArchimedeanCla
ss.FiniteResidueField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Archimedean (FiniteResidueField K) where
  arch x y hy := by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 ≤ n • y.1
      convert! ← hn
      · exact abs_of_pos <| lt_of_mk_lt_mk hx
      · exact abs_of_pos <| lt_of_mk_lt_mk hy

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ArchimedeanClass.FiniteResidueField.mk_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `Arch
imedeanClass.FiniteResidueField`。
形式化陈述：mk_ratCast (q : Rat) : mk (q : FiniteElement K) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.mk_ratCast_nonneg`：mk_ratCast_nonneg (q : Rat) : 0 <= m
k (q : R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `ArchimedeanClass.FiniteResidueField.instIsOrderedRing`：∀ {K : Type u_1} 
[inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   IsOrdere
dRing (ArchimedeanClass.FiniteResidueField …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `ArchimedeanClass.mk_natCast_nonneg`：mk_natCast_nonneg (n : Nat) : 0 <= m
k (n : S)
· 使用定理 `ArchimedeanClass.FiniteElement.mk_natCast`：∀ {K : Type u_1} [inst : Line
arOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] (n : ℕ),   ArchimedeanC
lass.FiniteElement.mk ↑n ⋯ = ↑n
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ArchimedeanClass.instIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : Linear
Order R] [inst_1 : CommRing R] [inst_2 : IsStrictOrderedRing R],   IsOrderedAddM
onoid (ArchimedeanClass R)
· 使用定理 `ArchimedeanClass.FiniteElement.mk_mul_mk`：mk_mul_mk (x y : K) (hx hy) : 
.mk x hx * .mk y hy = FiniteElement.mk (x * y) (add_nonneg hx hy)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ArchimedeanClass.FiniteElement.mk.congr_simp`：∀ {K : Type u_1} [inst : L
inearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] (x x_1 : K) (e_x : x
 = x_1)   (h : 0 ≤ ArchimedeanClas…
（共 39 条，此处仅展示前 30 条）
-/
theorem mk_ratCast (q : ℚ) : mk (q : FiniteElement K) = q := by
  change mk (FiniteElement.mk ..) = _
  cases q with | div n d hd
  rw [← mul_left_inj' (c := ↑d) (mod_cast hd), ← map_natCast mk d, ← map_mul,
    ← FiniteElement.mk_natCast, FiniteElement.mk_mul_mk]
  simp_all

set_option backward.isDefEq.respectTransparency.types false in
/-- An embedding from an Archimedean field into `K` induces an embedding into
`FiniteResidueField K`. -/
/-
**ArchimedeanClass.FiniteResidueField.ofArchimedean** 是 Mathlib 中的一个定义，位于命名空间 `A
rchimedeanClass.FiniteResidueField`。
形式化陈述：ofArchimedean (f : R ->+*o K) : R ->+*o FiniteResidueField K where toFun r
参数：f : R ->+*o K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding from an Archimedean field into `K` induces an embedding into
`FiniteResidueField K`.
-/
def ofArchimedean (f : R →+*o K) : R →+*o FiniteResidueField K where
  toFun r := mk <| .mk _ (mk_map_nonneg_of_archimedean f r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk.map_mul
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  monotone' x y h := mk.monotone' <| f.monotone' h
/-
**ArchimedeanClass.FiniteResidueField.ofArchimedean_apply** 是 Mathlib 中的一个定理，位于命
名空间 `ArchimedeanClass.FiniteResidueField`。
形式化陈述：ofArchimedean_apply (f : R ->+*o K) (r : R) : ofArchimedean f r = mk (.mk 
_ (mk_map_nonneg_of_archimedean f r))
参数：f : R ->+*o K；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofArchimedean_apply (f : R →+*o K) (r : R) :
    ofArchimedean f r = mk (.mk _ (mk_map_nonneg_of_archimedean f r)) :=
  rfl
/-
**ArchimedeanClass.FiniteResidueField.ofArchimedean_injective** 是 Mathlib 中的一个定理
，位于命名空间 `ArchimedeanClass.FiniteResidueField`。
形式化陈述：ofArchimedean_injective (f : R ->+*o K) : Function.Injective (ofArchimedea
n f)
参数：f : R ->+*o K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `ArchimedeanClass.mk_map_nonneg_of_archimedean`：mk_map_nonneg_of_archimed
ean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <= mk (f y)
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.FiniteResidueField.ofArchimedean_apply`：ofArchimedean_a
pply (f : R ->+*o K) (r : R) : ofArchimedean f r = mk (.mk _ (mk_map_nonneg_of_a
rchimedean f r))
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_ne_zero`：mk_ne_zero {x : FiniteEl
ement K} : mk x != 0 ↔ ArchimedeanClass.mk x.1 = 0
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
-/
theorem ofArchimedean_injective (f : R →+*o K) : Function.Injective (ofArchimedean f) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply, mk_ne_zero]
  exact mk_map_of_archimedean' f hr

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ArchimedeanClass.FiniteResidueField.ofArchimedean_inj** 是 Mathlib 中的一个定理，位于命名空
间 `ArchimedeanClass.FiniteResidueField`。
形式化陈述：ofArchimedean_inj (f : R ->+*o K) {x y : R} : ofArchimedean f x = ofArchim
edean f y ↔ x = y
参数：f : R ->+*o K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ArchimedeanClass.FiniteResidueField.ofArchimedean_injective`：ofArchimede
an_injective (f : R ->+*o K) : Function.Injective (ofArchimedean f)
-/
theorem ofArchimedean_inj (f : R →+*o K) {x y : R} :
    ofArchimedean f x = ofArchimedean f y ↔ x = y :=
  (ofArchimedean_injective f).eq_iff

end FiniteResidueField

/-! ### Standard part -/

set_option backward.isDefEq.respectTransparency.types false in
/-- The standard part of a `FiniteElement` is the unique real number with an infinitesimal
difference.

For any infinite inputs, this function outputs a junk value of 0. -/
@[no_expose]
/-
**ArchimedeanClass.stdPart** 是 Mathlib 中的一个定义，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart (x : K) : Real
参数：x : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard part of a `FiniteElement` is the unique real number with an infinit
esimal
difference.

For any infinite inputs, this function outputs a junk value of 0.
-/
def stdPart (x : K) : ℝ :=
  if h : 0 ≤ mk x then
    OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk (.mk x h) else 0

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.stdPart_of_mk_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCl
ass`。
形式化陈述：stdPart_of_mk_nonneg (f : FiniteResidueField K ->+*o Real) (h : 0 <= mk x)
 : stdPart x = f (.mk <| .mk x h)
参数：f : FiniteResidueField K ->+*o Real；h : 0 <= mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `OrderRingHom.comp_apply`：comp_apply (f : β ->+*o γ) (g : α ->+*o β) (a :
 α) : f.comp g a = f (g a)
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
-/
theorem stdPart_of_mk_nonneg (f : FiniteResidueField K →+*o ℝ) (h : 0 ≤ mk x) :
    stdPart x = f (.mk <| .mk x h) := by
  rw [stdPart, dif_pos h, OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ArchimedeanClass.stdPart_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_eq_zero {x : K} : stdPart x = 0 ↔ mk x != 0 where mpr h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `ArchimedeanClass.FiniteResidueField.instIsOrderedRing`：∀ {K : Type u_1} 
[inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   IsOrdere
dRing (ArchimedeanClass.FiniteResidueField …
· 使用定理 `ArchimedeanClass.FiniteResidueField.instArchimedean`：∀ {K : Type u_1} [i
nst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   Archimedea
n (ArchimedeanClass.FiniteResidueField K)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart_of_mk_nonneg`：stdPart_of_mk_nonneg (f : FiniteR
esidueField K ->+*o Real) (h : 0 <= mk x) : stdPart x = f (.mk <| .mk x h)
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_ne_zero`：mk_ne_zero {x : FiniteEl
ement K} : mk x != 0 ↔ ArchimedeanClass.mk x.1 = 0
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `OrderRingHom.comp_apply`：comp_apply (f : β ->+*o γ) (g : α ->+*o β) (a :
 α) : f.comp g a = f (g a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_eq_zero`：mk_eq_zero {x : FiniteEl
ement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem stdPart_eq_zero {x : K} : stdPart x = 0 ↔ mk x ≠ 0 where
  mpr h := by
    obtain h | h := h.lt_or_gt
    · exact dif_neg h.not_ge
    · rw [stdPart, dif_pos h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
        map_zero]
  mp := by
    contrapose!
    intro h
    rwa [stdPart_of_mk_nonneg Classical.ofNonempty h.ge, map_ne_zero, FiniteResidueField.mk_ne_zero]

alias ⟨_, stdPart_of_mk_ne_zero⟩ := stdPart_eq_zero
/-
**ArchimedeanClass.stdPart_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClas
s`。
形式化陈述：stdPart_monotoneOn : MonotoneOn stdPart {x : K | 0 <= mk x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `ArchimedeanClass.FiniteElement.mk_le_mk`：mk_le_mk (x y : K) (hx hy) : Fi
niteElement.mk x hx <= .mk y hy ↔ x <= y
-/
theorem stdPart_monotoneOn : MonotoneOn stdPart {x : K | 0 ≤ mk x} := by
  intro x (hx : 0 ≤ mk x) y (hy : 0 ≤ mk y) h
  unfold stdPart
  rw [dif_pos hx, dif_pos hy]
  apply OrderRingHom.monotone'
  rwa [FiniteElement.mk_le_mk]

@[simp]
/-
**ArchimedeanClass.stdPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_zero : stdPart (0 : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stdPart_zero : stdPart (0 : K) = 0 := by
  rw [stdPart, dif_pos] <;> simp

@[simp]
/-
**ArchimedeanClass.stdPart_one** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_one : stdPart (1 : K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stdPart_one : stdPart (1 : K) = 1 := by
  rw [stdPart, dif_pos] <;> simp

@[simp]
/-
**ArchimedeanClass.stdPart_neg** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_neg (x : K) : stdPart (-x) = -stdPart x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.mk_neg`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a : M),   ArchimedeanClass.m
k (-a) = Arch…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.FiniteElement.neg_mk`：neg_mk {x : K} (h : 0 <= mk x) : 
-FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg])
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stdPart_neg (x : K) : stdPart (-x) = -stdPart x := by
  simp_rw [stdPart, ArchimedeanClass.mk_neg]
  split_ifs
  · rw [← FiniteElement.neg_mk, map_neg]
  · simp

@[simp]
/-
**ArchimedeanClass.stdPart_inv** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_inv (x : K) : stdPart x⁻¹ = (stdPart x)⁻¹
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_inv_of_mul_eq_one_left`：eq_inv_of_mul_eq_one_left (h : a * b = 1) : a
 = b⁻¹
· 使用定理 `ArchimedeanClass.FiniteElement.ext`：∀ {K : Type u_1} [inst : LinearOrder
 K] [inst_1 : Field K] [inst_2 : IsOrderedRing K]   {x y : ArchimedeanClass.Fini
teElement K}, ↑x = ↑y → …
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ArchimedeanClass.stdPart_of_mk_ne_zero`：∀ {K : Type u_1} [inst : LinearO
rder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] {x : K},   ArchimedeanClas
s.mk x ≠ 0 → ArchimedeanClas…
· 使用定理 `ArchimedeanClass.mk_inv`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : Field R] [inst_2 : IsOrderedRing R] (x : R),   ArchimedeanClass.mk x⁻¹ = -Arc
himedeanClass…
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
-/
theorem stdPart_inv (x : K) : stdPart x⁻¹ = (stdPart x)⁻¹ := by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold stdPart
    have hx' : 0 ≤ mk x⁻¹ := by simp_all
    rw [dif_pos hx.ge, dif_pos hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices FiniteElement.mk x⁻¹ hx' * .mk x hx.ge = 1 by
        rw [← map_mul, this, map_one]
      ext
      apply inv_mul_cancel₀
      aesop
  · rw [stdPart_of_mk_ne_zero hx, stdPart_of_mk_ne_zero, inv_zero]
    rwa [mk_inv, neg_ne_zero]
/-
**ArchimedeanClass.stdPart_add** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_add (hx : 0 <= mk x) (hy : 0 <= mk y) : stdPart (x + y) = stdPart 
x + stdPart y
参数：hx : 0 <= mk x；hy : 0 <= mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `SubsemiringClass.nonUnitalSubsemiringClass`：∀ (S : Type u_1) (R : Type u
) [inst : NonAssocSemiring R] [inst_1 : SetLike S R] [SubsemiringClass S R],   N
onUnitalSubsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem stdPart_add (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) : stdPart (x + y) = stdPart x + stdPart y := by
  unfold stdPart
  rw [dif_pos hx, dif_pos hy, dif_pos]
  exact map_add _ (FiniteElement.mk x hx) (.mk y hy)
/-
**ArchimedeanClass.stdPart_add_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCl
ass`。
形式化陈述：stdPart_add_eq_right (hx : 0 < mk x) : stdPart (x + y) = stdPart y
参数：hx : 0 < mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart_add`：stdPart_add (hx : 0 <= mk x) (hy : 0 <= mk
 y) : stdPart (x + y) = stdPart x + stdPart y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ArchimedeanClass.stdPart_of_mk_ne_zero`：∀ {K : Type u_1} [inst : LinearO
rder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] {x : K},   ArchimedeanClas
s.mk x ≠ 0 → ArchimedeanClas…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ArchimedeanClass.mk_add_eq_mk_right`：∀ {M : Type u_1} [inst : AddCommGro
up M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M},   Arch
imedeanClass.mk b < Archi…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem stdPart_add_eq_right (hx : 0 < mk x) : stdPart (x + y) = stdPart y := by
  obtain hy | hy := le_or_gt 0 (mk y)
  · rw [stdPart_add hx.le hy, stdPart_of_mk_ne_zero hx.ne', zero_add]
  · rw [stdPart_of_mk_ne_zero hy.ne, stdPart_of_mk_ne_zero]
    rw [mk_add_eq_mk_right (hy.trans hx)]
    exact hy.ne
/-
**ArchimedeanClass.stdPart_add_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCla
ss`。
形式化陈述：stdPart_add_eq_left (hy : 0 < mk y) : stdPart (x + y) = stdPart x
参数：hy : 0 < mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ArchimedeanClass.stdPart_add_eq_right`：stdPart_add_eq_right (hx : 0 < mk
 x) : stdPart (x + y) = stdPart y
-/
theorem stdPart_add_eq_left (hy : 0 < mk y) : stdPart (x + y) = stdPart x := by
  rw [add_comm, stdPart_add_eq_right hy]
/-
**ArchimedeanClass.stdPart_sub** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_sub (hx : 0 <= mk x) (hy : 0 <= mk y) : stdPart (x - y) = stdPart 
x - stdPart y
参数：hx : 0 <= mk x；hy : 0 <= mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ArchimedeanClass.stdPart_add`：stdPart_add (hx : 0 <= mk x) (hy : 0 <= mk
 y) : stdPart (x + y) = stdPart x + stdPart y
· 使用定理 `ArchimedeanClass.mk_neg`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a : M),   ArchimedeanClass.m
k (-a) = Arch…
· 使用定理 `ArchimedeanClass.stdPart_neg`：stdPart_neg (x : K) : stdPart (-x) = -stdP
art x
-/
theorem stdPart_sub (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) : stdPart (x - y) = stdPart x - stdPart y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, stdPart_add hx, stdPart_neg]
  rwa [mk_neg]
/-
**ArchimedeanClass.stdPart_sub_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCl
ass`。
形式化陈述：stdPart_sub_eq_right (hx : 0 < mk x) : stdPart (x - y) = -stdPart y
参数：hx : 0 < mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ArchimedeanClass.stdPart_add_eq_right`：stdPart_add_eq_right (hx : 0 < mk
 x) : stdPart (x + y) = stdPart y
· 使用定理 `ArchimedeanClass.stdPart_neg`：stdPart_neg (x : K) : stdPart (-x) = -stdP
art x
-/
theorem stdPart_sub_eq_right (hx : 0 < mk x) : stdPart (x - y) = -stdPart y := by
  rw [sub_eq_add_neg, stdPart_add_eq_right hx, stdPart_neg]
/-
**ArchimedeanClass.stdPart_sub_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanCla
ss`。
形式化陈述：stdPart_sub_eq_left (hy : 0 < mk y) : stdPart (x - y) = stdPart x
参数：hy : 0 < mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ArchimedeanClass.stdPart_add_eq_left`：stdPart_add_eq_left (hy : 0 < mk y
) : stdPart (x + y) = stdPart x
· 使用定理 `ArchimedeanClass.mk_neg`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a : M),   ArchimedeanClass.m
k (-a) = Arch…
-/
theorem stdPart_sub_eq_left (hy : 0 < mk y) : stdPart (x - y) = stdPart x := by
  rw [sub_eq_add_neg, stdPart_add_eq_left (by simpa)]
/-
**ArchimedeanClass.stdPart_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_mul (hx : 0 <= mk x) (hy : 0 <= mk y) : stdPart (x * y) = stdPart 
x * stdPart y
参数：hx : 0 <= mk x；hy : 0 <= mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem stdPart_mul (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) : stdPart (x * y) = stdPart x * stdPart y := by
  unfold stdPart
  rw [dif_pos hx, dif_pos hy, dif_pos]
  exact map_mul _ (FiniteElement.mk x hx) (.mk y hy)
/-
**ArchimedeanClass.stdPart_div** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_div (hx : 0 <= mk x) (hy : 0 <= -mk y) : stdPart (x / y) = stdPart
 x / stdPart y
参数：hx : 0 <= mk x；hy : 0 <= -mk y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ArchimedeanClass.stdPart_mul`：stdPart_mul (hx : 0 <= mk x) (hy : 0 <= mk
 y) : stdPart (x * y) = stdPart x * stdPart y
· 使用定理 `ArchimedeanClass.mk_inv`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : Field R] [inst_2 : IsOrderedRing R] (x : R),   ArchimedeanClass.mk x⁻¹ = -Arc
himedeanClass…
· 使用定理 `ArchimedeanClass.stdPart_inv`：stdPart_inv (x : K) : stdPart x⁻¹ = (stdPa
rt x)⁻¹
-/
theorem stdPart_div (hx : 0 ≤ mk x) (hy : 0 ≤ -mk y) :
    stdPart (x / y) = stdPart x / stdPart y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, stdPart_mul hx, stdPart_inv]
  rwa [mk_inv]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ArchimedeanClass.stdPart_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_ratCast (q : Rat) : stdPart (q : K) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `ArchimedeanClass.FiniteResidueField.instIsOrderedRing`：∀ {K : Type u_1} 
[inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   IsOrdere
dRing (ArchimedeanClass.FiniteResidueField …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.FiniteResidueField.instArchimedean`：∀ {K : Type u_1} [i
nst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   Archimedea
n (ArchimedeanClass.FiniteResidueField K)
· 使用定理 `ArchimedeanClass.mk_ratCast_nonneg`：mk_ratCast_nonneg (q : Rat) : 0 <= m
k (q : R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart_of_mk_nonneg`：stdPart_of_mk_nonneg (f : FiniteR
esidueField K ->+*o Real) (h : 0 <= mk x) : stdPart x = f (.mk <| .mk x h)
· 使用定理 `ArchimedeanClass.FiniteElement.mk_ratCast`：∀ {K : Type u_1} [inst : Line
arOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] (q : ℚ),   ArchimedeanC
lass.FiniteElement.mk ↑q ⋯ = ↑q
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_ratCast`：mk_ratCast (q : Rat) : m
k (q : FiniteElement K) = q
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem stdPart_ratCast (q : ℚ) : stdPart (q : K) = q := by
  rw [stdPart_of_mk_nonneg Classical.ofNonempty (mk_ratCast_nonneg q), FiniteElement.mk_ratCast,
    FiniteResidueField.mk_ratCast, map_ratCast]

@[simp]
/-
**ArchimedeanClass.stdPart_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_intCast (n : Int) : stdPart (n : K) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart.congr_simp`：∀ {K : Type u_1} [inst : LinearOrde
r K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] (x x_1 : K),   x = x_1 → Arch
imedeanClass.stdPart x = …
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `ArchimedeanClass.stdPart_ratCast`：stdPart_ratCast (q : Rat) : stdPart (q
 : K) = q
-/
theorem stdPart_intCast (n : ℤ) : stdPart (n : K) = n :=
  mod_cast stdPart_ratCast n

@[simp]
/-
**ArchimedeanClass.stdPart_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_natCast (n : Nat) : stdPart (n : K) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart.congr_simp`：∀ {K : Type u_1} [inst : LinearOrde
r K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] (x x_1 : K),   x = x_1 → Arch
imedeanClass.stdPart x = …
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ArchimedeanClass.stdPart_intCast`：stdPart_intCast (n : Int) : stdPart (n
 : K) = n
-/
theorem stdPart_natCast (n : ℕ) : stdPart (n : K) = n :=
  mod_cast stdPart_intCast n

@[simp]
/-
**ArchimedeanClass.stdPart_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_ofNat (n : Nat) [n.AtLeastTwo] : stdPart (ofNat(n) : K) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.stdPart_natCast`：stdPart_natCast (n : Nat) : stdPart (n
 : K) = n
-/
theorem stdPart_ofNat (n : ℕ) [n.AtLeastTwo] : stdPart (ofNat(n) : K) = n :=
  stdPart_natCast n

@[simp]
/-
**ArchimedeanClass.stdPart_map_real** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`
。
形式化陈述：stdPart_map_real (f : Real ->+*o K) (r : Real) : stdPart (f r) = r
参数：f : Real ->+*o K；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Real.ringHom_apply`：Real.ringHom_apply {F : Type*} [FunLike F Real Real]
 [RingHomClass F Real Real] (f : F) (r : Real) : f r = r
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
theorem stdPart_map_real (f : ℝ →+*o K) (r : ℝ) : stdPart (f r) = r := by
  rw [stdPart, dif_pos]
  exact r.ringHom_apply <| OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

@[simp]
/-
**ArchimedeanClass.stdPart_real** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_real (r : Real) : stdPart r = r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.stdPart_map_real`：stdPart_map_real (f : Real ->+*o K) (
r : Real) : stdPart (f r) = r
-/
theorem stdPart_real (r : ℝ) : stdPart r = r :=
  stdPart_map_real (.id ℝ) r

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArchimedeanClass.ofArchimedean_stdPart** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanC
lass`。
形式化陈述：ofArchimedean_stdPart (f : Real ->+*o K) (hx : 0 <= mk x) : FiniteResidueF
ield.ofArchimedean f (stdPart x) = .mk (.mk x hx)
参数：f : Real ->+*o K；hx : 0 <= mk x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderRingHom.comp_apply`：comp_apply (f : β ->+*o γ) (g : α ->+*o β) (a :
 α) : f.comp g a = f (g a)
· 使用定理 `OrderRingHom.comp_assoc`：comp_assoc (f : γ ->+*o δ) (g : β ->+*o γ) (h :
 α ->+*o β) : (f.comp g).comp h = f.comp (g.comp h)
· 使用定理 `OrderRingHom.apply_eq_self`：OrderRingHom.apply_eq_self [IsStrictOrderedR
ing α] [Archimedean α] (f : α ->+*o α) (x : α) : f x = x
· 使用定理 `ArchimedeanClass.FiniteResidueField.instIsOrderedRing`：∀ {K : Type u_1} 
[inst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   IsOrdere
dRing (ArchimedeanClass.FiniteResidueField …
· 使用定理 `ArchimedeanClass.FiniteResidueField.instArchimedean`：∀ {K : Type u_1} [i
nst : LinearOrder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K],   Archimedea
n (ArchimedeanClass.FiniteResidueField K)
-/
theorem ofArchimedean_stdPart (f : ℝ →+*o K) (hx : 0 ≤ mk x) :
    FiniteResidueField.ofArchimedean f (stdPart x) = .mk (.mk x hx) := by
  rw [stdPart, dif_pos hx, ← OrderRingHom.comp_apply, ← OrderRingHom.comp_assoc,
    OrderRingHom.comp_apply, OrderRingHom.apply_eq_self]
/-
**ArchimedeanClass.stdPart_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_nonneg {x : K} (h : 0 <= x) : 0 <= stdPart x
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Order.Ring.StandardPart.0.ArchimedeanClass.stdP
art.eq_1`：∀ {K : Type u_1} [inst : LinearOrder K] [inst_1 : Field K] [inst_2 : I
sOrderedRing K] (x : K),   ArchimedeanClass.stdPart x =     if h : 0 ≤…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `map_nonneg`：map_nonneg (ha : 0 <= a) : 0 <= f a
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `ArchimedeanClass.stdPart_of_mk_ne_zero`：∀ {K : Type u_1} [inst : LinearO
rder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] {x : K},   ArchimedeanClas
s.mk x ≠ 0 → ArchimedeanClas…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem stdPart_nonneg {x : K} (h : 0 ≤ x) : 0 ≤ stdPart x := by
  obtain hx | hx := eq_or_ne (ArchimedeanClass.mk x) 0
  · rw [stdPart, dif_pos hx.ge]
    exact map_nonneg _ h
  · rw [stdPart_of_mk_ne_zero hx]
/-
**ArchimedeanClass.stdPart_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_nonpos {x : K} (h : x <= 0) : stdPart x <= 0
参数：h : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.stdPart_neg`：stdPart_neg (x : K) : stdPart (-x) = -stdP
art x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ArchimedeanClass.stdPart_nonneg`：stdPart_nonneg {x : K} (h : 0 <= x) : 0
 <= stdPart x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
theorem stdPart_nonpos {x : K} (h : x ≤ 0) : stdPart x ≤ 0 := by
  simpa using stdPart_nonneg (neg_nonneg.2 h)

/-- The standard part of `x` is the unique real `r` such that `x - r` is infinitesimal. -/
/-
**ArchimedeanClass.mk_sub_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：mk_sub_pos_iff (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) : 0 < mk (x 
- f r) ↔ stdPart x = r
参数：f : Real ->+*o K；hx : 0 <= mk x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ArchimedeanClass.mk_map_nonneg_of_archimedean`：mk_map_nonneg_of_archimed
ean [Archimedean S] (f : S ->+*o R) (y : S) : 0 <= mk (f y)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ArchimedeanClass.FiniteResidueField.mk_eq_zero`：mk_eq_zero {x : FiniteEl
ement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.FiniteResidueField.ofArchimedean_apply`：ofArchimedean_a
pply (f : R ->+*o K) (r : R) : ofArchimedean f r = mk (.mk _ (mk_map_nonneg_of_a
rchimedean f r))
· 使用定理 `ArchimedeanClass.ofArchimedean_stdPart`：ofArchimedean_stdPart (f : Real 
->+*o K) (hx : 0 <= mk x) : FiniteResidueField.ofArchimedean f (stdPart x) = .mk
 (.mk x hx)
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `ArchimedeanClass.FiniteResidueField.ofArchimedean_inj`：ofArchimedean_inj
 (f : R ->+*o K) {x y : R} : ofArchimedean f x = ofArchimedean f y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The standard part of `x` is the unique real `r` such that `x - r` is infinitesim
al.
-/
theorem mk_sub_pos_iff (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) :
    0 < mk (x - f r) ↔ stdPart x = r := by
  refine (FiniteResidueField.mk_eq_zero
    (x := .mk x hx - .mk _ (mk_map_nonneg_of_archimedean f r))).symm.trans ?_
  rw [map_sub, ← FiniteResidueField.ofArchimedean_apply, ← ofArchimedean_stdPart f hx,
    sub_eq_zero, FiniteResidueField.ofArchimedean_inj f]
/-
**ArchimedeanClass.mk_sub_stdPart_pos** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClas
s`。
形式化陈述：mk_sub_stdPart_pos (f : Real ->+*o K) (hx : 0 <= mk x) : 0 < mk (x - f (st
dPart x))
参数：f : Real ->+*o K；hx : 0 <= mk x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArchimedeanClass.mk_sub_pos_iff`：mk_sub_pos_iff (f : Real ->+*o K) {r : 
Real} (hx : 0 <= mk x) : 0 < mk (x - f r) ↔ stdPart x = r
-/
theorem mk_sub_stdPart_pos (f : ℝ →+*o K) (hx : 0 ≤ mk x) : 0 < mk (x - f (stdPart x)) :=
  (mk_sub_pos_iff f hx).2 rfl
/-
**ArchimedeanClass.lt_of_lt_stdPart** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`
。
形式化陈述：lt_of_lt_stdPart (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : r < s
tdPart x) : f r < x
参数：f : Real ->+*o K；hx : 0 <= mk x；h : r < stdPart x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_lt_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α]
 [AddRightStrictMono α] {a b : α} (c : α), a - c < b - c ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonpos`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ArchimedeanClass.mk_map_of_archimedean'`：mk_map_of_archimedean' [Archime
dean S] (f : S ->+*o R) {x : S} (h : x != 0) : mk (f x) = 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ArchimedeanClass.mk_sub_pos_iff`：mk_sub_pos_iff (f : Real ->+*o K) {r : 
Real} (hx : 0 <= mk x) : 0 < mk (x - f r) ↔ stdPart x = r
（共 40 条，此处仅展示前 30 条）
-/
theorem lt_of_lt_stdPart (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : r < stdPart x) : f r < x := by
  rw [← sub_lt_sub_iff_right (c := f (stdPart x)), ← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', mk_sub_pos_iff f hx]
    rw [ne_eq, sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le
/-
**ArchimedeanClass.lt_of_stdPart_lt** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`
。
形式化陈述：lt_of_stdPart_lt (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : stdPa
rt x < r) : x < f r
参数：f : Real ->+*o K；hx : 0 <= mk x；h : stdPart x < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `ArchimedeanClass.lt_of_lt_stdPart`：lt_of_lt_stdPart (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : r < stdPart x) : f r < x
· 使用定理 `ArchimedeanClass.mk_neg`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a : M),   ArchimedeanClass.m
k (-a) = Arch…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ArchimedeanClass.stdPart_neg`：stdPart_neg (x : K) : stdPart (-x) = -stdP
art x
-/
theorem lt_of_stdPart_lt (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : stdPart x < r) : x < f r := by
  rw [← neg_lt_neg_iff, ← map_neg]
  apply lt_of_lt_stdPart <;> simpa
/-
**ArchimedeanClass.stdPart_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`
。
形式化陈述：stdPart_le_of_le (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : x <= 
f r) : stdPart x <= r
参数：f : Real ->+*o K；hx : 0 <= mk x；h : x <= f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_imp_le_iff_lt_imp_lt`：le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : a <= b -> c <= d ↔ d < c -> b < a
· 使用定理 `ArchimedeanClass.lt_of_lt_stdPart`：lt_of_lt_stdPart (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : r < stdPart x) : f r < x
-/
theorem stdPart_le_of_le (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : x ≤ f r) : stdPart x ≤ r :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_lt_stdPart f hx) h
/-
**ArchimedeanClass.le_stdPart_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`
。
形式化陈述：le_stdPart_of_le (f : Real ->+*o K) {r : Real} (hx : 0 <= mk x) (h : f r <
= x) : r <= stdPart x
参数：f : Real ->+*o K；hx : 0 <= mk x；h : f r <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_imp_le_iff_lt_imp_lt`：le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : a <= b -> c <= d ↔ d < c -> b < a
· 使用定理 `ArchimedeanClass.lt_of_stdPart_lt`：lt_of_stdPart_lt (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : stdPart x < r) : x < f r
-/
theorem le_stdPart_of_le (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : f r ≤ x) : r ≤ stdPart x :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_stdPart_lt f hx) h
/-
**ArchimedeanClass.stdPart_eq** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_eq (f : Real ->+*o K) {r : Real} (hl : forall s < r, f s <= x) (hr
 : forall s > r, x <= f s) : stdPart x = r
参数：f : Real ->+*o K；hl : forall s < r, f s <= x；hr : forall s > r, x <= f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean`：mk_nonneg_of_le_o
f_le_of_archimedean [Archimedean S] (f : S ->+*o R) {x : R} {r s : S} (hr : f r 
<= x) (hs : x <= f s) : 0 <= mk x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `ArchimedeanClass.le_stdPart_of_le`：le_stdPart_of_le (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : f r <= x) : r <= stdPart x
· 使用定理 `ArchimedeanClass.stdPart_le_of_le`：stdPart_le_of_le (f : Real ->+*o K) {
r : Real} (hx : 0 <= mk x) (h : x <= f r) : stdPart x <= r
-/
theorem stdPart_eq (f : ℝ →+*o K) {r : ℝ} (hl : ∀ s < r, f s ≤ x) (hr : ∀ s > r, x ≤ f s) :
    stdPart x = r := by
  have hx : 0 ≤ mk x := by
    apply mk_nonneg_of_le_of_le_of_archimedean f (hl (r - 1) _) (hr (r + 1) _) <;> simp
  obtain h | rfl | h := lt_trichotomy (stdPart x) r
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (le_stdPart_of_le f hx (hl _ hs')).not_gt hs
  · rfl
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (stdPart_le_of_le f hx (hr _ hs)).not_gt hs'
/-
**ArchimedeanClass.stdPart_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_eq_sInf (f : Real ->+*o K) (x : K) : stdPart x = sInf {r | x < f r
}
参数：f : Real ->+*o K；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `ArchimedeanClass.exists_int_lt_of_mk_nonneg`：exists_int_lt_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Int, n < x
· 使用定理 `ArchimedeanClass.exists_int_gt_of_mk_nonneg`：exists_int_gt_of_mk_nonneg 
{x : R} (hx : 0 <= mk x) : exists n : Int, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderRingHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : α ->+*o β) : f.toRi
ngHom = f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ArchimedeanClass.stdPart_eq`：stdPart_eq (f : Real ->+*o K) {r : Real} (h
l : forall s < r, f s <= x) (hr : forall s > r, x <= f s) : stdPart x = r
· 使用定理 `notMem_of_lt_csInf`：notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf
 s) (hs : BddBelow s) : x ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `csInf_lt_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLinearOrder 
α] {s : Set α} {a : α},   BddBelow s → s.Nonempty → (sInf s < a ↔ ∃ b ∈ s, b < a
)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ArchimedeanClass.stdPart_of_mk_ne_zero`：∀ {K : Type u_1} [inst : LinearO
rder K] [inst_1 : Field K] [inst_2 : IsOrderedRing K] {x : K},   ArchimedeanClas
s.mk x ≠ 0 → ArchimedeanClas…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 42 条，此处仅展示前 30 条）
-/
theorem stdPart_eq_sInf (f : ℝ →+*o K) (x : K) : stdPart x = sInf {r | x < f r} := by
  obtain hx | hx := le_or_gt 0 (mk x)
  · obtain ⟨a, ha⟩ := exists_int_lt_of_mk_nonneg hx
    obtain ⟨b, hb⟩ := exists_int_gt_of_mk_nonneg hx
    have hn : {r | x < f r}.Nonempty := ⟨b, by simpa using hb⟩
    have hb : BddBelow {r | x < f r} := by
      refine ⟨a, fun r hr ↦ ?_⟩
      by_contra! hra
      exact (f.monotone' hra.le).not_gt (by simpa using ha.trans hr)
    apply stdPart_eq f <;> intro r hr
    · simpa using notMem_of_lt_csInf hr hb
    · obtain ⟨s, hs, hs'⟩ := (csInf_lt_iff hb hn).1 hr
      exact hs.le.trans (f.monotone' hs'.le)
  · rw [stdPart_of_mk_ne_zero hx.ne]
    have hr {r} := hx.trans_le (mk_map_nonneg_of_archimedean f r)
    obtain h | h := le_or_gt 0 x
    · convert! Real.sInf_empty.symm
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun r ↦ (lt_of_mk_lt_mk_of_nonneg hr h).not_gt
    · convert! Real.sInf_univ.symm
      rw [Set.eq_univ_iff_forall]
      exact fun r ↦ lt_of_mk_lt_mk_of_nonpos hr h.le
/-
**ArchimedeanClass.stdPart_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ArchimedeanClass`。
形式化陈述：stdPart_eq_sSup (f : Real ->+*o K) (x : K) : stdPart x = sSup {r | f r < x
}
参数：f : Real ->+*o K；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `ArchimedeanClass.stdPart_neg`：stdPart_neg (x : K) : stdPart (-x) = -stdP
art x
· 使用定理 `ArchimedeanClass.stdPart_eq_sInf`：stdPart_eq_sInf (f : Real ->+*o K) (x 
: K) : stdPart x = sInf {r | x < f r}
· 使用定理 `Real.sInf_neg`：sInf_neg (s : Set Real) : sInf (-s) = -sSup s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsOrderedRing.toIsStrictOrderedRing`：∀ (R : Type u_1) [inst : Ring R] [i
nst_1 : PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R],   I
sStrictOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 35 条，此处仅展示前 30 条）
-/
theorem stdPart_eq_sSup (f : ℝ →+*o K) (x : K) : stdPart x = sSup {r | f r < x} := by
  rw [← neg_inj, ← stdPart_neg, stdPart_eq_sInf f, ← Real.sInf_neg]
  congr 1
  ext
  simp [neg_lt]

end ArchimedeanClass

