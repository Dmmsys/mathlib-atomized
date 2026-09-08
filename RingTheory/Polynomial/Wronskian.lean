/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Wronskian of a pair of polynomial

This file defines Wronskian of a pair of polynomials, which is `W(a, b) = ab' - a'b`.
We also prove basic properties of it.

## Main declarations

- `Polynomial.wronskian_eq_of_sum_zero`: We have `W(a, b) = W(b, c)` when `a + b + c = 0`.
- `Polynomial.degree_wronskian_lt_add`: Degree of Wronskian `W(a, b)` is strictly smaller than
  the sum of degrees of `a` and `b`
- `Polynomial.natDegree_wronskian_lt_add`: `natDegree` version of the above theorem.
  We need to assume that the Wronskian is nonzero. (Otherwise, `a = b = 1` gives a counterexample.)

## TODO

- Define Wronskian for n-tuple of polynomials, not necessarily two.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Wronskian of a pair of polynomials, `W(a, b) = ab' - a'b`. -/
/-
**Polynomial.wronskian** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：wronskian (a b : R[X]) : R[X]
参数：a b : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Wronskian of a pair of polynomials, `W(a, b) = ab' - a'b`.
-/
def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b

variable (R) in
/-- `Polynomial.wronskian` as a bilinear map. -/
/-
**Polynomial.wronskianBilin** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：wronskianBilin : R[X] ->ₗ[R] R[X] ->ₗ[R] R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Polynomial.wronskian` as a bilinear map.
-/
def wronskianBilin : R[X] →ₗ[R] R[X] →ₗ[R] R[X] :=
  (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative

@[simp]
/-
**Polynomial.wronskianBilin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskianBilin_apply (a b : R[X]) : wronskianBilin R a b = wronskian a b
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem wronskianBilin_apply (a b : R[X]) : wronskianBilin R a b = wronskian a b := rfl

@[simp]
/-
**Polynomial.wronskian_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_zero_left (a : R[X]) : wronskian 0 a = 0
参数：a : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.wronskianBilin_apply`：wronskianBilin_apply (a b : R[X]) : wro
nskianBilin R a b = wronskian a b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  rw [← wronskianBilin_apply 0 a, map_zero]; rfl

@[simp]
/-
**Polynomial.wronskian_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_zero_right (a : R[X]) : wronskian a 0 = 0
参数：a : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := (wronskianBilin R a).map_zero
/-
**Polynomial.wronskian_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg₂`：map_neg₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y) : f
 (-x) y = -f x y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b :=
  LinearMap.map_neg₂ (wronskianBilin R) a b
/-
**Polynomial.wronskian_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b :=
  (wronskianBilin R a).map_neg b
/-
**Polynomial.wronskian_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_add_right (a b c : R[X]) : wronskian a (b + c) = wronskian a b +
 wronskian a c
参数：a b c : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem wronskian_add_right (a b c : R[X]) : wronskian a (b + c) = wronskian a b + wronskian a c :=
  (wronskianBilin R a).map_add b c
/-
**Polynomial.wronskian_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_add_left (a b c : R[X]) : wronskian (a + b) c = wronskian a c + 
wronskian b c
参数：a b c : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add₂`：map_add₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y) :
 f (x₁ + x₂) y = f x₁ y + f x₂ y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem wronskian_add_left (a b c : R[X]) : wronskian (a + b) c = wronskian a c + wronskian b c :=
  (wronskianBilin R).map_add₂ a b c
/-
**Polynomial.wronskian_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_self_eq_zero (a : R[X]) : wronskian a a = 0
参数：a : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.wronskian.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (a b : P
olynomial R),   a.wronskian b = a * Polynomial.derivative b - Polynomial.derivat
ive a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem wronskian_self_eq_zero (a : R[X]) : wronskian a a = 0 := by
  rw [wronskian, mul_comm, sub_self]
/-
**Polynomial.isAlt_wronskianBilin** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：isAlt_wronskianBilin : (wronskianBilin R).IsAlt
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.wronskian_self_eq_zero`：wronskian_self_eq_zero (a : R[X]) : w
ronskian a a = 0
-/
theorem isAlt_wronskianBilin : (wronskianBilin R).IsAlt := wronskian_self_eq_zero
/-
**Polynomial.wronskian_neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_neg_eq (a b : R[X]) : -wronskian a b = wronskian b a
参数：a b : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.neg`：neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x
· 使用定理 `Polynomial.isAlt_wronskianBilin`：isAlt_wronskianBilin : (wronskianBilin 
R).IsAlt
-/
theorem wronskian_neg_eq (a b : R[X]) : -wronskian a b = wronskian b a :=
  LinearMap.IsAlt.neg isAlt_wronskianBilin a b
/-
**Polynomial.wronskian_eq_of_sum_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：wronskian_eq_of_sum_zero {a b c : R[X]} (hAdd : a + b + c = 0) : wronskian
 a b = wronskian b c
参数：hAdd : a + b + c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.eq_of_add_add_eq_zero`：∀ {R : Type u_1} {R₁ : Type u_2} 
{M : Type u_5} {M₁ : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M
]   [inst_2 : _root_.Module…
· 使用定理 `Polynomial.isAlt_wronskianBilin`：isAlt_wronskianBilin : (wronskianBilin 
R).IsAlt
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
-/
theorem wronskian_eq_of_sum_zero {a b c : R[X]} (hAdd : a + b + c = 0) :
    wronskian a b = wronskian b c := isAlt_wronskianBilin.eq_of_add_add_eq_zero hAdd

/-- Degree of `W(a,b)` is strictly less than the sum of degrees of `a` and `b` (both nonzero). -/
/-
**Polynomial.degree_wronskian_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_wronskian_lt_add {a b : R[X]} (ha : a != 0) (hb : b != 0) : (wronsk
ian a b).degree < a.degree + b.degree
参数：ha : a != 0；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_sub_le`：degree_sub_le (p q : R[X]) : degree (p - q) <=
 max (degree p) (degree q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `WithBot.add_lt_add_iff_left`：∀ {α : Type u} [inst : Add α] {x y z : With
Bot α} [inst_1 : LT α] [AddLeftStrictMono α] [AddLeftReflectLT α],   x ≠ ⊥ → (x 
+ y < x + z ↔ y <…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用定理 `Polynomial.degree_derivative_lt`：degree_derivative_lt {p : R[X]} (hp : p
 != 0) : p.derivative.degree < p.degree
· 使用定理 `WithBot.add_lt_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hBot α} [inst_1 : LT α] [AddRightStrictMono α] [AddRightReflectLT α],   z ≠ ⊥ → 
(x + z < y + z ↔ x…
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …

--- 原说明 ---
Degree of `W(a,b)` is strictly less than the sum of degrees of `a` and `b` (both
 nonzero).
-/
theorem degree_wronskian_lt_add {a b : R[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left =>
        apply lt_of_le_of_lt
        · exact degree_mul_le a (derivative b)
        · rw [← Polynomial.degree_ne_bot] at ha
          rw [WithBot.add_lt_add_iff_left ha]
          exact Polynomial.degree_derivative_lt hb
      case right =>
        apply lt_of_le_of_lt
        · exact degree_mul_le (derivative a) b
        · rw [← Polynomial.degree_ne_bot] at hb
          rw [WithBot.add_lt_add_iff_right hb]
          exact Polynomial.degree_derivative_lt ha

/--
`natDegree` version of the above theorem.
Note this would be false with just `(ha : a ≠ 0)` and `(hb : b ≠ 0)`,
since when `a = b = 1` we have `(wronskian a b).natDegree = a.natDegree = b.natDegree = 0`.
-/
/-
**Polynomial.natDegree_wronskian_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_wronskian_lt_add {a b : R[X]} (hw : wronskian a b != 0) : (wrons
kian a b).natDegree < a.natDegree + b.natDegree
参数：hw : wronskian a b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.wronskian_zero_left`：wronskian_zero_left (a : R[X]) : wronski
an 0 a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.wronskian_zero_right`：wronskian_zero_right (a : R[X]) : wrons
kian a 0 = 0
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `WithBot.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.degree_wronskian_lt_add`：degree_wronskian_lt_add {a b : R[X]}
 (ha : a != 0) (hb : b != 0) : (wronskian a b).degree < a.degree + b.degree

--- 原说明 ---
`natDegree` version of the above theorem.
Note this would be false with just `(ha : a ≠ 0)` and `(hb : b ≠ 0)`,
since when `a = b = 1` we have `(wronskian a b).natDegree = a.natDegree = b.natD
egree = 0`.
-/
theorem natDegree_wronskian_lt_add {a b : R[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a ≠ 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b ≠ 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe, WithBot.coe_add]
  convert! ← degree_wronskian_lt_add ha hb
  · exact Polynomial.degree_eq_natDegree hw
  · exact Polynomial.degree_eq_natDegree ha
  · exact Polynomial.degree_eq_natDegree hb

/--
For coprime polynomials `a` and `b`, their Wronskian is zero
if and only if their derivatives are zeros.
-/
/-
**Polynomial._root_.IsCoprime.wronskian_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For coprime polynomials `a` and `b`, their Wronskian is zero
if and only if their derivatives are zeros.
-/
theorem _root_.IsCoprime.wronskian_eq_zero_iff
    [NoZeroDivisors R] {a b : R[X]} (hc : IsCoprime a b) :
    wronskian a b = 0 ↔ derivative a = 0 ∧ derivative b = 0 where
  mp hw := by
    rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ _
  mpr hdab := by
    obtain ⟨hda, hdb⟩ := hdab
    rw [wronskian]
    rw [hda, hdb]; simp only [mul_zero, zero_mul, sub_self]

end Polynomial

