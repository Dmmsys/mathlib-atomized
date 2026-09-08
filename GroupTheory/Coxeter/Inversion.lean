/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee, Óscar Álvarez
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Group

/-!
# Reflections, inversions, and inversion sequences

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

We define a *reflection* (`CoxeterSystem.IsReflection`) to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* (`CoxeterSystem.IsLeftInversion`) of an element $w \in W$ if
$\ell(t w) < \ell(w)$, and we say it is a *right inversion* (`CoxeterSystem.IsRightInversion`) of
$w$ if $\ell(w t) > \ell(w)$. Here $\ell$ is the length function
(see `Mathlib/GroupTheory/Coxeter/Length.lean`).

Given a word, we define its *left inversion sequence* (`CoxeterSystem.leftInvSeq`) and its
*right inversion sequence* (`CoxeterSystem.rightInvSeq`). We prove that if a word is reduced, then
both of its inversion sequences contain no duplicates. In fact, the right (respectively, left)
inversion sequence of a reduced word for $w$ consists of all of the right (respectively, left)
inversions of $w$ in some order, but we do not prove that in this file.

## Main definitions

* `CoxeterSystem.IsReflection`
* `CoxeterSystem.IsLeftInversion`
* `CoxeterSystem.IsRightInversion`
* `CoxeterSystem.leftInvSeq`
* `CoxeterSystem.rightInvSeq`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length

/-- `t : W` is a *reflection* of the Coxeter system `cs` if it is of the form
$w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection. -/
/-
**CoxeterSystem.IsReflection** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：IsReflection (t : W) : Prop
参数：t : W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`t : W` is a *reflection* of the Coxeter system `cs` if it is of the form
$w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection.
-/
def IsReflection (t : W) : Prop := ∃ w i, t = w * s i * w⁻¹
/-
**CoxeterSystem.isReflection_simple** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：isReflection_simple (i : B) : cs.IsReflection (s i)
参数：i : B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

namespace IsReflection

variable {cs}
variable {t : W} (ht : cs.IsReflection t)
include ht

/-
**CoxeterSystem.IsReflection.pow_two** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.Is
Reflection`。
形式化陈述：pow_two : t ^ 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `conj_pow`：conj_pow {i : Nat} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i *
 a⁻¹
· 使用定理 `CoxeterSystem.simple_sq`：∀ {B : Type u_1} {W : Type u_3} [inst : Group W
] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.simple i ^ 2 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_two : t ^ 2 = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp
/-
**CoxeterSystem.IsReflection.mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.I
sReflection`。
形式化陈述：mul_self : t * t = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `conj_mul`：conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * 
c) * b⁻¹
· 使用定理 `CoxeterSystem.simple_mul_simple_self`：simple_mul_simple_self (i : B) : s
 i * s i = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_self : t * t = 1 := by
  rcases ht with ⟨w, i, rfl⟩
  simp
/-
**CoxeterSystem.IsReflection.inv** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.IsRefl
ection`。
形式化陈述：inv : t⁻¹ = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem inv : t⁻¹ = t := by
  rcases ht with ⟨w, i, rfl⟩
  simp [mul_assoc]
/-
**CoxeterSystem.IsReflection.isReflection_inv** 是 Mathlib 中的一个定理，位于命名空间 `Coxeter
System.IsReflection`。
形式化陈述：isReflection_inv : cs.IsReflection t⁻¹
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.IsReflection.inv`：inv : t⁻¹ = t
-/
theorem isReflection_inv : cs.IsReflection t⁻¹ := by rwa [ht.inv]
/-
**CoxeterSystem.IsReflection.odd_length** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem
.IsReflection`。
形式化陈述：odd_length : Odd (ℓ t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.lengthParity_simple`：lengthParity_simple (i : B) : cs.leng
thParity (s i) = Multiplicative.ofAdd 1
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.lengthParity_eq_ofAdd_length`：lengthParity_eq_ofAdd_length
 (w : W) : cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w))
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem odd_length : Odd (ℓ t) := by
  suffices cs.lengthParity t = Multiplicative.ofAdd 1 by
    simpa [lengthParity_eq_ofAdd_length, ZMod.natCast_eq_one_iff_odd]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]
/-
**CoxeterSystem.IsReflection.length_mul_left_ne** 是 Mathlib 中的一个定理，位于命名空间 `Coxet
erSystem.IsReflection`。
形式化陈述：length_mul_left_ne (w : W) : ℓ (w * t) != ℓ w
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.lengthParity_simple`：lengthParity_simple (i : B) : cs.leng
thParity (s i) = Multiplicative.ofAdd 1
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `CoxeterSystem.lengthParity_eq_ofAdd_length`：lengthParity_eq_ofAdd_length
 (w : W) : cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_mul_left_ne (w : W) : ℓ (w * t) ≠ ℓ w := by
  suffices cs.lengthParity (w * t) ≠ cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]
/-
**CoxeterSystem.IsReflection.length_mul_right_ne** 是 Mathlib 中的一个定理，位于命名空间 `Coxe
terSystem.IsReflection`。
形式化陈述：length_mul_right_ne (w : W) : ℓ (t * w) != ℓ w
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.lengthParity_simple`：lengthParity_simple (i : B) : cs.leng
thParity (s i) = Multiplicative.ofAdd 1
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `CoxeterSystem.lengthParity_eq_ofAdd_length`：lengthParity_eq_ofAdd_length
 (w : W) : cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_mul_right_ne (w : W) : ℓ (t * w) ≠ ℓ w := by
  suffices cs.lengthParity (t * w) ≠ cs.lengthParity w by
    contrapose this
    simp only [lengthParity_eq_ofAdd_length, this]
  rcases ht with ⟨w, i, rfl⟩
  simp [lengthParity_simple]
/-
**CoxeterSystem.IsReflection.conj** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem.IsRef
lection`。
形式化陈述：conj (w : W) : cs.IsReflection (w * t * w⁻¹)
参数：w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mul_zpow_neg_one`：mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : Int) = b 
^ (-1 : Int) * a ^ (-1 : Int)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem conj (w : W) : cs.IsReflection (w * t * w⁻¹) := by
  obtain ⟨u, i, rfl⟩ := ht
  use w * u, i
  group

end IsReflection

@[simp]
/-
**CoxeterSystem.isReflection_conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：isReflection_conj_iff (w t : W) : cs.IsReflection (w * t * w⁻¹) ↔ cs.IsRef
lection t
参数：w t : W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `CoxeterSystem.IsReflection.conj`：conj (w : W) : cs.IsReflection (w * t *
 w⁻¹)
-/
theorem isReflection_conj_iff (w t : W) :
    cs.IsReflection (w * t * w⁻¹) ↔ cs.IsReflection t := by
  constructor
  · intro h
    simpa [← mul_assoc] using h.conj w⁻¹
  · exact IsReflection.conj (w := w)

/-- The proposition that `t` is a right inversion of `w`; i.e., `t` is a reflection and
$\ell (w t) < \ell(w)$. -/
/-
**CoxeterSystem.IsRightInversion** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：IsRightInversion (w t : W) : Prop
参数：w t : W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that `t` is a right inversion of `w`; i.e., `t` is a reflection 
and
$\ell (w t) < \ell(w)$.
-/
def IsRightInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (w * t) < ℓ w

/-- The proposition that `t` is a left inversion of `w`; i.e., `t` is a reflection and
$\ell (t w) < \ell(w)$. -/
/-
**CoxeterSystem.IsLeftInversion** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：IsLeftInversion (w t : W) : Prop
参数：w t : W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that `t` is a left inversion of `w`; i.e., `t` is a reflection a
nd
$\ell (t w) < \ell(w)$.
-/
def IsLeftInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (t * w) < ℓ w
/-
**CoxeterSystem.isRightInversion_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSyste
m`。
形式化陈述：isRightInversion_inv_iff {w t : W} : cs.IsRightInversion w⁻¹ t ↔ cs.IsLeft
Inversion w t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.length_inv`：length_inv (w : W) : ℓ (w⁻¹) = ℓ w
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `CoxeterSystem.IsReflection.inv`：inv : t⁻¹ = t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isRightInversion_inv_iff {w t : W} :
    cs.IsRightInversion w⁻¹ t ↔ cs.IsLeftInversion w t := by
  apply and_congr_right
  intro ht
  rw [← length_inv, mul_inv_rev, inv_inv, ht.inv, cs.length_inv w]
/-
**CoxeterSystem.isLeftInversion_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem
`。
形式化陈述：isLeftInversion_inv_iff {w t : W} : cs.IsLeftInversion w⁻¹ t ↔ cs.IsRightI
nversion w t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CoxeterSystem.isRightInversion_inv_iff`：isRightInversion_inv_iff {w t : 
W} : cs.IsRightInversion w⁻¹ t ↔ cs.IsLeftInversion w t
-/
theorem isLeftInversion_inv_iff {w t : W} :
    cs.IsLeftInversion w⁻¹ t ↔ cs.IsRightInversion w t := by
  convert! cs.isRightInversion_inv_iff.symm
  simp

namespace IsReflection

variable {cs}
variable {t : W} (ht : cs.IsReflection t)
include ht

/-
**CoxeterSystem.IsReflection.isRightInversion_mul_left_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CoxeterSystem.IsReflection`。
形式化陈述：isRightInversion_mul_left_iff {w : W} : cs.IsRightInversion (w * t) t ↔ ¬c
s.IsRightInversion w t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CoxeterSystem.IsReflection.mul_self`：mul_self : t * t = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `CoxeterSystem.IsReflection.length_mul_left_ne`：length_mul_left_ne (w : W
) : ℓ (w * t) != ℓ w
-/
theorem isRightInversion_mul_left_iff {w : W} :
    cs.IsRightInversion (w * t) t ↔ ¬cs.IsRightInversion w t := by
  unfold IsRightInversion
  simp only [mul_assoc, ht.mul_self, mul_one, ht, true_and, not_lt]
  constructor
  · exact le_of_lt
  · exact (lt_of_le_of_ne' · (ht.length_mul_left_ne w))
/-
**CoxeterSystem.IsReflection.not_isRightInversion_mul_left_iff** 是 Mathlib 中的一个定
理，位于命名空间 `CoxeterSystem.IsReflection`。
形式化陈述：not_isRightInversion_mul_left_iff {w : W} : ¬cs.IsRightInversion (w * t) t
 ↔ cs.IsRightInversion w t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `CoxeterSystem.IsReflection.isRightInversion_mul_left_iff`：isRightInversi
on_mul_left_iff {w : W} : cs.IsRightInversion (w * t) t ↔ ¬cs.IsRightInversion w
 t
-/
theorem not_isRightInversion_mul_left_iff {w : W} :
    ¬cs.IsRightInversion (w * t) t ↔ cs.IsRightInversion w t :=
  ht.isRightInversion_mul_left_iff.not_left
/-
**CoxeterSystem.IsReflection.isLeftInversion_mul_right_iff** 是 Mathlib 中的一个定理，位于
命名空间 `CoxeterSystem.IsReflection`。
形式化陈述：isLeftInversion_mul_right_iff {w : W} : cs.IsLeftInversion (t * w) t ↔ ¬cs
.IsLeftInversion w t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoxeterSystem.isRightInversion_inv_iff`：isRightInversion_inv_iff {w t : 
W} : cs.IsRightInversion w⁻¹ t ↔ cs.IsLeftInversion w t
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `CoxeterSystem.IsReflection.inv`：inv : t⁻¹ = t
· 使用定理 `CoxeterSystem.IsReflection.isRightInversion_mul_left_iff`：isRightInversi
on_mul_left_iff {w : W} : cs.IsRightInversion (w * t) t ↔ ¬cs.IsRightInversion w
 t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLeftInversion_mul_right_iff {w : W} :
    cs.IsLeftInversion (t * w) t ↔ ¬cs.IsLeftInversion w t := by
  rw [← isRightInversion_inv_iff, ← isRightInversion_inv_iff, mul_inv_rev, ht.inv,
    ht.isRightInversion_mul_left_iff]
/-
**CoxeterSystem.IsReflection.not_isLeftInversion_mul_right_iff** 是 Mathlib 中的一个定
理，位于命名空间 `CoxeterSystem.IsReflection`。
形式化陈述：not_isLeftInversion_mul_right_iff {w : W} : ¬cs.IsLeftInversion (t * w) t 
↔ cs.IsLeftInversion w t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `CoxeterSystem.IsReflection.isLeftInversion_mul_right_iff`：isLeftInversio
n_mul_right_iff {w : W} : cs.IsLeftInversion (t * w) t ↔ ¬cs.IsLeftInversion w t
-/
theorem not_isLeftInversion_mul_right_iff {w : W} :
    ¬cs.IsLeftInversion (t * w) t ↔ cs.IsLeftInversion w t :=
  ht.isLeftInversion_mul_right_iff.not_left

end IsReflection

@[simp]
/-
**CoxeterSystem.isRightInversion_simple_iff_isRightDescent** 是 Mathlib 中的一个定理，位于
命名空间 `CoxeterSystem`。
形式化陈述：isRightInversion_simple_iff_isRightDescent (w : W) (i : B) : cs.IsRightInv
ersion w (s i) ↔ cs.IsRightDescent w i
参数：w : W；i : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CoxeterSystem.isReflection_simple`：isReflection_simple (i : B) : cs.IsRe
flection (s i)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isRightInversion_simple_iff_isRightDescent (w : W) (i : B) :
    cs.IsRightInversion w (s i) ↔ cs.IsRightDescent w i := by
  simp [IsRightInversion, IsRightDescent, cs.isReflection_simple i]

@[simp]
/-
**CoxeterSystem.isLeftInversion_simple_iff_isLeftDescent** 是 Mathlib 中的一个定理，位于命名
空间 `CoxeterSystem`。
形式化陈述：isLeftInversion_simple_iff_isLeftDescent (w : W) (i : B) : cs.IsLeftInvers
ion w (s i) ↔ cs.IsLeftDescent w i
参数：w : W；i : B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CoxeterSystem.isReflection_simple`：isReflection_simple (i : B) : cs.IsRe
flection (s i)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLeftInversion_simple_iff_isLeftDescent (w : W) (i : B) :
    cs.IsLeftInversion w (s i) ↔ cs.IsLeftDescent w i := by
  simp [IsLeftInversion, IsLeftDescent, cs.isReflection_simple i]

/-- The right inversion sequence of `ω`. The right inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_\ell}\cdots s_{i_1}\cdots s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_{\ell - 2}}s_{i_{\ell - 1}}s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_\ell}, s_{i_\ell}.$$
-/
/-
**CoxeterSystem.rightInvSeq** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：rightInvSeq (ω : List B) : List W
参数：ω : List B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inversion sequence of `ω`. The right inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_\ell}\cdots s_{i_1}\cdots s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_{\ell - 2}}s_{i_{\ell - 1}}s_{i_\ell}, \ldo
ts,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_\ell}, s_{i_\ell}.$$
-/
def rightInvSeq (ω : List B) : List W :=
  match ω with
  | [] => []
  | i :: ω => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

/-- The left inversion sequence of `ω`. The left inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_1}, s_{i_1}s_{i_2}s_{i_1}, s_{i_1}s_{i_2}s_{i_3}s_{i_2}s_{i_1}, \ldots,
    s_{i_1}\cdots s_{i_\ell}\cdots s_{i_1}.$$
-/
/-
**CoxeterSystem.leftInvSeq** 是 Mathlib 中的一个定义，位于命名空间 `CoxeterSystem`。
形式化陈述：leftInvSeq (ω : List B) : List W
参数：ω : List B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inversion sequence of `ω`. The left inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_1}, s_{i_1}s_{i_2}s_{i_1}, s_{i_1}s_{i_2}s_{i_3}s_{i_2}s_{i_1}, \ldots,
    s_{i_1}\cdots s_{i_\ell}\cdots s_{i_1}.$$
-/
def leftInvSeq (ω : List B) : List W :=
  match ω with
  | [] => []
  | i :: ω => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq
/-
**CoxeterSystem.rightInvSeq_nil** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W), cs.rightInvSeq [] = []
参数：cs : CoxeterSystem M W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rightInvSeq_nil : ris [] = [] := rfl
/-
**CoxeterSystem.leftInvSeq_nil** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W), cs.leftInvSeq [] = []
参数：cs : CoxeterSystem M W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem leftInvSeq_nil : lis [] = [] := rfl
/-
**CoxeterSystem.rightInvSeq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) (i : B),   cs.rightInvSeq [i] = [cs.simple i]
参数：cs : CoxeterSystem M W；i : B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem rightInvSeq_singleton (i : B) : ris [i] = [s i] := by simp [rightInvSeq]
/-
**CoxeterSystem.leftInvSeq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) (i : B),   cs.leftInvSeq [i] = [cs.simple i]
参数：cs : CoxeterSystem M W；i : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem leftInvSeq_singleton (i : B) : lis [i] = [s i] := rfl
/-
**CoxeterSystem.rightInvSeq_concat** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：rightInvSeq_concat (ω : List B) (i : B) : ris (ω.concat i) = (List.map (Mu
lAut.conj (s i)) (ris ω)).concat (s i)
参数：ω : List B；i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `CoxeterSystem.rightInvSeq_singleton`：∀ {B : Type u_1} {W : Type u_2} [in
st : Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.right
InvSeq [i] = [cs.simple i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CoxeterSystem.wordProd_append`：wordProd_append (ω ω' : List B) : π (ω ++
 ω') = π ω * π ω'
· 使用定理 `CoxeterSystem.wordProd_cons`：wordProd_cons (i : B) (ω : List B) : π (i :
: ω) = s i * π ω
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem rightInvSeq_concat (ω : List B) (i : B) :
    ris (ω.concat i) = (List.map (MulAut.conj (s i)) (ris ω)).concat (s i) := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    dsimp [rightInvSeq, concat]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      inv_simple, map_cons, MulAut.conj_apply, cons_append, cons.injEq, and_true]
    group
/-
**CoxeterSystem.leftInvSeq_eq_reverse_rightInvSeq_reverse** 是 Mathlib 中的一个定理，位于命
名空间 `CoxeterSystem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem leftInvSeq_eq_reverse_rightInvSeq_reverse (ω : List B) :
    lis ω = (ris ω.reverse).reverse := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [leftInvSeq, reverse_cons, ← concat_eq_append, rightInvSeq_concat, ih]
    simp [map_reverse]
/-
**CoxeterSystem.leftInvSeq_concat** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：leftInvSeq_concat (ω : List B) (i : B) : lis (ω.concat i) = (lis ω).concat
 ((π ω) * (s i) * (π ω)⁻¹)
参数：ω : List B；i : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `CoxeterSystem.rightInvSeq.eq_2`：∀ {B : Type u_1} {W : Type u_2} [inst : 
Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B) (ω_2 : List B), 
  cs.rightInvSeq (i …
· 使用定理 `CoxeterSystem.wordProd_reverse`：∀ {B : Type u_1} {W : Type u_3} [inst : 
Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.wordP
rod ω.reverse = (cs.…
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftInvSeq_concat (ω : List B) (i : B) :
    lis (ω.concat i) = (lis ω).concat ((π ω) * (s i) * (π ω)⁻¹) := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, rightInvSeq]
/-
**CoxeterSystem.rightInvSeq_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：rightInvSeq_reverse (ω : List B) : ris (ω.reverse) = (lis ω).reverse
参数：ω : List B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightInvSeq_reverse (ω : List B) :
    ris (ω.reverse) = (lis ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]
/-
**CoxeterSystem.leftInvSeq_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：leftInvSeq_reverse (ω : List B) : lis (ω.reverse) = (ris ω).reverse
参数：ω : List B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftInvSeq_reverse (ω : List B) :
    lis (ω.reverse) = (ris ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]
/-
**CoxeterSystem.length_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) (ω : List B),   (cs.rightInvSeq ω).length = ω.length
参数：cs : CoxeterSystem M W；ω : List B；cs.rightInvSeq ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem length_rightInvSeq (ω : List B) : (ris ω).length = ω.length := by
  induction ω with
  | nil => simp
  | cons i ω ih => simpa [rightInvSeq]
/-
**CoxeterSystem.length_leftInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) (ω : List B),   (cs.leftInvSeq ω).length = ω.length
参数：cs : CoxeterSystem M W；ω : List B；cs.leftInvSeq ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `CoxeterSystem.length_rightInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.ri
ghtInvSeq ω).length = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem length_leftInvSeq (ω : List B) : (lis ω).length = ω.length := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]
/-
**CoxeterSystem.getD_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：getD_rightInvSeq (ω : List B) (j : Nat) : (ris ω).getD j 1 = (π (ω.drop (j
 + 1)))⁻¹ * (Option.map (cs.simple) ω[j]?).getD 1 * π (ω.drop (j + 1))
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `CoxeterSystem.length_rightInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.ri
ghtInvSeq ω).length = …
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem getD_rightInvSeq (ω : List B) (j : ℕ) :
    (ris ω).getD j 1 =
      (π (ω.drop (j + 1)))⁻¹
        * (Option.map (cs.simple) ω[j]?).getD 1
        * π (ω.drop (j + 1)) := by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp only [rightInvSeq]
    rcases j with _ | j'
    · simp
    · simp only [getD_eq_getElem?_getD] at ih
      simp [ih j']
/-
**CoxeterSystem.getElem_rightInvSeq** 是 Mathlib 中的一个引理，位于命名空间 `CoxeterSystem`。
形式化陈述：getElem_rightInvSeq (ω : List B) (j : Nat) (h : j < ω.length) : (ris ω)[j]
'(by simp [h]) = (π (ω.drop (j + 1)))⁻¹ * (Option.map (cs.simple) ω[j]?).getD 1 
* π (ω.drop (j + 1))
参数：ω : List B；j : Nat；h : j < ω.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `CoxeterSystem.getD_rightInvSeq`：getD_rightInvSeq (ω : List B) (j : Nat) 
: (ris ω).getD j 1 = (π (ω.drop (j + 1)))⁻¹ * (Option.map (cs.simple) ω[j]?).get
D 1 * π (ω.drop (j +…
-/
lemma getElem_rightInvSeq (ω : List B) (j : ℕ) (h : j < ω.length) :
    (ris ω)[j]'(by simp [h]) =
    (π (ω.drop (j + 1)))⁻¹
      * (Option.map (cs.simple) ω[j]?).getD 1
      * π (ω.drop (j + 1)) := by
  rw [← List.getD_eq_getElem (ris ω) 1, getD_rightInvSeq]
/-
**CoxeterSystem.getD_leftInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：getD_leftInvSeq (ω : List B) (j : Nat) : (lis ω).getD j 1 = π (ω.take j) *
 (Option.map (cs.simple) ω[j]?).getD 1 * (π (ω.take j))⁻¹
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `CoxeterSystem.length_leftInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst :
 Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.lef
tInvSeq ω).length = ω…
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `List.getD_cons_succ`：∀ {α : Type u_1} {x : α} {xs : List α} {n : ℕ} {d :
 α}, (x :: xs).getD (n + 1) d = xs.getD n d
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `CoxeterSystem.simple_mul_simple_self`：simple_mul_simple_self (i : B) : s
 i * s i = 1
（共 33 条，此处仅展示前 30 条）
-/
theorem getD_leftInvSeq (ω : List B) (j : ℕ) :
    (lis ω).getD j 1 =
      π (ω.take j)
        * (Option.map (cs.simple) ω[j]?).getD 1
        * (π (ω.take j))⁻¹ := by
  induction ω generalizing j with
  | nil => simp
  | cons i ω ih =>
    dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (s i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc, wordProd_cons]
/-
**CoxeterSystem.getElem_leftInvSeq** 是 Mathlib 中的一个引理，位于命名空间 `CoxeterSystem`。
形式化陈述：getElem_leftInvSeq (ω : List B) (j : Nat) (h : j < ω.length) : (lis ω)[j]'
(by simp [h]) = cs.wordProd (List.take j ω) * s ω[j] * (cs.wordProd (List.take j
 ω))⁻¹
参数：ω : List B；j : Nat；h : j < ω.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `CoxeterSystem.getD_leftInvSeq`：getD_leftInvSeq (ω : List B) (j : Nat) : 
(lis ω).getD j 1 = π (ω.take j) * (Option.map (cs.simple) ω[j]?).getD 1 * (π (ω.
take j))⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma getElem_leftInvSeq (ω : List B) (j : ℕ) (h : j < ω.length) :
    (lis ω)[j]'(by simp [h]) =
    cs.wordProd (List.take j ω) * s ω[j] * (cs.wordProd (List.take j ω))⁻¹ := by
  rw [← List.getD_eq_getElem (lis ω) 1, getD_leftInvSeq]
  simp [h]
/-
**CoxeterSystem.getD_rightInvSeq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSyst
em`。
形式化陈述：getD_rightInvSeq_mul_self (ω : List B) (j : Nat) : ((ris ω).getD j 1) * ((
ris ω).getD j 1) = 1
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.getD_rightInvSeq`：getD_rightInvSeq (ω : List B) (j : Nat) 
: (ris ω).getD j 1 = (π (ω.drop (j + 1)))⁻¹ * (Option.map (cs.simple) ω[j]?).get
D 1 * π (ω.drop (j +…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `CoxeterSystem.simple_mul_simple_self`：simple_mul_simple_self (i : B) : s
 i * s i = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.getElem?_eq_none_iff`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l[i]? 
= none ↔ l.length ≤ i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem getD_rightInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1 := by
  simp_rw [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp
/-
**CoxeterSystem.getD_leftInvSeq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSyste
m`。
形式化陈述：getD_leftInvSeq_mul_self (ω : List B) (j : Nat) : ((lis ω).getD j 1) * ((l
is ω).getD j 1) = 1
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoxeterSystem.getD_leftInvSeq`：getD_leftInvSeq (ω : List B) (j : Nat) : 
(lis ω).getD j 1 = π (ω.take j) * (Option.map (cs.simple) ω[j]?).getD 1 * (π (ω.
take j))⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `CoxeterSystem.simple_mul_simple_self`：simple_mul_simple_self (i : B) : s
 i * s i = 1
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.getElem?_eq_none_iff`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l[i]? 
= none ↔ l.length ≤ i
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem getD_leftInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * ((lis ω).getD j 1) = 1 := by
  simp_rw [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [getElem?_eq_getElem hj]
    simp [← mul_assoc]
  · rw [getElem?_eq_none_iff.mpr (by lia)]
    simp
/-
**CoxeterSystem.rightInvSeq_drop** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：rightInvSeq_drop (ω : List B) (j : Nat) : ris (ω.drop j) = (ris ω).drop j
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `List.drop_succ_cons`：∀ {α : Type u} {a : α} {l : List α} {i : ℕ}, List.d
rop (i + 1) (a :: l) = List.drop i l
· 使用定理 `CoxeterSystem.rightInvSeq.eq_2`：∀ {B : Type u_1} {W : Type u_2} [inst : 
Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B) (ω_2 : List B), 
  cs.rightInvSeq (i …
-/
theorem rightInvSeq_drop (ω : List B) (j : ℕ) :
    ris (ω.drop j) = (ris ω).drop j := by
  induction j generalizing ω with
  | zero => simp
  | succ j ih₁ =>
    induction ω with
    | nil => simp
    | cons k ω _ => rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]
/-
**CoxeterSystem.leftInvSeq_take** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：leftInvSeq_take (ω : List B) (j : Nat) : lis (ω.take j) = (lis ω).take j
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `List.take_reverse`：∀ {α : Type u_1} {xs : List α} {i : ℕ}, List.take i x
s.reverse = (List.drop (xs.length - i) xs).reverse
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `CoxeterSystem.rightInvSeq_drop`：rightInvSeq_drop (ω : List B) (j : Nat) 
: ris (ω.drop j) = (ris ω).drop j
· 使用定理 `CoxeterSystem.length_rightInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.ri
ghtInvSeq ω).length = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftInvSeq_take (ω : List B) (j : ℕ) :
    lis (ω.take j) = (lis ω).take j := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse]
  rw [List.take_reverse]
  nth_rw 1 [← List.reverse_reverse ω]
  rw [List.take_reverse]
  simp [rightInvSeq_drop]
/-
**CoxeterSystem.isReflection_of_mem_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `Coxet
erSystem`。
形式化陈述：isReflection_of_mem_rightInvSeq (ω : List B) {t : W} (ht : t in ris ω) : c
s.IsReflection t
参数：ω : List B；ht : t in ris ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.mul_neg`：∀ (a b : ℤ), a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem isReflection_of_mem_rightInvSeq (ω : List B) {t : W} (ht : t ∈ ris ω) :
    cs.IsReflection t := by
  induction ω with
  | nil => simp at ht
  | cons i ω ih =>
    dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem
/-
**CoxeterSystem.isReflection_of_mem_leftInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `Coxete
rSystem`。
形式化陈述：isReflection_of_mem_leftInvSeq (ω : List B) {t : W} (ht : t in lis ω) : cs
.IsReflection t
参数：ω : List B；ht : t in lis ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.isReflection_of_mem_rightInvSeq`：isReflection_of_mem_right
InvSeq (ω : List B) {t : W} (ht : t in ris ω) : cs.IsReflection t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
-/
theorem isReflection_of_mem_leftInvSeq (ω : List B) {t : W} (ht : t ∈ lis ω) :
    cs.IsReflection t := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, mem_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse ht
/-
**CoxeterSystem.wordProd_mul_getD_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `Coxeter
System`。
形式化陈述：wordProd_mul_getD_rightInvSeq (ω : List B) (j : Nat) : π ω * ((ris ω).getD
 j 1) = π (ω.eraseIdx j)
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.getD_rightInvSeq`：getD_rightInvSeq (ω : List B) (j : Nat) 
: (ris ω).getD j 1 = (π (ω.drop (j + 1)))⁻¹ * (Option.map (cs.simple) ω[j]?).get
D 1 * π (ω.drop (j +…
· 使用定理 `List.eraseIdx_eq_take_drop_succ`：∀ {α : Type u_1} (l : List α) (i : ℕ), 
l.eraseIdx i = List.take i l ++ List.drop (i + 1) l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `List.take_add_one`：∀ {α : Type u_1} {l : List α} {i : ℕ}, List.take (i +
 1) l = List.take i l ++ l[i]?.toList
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `CoxeterSystem.wordProd_append`：wordProd_append (ω ω' : List B) : π (ω ++
 ω') = π ω * π ω'
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CoxeterSystem.wordProd_singleton`：∀ {B : Type u_1} {W : Type u_3} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.wordProd
 [i] = cs.simple i
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `CoxeterSystem.simple_mul_simple_cancel_left`：simple_mul_simple_cancel_le
ft {w : W} (i : B) : s i * (s i * w) = w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem wordProd_mul_getD_rightInvSeq (ω : List B) (j : ℕ) :
    π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j) := by
  rw [getD_rightInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp
/-
**CoxeterSystem.getD_leftInvSeq_mul_wordProd** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterS
ystem`。
形式化陈述：getD_leftInvSeq_mul_wordProd (ω : List B) (j : Nat) : ((lis ω).getD j 1) *
 π ω = π (ω.eraseIdx j)
参数：ω : List B；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.getD_leftInvSeq`：getD_leftInvSeq (ω : List B) (j : Nat) : 
(lis ω).getD j 1 = π (ω.take j) * (Option.map (cs.simple) ω[j]?).getD 1 * (π (ω.
take j))⁻¹
· 使用定理 `List.eraseIdx_eq_take_drop_succ`：∀ {α : Type u_1} (l : List α) (i : ℕ), 
l.eraseIdx i = List.take i l ++ List.drop (i + 1) l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `List.take_add_one`：∀ {α : Type u_1} {l : List α} {i : ℕ}, List.take (i +
 1) l = List.take i l ++ l[i]?.toList
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CoxeterSystem.wordProd_append`：wordProd_append (ω ω' : List B) : π (ω ++
 ω') = π ω * π ω'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CoxeterSystem.wordProd_singleton`：∀ {B : Type u_1} {W : Type u_3} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.wordProd
 [i] = cs.simple i
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `CoxeterSystem.simple_mul_simple_cancel_left`：simple_mul_simple_cancel_le
ft {w : W} (i : B) : s i * (s i * w) = w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem getD_leftInvSeq_mul_wordProd (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j) := by
  rw [getD_leftInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_add_one]
  obtain lt | le := lt_or_ge j ω.length
  · simp only [getElem?_eq_getElem lt, wordProd_append, mul_assoc]
    simp
  · simp only [getElem?_eq_none le]
    simp
/-
**CoxeterSystem.isRightInversion_of_mem_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `C
oxeterSystem`。
形式化陈述：isRightInversion_of_mem_rightInvSeq {ω : List B} (hω : cs.IsReduced ω) {t 
: W} (ht : t in ris ω) : cs.IsRightInversion (π ω) t
参数：hω : cs.IsReduced ω；ht : t in ris ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.isReflection_of_mem_rightInvSeq`：isReflection_of_mem_right
InvSeq (ω : List B) {t : W} (ht : t in ris ω) : cs.IsReflection t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_iff_getElem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ i
, ∃ (h : i < l.length), l[i] = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `CoxeterSystem.wordProd_mul_getD_rightInvSeq`：wordProd_mul_getD_rightInvS
eq (ω : List B) (j : Nat) : π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j)
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
· 使用定理 `List.length_eraseIdx_add_one`：length_eraseIdx_add_one {l : List ι} {i : 
Nat} (h : i < l.length) : (l.eraseIdx i).length + 1 = l.length
· 使用定理 `CoxeterSystem.length_rightInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.ri
ghtInvSeq ω).length = …
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
-/
theorem isRightInversion_of_mem_rightInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t ∈ ris ω) : cs.IsRightInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_rightInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj, wordProd_mul_getD_rightInvSeq]
    rw [cs.length_rightInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ ≤ (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm
/-
**CoxeterSystem.isLeftInversion_of_mem_leftInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `Cox
eterSystem`。
形式化陈述：isLeftInversion_of_mem_leftInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : 
W} (ht : t in lis ω) : cs.IsLeftInversion (π ω) t
参数：hω : cs.IsReduced ω；ht : t in lis ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoxeterSystem.isReflection_of_mem_leftInvSeq`：isReflection_of_mem_leftIn
vSeq (ω : List B) {t : W} (ht : t in lis ω) : cs.IsReflection t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_iff_getElem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ i
, ∃ (h : i < l.length), l[i] = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `CoxeterSystem.getD_leftInvSeq_mul_wordProd`：getD_leftInvSeq_mul_wordProd
 (ω : List B) (j : Nat) : ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j)
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
· 使用定理 `List.length_eraseIdx_add_one`：length_eraseIdx_add_one {l : List ι} {i : 
Nat} (h : i < l.length) : (l.eraseIdx i).length + 1 = l.length
· 使用定理 `CoxeterSystem.length_leftInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst :
 Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.lef
tInvSeq ω).length = ω…
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
-/
theorem isLeftInversion_of_mem_leftInvSeq {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : t ∈ lis ω) : cs.IsLeftInversion (π ω) t := by
  constructor
  · exact cs.isReflection_of_mem_leftInvSeq ω ht
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rw [← List.getD_eq_getElem _ 1 hj, getD_leftInvSeq_mul_wordProd]
    rw [cs.length_leftInvSeq] at hj
    calc
      ℓ (π (ω.eraseIdx j))
      _ ≤ (ω.eraseIdx j).length := cs.length_wordProd_le _
      _ < ω.length := by rw [← List.length_eraseIdx_add_one hj]; exact lt_add_one _
      _ = ℓ (π ω) := hω.symm
/-
**CoxeterSystem.prod_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹
参数：ω : List B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `CoxeterSystem.wordProd_cons`：wordProd_cons (i : B) (ω : List B) : π (i :
: ω) = s i * π ω
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
-/
theorem prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih => simp [rightInvSeq, ih, wordProd_cons]
/-
**CoxeterSystem.prod_leftInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSystem`。
形式化陈述：prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹
参数：ω : List B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `List.prod_reverse_noncomm`：prod_reverse_noncomm : forall L : List G, L.r
everse.prod = (L.map fun x => x⁻¹).prod⁻¹
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
· 使用定理 `CoxeterSystem.IsReflection.inv`：inv : t⁻¹ = t
· 使用定理 `CoxeterSystem.isReflection_of_mem_rightInvSeq`：isReflection_of_mem_right
InvSeq (ω : List B) {t : W} (ht : t in ris ω) : cs.IsReflection t
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `CoxeterSystem.wordProd_reverse`：∀ {B : Type u_1} {W : Type u_3} [inst : 
Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.wordP
rod ω.reverse = (cs.…
· 使用定理 `CoxeterSystem.prod_rightInvSeq`：prod_rightInvSeq (ω : List B) : prod (ri
s ω) = (π ω)⁻¹
-/
theorem prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹ := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm, inv_inj]
  have : List.map (fun x ↦ x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x ↦ x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse) := by
        apply List.map_congr_left
        intro t ht
        exact (cs.isReflection_of_mem_rightInvSeq _ ht).inv
    _ = ris ω.reverse := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _
/-
**CoxeterSystem.IsReduced.nodup_rightInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSy
stem.IsReduced`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) {ω : List B},   cs.IsReduced ω → (cs.rightInvSeq ω).Nodup
参数：cs : CoxeterSystem M W；cs.rightInvSeq ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_iff_getElem?_ne_getElem?`：∀ {α : Type u} {l : List α}, l.Nodu
p ↔ ∀ (i j : ℕ), i < j → j < l.length → l[i]? ≠ l[j]?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.length_rightInvSeq`：∀ {B : Type u_1} {W : Type u_2} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   (cs.ri
ghtInvSeq ω).length = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getD_eq_getElem`：getD_eq_getElem {n : Nat} (hn : n < l.length) : l.
getD n d = l[n]
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `CoxeterSystem.getD_rightInvSeq_mul_self`：getD_rightInvSeq_mul_self (ω : 
List B) (j : Nat) : ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CoxeterSystem.wordProd_mul_getD_rightInvSeq`：wordProd_mul_getD_rightInvS
eq (ω : List B) (j : Nat) : π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j)
· 使用定理 `CoxeterSystem.length_wordProd_le`：length_wordProd_le (ω : List B) : ℓ (π
 ω) <= ω.length
-/
theorem IsReduced.nodup_rightInvSeq {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (ris ω) := by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr
  intro j j' j_lt_j' j'_lt_length (dup : (rightInvSeq cs ω)[j]? = (rightInvSeq cs ω)[j']?)
  show False
  replace j'_lt_length : j' < List.length ω := by simpa using j'_lt_length
  rw [getElem?_eq_getElem (by simp; lia), getElem?_eq_getElem (by simp; lia)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_getElem _ 1, ← getD_eq_getElem _ 1] at dup
  set! t := (ris ω).getD j 1 with h₁
  set! t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1 with h₂
  have h₃ : t' = (ris ω).getD j' 1 := by
    grind only [cs.getD_rightInvSeq, = eraseIdx_eq_take_drop_succ, = getElem?_eraseIdx,
      = drop_append, drop_of_length_le, drop_drop, = length_append, = length_take, = length_drop,
      = min_def]
  have h₄ : t * t' = 1 := by
    rw [h₁, h₃, dup]
    exact cs.getD_rightInvSeq_mul_self _ _
  have h₅ := calc
    π ω = π ω * t * t' := by rw [mul_assoc, h₄]; group
    _ = (π (ω.eraseIdx j)) * t' :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _ = π ((ω.eraseIdx j).eraseIdx (j' - 1)) :=
        cs.wordProd_mul_getD_rightInvSeq _ _
  have h₆ := calc
    ω.length = ℓ (π ω) := rω.symm
    _ = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1))) := congrArg cs.length h₅
    _ ≤ ((ω.eraseIdx j).eraseIdx (j' - 1)).length := cs.length_wordProd_le _
  grind
/-
**CoxeterSystem.IsReduced.nodup_leftInvSeq** 是 Mathlib 中的一个定理，位于命名空间 `CoxeterSys
tem.IsReduced`。
形式化陈述：∀ {B : Type u_1} {W : Type u_2} [inst : Group W] {M : CoxeterMatrix B} (cs
 : CoxeterSystem M W) {ω : List B},   cs.IsReduced ω → (cs.leftInvSeq ω).Nodup
参数：cs : CoxeterSystem M W；cs.leftInvSeq ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.GroupTheory.Coxeter.Inversion.0.CoxeterSystem.leftInvSe
q_eq_reverse_rightInvSeq_reverse`：∀ {B : Type u_1} {W : Type u_2} [inst : Group 
W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (ω : List B),   cs.leftInvSeq 
ω = (cs.rightI…
· 使用定理 `CoxeterSystem.IsReduced.nodup_rightInvSeq`：∀ {B : Type u_1} {W : Type u_
2} [inst : Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) {ω : List B},
   cs.IsReduced ω → (cs.rightIn…
· 使用定理 `CoxeterSystem.isReduced_reverse_iff`：isReduced_reverse_iff (ω : List B) 
: cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω
-/
theorem IsReduced.nodup_leftInvSeq {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (lis ω) := by
  simp only [leftInvSeq_eq_reverse_rightInvSeq_reverse, nodup_reverse]
  apply nodup_rightInvSeq
  rwa [isReduced_reverse_iff]
/-
**CoxeterSystem.getElem_succ_leftInvSeq_alternatingWord** 是 Mathlib 中的一个引理，位于命名空
间 `CoxeterSystem`。
形式化陈述：getElem_succ_leftInvSeq_alternatingWord (i j : B) (p k : Nat) (h : k + 1 <
 2 * p) : (lis (alternatingWord i j (2 * p)))[k + 1]'(by simpa using h) = MulAut
.conj (s i) ((lis (alternatingWord j i (2 * p)))[k]'(by simp; lia))
参数：i j : B；p k : Nat；h : k + 1 < 2 * p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.length_alternatingWord`：length_alternatingWord (i i' : B) 
(m : Nat) : List.length (alternatingWord i i' m) = m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `CoxeterSystem.getElem_leftInvSeq`：getElem_leftInvSeq (ω : List B) (j : N
at) (h : j < ω.length) : (lis ω)[j]'(by simp [h]) = cs.wordProd (List.take j ω) 
* s ω[j] * (cs.wordPro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CoxeterSystem.listTake_succ_alternatingWord`：listTake_succ_alternatingWo
rd (i j : B) (p : Nat) (k : Nat) (h : k + 1 < 2 * p) : List.take (k + 1) (altern
atingWord i j (2 * p)) = i :: (Li…
· 使用定理 `CoxeterSystem.wordProd_cons`：wordProd_cons (i : B) (ω : List B) : π (i :
: ω) = s i * π ω
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `MulEquiv.mk.congr_simp`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] 
[inst_1 : Mul N] (toEquiv toEquiv_1 : M ≃ N)   (e_toEquiv : toEquiv = toEquiv_1)
 (map_mul' :…
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用引理 `CoxeterSystem.getElem_alternatingWord_swapIndices`：getElem_alternatingWo
rd_swapIndices (i j : B) (p k : Nat) (h : k + 1 < p) : (alternatingWord i j p)[k
 + 1]'(by simp [h]) = (alternatingWord …
-/
lemma getElem_succ_leftInvSeq_alternatingWord
    (i j : B) (p k : ℕ) (h : k + 1 < 2 * p) :
    (lis (alternatingWord i j (2 * p)))[k + 1]'(by simpa using h) =
    MulAut.conj (s i) ((lis (alternatingWord j i (2 * p)))[k]'(by simp; lia)) := by
  rw [cs.getElem_leftInvSeq (alternatingWord i j (2 * p)) (k + 1) (by simp [h]),
    cs.getElem_leftInvSeq (alternatingWord j i (2 * p)) k (by simp; lia)]
  simp only [MulAut.conj, listTake_succ_alternatingWord i j p k h, cs.wordProd_cons, mul_assoc,
    mul_inv_rev, inv_simple, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    mul_right_inj, mul_left_inj]
  rw [getElem_alternatingWord_swapIndices i j (2 * p) k]
  lia
/-
**CoxeterSystem.getElem_leftInvSeq_alternatingWord** 是 Mathlib 中的一个定理，位于命名空间 `Co
xeterSystem`。
形式化陈述：getElem_leftInvSeq_alternatingWord (i j : B) (p k : Nat) (h : k < 2 * p) :
 (lis (alternatingWord i j (2 * p)))[k]'(by simp; lia) = π alternatingWord j i (
2 * k + 1)
参数：i j : B；p k : Nat；h : k < 2 * p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CoxeterSystem.length_alternatingWord`：length_alternatingWord (i i' : B) 
(m : Nat) : List.length (alternatingWord i i' m) = m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CoxeterSystem.getElem_leftInvSeq`：getElem_leftInvSeq (ω : List B) (j : N
at) (h : j < ω.length) : (lis ω)[j]'(by simp [h]) = cs.wordProd (List.take j ω) 
* s ω[j] * (cs.wordPro…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CoxeterSystem.wordProd_nil`：∀ {B : Type u_1} {W : Type u_3} [inst : Grou
p W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W), cs.wordProd [] = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `CoxeterSystem.wordProd_singleton`：∀ {B : Type u_1} {W : Type u_3} [inst 
: Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W) (i : B),   cs.wordProd
 [i] = cs.simple i
· 使用引理 `CoxeterSystem.getElem_alternatingWord`：getElem_alternatingWord (i j : B)
 (p k : Nat) (hk : k < p) : (alternatingWord i j p)[k]'(by simp [hk]) = (if Even
 (p + k) then i else j)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CoxeterSystem.getElem_succ_leftInvSeq_alternatingWord`：getElem_succ_left
InvSeq_alternatingWord (i j : B) (p k : Nat) (h : k + 1 < 2 * p) : (lis (alterna
tingWord i j (2 * p)))[k + 1]'(by simpa usi…
· 使用定理 `CoxeterSystem.inv_simple`：inv_simple (i : B) : (s i)⁻¹ = s i
· 使用定理 `CoxeterSystem.alternatingWord_succ'`：alternatingWord_succ' (i i' : B) (m
 : Nat) : alternatingWord i i' (m + 1) = (if Even m then i' else i) :: alternati
ngWord i i' m
· 使用定理 `CoxeterSystem.wordProd_cons`：wordProd_cons (i : B) (ω : List B) : π (i :
: ω) = s i * π ω
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 49 条，此处仅展示前 30 条）
-/
theorem getElem_leftInvSeq_alternatingWord
    (i j : B) (p k : ℕ) (h : k < 2 * p) :
    (lis (alternatingWord i j (2 * p)))[k]'(by simp; lia) =
    π alternatingWord j i (2 * k + 1) := by
  induction k generalizing i j with
  | zero =>
    simp only [CoxeterSystem.getElem_leftInvSeq cs (alternatingWord i j (2 * p)) 0 (by simp [h]),
      take_zero, wordProd_nil, one_mul, inv_one, mul_one, alternatingWord, concat_eq_append,
      nil_append, wordProd_singleton]
    simp only [getElem_alternatingWord i j (2 * p) 0 (by simp [h]), add_zero, even_two,
      Even.mul_right, ↓reduceIte]
  | succ k hk =>
    simp only [getElem_succ_leftInvSeq_alternatingWord cs i j p k h, hk _ _ (by lia),
      MulAut.conj_apply, inv_simple, alternatingWord_succ' j i, even_two, Even.mul_right,
      ↓reduceIte, wordProd_cons]
    rw [(by ring : 2 * (k + 1) = 2 * k + 1 + 1), alternatingWord_succ j i, wordProd_concat]
    simp [mul_assoc]

end CoxeterSystem

