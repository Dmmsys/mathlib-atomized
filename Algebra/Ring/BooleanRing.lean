/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `BooleanRing`: a typeclass for rings where multiplication is idempotent.
* `BooleanRing.toBooleanAlgebra`: Turn a Boolean ring into a Boolean algebra.
* `BooleanAlgebra.toBooleanRing`: Turn a Boolean algebra into a Boolean ring.
* `AsBoolAlg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `AsBoolRing`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `BooleanAlgebraOfBooleanRing` and
  `BooleanRingOfBooleanAlgebra`.
* Type-synonyms `AsBoolAlg` and `AsBoolRing`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`ofBoolAlg`/`toBoolAlg`/`ofBoolRing`/`toBoolRing` explicitly.

## Tags

boolean ring, boolean algebra
-/

@[expose] public section

open scoped symmDiff

variable {α β γ : Type*}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
/-
**BooleanRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean ring is a ring where multiplication is idempotent.
-/
class BooleanRing (α) extends Ring α where
  /-- Multiplication in a Boolean ring is idempotent. -/
  isIdempotentElem (a : α) : IsIdempotentElem a

namespace BooleanRing

variable [BooleanRing α] (a b : α)

@[scoped simp]
/-
**BooleanRing.mul_self** 是 Mathlib 中的一个引理，位于命名空间 `BooleanRing`。
形式化陈述：mul_self : a * a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `BooleanRing.isIdempotentElem`：∀ {α : Type u_4} [self : BooleanRing α] (a
 : α), IsIdempotentElem a
-/
lemma mul_self : a * a = a := IsIdempotentElem.eq (isIdempotentElem a)
/-
**BooleanRing.** 是 Mathlib 中的一个实例，位于命名空间 `BooleanRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.IdempotentOp (α := α) (· * ·) :=
  ⟨BooleanRing.mul_self⟩

@[scoped simp]
/-
**BooleanRing.add_self** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：add_self : a + a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `right_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, b = a + b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [right_eq_add] at this

@[scoped simp]
/-
**BooleanRing.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：neg_eq : -a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `BooleanRing.add_self`：add_self : a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self, zero_add]
/-
**BooleanRing.add_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：add_eq_zero' : a + b = 0 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BooleanRing.neg_eq`：neg_eq : -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_eq_zero' : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]

@[simp]
/-
**BooleanRing.mul_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：mul_add_mul : a * b + b * a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.Algebra.Ring.BooleanRing.0.BooleanRing.mul_add_mul._abe
l_1_1`：∀ {α : Type u_1} [inst : BooleanRing α] (a b : α), a + a * b + (b * a + b
) = a + b + (a * b + b * a)
· 使用定理 `left_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a = a + b ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [left_eq_add] at this

@[scoped simp]
/-
**BooleanRing.sub_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：sub_eq_add : a - b = a + b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `BooleanRing.neg_eq`：neg_eq : -a = a
-/
theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, neg_eq]

@[simp]
/-
**BooleanRing.mul_one_add_self** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：mul_one_add_self : a * (1 + a) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `BooleanRing.add_self`：add_self : a + a = 0
-/
theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]

-- Note [lower instance priority]
/-
**BooleanRing.** 是 Mathlib 中的一个实例，位于命名空间 `BooleanRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toCommRing : CommRing α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by rw [← add_eq_zero', mul_add_mul] }

end BooleanRing

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
/-
**AsBoolAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AsBoolAlg (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym to view a Boolean ring as a Boolean algebra.
-/
def AsBoolAlg (α : Type*) :=
  α

/-- The "identity" equivalence between `AsBoolAlg α` and `α`. -/
/-
**toBoolAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toBoolAlg : α ≃ AsBoolAlg α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The "identity" equivalence between `AsBoolAlg α` and `α`.
-/
def toBoolAlg : α ≃ AsBoolAlg α :=
  Equiv.refl _

/-- The "identity" equivalence between `α` and `AsBoolAlg α`. -/
/-
**ofBoolAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofBoolAlg : AsBoolAlg α ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The "identity" equivalence between `α` and `AsBoolAlg α`.
-/
def ofBoolAlg : AsBoolAlg α ≃ α :=
  Equiv.refl _

@[simp]
/-
**toBoolAlg_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg :=
  rfl

@[simp]
/-
**ofBoolAlg_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg :=
  rfl

@[simp]
/-
**toBoolAlg_ofBoolAlg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a
参数：a : AsBoolAlg α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a :=
  rfl

@[simp]
/-
**ofBoolAlg_toBoolAlg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a :=
  rfl
/-
**toBoolAlg_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b :=
  Iff.rfl
/-
**ofBoolAlg_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b :=
  Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (AsBoolAlg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
@[instance_reducible]
/-
**BooleanRing.sup** 是 Mathlib 中的一个定义，位于命名空间 `BooleanRing`。
形式化陈述：sup : Max α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The join operation in a Boolean ring is `x + y + x * y`.
-/
def sup : Max α :=
  ⟨fun x y => x + y + x * y⟩

/-- The meet operation in a Boolean ring is `x * y`. -/
@[instance_reducible]
/-
**BooleanRing.inf** 是 Mathlib 中的一个定义，位于命名空间 `BooleanRing`。
形式化陈述：inf : Min α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The meet operation in a Boolean ring is `x * y`.
-/
def inf : Min α :=
  ⟨(· * ·)⟩

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup
scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf
open BooleanAlgebraOfBooleanRing
/-
**BooleanRing.sup_comm** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：sup_comm (a b : α) : a ⊔ b = b ⊔ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  dsimp only [(· ⊔ ·)]
  ring
/-
**BooleanRing.inf_comm** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：inf_comm (a b : α) : a ⊓ b = b ⊓ a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  dsimp only [(· ⊓ ·)]
  ring
/-
**BooleanRing.sup_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  dsimp only [(· ⊔ ·)]
  ring
/-
**BooleanRing.inf_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  dsimp only [(· ⊓ ·)]
  ring
/-
**BooleanRing.sup_inf_self** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：sup_inf_self (a b : α) : a ⊔ a ⊓ b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `BooleanRing.add_self`：add_self : a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem sup_inf_self (a b : α) : a ⊔ a ⊓ b = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [← mul_assoc, mul_self, add_assoc, add_self, add_zero]
/-
**BooleanRing.inf_sup_self** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `BooleanRing.add_self`：add_self : a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add, mul_add, mul_self, ← mul_assoc, mul_self, add_assoc, add_self, add_zero]
/-
**BooleanRing.le_sup_inf_aux** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c
 + a * (b * c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `BooleanRing.add_self`：add_self : a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 31 条，此处仅展示前 30 条）
-/
theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) := by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]
/-
**BooleanRing.le_sup_inf** 是 Mathlib 中的一个定理，位于命名空间 `BooleanRing`。
形式化陈述：le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BooleanRing.le_sup_inf_aux`：le_sup_inf_aux (a b c : α) : (a + b + a * b)
 * (a + c + a * c) = a + b * c + a * (b * c)
· 使用定理 `BooleanRing.add_self`：add_self : a + a = 0
· 使用引理 `BooleanRing.mul_self`：mul_self : a * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux, add_self, mul_self, zero_add]

/-- The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
@[instance_reducible]
/-
**BooleanRing.toBooleanAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `BooleanRing`。
形式化陈述：toBooleanAlgebra : BooleanAlgebra α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanRing.sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `BooleanRing.sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `BooleanRing.inf_comm`：inf_comm (a b : α) : a ⊓ b = b ⊓ a
· 使用定理 `BooleanRing.inf_assoc`：inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
· 使用定理 `BooleanRing.sup_inf_self`：sup_inf_self (a b : α) : a ⊔ a ⊓ b = a
· 使用定理 `BooleanRing.inf_sup_self`：inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a
· 使用定理 `BooleanRing.le_sup_inf`：le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a 
⊔ b ⊓ c) = a ⊔ b ⊓ c
· 使用定理 `Lattice.inf_le_left`：∀ {α : Type u} [self : Lattice α] (a b : α), Lattic
e.inf a b ≤ a
· 使用定理 `Lattice.inf_le_right`：∀ {α : Type u} [self : Lattice α] (a b : α), Latti
ce.inf a b ≤ b
· 使用定理 `Lattice.le_inf`：∀ {α : Type u} [self : Lattice α] (a b c : α), a ≤ b → a
 ≤ c → a ≤ Lattice.inf b c

--- 原说明 ---
The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
def toBooleanAlgebra : BooleanAlgebra α :=
  { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self with
    le_sup_inf := le_sup_inf
    top := 1
    le_top := fun a => show a + 1 + a * 1 = 1 by rw [mul_one, add_comm a 1,
                                                     add_assoc, add_self, add_zero]
    bot := 0
    bot_le := fun a => show 0 + a + 0 * a = a by rw [zero_mul, zero_add, add_zero]
    compl := fun a => 1 + a
    inf_compl_le_bot := fun a =>
      show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by simp [mul_add, mul_self, add_self]
    top_le_sup_compl := fun a => by
      change
        1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) =
          a + (1 + a) + a * (1 + a)
      simp [mul_add, mul_self, add_self, ← add_assoc 1 a] }

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.toBooleanAlgebra

end BooleanRing

open BooleanRing

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanAlgebra (AsBoolAlg α) :=
  fast_instance% @BooleanRing.toBooleanAlgebra α _

@[simp]
/-
**ofBoolAlg_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1 :=
  rfl

@[simp]
/-
**ofBoolAlg_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0 :=
  rfl

@[simp]
/-
**ofBoolAlg_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_sup (a b : AsBoolAlg α) : ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBo
olAlg b + ofBoolAlg a * ofBoolAlg b
参数：a b : AsBoolAlg α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_sup (a b : AsBoolAlg α) :
    ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBoolAlg b + ofBoolAlg a * ofBoolAlg b :=
  rfl

@[simp]
/-
**ofBoolAlg_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_inf (a b : AsBoolAlg α) : ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBo
olAlg b
参数：a b : AsBoolAlg α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_inf (a b : AsBoolAlg α) : ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBoolAlg b :=
  rfl

@[simp]
/-
**ofBoolAlg_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a
参数：a : AsBoolAlg α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a :=
  rfl

@[simp]
/-
**ofBoolAlg_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_sdiff (a b : AsBoolAlg α) : ofBoolAlg (a \ b) = ofBoolAlg a * (1
 + ofBoolAlg b)
参数：a b : AsBoolAlg α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolAlg_sdiff (a b : AsBoolAlg α) : ofBoolAlg (a \ b) = ofBoolAlg a * (1 + ofBoolAlg b) :=
  rfl
/-
**of_boolalg_symmDiff_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]

@[simp]
/-
**ofBoolAlg_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (a ∆ b) = ofBoolAlg a +
 ofBoolAlg b
参数：a b : AsBoolAlg α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_eq_sup_sdiff_inf`：symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \
 (a ⊓ b)
· 使用定理 `_private.Mathlib.Algebra.Ring.BooleanRing.0.of_boolalg_symmDiff_aux`：∀ {
α : Type u_1} [inst : BooleanRing α] (a b : α), (a + b + a * b) * (1 + a * b) = 
a + b
-/
theorem ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (a ∆ b) = ofBoolAlg a + ofBoolAlg b := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symmDiff_aux _ _

@[simp]
/-
**ofBoolAlg_mul_ofBoolAlg_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolAlg_mul_ofBoolAlg_eq_left_iff {a b : AsBoolAlg α} : ofBoolAlg a * of
BoolAlg b = ofBoolAlg a ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
theorem ofBoolAlg_mul_ofBoolAlg_eq_left_iff {a b : AsBoolAlg α} :
    ofBoolAlg a * ofBoolAlg b = ofBoolAlg a ↔ a ≤ b :=
  @inf_eq_left (AsBoolAlg α) _ _ _

@[simp]
/-
**toBoolAlg_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_zero : toBoolAlg (0 : α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolAlg_zero : toBoolAlg (0 : α) = ⊥ :=
  rfl

@[simp]
/-
**toBoolAlg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_one : toBoolAlg (1 : α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolAlg_one : toBoolAlg (1 : α) = ⊤ :=
  rfl

@[simp]
/-
**toBoolAlg_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_mul (a b : α) : toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolAlg_mul (a b : α) : toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b :=
  rfl

@[simp]
/-
**toBoolAlg_add_add_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_add_add_mul (a b : α) : toBoolAlg (a + b + a * b) = toBoolAlg a 
⊔ toBoolAlg b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolAlg_add_add_mul (a b : α) : toBoolAlg (a + b + a * b) = toBoolAlg a ⊔ toBoolAlg b :=
  rfl

@[simp]
/-
**toBoolAlg_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolAlg_add (a b : α) : toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofBoolAlg_symmDiff`：ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (
a ∆ b) = ofBoolAlg a + ofBoolAlg b
-/
theorem toBoolAlg_add (a b : α) : toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b :=
  (ofBoolAlg_symmDiff a b).symm

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
/-
**RingHom.asBoolAlg** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : BooleanRing α] → [inst_1 :
 BooleanRing β] → (α →+* β) → BoundedLatticeHom (AsBoolAlg α) (AsBoolAlg β)
参数：α →+* β；AsBoolAlg α；AsBoolAlg β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice ho
momorphism
from `α` to `β` considered as Boolean algebras.
-/
protected def RingHom.asBoolAlg (f : α →+* β) : BoundedLatticeHom (AsBoolAlg α) (AsBoolAlg β) where
  toFun := toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

@[simp]
/-
**RingHom.asBoolAlg_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.asBoolAlg_id : (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.asBoolAlg_id : (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _ :=
  rfl

@[simp]
/-
**RingHom.asBoolAlg_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.asBoolAlg_comp (g : β ->+* γ) (f : α ->+* β) : (g.comp f).asBoolAl
g = g.asBoolAlg.comp f.asBoolAlg
参数：g : β ->+* γ；f : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.asBoolAlg_comp (g : β →+* γ) (f : α →+* β) :
    (g.comp f).asBoolAlg = g.asBoolAlg.comp f.asBoolAlg :=
  rfl

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
/-
**AsBoolRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AsBoolRing (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym to view a Boolean ring as a Boolean algebra.
-/
def AsBoolRing (α : Type*) :=
  α

/-- The "identity" equivalence between `AsBoolRing α` and `α`. -/
/-
**toBoolRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toBoolRing : α ≃ AsBoolRing α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The "identity" equivalence between `AsBoolRing α` and `α`.
-/
def toBoolRing : α ≃ AsBoolRing α :=
  Equiv.refl _

/-- The "identity" equivalence between `α` and `AsBoolRing α`. -/
/-
**ofBoolRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofBoolRing : AsBoolRing α ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The "identity" equivalence between `α` and `AsBoolRing α`.
-/
def ofBoolRing : AsBoolRing α ≃ α :=
  Equiv.refl _

@[simp]
/-
**toBoolRing_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_symm_eq : (@toBoolRing α).symm = ofBoolRing
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toBoolRing_symm_eq : (@toBoolRing α).symm = ofBoolRing :=
  rfl

@[simp]
/-
**ofBoolRing_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing :=
  rfl

@[simp]
/-
**toBoolRing_ofBoolRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_ofBoolRing (a : AsBoolRing α) : toBoolRing (ofBoolRing a) = a
参数：a : AsBoolRing α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolRing_ofBoolRing (a : AsBoolRing α) : toBoolRing (ofBoolRing a) = a :=
  rfl

@[simp]
/-
**ofBoolRing_toBoolRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_toBoolRing (a : α) : ofBoolRing (toBoolRing a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_toBoolRing (a : α) : ofBoolRing (toBoolRing a) = a :=
  rfl
/-
**toBoolRing_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_inj {a b : α} : toBoolRing a = toBoolRing b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toBoolRing_inj {a b : α} : toBoolRing a = toBoolRing b ↔ a = b :=
  Iff.rfl
/-
**ofBoolRing_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_inj {a b : AsBoolRing α} : ofBoolRing a = ofBoolRing b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofBoolRing_inj {a b : AsBoolRing α} : ofBoolRing a = ofBoolRing b ↔ a = b :=
  Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (AsBoolRing α) :=
  ⟨default (α := α)⟩

-- See note [reducible non-instances]
/-- Every generalized Boolean algebra has the structure of a nonunital commutative ring with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
/-
**GeneralizedBooleanAlgebra.toNonUnitalCommRing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GeneralizedBooleanAlgebra.toNonUnitalCommRing [GeneralizedBooleanAlgebra α
] : NonUnitalCommRing α where add
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_assoc`：symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c)
· 使用定理 `inf_symmDiff_distrib_left`：inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ 
b) ∆ (a ⊓ c)
· 使用定理 `inf_symmDiff_distrib_right`：inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a 
⊓ c) ∆ (b ⊓ c)

--- 原说明 ---
Every generalized Boolean algebra has the structure of a nonunital commutative r
ing with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
abbrev GeneralizedBooleanAlgebra.toNonUnitalCommRing [GeneralizedBooleanAlgebra α] :
    NonUnitalCommRing α where
  add := (· ∆ ·)
  add_assoc := symmDiff_assoc
  zero := ⊥
  zero_add := bot_symmDiff
  add_zero := symmDiff_bot
  zero_mul := bot_inf_eq
  mul_zero := inf_bot_eq
  neg := id
  neg_add_cancel := symmDiff_self
  add_comm := symmDiff_comm
  mul := (· ⊓ ·)
  mul_assoc := inf_assoc
  mul_comm := inf_comm
  left_distrib := inf_symmDiff_distrib_left
  right_distrib := inf_symmDiff_distrib_right
  nsmul := letI : Zero α := ⟨⊥⟩; letI : Add α := ⟨(· ∆ ·)⟩; nsmulRec
  zsmul := letI : Zero α := ⟨⊥⟩; letI : Add α := ⟨(· ∆ ·)⟩; letI : Neg α := ⟨id⟩; zsmulRec
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GeneralizedBooleanAlgebra α] : NonUnitalCommRing (AsBoolRing α) :=
  @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

-- See note [reducible non-instances]
/-- Every Boolean algebra has the structure of a Boolean ring with the following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
/-
**BooleanAlgebra.toBooleanRing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：BooleanAlgebra.toBooleanRing : BooleanRing α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Boolean algebra has the structure of a Boolean ring with the following dat
a:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
abbrev BooleanAlgebra.toBooleanRing : BooleanRing α where
  __ := GeneralizedBooleanAlgebra.toNonUnitalCommRing
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  isIdempotentElem := inf_idem

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanRing (AsBoolRing α) :=
  fast_instance% @BooleanAlgebra.toBooleanRing α _

@[simp]
/-
**ofBoolRing_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_zero : ofBoolRing (0 : AsBoolRing α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_zero : ofBoolRing (0 : AsBoolRing α) = ⊥ :=
  rfl

@[simp]
/-
**ofBoolRing_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_one : ofBoolRing (1 : AsBoolRing α) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_one : ofBoolRing (1 : AsBoolRing α) = ⊤ :=
  rfl

@[simp]
/-
**ofBoolRing_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_neg (a : AsBoolRing α) : ofBoolRing (-a) = ofBoolRing a
参数：a : AsBoolRing α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_neg (a : AsBoolRing α) : ofBoolRing (-a) = ofBoolRing a :=
  rfl

@[simp]
/-
**ofBoolRing_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ 
ofBoolRing b
参数：a b : AsBoolRing α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

@[simp]
/-
**ofBoolRing_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ 
ofBoolRing b
参数：a b : AsBoolRing α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

@[simp]
/-
**ofBoolRing_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_mul (a b : AsBoolRing α) : ofBoolRing (a * b) = ofBoolRing a ⊓ 
ofBoolRing b
参数：a b : AsBoolRing α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoolRing_mul (a b : AsBoolRing α) : ofBoolRing (a * b) = ofBoolRing a ⊓ ofBoolRing b :=
  rfl

@[simp]
/-
**ofBoolRing_le_ofBoolRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofBoolRing_le_ofBoolRing_iff {a b : AsBoolRing α} : ofBoolRing a <= ofBool
Ring b ↔ a * b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
theorem ofBoolRing_le_ofBoolRing_iff {a b : AsBoolRing α} :
    ofBoolRing a ≤ ofBoolRing b ↔ a * b = a :=
  inf_eq_left.symm

@[simp]
/-
**toBoolRing_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_bot : toBoolRing (⊥ : α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolRing_bot : toBoolRing (⊥ : α) = 0 :=
  rfl

@[simp]
/-
**toBoolRing_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_top : toBoolRing (⊤ : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolRing_top : toBoolRing (⊤ : α) = 1 :=
  rfl

@[simp]
/-
**toBoolRing_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_inf (a b : α) : toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing 
b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolRing_inf (a b : α) : toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing b :=
  rfl

@[simp]
/-
**toBoolRing_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toBoolRing_symmDiff (a b : α) : toBoolRing (a ∆ b) = toBoolRing a + toBool
Ring b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toBoolRing_symmDiff (a b : α) : toBoolRing (a ∆ b) = toBoolRing a + toBoolRing b :=
  rfl

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps]
/-
**BoundedLatticeHom.asBoolRing** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : BooleanAlgebra α] → [inst_
1 : BooleanAlgebra β] → BoundedLatticeHom α β → AsBoolRing α →+* AsBoolRing β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring
 homomorphism
from `α` to `β` considered as Boolean rings.
-/
protected def BoundedLatticeHom.asBoolRing (f : BoundedLatticeHom α β) :
    AsBoolRing α →+* AsBoolRing β where
  toFun := toBoolRing ∘ f ∘ ofBoolRing
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symmDiff' f
  map_mul' := f.map_inf'

@[simp]
/-
**BoundedLatticeHom.asBoolRing_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BoundedLatticeHom.asBoolRing_id : (BoundedLatticeHom.id α).asBoolRing = Ri
ngHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BoundedLatticeHom.asBoolRing_id : (BoundedLatticeHom.id α).asBoolRing = RingHom.id _ :=
  rfl

@[simp]
/-
**BoundedLatticeHom.asBoolRing_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BoundedLatticeHom.asBoolRing_comp (g : BoundedLatticeHom β γ) (f : Bounded
LatticeHom α β) : (g.comp f).asBoolRing = g.asBoolRing.comp f.asBoolRing
参数：g : BoundedLatticeHom β γ；f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BoundedLatticeHom.asBoolRing_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).asBoolRing = g.asBoolRing.comp f.asBoolRing :=
  rfl

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps!]
/-
**OrderIso.asBoolAlgAsBoolRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.asBoolAlgAsBoolRing (α : Type*) [BooleanAlgebra α] : AsBoolAlg (A
sBoolRing α) ≃o α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Order isomorphism between `α` considered as a Boolean ring considered as a Boole
an algebra and
`α`.
-/
def OrderIso.asBoolAlgAsBoolRing (α : Type*) [BooleanAlgebra α] : AsBoolAlg (AsBoolRing α) ≃o α :=
  ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps!]
/-
**RingEquiv.asBoolRingAsBoolAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.asBoolRingAsBoolAlg (α : Type*) [BooleanRing α] : AsBoolRing (As
BoolAlg α) ≃+* α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `ofBoolAlg_symmDiff`：ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (
a ∆ b) = ofBoolAlg a + ofBoolAlg b

--- 原说明 ---
Ring isomorphism between `α` considered as a Boolean algebra considered as a Boo
lean ring and
`α`.
-/
def RingEquiv.asBoolRingAsBoolAlg (α : Type*) [BooleanRing α] : AsBoolRing (AsBoolAlg α) ≃+* α :=
  { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }

open Bool
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero Bool where zero := false
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One Bool where one := true
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add Bool where add := xor
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg Bool where neg := id
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub Bool where sub := xor
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul Bool where mul := and
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanRing Bool where
  add_assoc := xor_assoc
  zero_add := Bool.false_xor
  add_zero := Bool.xor_false
  neg_add_cancel := Bool.xor_self
  add_comm := xor_comm
  mul_assoc := and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := and_xor_distrib_left
  right_distrib := and_xor_distrib_right
  isIdempotentElem := Bool.and_self
  zero_mul _ := rfl
  mul_zero a := by cases a <;> rfl
  nsmul := nsmulRec
  zsmul := zsmulRec
/-
**Bool.zero_eq_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.zero_eq_false : 0 = false
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.zero_eq_false : 0 = false := rfl
/-
**Bool.one_eq_true** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.one_eq_true : 1 = true
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.one_eq_true : 1 = true := rfl
/-
**Bool.add_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.add_eq_xor (b c : Bool) : b + c = (b ^^ c)
参数：b c : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.add_eq_xor (b c : Bool) : b + c = (b ^^ c) := rfl
/-
**Bool.neg_eq_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.neg_eq_id (b : Bool) : -b = b
参数：b : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.neg_eq_id (b : Bool) : -b = b := rfl
/-
**Bool.sub_eq_xor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.sub_eq_xor (b c : Bool) : b - c = (b ^^ c)
参数：b c : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.sub_eq_xor (b c : Bool) : b - c = (b ^^ c) := rfl
/-
**Bool.mul_eq_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.mul_eq_and (b c : Bool) : b * c = (b && c)
参数：b c : Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.mul_eq_and (b c : Bool) : b * c = (b && c) := rfl
