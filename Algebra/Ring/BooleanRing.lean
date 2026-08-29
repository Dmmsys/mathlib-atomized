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

/--
Definition of `BooleanRing` / `BooleanRing` 的定义

English:
class BooleanRing
  parameters: (α)
  extends: Ring α
  axioms and operations (1):
    - isIdempotentElem((a : α)) : IsIdempotentElem a

中文:
类 BooleanRing
  参数: (α)
  继承: Ring α
  公理与运算 (1 个):
    - isIdempotentElem((a : α)) : IsIdempotentElem a
-/
class BooleanRing (α) extends Ring α where
  /-- Multiplication in a Boolean ring is idempotent. -/
  isIdempotentElem (a : α) : IsIdempotentElem a

namespace BooleanRing

variable [BooleanRing α] (a b : α)

@[scoped simp]
/--
lemma `mul_self` / 引理 `mul_self`

English:
lemma mul_self
  statement: a * a = a
  proof: IsIdempotentElem.eq (isIdempotentElem a)

中文:
引理 mul_self
  结论: a * a = a
  证明: IsIdempotentElem.eq (isIdempotentElem a)

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.eq, isIdempotentElem
-/
lemma mul_self : a * a = a := IsIdempotentElem.eq (isIdempotentElem a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.IdempotentOp (α := α) (· * ·)
  body: ⟨BooleanRing.mul_self⟩

@[scoped simp]

中文:
实例 :
  签名: Std.IdempotentOp (α := α) (· * ·)
  定义体: ⟨BooleanRing.mul_self⟩

@[scoped simp]
-/
instance : Std.IdempotentOp (α := α) (· * ·) :=
  ⟨BooleanRing.mul_self⟩

@[scoped simp]
/--
theorem `add_self` / 定理 `add_self`

English:
theorem add_self
  statement: a + a = 0
  proof: by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [right_eq_add] at this

@[scoped simp]

中文:
定理 add_self
  结论: a + a = 0
  证明: by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [right_eq_add] at this

@[scoped simp]

Depends on / 依赖: add_mul, mul_add, mul_self, right_eq_add
-/
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [mul_self]
  rwa [right_eq_add] at this

@[scoped simp]
/--
theorem `neg_eq` / 定理 `neg_eq`

English:
theorem neg_eq
  statement: -a = a
  proof: calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self, zero_add]

中文:
定理 neg_eq
  结论: -a = a
  证明: calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self, zero_add]

Depends on / 依赖: add_assoc, add_self, add_zero, neg_add_cancel, zero_add
-/
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by rw [← neg_add_cancel, add_assoc]
    _ = a := by rw [add_self, zero_add]

/--
theorem `add_eq_zero'` / 定理 `add_eq_zero'`

English:
theorem add_eq_zero'
  statement: a + b = 0 ↔ a = b
  proof: calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]

@[simp]

中文:
定理 add_eq_zero'
  结论: a + b = 0 ↔ a = b
  证明: calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]

@[simp]

Depends on / 依赖: add_eq_zero_iff_eq_neg, neg_eq
-/
theorem add_eq_zero' : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by rw [neg_eq]

@[simp]
/--
theorem `mul_add_mul` / 定理 `mul_add_mul`

English:
theorem mul_add_mul
  statement: a * b + b * a = 0
  proof: by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [

中文:
定理 mul_add_mul
  结论: a * b + b * a = 0
  证明: by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [

Depends on / 依赖: add_mul, left_eq_add, mul_add, mul_self
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
/--
theorem `sub_eq_add` / 定理 `sub_eq_add`

English:
theorem sub_eq_add
  statement: a - b = a + b
  proof: by rw [sub_eq_add_neg, add_right_inj, neg_eq]

@[simp]

中文:
定理 sub_eq_add
  结论: a - b = a + b
  证明: by rw [sub_eq_add_neg, add_right_inj, neg_eq]

@[simp]

Depends on / 依赖: add_right_inj, neg_eq, sub_eq_add_neg
-/
theorem sub_eq_add : a - b = a + b := by rw [sub_eq_add_neg, add_right_inj, neg_eq]

@[simp]
/--
theorem `mul_one_add_self` / 定理 `mul_one_add_self`

English:
theorem mul_one_add_self
  statement: a * (1 + a) = 0
  proof: by rw [mul_add, mul_one, mul_self, add_self]

中文:
定理 mul_one_add_self
  结论: a * (1 + a) = 0
  证明: by rw [mul_add, mul_one, mul_self, add_self]

Depends on / 依赖: add_self, mul_add, mul_one, mul_self
-/
theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, mul_self, add_self]

-- Note [lower instance priority]
instance (priority := 100) toCommRing : CommRing α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by rw [← add_eq_zero', mul_add_mul] }

end BooleanRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BooleanRing PUnit
  body: ⟨fun _ => Subsingleton.elim _ _⟩

中文:
实例 :
  签名: 布尔eanRing PUnit
  定义体: ⟨fun _ => Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elim _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/--
Definition of `AsBoolAlg` / `AsBoolAlg` 的定义

English:
definition AsBoolAlg
  signature: (α : Type*)
  body: α

中文:
定义 AsBoolAlg
  签名: (α : 类型)
  定义体: α
-/
def AsBoolAlg (α : Type*) :=
  α

/--
Definition of `toBoolAlg` / `toBoolAlg` 的定义

English:
definition toBoolAlg
  signature: : α ≃ AsBoolAlg α
  body: Equiv.refl _

中文:
定义 toBoolAlg
  签名: : α ≃ As布尔Alg α
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toBoolAlg : α ≃ AsBoolAlg α :=
  Equiv.refl _

/--
Definition of `ofBoolAlg` / `ofBoolAlg` 的定义

English:
definition ofBoolAlg
  signature: : AsBoolAlg α ≃ α
  body: Equiv.refl _

@[simp]

中文:
定义 ofBoolAlg
  签名: : As布尔Alg α ≃ α
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofBoolAlg : AsBoolAlg α ≃ α :=
  Equiv.refl _

@[simp]
/--
theorem `toBoolAlg_symm_eq` / 定理 `toBoolAlg_symm_eq`

English:
theorem toBoolAlg_symm_eq
  statement: (@toBoolAlg α).symm = ofBoolAlg
  proof: rfl

@[simp]

中文:
定理 toBoolAlg_symm_eq
  结论: (@to布尔Alg α).symm = of布尔Alg
  证明: rfl

@[simp]
-/
theorem toBoolAlg_symm_eq : (@toBoolAlg α).symm = ofBoolAlg :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_symm_eq` / 定理 `ofBoolAlg_symm_eq`

English:
theorem ofBoolAlg_symm_eq
  statement: (@ofBoolAlg α).symm = toBoolAlg
  proof: rfl

@[simp]

中文:
定理 ofBoolAlg_symm_eq
  结论: (@of布尔Alg α).symm = to布尔Alg
  证明: rfl

@[simp]
-/
theorem ofBoolAlg_symm_eq : (@ofBoolAlg α).symm = toBoolAlg :=
  rfl

@[simp]
/--
theorem `toBoolAlg_ofBoolAlg` / 定理 `toBoolAlg_ofBoolAlg`

English:
theorem toBoolAlg_ofBoolAlg
  given: (a : AsBoolAlg α)
  statement: toBoolAlg (ofBoolAlg a) = a
  proof: rfl

@[simp]

中文:
定理 toBoolAlg_ofBoolAlg
  条件: (a : As布尔Alg α)
  结论: to布尔Alg (of布尔Alg a) = a
  证明: rfl

@[simp]
-/
theorem toBoolAlg_ofBoolAlg (a : AsBoolAlg α) : toBoolAlg (ofBoolAlg a) = a :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_toBoolAlg` / 定理 `ofBoolAlg_toBoolAlg`

English:
theorem ofBoolAlg_toBoolAlg
  given: (a : α)
  statement: ofBoolAlg (toBoolAlg a) = a
  proof: rfl

中文:
定理 ofBoolAlg_toBoolAlg
  条件: (a : α)
  结论: of布尔Alg (to布尔Alg a) = a
  证明: rfl
-/
theorem ofBoolAlg_toBoolAlg (a : α) : ofBoolAlg (toBoolAlg a) = a :=
  rfl

/--
theorem `toBoolAlg_inj` / 定理 `toBoolAlg_inj`

English:
theorem toBoolAlg_inj
  given: {a b : α}
  statement: toBoolAlg a = toBoolAlg b ↔ a = b
  proof: Iff.rfl

中文:
定理 toBoolAlg_inj
  条件: {a b : α}
  结论: to布尔Alg a = to布尔Alg b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toBoolAlg_inj {a b : α} : toBoolAlg a = toBoolAlg b ↔ a = b :=
  Iff.rfl

/--
theorem `ofBoolAlg_inj` / 定理 `ofBoolAlg_inj`

English:
theorem ofBoolAlg_inj
  given: {a b : AsBoolAlg α}
  statement: ofBoolAlg a = ofBoolAlg b ↔ a = b
  proof: Iff.rfl

中文:
定理 ofBoolAlg_inj
  条件: {a b : As布尔Alg α}
  结论: of布尔Alg a = of布尔Alg b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ofBoolAlg_inj {a b : AsBoolAlg α} : ofBoolAlg a = ofBoolAlg b ↔ a = b :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (AsBoolAlg α)
  body: ‹Inhabited α›

中文:
实例 [Inhabited
  签名: α] : Inhabited (As布尔Alg α)
  定义体: ‹Inhabited α›

Depends on / 依赖: Inhabited
-/
instance [Inhabited α] : Inhabited (AsBoolAlg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
@[instance_reducible]
/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: : Max α
  body: ⟨fun x y => x + y + x * y⟩

中文:
定义 sup
  签名: : Max α
  定义体: ⟨fun x y => x + y + x * y⟩
-/
def sup : Max α :=
  ⟨fun x y => x + y + x * y⟩

/-- The meet operation in a Boolean ring is `x * y`. -/
@[instance_reducible]
/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: : Min α
  body: ⟨(· * ·)⟩

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup
scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf

中文:
定义 inf
  签名: : Min α
  定义体: ⟨(· * ·)⟩

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup
scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf
-/
def inf : Min α :=
  ⟨(· * ·)⟩

scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.sup
scoped[BooleanAlgebraOfBooleanRing] attribute [instance 100] BooleanRing.inf
open BooleanAlgebraOfBooleanRing

/--
theorem `sup_comm` / 定理 `sup_comm`

English:
theorem sup_comm
  given: (a b : α)
  statement: a ⊔ b = b ⊔ a
  proof: by
  dsimp only [(· ⊔ ·)]
  ring

中文:
定理 sup_comm
  条件: (a b : α)
  结论: a ⊔ b = b ⊔ a
  证明: by
  dsimp only [(· ⊔ ·)]
  ring
-/
theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  dsimp only [(· ⊔ ·)]
  ring

/--
theorem `inf_comm` / 定理 `inf_comm`

English:
theorem inf_comm
  given: (a b : α)
  statement: a ⊓ b = b ⊓ a
  proof: by
  dsimp only [(· ⊓ ·)]
  ring

中文:
定理 inf_comm
  条件: (a b : α)
  结论: a ⊓ b = b ⊓ a
  证明: by
  dsimp only [(· ⊓ ·)]
  ring
-/
theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  dsimp only [(· ⊓ ·)]
  ring

/--
theorem `sup_assoc` / 定理 `sup_assoc`

English:
theorem sup_assoc
  given: (a b c : α)
  statement: a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
  proof: by
  dsimp only [(· ⊔ ·)]
  ring

中文:
定理 sup_assoc
  条件: (a b c : α)
  结论: a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
  证明: by
  dsimp only [(· ⊔ ·)]
  ring
-/
theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  dsimp only [(· ⊔ ·)]
  ring

/--
theorem `inf_assoc` / 定理 `inf_assoc`

English:
theorem inf_assoc
  given: (a b c : α)
  statement: a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
  proof: by
  dsimp only [(· ⊓ ·)]
  ring

中文:
定理 inf_assoc
  条件: (a b c : α)
  结论: a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
  证明: by
  dsimp only [(· ⊓ ·)]
  ring
-/
theorem inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  dsimp only [(· ⊓ ·)]
  ring

/--
theorem `sup_inf_self` / 定理 `sup_inf_self`

English:
theorem sup_inf_self
  given: (a b : α)
  statement: a ⊔ a ⊓ b = a
  proof: by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [← mul_assoc]; rw [mul_self]; rw [add_assoc]; rw [add_self]; rw [add_zero]

中文:
定理 sup_inf_self
  条件: (a b : α)
  结论: a ⊔ a ⊓ b = a
  证明: by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [← mul_assoc]; rw [mul_self]; rw [add_assoc]; rw [add_self]; rw [add_zero]

Depends on / 依赖: add_assoc, add_self, add_zero, mul_assoc, mul_self
-/
theorem sup_inf_self (a b : α) : a ⊔ a ⊓ b = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [← mul_assoc]; rw [mul_self]; rw [add_assoc]; rw [add_self]; rw [add_zero]

/--
theorem `inf_sup_self` / 定理 `inf_sup_self`

English:
theorem inf_sup_self
  given: (a b : α)
  statement: a ⊓ (a ⊔ b) = a
  proof: by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add]; rw [mul_add]; rw [mul_self]; rw [← mul_assoc]; rw [mul_self]; rw [add_assoc]; rw [add_self]; rw [add_zero]

中文:
定理 inf_sup_self
  条件: (a b : α)
  结论: a ⊓ (a ⊔ b) = a
  证明: by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add]; rw [mul_add]; rw [mul_self]; rw [← mul_assoc]; rw [mul_self]; rw [add_assoc]; rw [add_self]; rw [add_zero]

Depends on / 依赖: add_assoc, add_self, add_zero, mul_add, mul_assoc, mul_self
-/
theorem inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [mul_add]; rw [mul_add]; rw [mul_self]; rw [← mul_assoc]; rw [mul_self]; rw [add_assoc]; rw [add_self]; rw [add_zero]

/--
theorem `le_sup_inf_aux` / 定理 `le_sup_inf_aux`

English:
theorem le_sup_inf_aux
  given: (a b c : α)
  statement: (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c)
  proof: calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) := by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]

中文:
定理 le_sup_inf_aux
  条件: (a b c : α)
  结论: (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c)
  证明: calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) := by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]

Depends on / 依赖: add_self, add_zero, mul_self
-/
theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) +
          (a * b * c + a * a * b * c) := by ring
    _ = a + b * c + a * (b * c) := by simp only [mul_self, add_self, add_zero]

/--
theorem `le_sup_inf` / 定理 `le_sup_inf`

English:
theorem le_sup_inf
  given: (a b c : α)
  statement: (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c
  proof: by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux]; rw [add_self]; rw [mul_self]; rw [zero_add]

中文:
定理 le_sup_inf
  条件: (a b c : α)
  结论: (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c
  证明: by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux]; rw [add_self]; rw [mul_self]; rw [zero_add]

Depends on / 依赖: add_self, le_sup_inf_aux, mul_self, zero_add
-/
theorem le_sup_inf (a b c : α) : (a ⊔ b) ⊓ (a ⊔ c) ⊔ (a ⊔ b ⊓ c) = a ⊔ b ⊓ c := by
  dsimp only [(· ⊔ ·), (· ⊓ ·)]
  rw [le_sup_inf_aux]; rw [add_self]; rw [mul_self]; rw [zero_add]

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
/--
Definition of `toBooleanAlgebra` / `toBooleanAlgebra` 的定义

English:
definition toBooleanAlgebra
  signature: : BooleanAlgebra α
  body: { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self with
    le_sup_inf := le_sup_inf
    top := 1
    le_top := fun a => show a + 1 + a * 1 = 1 by rw [mul_one, add_comm a 1,
                                                     add_assoc, add_self, add_zero]
    bot := 0
  

中文:
定义 toBooleanAlgebra
  签名: : 布尔eanAlgebra α
  定义体: { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self with
    le_sup_inf := le_sup_inf
    top := 1
    le_top := fun a => show a + 1 + a * 1 = 1 by rw [mul_one, add_comm a 1,
                                                     add_assoc, add_self, add_zero]
    bot := 0
  

Depends on / 依赖: Lattice, Lattice.mk, add_assoc, add_comm, add_self, add_zero, bot_le, inf_assoc, inf_comm, inf_compl_le_bot, inf_sup_self, le_sup_inf, le_top, mul_add, mul_one, mul_self, sup_assoc, sup_comm, sup_inf_self, top_le_sup_compl
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BooleanAlgebra (AsBoolAlg α)
  body: fast_instance% @BooleanRing.toBooleanAlgebra α _

@[simp]

中文:
实例 :
  签名: 布尔eanAlgebra (As布尔Alg α)
  定义体: fast_instance% @BooleanRing.toBooleanAlgebra α _

@[simp]

Depends on / 依赖: BooleanRing, BooleanRing.toBooleanAlgebra, fast_instance, toBooleanAlgebra
-/
instance : BooleanAlgebra (AsBoolAlg α) :=
  fast_instance% @BooleanRing.toBooleanAlgebra α _

@[simp]
/--
theorem `ofBoolAlg_top` / 定理 `ofBoolAlg_top`

English:
theorem ofBoolAlg_top
  statement: ofBoolAlg (⊤ : AsBoolAlg α) = 1
  proof: rfl

@[simp]

中文:
定理 ofBoolAlg_top
  结论: of布尔Alg (⊤ : As布尔Alg α) = 1
  证明: rfl

@[simp]
-/
theorem ofBoolAlg_top : ofBoolAlg (⊤ : AsBoolAlg α) = 1 :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_bot` / 定理 `ofBoolAlg_bot`

English:
theorem ofBoolAlg_bot
  statement: ofBoolAlg (⊥ : AsBoolAlg α) = 0
  proof: rfl

@[simp]

中文:
定理 ofBoolAlg_bot
  结论: of布尔Alg (⊥ : As布尔Alg α) = 0
  证明: rfl

@[simp]
-/
theorem ofBoolAlg_bot : ofBoolAlg (⊥ : AsBoolAlg α) = 0 :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_sup` / 定理 `ofBoolAlg_sup`

English:
theorem ofBoolAlg_sup
  given: (a b : AsBoolAlg α)
  proof: rfl

@[simp]

中文:
定理 ofBoolAlg_sup
  条件: (a b : As布尔Alg α)
  证明: rfl

@[simp]
-/
theorem ofBoolAlg_sup (a b : AsBoolAlg α) :
    ofBoolAlg (a ⊔ b) = ofBoolAlg a + ofBoolAlg b + ofBoolAlg a * ofBoolAlg b :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_inf` / 定理 `ofBoolAlg_inf`

English:
theorem ofBoolAlg_inf
  given: (a b : AsBoolAlg α)
  statement: ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBoolAlg b
  proof: rfl

@[simp]

中文:
定理 ofBoolAlg_inf
  条件: (a b : As布尔Alg α)
  结论: of布尔Alg (a ⊓ b) = of布尔Alg a * of布尔Alg b
  证明: rfl

@[simp]
-/
theorem ofBoolAlg_inf (a b : AsBoolAlg α) : ofBoolAlg (a ⊓ b) = ofBoolAlg a * ofBoolAlg b :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_compl` / 定理 `ofBoolAlg_compl`

English:
theorem ofBoolAlg_compl
  given: (a : AsBoolAlg α)
  statement: ofBoolAlg aᶜ = 1 + ofBoolAlg a
  proof: rfl

@[simp]

中文:
定理 ofBoolAlg_compl
  条件: (a : As布尔Alg α)
  结论: of布尔Alg aᶜ = 1 + of布尔Alg a
  证明: rfl

@[simp]
-/
theorem ofBoolAlg_compl (a : AsBoolAlg α) : ofBoolAlg aᶜ = 1 + ofBoolAlg a :=
  rfl

@[simp]
/--
theorem `ofBoolAlg_sdiff` / 定理 `ofBoolAlg_sdiff`

English:
theorem ofBoolAlg_sdiff
  given: (a b : AsBoolAlg α)
  statement: ofBoolAlg (a \ b) = ofBoolAlg a * (1 + ofBoolAlg b)
  proof: rfl

中文:
定理 ofBoolAlg_sdiff
  条件: (a b : As布尔Alg α)
  结论: of布尔Alg (a \ b) = of布尔Alg a * (1 + of布尔Alg b)
  证明: rfl
-/
theorem ofBoolAlg_sdiff (a b : AsBoolAlg α) : ofBoolAlg (a \ b) = ofBoolAlg a * (1 + ofBoolAlg b) :=
  rfl

/--
theorem `of_boolalg_symmDiff_aux` / 定理 `of_boolalg_symmDiff_aux`

English:
theorem of_boolalg_symmDiff_aux
  given: (a b : α)
  statement: (a + b + a * b) * (1 + a * b) = a + b
  proof: calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]

@[simp]

中文:
定理 of_boolalg_symmDiff_aux
  条件: (a b : α)
  结论: (a + b + a * b) * (1 + a * b) = a + b
  证明: calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]

@[simp]
-/
private theorem of_boolalg_symmDiff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc (a + b + a * b) * (1 + a * b)
    _ = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by ring
    _ = a + b := by simp only [mul_self, add_self, add_zero]

@[simp]
/--
theorem `ofBoolAlg_symmDiff` / 定理 `ofBoolAlg_symmDiff`

English:
theorem ofBoolAlg_symmDiff
  given: (a b : AsBoolAlg α)
  statement: ofBoolAlg (a ∆ b) = ofBoolAlg a + ofBoolAlg b
  proof: by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symmDiff_aux _ _

@[simp]

中文:
定理 ofBoolAlg_symmDiff
  条件: (a b : As布尔Alg α)
  结论: of布尔Alg (a ∆ b) = of布尔Alg a + of布尔Alg b
  证明: by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symmDiff_aux _ _

@[simp]

Depends on / 依赖: of_boolalg_symmDiff_aux, symmDiff_eq_sup_sdiff_inf
-/
theorem ofBoolAlg_symmDiff (a b : AsBoolAlg α) : ofBoolAlg (a ∆ b) = ofBoolAlg a + ofBoolAlg b := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact of_boolalg_symmDiff_aux _ _

@[simp]
/--
theorem `ofBoolAlg_mul_ofBoolAlg_eq_left_iff` / 定理 `ofBoolAlg_mul_ofBoolAlg_eq_left_iff`

English:
theorem ofBoolAlg_mul_ofBoolAlg_eq_left_iff
  given: {a b : AsBoolAlg α}
  proof: @inf_eq_left (AsBoolAlg α) _ _ _

@[simp]

中文:
定理 ofBoolAlg_mul_ofBoolAlg_eq_left_iff
  条件: {a b : As布尔Alg α}
  证明: @inf_eq_left (AsBoolAlg α) _ _ _

@[simp]

Depends on / 依赖: AsBoolAlg, inf_eq_left
-/
theorem ofBoolAlg_mul_ofBoolAlg_eq_left_iff {a b : AsBoolAlg α} :
    ofBoolAlg a * ofBoolAlg b = ofBoolAlg a ↔ a <= b :=
  @inf_eq_left (AsBoolAlg α) _ _ _

@[simp]
/--
theorem `toBoolAlg_zero` / 定理 `toBoolAlg_zero`

English:
theorem toBoolAlg_zero
  statement: toBoolAlg (0 : α) = ⊥
  proof: rfl

@[simp]

中文:
定理 toBoolAlg_zero
  结论: to布尔Alg (0 : α) = ⊥
  证明: rfl

@[simp]
-/
theorem toBoolAlg_zero : toBoolAlg (0 : α) = ⊥ :=
  rfl

@[simp]
/--
theorem `toBoolAlg_one` / 定理 `toBoolAlg_one`

English:
theorem toBoolAlg_one
  statement: toBoolAlg (1 : α) = ⊤
  proof: rfl

@[simp]

中文:
定理 toBoolAlg_one
  结论: to布尔Alg (1 : α) = ⊤
  证明: rfl

@[simp]
-/
theorem toBoolAlg_one : toBoolAlg (1 : α) = ⊤ :=
  rfl

@[simp]
/--
theorem `toBoolAlg_mul` / 定理 `toBoolAlg_mul`

English:
theorem toBoolAlg_mul
  given: (a b : α)
  statement: toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b
  proof: rfl

@[simp]

中文:
定理 toBoolAlg_mul
  条件: (a b : α)
  结论: to布尔Alg (a * b) = to布尔Alg a ⊓ to布尔Alg b
  证明: rfl

@[simp]
-/
theorem toBoolAlg_mul (a b : α) : toBoolAlg (a * b) = toBoolAlg a ⊓ toBoolAlg b :=
  rfl

@[simp]
/--
theorem `toBoolAlg_add_add_mul` / 定理 `toBoolAlg_add_add_mul`

English:
theorem toBoolAlg_add_add_mul
  given: (a b : α)
  statement: toBoolAlg (a + b + a * b) = toBoolAlg a ⊔ toBoolAlg b
  proof: rfl

@[simp]

中文:
定理 toBoolAlg_add_add_mul
  条件: (a b : α)
  结论: to布尔Alg (a + b + a * b) = to布尔Alg a ⊔ to布尔Alg b
  证明: rfl

@[simp]
-/
theorem toBoolAlg_add_add_mul (a b : α) : toBoolAlg (a + b + a * b) = toBoolAlg a ⊔ toBoolAlg b :=
  rfl

@[simp]
/--
theorem `toBoolAlg_add` / 定理 `toBoolAlg_add`

English:
theorem toBoolAlg_add
  given: (a b : α)
  statement: toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b
  proof: (ofBoolAlg_symmDiff a b).symm

中文:
定理 toBoolAlg_add
  条件: (a b : α)
  结论: to布尔Alg (a + b) = to布尔Alg a ∆ to布尔Alg b
  证明: (ofBoolAlg_symmDiff a b).symm

Depends on / 依赖: ofBoolAlg_symmDiff
-/
theorem toBoolAlg_add (a b : α) : toBoolAlg (a + b) = toBoolAlg a ∆ toBoolAlg b :=
  (ofBoolAlg_symmDiff a b).symm

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
/--
Definition of `RingHom.asBoolAlg` / `RingHom.asBoolAlg` 的定义

English:
definition RingHom.asBoolAlg
  signature: (f : α ->+* β)
  body: toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

@[simp]

中文:
定义 RingHom.asBoolAlg
  签名: (f : α ->+* β)
  定义体: toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

@[simp]
-/
protected def RingHom.asBoolAlg (f : α ->+* β) : BoundedLatticeHom (AsBoolAlg α) (AsBoolAlg β) where
  toFun := toBoolAlg ∘ f ∘ ofBoolAlg
  map_sup' a b := by
    dsimp
    simp_rw [map_add f, map_mul f, toBoolAlg_add_add_mul]
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

@[simp]
/--
theorem `RingHom.asBoolAlg_id` / 定理 `RingHom.asBoolAlg_id`

English:
theorem RingHom.asBoolAlg_id
  statement: (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _
  proof: rfl

@[simp]

中文:
定理 RingHom.asBoolAlg_id
  结论: (RingHom.id α).as布尔Alg = BoundedLatticeHom.id _
  证明: rfl

@[simp]
-/
theorem RingHom.asBoolAlg_id : (RingHom.id α).asBoolAlg = BoundedLatticeHom.id _ :=
  rfl

@[simp]
/--
theorem `RingHom.asBoolAlg_comp` / 定理 `RingHom.asBoolAlg_comp`

English:
theorem RingHom.asBoolAlg_comp
  given: (g : β ->+* γ) (f : α ->+* β)
  proof: rfl

中文:
定理 RingHom.asBoolAlg_comp
  条件: (g : β ->+* γ) (f : α ->+* β)
  证明: rfl
-/
theorem RingHom.asBoolAlg_comp (g : β ->+* γ) (f : α ->+* β) :
    (g.comp f).asBoolAlg = g.asBoolAlg.comp f.asBoolAlg :=
  rfl

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/--
Definition of `AsBoolRing` / `AsBoolRing` 的定义

English:
definition AsBoolRing
  signature: (α : Type*)
  body: α

中文:
定义 AsBoolRing
  签名: (α : 类型)
  定义体: α
-/
def AsBoolRing (α : Type*) :=
  α

/--
Definition of `toBoolRing` / `toBoolRing` 的定义

English:
definition toBoolRing
  signature: : α ≃ AsBoolRing α
  body: Equiv.refl _

中文:
定义 toBoolRing
  签名: : α ≃ As布尔Ring α
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toBoolRing : α ≃ AsBoolRing α :=
  Equiv.refl _

/--
Definition of `ofBoolRing` / `ofBoolRing` 的定义

English:
definition ofBoolRing
  signature: : AsBoolRing α ≃ α
  body: Equiv.refl _

@[simp]

中文:
定义 ofBoolRing
  签名: : As布尔Ring α ≃ α
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofBoolRing : AsBoolRing α ≃ α :=
  Equiv.refl _

@[simp]
/--
theorem `toBoolRing_symm_eq` / 定理 `toBoolRing_symm_eq`

English:
theorem toBoolRing_symm_eq
  statement: (@toBoolRing α).symm = ofBoolRing
  proof: rfl

@[simp]

中文:
定理 toBoolRing_symm_eq
  结论: (@to布尔Ring α).symm = of布尔Ring
  证明: rfl

@[simp]
-/
theorem toBoolRing_symm_eq : (@toBoolRing α).symm = ofBoolRing :=
  rfl

@[simp]
/--
theorem `ofBoolRing_symm_eq` / 定理 `ofBoolRing_symm_eq`

English:
theorem ofBoolRing_symm_eq
  statement: (@ofBoolRing α).symm = toBoolRing
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_symm_eq
  结论: (@of布尔Ring α).symm = to布尔Ring
  证明: rfl

@[simp]
-/
theorem ofBoolRing_symm_eq : (@ofBoolRing α).symm = toBoolRing :=
  rfl

@[simp]
/--
theorem `toBoolRing_ofBoolRing` / 定理 `toBoolRing_ofBoolRing`

English:
theorem toBoolRing_ofBoolRing
  given: (a : AsBoolRing α)
  statement: toBoolRing (ofBoolRing a) = a
  proof: rfl

@[simp]

中文:
定理 toBoolRing_ofBoolRing
  条件: (a : As布尔Ring α)
  结论: to布尔Ring (of布尔Ring a) = a
  证明: rfl

@[simp]
-/
theorem toBoolRing_ofBoolRing (a : AsBoolRing α) : toBoolRing (ofBoolRing a) = a :=
  rfl

@[simp]
/--
theorem `ofBoolRing_toBoolRing` / 定理 `ofBoolRing_toBoolRing`

English:
theorem ofBoolRing_toBoolRing
  given: (a : α)
  statement: ofBoolRing (toBoolRing a) = a
  proof: rfl

中文:
定理 ofBoolRing_toBoolRing
  条件: (a : α)
  结论: of布尔Ring (to布尔Ring a) = a
  证明: rfl
-/
theorem ofBoolRing_toBoolRing (a : α) : ofBoolRing (toBoolRing a) = a :=
  rfl

/--
theorem `toBoolRing_inj` / 定理 `toBoolRing_inj`

English:
theorem toBoolRing_inj
  given: {a b : α}
  statement: toBoolRing a = toBoolRing b ↔ a = b
  proof: Iff.rfl

中文:
定理 toBoolRing_inj
  条件: {a b : α}
  结论: to布尔Ring a = to布尔Ring b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toBoolRing_inj {a b : α} : toBoolRing a = toBoolRing b ↔ a = b :=
  Iff.rfl

/--
theorem `ofBoolRing_inj` / 定理 `ofBoolRing_inj`

English:
theorem ofBoolRing_inj
  given: {a b : AsBoolRing α}
  statement: ofBoolRing a = ofBoolRing b ↔ a = b
  proof: Iff.rfl

中文:
定理 ofBoolRing_inj
  条件: {a b : As布尔Ring α}
  结论: of布尔Ring a = of布尔Ring b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ofBoolRing_inj {a b : AsBoolRing α} : ofBoolRing a = ofBoolRing b ↔ a = b :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (AsBoolRing α)
  body: ⟨default (α := α)⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (As布尔Ring α)
  定义体: ⟨default (α := α)⟩
-/
instance [Inhabited α] : Inhabited (AsBoolRing α) :=
  ⟨default (α := α)⟩

-- See note [reducible non-instances]
/--
Definition of `GeneralizedBooleanAlgebra.toNonUnitalCommRing` / `GeneralizedBooleanAlgebra.toNonUnitalCommRing` 的定义

English:
abbreviation GeneralizedBooleanAlgebra.toNonUnitalCommRing
  signature: [GeneralizedBooleanAlgebra α]
  body: (· ∆ ·)
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
  left_

中文:
缩写 GeneralizedBooleanAlgebra.toNonUnitalCommRing
  签名: [Generalized布尔eanAlgebra α]
  定义体: (· ∆ ·)
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
  left_
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeneralizedBooleanAlgebra
  signature: α] : NonUnitalCommRing (AsBoolRing α)
  body: @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

中文:
实例 [GeneralizedBooleanAlgebra
  签名: α] : NonUnitalCommRing (As布尔Ring α)
  定义体: @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.toNonUnitalCommRing, toNonUnitalCommRing
-/
instance [GeneralizedBooleanAlgebra α] : NonUnitalCommRing (AsBoolRing α) :=
  @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

-- See note [reducible non-instances]
/--
Definition of `BooleanAlgebra.toBooleanRing` / `BooleanAlgebra.toBooleanRing` 的定义

English:
abbreviation BooleanAlgebra.toBooleanRing
  signature: : BooleanRing α where
  body: GeneralizedBooleanAlgebra.toNonUnitalCommRing
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  isIdempotentElem := inf_idem

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

中文:
缩写 BooleanAlgebra.toBooleanRing
  签名: : 布尔eanRing α where
  定义体: GeneralizedBooleanAlgebra.toNonUnitalCommRing
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  isIdempotentElem := inf_idem

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

Depends on / 依赖: GeneralizedBooleanAlgebra, GeneralizedBooleanAlgebra.toNonUnitalCommRing, toNonUnitalCommRing
-/
abbrev BooleanAlgebra.toBooleanRing : BooleanRing α where
  __ := GeneralizedBooleanAlgebra.toNonUnitalCommRing
  one := ⊤
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  isIdempotentElem := inf_idem

scoped[BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BooleanRing (AsBoolRing α)
  body: fast_instance% @BooleanAlgebra.toBooleanRing α _

@[simp]

中文:
实例 :
  签名: 布尔eanRing (As布尔Ring α)
  定义体: fast_instance% @BooleanAlgebra.toBooleanRing α _

@[simp]

Depends on / 依赖: BooleanAlgebra, BooleanAlgebra.toBooleanRing, fast_instance, toBooleanRing
-/
instance : BooleanRing (AsBoolRing α) :=
  fast_instance% @BooleanAlgebra.toBooleanRing α _

@[simp]
/--
theorem `ofBoolRing_zero` / 定理 `ofBoolRing_zero`

English:
theorem ofBoolRing_zero
  statement: ofBoolRing (0 : AsBoolRing α) = ⊥
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_zero
  结论: of布尔Ring (0 : As布尔Ring α) = ⊥
  证明: rfl

@[simp]
-/
theorem ofBoolRing_zero : ofBoolRing (0 : AsBoolRing α) = ⊥ :=
  rfl

@[simp]
/--
theorem `ofBoolRing_one` / 定理 `ofBoolRing_one`

English:
theorem ofBoolRing_one
  statement: ofBoolRing (1 : AsBoolRing α) = ⊤
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_one
  结论: of布尔Ring (1 : As布尔Ring α) = ⊤
  证明: rfl

@[simp]
-/
theorem ofBoolRing_one : ofBoolRing (1 : AsBoolRing α) = ⊤ :=
  rfl

@[simp]
/--
theorem `ofBoolRing_neg` / 定理 `ofBoolRing_neg`

English:
theorem ofBoolRing_neg
  given: (a : AsBoolRing α)
  statement: ofBoolRing (-a) = ofBoolRing a
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_neg
  条件: (a : As布尔Ring α)
  结论: of布尔Ring (-a) = of布尔Ring a
  证明: rfl

@[simp]
-/
theorem ofBoolRing_neg (a : AsBoolRing α) : ofBoolRing (-a) = ofBoolRing a :=
  rfl

@[simp]
/--
theorem `ofBoolRing_add` / 定理 `ofBoolRing_add`

English:
theorem ofBoolRing_add
  given: (a b : AsBoolRing α)
  statement: ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_add
  条件: (a b : As布尔Ring α)
  结论: of布尔Ring (a + b) = of布尔Ring a ∆ of布尔Ring b
  证明: rfl

@[simp]
-/
theorem ofBoolRing_add (a b : AsBoolRing α) : ofBoolRing (a + b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

@[simp]
/--
theorem `ofBoolRing_sub` / 定理 `ofBoolRing_sub`

English:
theorem ofBoolRing_sub
  given: (a b : AsBoolRing α)
  statement: ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_sub
  条件: (a b : As布尔Ring α)
  结论: of布尔Ring (a - b) = of布尔Ring a ∆ of布尔Ring b
  证明: rfl

@[simp]
-/
theorem ofBoolRing_sub (a b : AsBoolRing α) : ofBoolRing (a - b) = ofBoolRing a ∆ ofBoolRing b :=
  rfl

@[simp]
/--
theorem `ofBoolRing_mul` / 定理 `ofBoolRing_mul`

English:
theorem ofBoolRing_mul
  given: (a b : AsBoolRing α)
  statement: ofBoolRing (a * b) = ofBoolRing a ⊓ ofBoolRing b
  proof: rfl

@[simp]

中文:
定理 ofBoolRing_mul
  条件: (a b : As布尔Ring α)
  结论: of布尔Ring (a * b) = of布尔Ring a ⊓ of布尔Ring b
  证明: rfl

@[simp]
-/
theorem ofBoolRing_mul (a b : AsBoolRing α) : ofBoolRing (a * b) = ofBoolRing a ⊓ ofBoolRing b :=
  rfl

@[simp]
/--
theorem `ofBoolRing_le_ofBoolRing_iff` / 定理 `ofBoolRing_le_ofBoolRing_iff`

English:
theorem ofBoolRing_le_ofBoolRing_iff
  given: {a b : AsBoolRing α}
  proof: inf_eq_left.symm

@[simp]

中文:
定理 ofBoolRing_le_ofBoolRing_iff
  条件: {a b : As布尔Ring α}
  证明: inf_eq_left.symm

@[simp]

Depends on / 依赖: inf_eq_left, inf_eq_left.symm
-/
theorem ofBoolRing_le_ofBoolRing_iff {a b : AsBoolRing α} :
    ofBoolRing a <= ofBoolRing b ↔ a * b = a :=
  inf_eq_left.symm

@[simp]
/--
theorem `toBoolRing_bot` / 定理 `toBoolRing_bot`

English:
theorem toBoolRing_bot
  statement: toBoolRing (⊥ : α) = 0
  proof: rfl

@[simp]

中文:
定理 toBoolRing_bot
  结论: to布尔Ring (⊥ : α) = 0
  证明: rfl

@[simp]
-/
theorem toBoolRing_bot : toBoolRing (⊥ : α) = 0 :=
  rfl

@[simp]
/--
theorem `toBoolRing_top` / 定理 `toBoolRing_top`

English:
theorem toBoolRing_top
  statement: toBoolRing (⊤ : α) = 1
  proof: rfl

@[simp]

中文:
定理 toBoolRing_top
  结论: to布尔Ring (⊤ : α) = 1
  证明: rfl

@[simp]
-/
theorem toBoolRing_top : toBoolRing (⊤ : α) = 1 :=
  rfl

@[simp]
/--
theorem `toBoolRing_inf` / 定理 `toBoolRing_inf`

English:
theorem toBoolRing_inf
  given: (a b : α)
  statement: toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing b
  proof: rfl

@[simp]

中文:
定理 toBoolRing_inf
  条件: (a b : α)
  结论: to布尔Ring (a ⊓ b) = to布尔Ring a * to布尔Ring b
  证明: rfl

@[simp]
-/
theorem toBoolRing_inf (a b : α) : toBoolRing (a ⊓ b) = toBoolRing a * toBoolRing b :=
  rfl

@[simp]
/--
theorem `toBoolRing_symmDiff` / 定理 `toBoolRing_symmDiff`

English:
theorem toBoolRing_symmDiff
  given: (a b : α)
  statement: toBoolRing (a ∆ b) = toBoolRing a + toBoolRing b
  proof: rfl

中文:
定理 toBoolRing_symmDiff
  条件: (a b : α)
  结论: to布尔Ring (a ∆ b) = to布尔Ring a + to布尔Ring b
  证明: rfl
-/
theorem toBoolRing_symmDiff (a b : α) : toBoolRing (a ∆ b) = toBoolRing a + toBoolRing b :=
  rfl

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps]
/--
Definition of `BoundedLatticeHom.asBoolRing` / `BoundedLatticeHom.asBoolRing` 的定义

English:
definition BoundedLatticeHom.asBoolRing
  signature: (f : BoundedLatticeHom α β)
  body: toBoolRing ∘ f ∘ ofBoolRing
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symmDiff' f
  map_mul' := f.map_inf'

@[simp]

中文:
定义 BoundedLatticeHom.asBoolRing
  签名: (f : BoundedLatticeHom α β)
  定义体: toBoolRing ∘ f ∘ ofBoolRing
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symmDiff' f
  map_mul' := f.map_inf'

@[simp]
-/
protected def BoundedLatticeHom.asBoolRing (f : BoundedLatticeHom α β) :
    AsBoolRing α ->+* AsBoolRing β where
  toFun := toBoolRing ∘ f ∘ ofBoolRing
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symmDiff' f
  map_mul' := f.map_inf'

@[simp]
/--
theorem `BoundedLatticeHom.asBoolRing_id` / 定理 `BoundedLatticeHom.asBoolRing_id`

English:
theorem BoundedLatticeHom.asBoolRing_id
  statement: (BoundedLatticeHom.id α).asBoolRing = RingHom.id _
  proof: rfl

@[simp]

中文:
定理 BoundedLatticeHom.asBoolRing_id
  结论: (BoundedLatticeHom.id α).as布尔Ring = RingHom.id _
  证明: rfl

@[simp]
-/
theorem BoundedLatticeHom.asBoolRing_id : (BoundedLatticeHom.id α).asBoolRing = RingHom.id _ :=
  rfl

@[simp]
/--
theorem `BoundedLatticeHom.asBoolRing_comp` / 定理 `BoundedLatticeHom.asBoolRing_comp`

English:
theorem BoundedLatticeHom.asBoolRing_comp
  given: (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β)
  proof: rfl

中文:
定理 BoundedLatticeHom.asBoolRing_comp
  条件: (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β)
  证明: rfl
-/
theorem BoundedLatticeHom.asBoolRing_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).asBoolRing = g.asBoolRing.comp f.asBoolRing :=
  rfl

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps!]
/--
Definition of `OrderIso.asBoolAlgAsBoolRing` / `OrderIso.asBoolAlgAsBoolRing` 的定义

English:
definition OrderIso.asBoolAlgAsBoolRing
  signature: (α : Type*) [BooleanAlgebra α]
  body: ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩

中文:
定义 OrderIso.asBoolAlgAsBoolRing
  签名: (α : 类型) [布尔eanAlgebra α]
  定义体: ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩

Depends on / 依赖: ofBoolAlg, ofBoolAlg.trans, ofBoolAlg_mul_ofBoolAlg_eq_left_iff, ofBoolRing, ofBoolRing_le_ofBoolRing_iff, ofBoolRing_le_ofBoolRing_iff.trans
-/
def OrderIso.asBoolAlgAsBoolRing (α : Type*) [BooleanAlgebra α] : AsBoolAlg (AsBoolRing α) ≃o α :=
  ⟨ofBoolAlg.trans ofBoolRing,
   ofBoolRing_le_ofBoolRing_iff.trans ofBoolAlg_mul_ofBoolAlg_eq_left_iff⟩

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps!]
/--
Definition of `RingEquiv.asBoolRingAsBoolAlg` / `RingEquiv.asBoolRingAsBoolAlg` 的定义

English:
definition RingEquiv.asBoolRingAsBoolAlg
  signature: (α : Type*) [BooleanRing α]
  body: { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }

中文:
定义 RingEquiv.asBoolRingAsBoolAlg
  签名: (α : 类型) [布尔eanRing α]
  定义体: { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }

Depends on / 依赖: map_add, map_mul, ofBoolAlg, ofBoolAlg_symmDiff, ofBoolRing, ofBoolRing.trans
-/
def RingEquiv.asBoolRingAsBoolAlg (α : Type*) [BooleanRing α] : AsBoolRing (AsBoolAlg α) ≃+* α :=
  { ofBoolRing.trans ofBoolAlg with
    map_mul' := fun _a _b => rfl
    map_add' := ofBoolAlg_symmDiff }

open Bool

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Bool
  body: false

中文:
实例 :
  签名: Zero 布尔
  定义体: false
-/
instance : Zero Bool where zero := false

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Bool
  body: true

中文:
实例 :
  签名: One 布尔
  定义体: true
-/
instance : One Bool where one := true

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add Bool
  body: xor

中文:
实例 :
  签名: Add 布尔
  定义体: xor
-/
instance : Add Bool where add := xor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg Bool
  body: id

中文:
实例 :
  签名: Neg 布尔
  定义体: id
-/
instance : Neg Bool where neg := id

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub Bool
  body: xor

中文:
实例 :
  签名: Sub 布尔
  定义体: xor
-/
instance : Sub Bool where sub := xor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul Bool
  body: and

中文:
实例 :
  签名: Mul 布尔
  定义体: and
-/
instance : Mul Bool where mul := and

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BooleanRing Bool
  body: xor_assoc
  zero_add := Bool.false_xor
  add_zero := Bool.xor_false
  neg_add_cancel := Bool.xor_self
  add_comm := xor_comm
  mul_assoc := and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := and_xor_distrib_left
  right_distrib := and_xor_distrib_right
  isIdempotentEl

中文:
实例 :
  签名: 布尔eanRing 布尔
  定义体: xor_assoc
  zero_add := Bool.false_xor
  add_zero := Bool.xor_false
  neg_add_cancel := Bool.xor_self
  add_comm := xor_comm
  mul_assoc := and_assoc
  one_mul := Bool.true_and
  mul_one := Bool.and_true
  left_distrib := and_xor_distrib_left
  right_distrib := and_xor_distrib_right
  isIdempotentEl

Depends on / 依赖: xor_assoc
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

/--
theorem `Bool.zero_eq_false` / 定理 `Bool.zero_eq_false`

English:
theorem Bool.zero_eq_false
  statement: 0 = false
  proof: rfl

中文:
定理 Bool.zero_eq_false
  结论: 0 = false
  证明: rfl
-/
theorem Bool.zero_eq_false : 0 = false := rfl

/--
theorem `Bool.one_eq_true` / 定理 `Bool.one_eq_true`

English:
theorem Bool.one_eq_true
  statement: 1 = true
  proof: rfl

中文:
定理 Bool.one_eq_true
  结论: 1 = true
  证明: rfl
-/
theorem Bool.one_eq_true : 1 = true := rfl

/--
theorem `Bool.add_eq_xor` / 定理 `Bool.add_eq_xor`

English:
theorem Bool.add_eq_xor
  given: (b c : Bool)
  statement: b + c = (b ^^ c)
  proof: rfl

中文:
定理 Bool.add_eq_xor
  条件: (b c : 布尔)
  结论: b + c = (b ^^ c)
  证明: rfl
-/
theorem Bool.add_eq_xor (b c : Bool) : b + c = (b ^^ c) := rfl

/--
theorem `Bool.neg_eq_id` / 定理 `Bool.neg_eq_id`

English:
theorem Bool.neg_eq_id
  given: (b : Bool)
  statement: -b = b
  proof: rfl

中文:
定理 Bool.neg_eq_id
  条件: (b : 布尔)
  结论: -b = b
  证明: rfl
-/
theorem Bool.neg_eq_id (b : Bool) : -b = b := rfl

/--
theorem `Bool.sub_eq_xor` / 定理 `Bool.sub_eq_xor`

English:
theorem Bool.sub_eq_xor
  given: (b c : Bool)
  statement: b - c = (b ^^ c)
  proof: rfl

中文:
定理 Bool.sub_eq_xor
  条件: (b c : 布尔)
  结论: b - c = (b ^^ c)
  证明: rfl
-/
theorem Bool.sub_eq_xor (b c : Bool) : b - c = (b ^^ c) := rfl

/--
theorem `Bool.mul_eq_and` / 定理 `Bool.mul_eq_and`

English:
theorem Bool.mul_eq_and
  given: (b c : Bool)
  statement: b * c = (b && c)
  proof: rfl

中文:
定理 Bool.mul_eq_and
  条件: (b c : 布尔)
  结论: b * c = (b && c)
  证明: rfl
-/
theorem Bool.mul_eq_and (b c : Bool) : b * c = (b && c) := rfl
