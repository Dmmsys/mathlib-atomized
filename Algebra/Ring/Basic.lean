/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.TFAE

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib/Algebra/Group/Basic.lean`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib/Algebra/Ring/Defs.lean`.
-/

@[expose] public section

assert_not_exists Nat.cast_sub

variable {R S : Type*}

open Function

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps -fullyApplied]
/-
**AddHom.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddHom`。
形式化陈述：mulLeft [Distrib R] (r : R) : AddHom R R where toFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by an element of a type with distributive multiplication is 
an `AddHom`.
-/
def mulLeft [Distrib R] (r : R) : AddHom R R where
  toFun := (r * ·)
  map_add' := mul_add r

/-- Right multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps -fullyApplied]
/-
**AddHom.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddHom`。
形式化陈述：mulRight [Distrib R] (r : R) : AddHom R R where toFun a
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by an element of a type with distributive multiplication is
 an `AddHom`.
-/
def mulRight [Distrib R] (r : R) : AddHom R R where
  toFun a := a * r
  map_add' _ _ := add_mul _ _ r

end AddHom

namespace AddMonoidHom
variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

/-- Left multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
/-
**AddMonoidHom.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulLeft (r : R) : R ->+ R where toFun
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by an element of a (semi)ring is an `AddMonoidHom`
-/
def mulLeft (r : R) : R →+ R where
  toFun := (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r
/-
**AddMonoidHom.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R] (r : R), ⇑(AddMonoid
Hom.mulLeft r) = HMul.hMul r
参数：r : R；AddMonoidHom.mulLeft r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mulLeft (r : R) : (mulLeft r : R → R) = HMul.hMul r := rfl

/-- Right multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
/-
**AddMonoidHom.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mulRight (r : R) : R ->+ R where toFun a
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by an element of a (semi)ring is an `AddMonoidHom`
-/
def mulRight (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r
/-
**AddMonoidHom.coe_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R] (r : R), ⇑(AddMonoid
Hom.mulRight r) = fun x => x * r
参数：r : R；AddMonoidHom.mulRight r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mulRight (r : R) : (mulRight r) = (· * r) := rfl
/-
**AddMonoidHom.mulRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidHom`。
形式化陈述：mulRight_apply (a r : R) : mulRight r a = a * r
参数：a r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulRight_apply (a r : R) : mulRight r a = a * r := rfl

/-- Multiplication of an element of a (semi)ring is an `AddMonoidHom` in both arguments.

This is a more-strongly bundled version of `AddMonoidHom.mulLeft` and `AddMonoidHom.mulRight`.

Stronger versions of this exists for algebras as `LinearMap.mul`, `NonUnitalAlgHom.mul`
and `Algebra.lmul`.
-/
/-
**AddMonoidHom.mul** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：mul : R ->+ R ->+ R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of an element of a (semi)ring is an `AddMonoidHom` in both argume
nts.

This is a more-strongly bundled version of `AddMonoidHom.mulLeft` and `AddMonoid
Hom.mulRight`.

Stronger versions of this exists for algebras as `LinearMap.mul`, `NonUnitalAlgH
om.mul`
and `Algebra.lmul`.
-/
def mul : R →+ R →+ R where
  toFun := mulLeft
  map_zero' := ext <| zero_mul
  map_add' a b := ext <| add_mul a b
/-
**AddMonoidHom.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidHom`。
形式化陈述：mul_apply (x y : R) : mul x y = x * y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply (x y : R) : mul x y = x * y := rfl
/-
**AddMonoidHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R], ⇑AddMonoidHom.mul =
 AddMonoidHom.mulLeft
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul : ⇑(mul : R →+ R →+ R) = mulLeft := rfl
/-
**AddMonoidHom.coe_flip_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R], ⇑AddMonoidHom.mul.f
lip = AddMonoidHom.mulRight
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_flip_mul : ⇑(mul : R →+ R →+ R).flip = mulRight := rfl

/-- An `AddMonoidHom` preserves multiplication if pre- and post- composition with
`mul` are equivalent. By converting the statement into an equality of
`AddMonoidHom`s, this lemma allows various specialized `ext` lemmas about `→+` to then be applied.
-/
/-
**AddMonoidHom.map_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidHom`。
形式化陈述：map_mul_iff (f : R ->+ S) : (forall x y, f (x * y) = f x * f y) ↔ (mul : R
 ->+ R ->+ R).compr₂ f = (mul.comp f).compl₂ f
参数：f : R ->+ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AddMonoidHom.ext_iff₂`：∀ {M : Type uM} {N : Type uN} {P : Type uP} {x : 
AddZeroClass M} {x_1 : AddZeroClass N} {x_2 : AddCommMonoid P}   {f g : M →+ N →
+ P}, f = g…

--- 原说明 ---
An `AddMonoidHom` preserves multiplication if pre- and post- composition with
`mul` are equivalent. By converting the statement into an equality of
`AddMonoidHom`s, this lemma allows various specialized `ext` lemmas about `→+` t
o then be applied.
-/
lemma map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔ (mul : R →+ R →+ R).compr₂ f = (mul.comp f).compl₂ f :=
  Iff.symm ext_iff₂
/-
**AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute** 是 Mathlib 中的一个引理，位于命名空间 
`AddMonoidHom`。
形式化陈述：mulLeft_eq_mulRight_iff_forall_commute : mulLeft a = mulRight a ↔ forall b
, Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
lemma mulLeft_eq_mulRight_iff_forall_commute : mulLeft a = mulRight a ↔ ∀ b, Commute a b :=
  DFunLike.ext_iff
/-
**AddMonoidHom.mulRight_eq_mulLeft_iff_forall_commute** 是 Mathlib 中的一个引理，位于命名空间 
`AddMonoidHom`。
形式化陈述：mulRight_eq_mulLeft_iff_forall_commute : mulRight b = mulLeft b ↔ forall a
, Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
lemma mulRight_eq_mulLeft_iff_forall_commute : mulRight b = mulLeft b ↔ ∀ a, Commute a b :=
  DFunLike.ext_iff

end AddMonoidHom

namespace AddMonoid.End
section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-- The left multiplication map: `(a, b) ↦ a * b`. See also `AddMonoidHom.mulLeft`. -/
@[simps!]
/-
**AddMonoid.End.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoid.End`。
形式化陈述：mulLeft : R ->+ AddMonoid.End R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left multiplication map: `(a, b) ↦ a * b`. See also `AddMonoidHom.mulLeft`.
-/
def mulLeft : R →+ AddMonoid.End R := .mul

/-- The right multiplication map: `(a, b) ↦ b * a`. See also `AddMonoidHom.mulRight`. -/
@[simps!]
/-
**AddMonoid.End.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoid.End`。
形式化陈述：mulRight : R ->+ AddMonoid.End R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right multiplication map: `(a, b) ↦ b * a`. See also `AddMonoidHom.mulRight`
.
-/
def mulRight : R →+ AddMonoid.End R := (.mul : R →+ AddMonoid.End R).flip

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocCommSemiring
variable [NonUnitalNonAssocCommSemiring R]

/-
**AddMonoid.End.mulRight_eq_mulLeft** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoid.End`。
形式化陈述：mulRight_eq_mulLeft : mulRight = (mulLeft : R ->+ AddMonoid.End R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute`：mulLeft_eq_mulRight
_iff_forall_commute : mulLeft a = mulRight a ↔ forall b, Commute a b
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma mulRight_eq_mulLeft : mulRight = (mulLeft : R →+ AddMonoid.End R) :=
  AddMonoidHom.ext fun _ =>
    Eq.symm <| AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

end NonUnitalNonAssocCommSemiring
end AddMonoid.End

section HasDistribNeg

section Mul

variable {α : Type*} [Mul α] [HasDistribNeg α]

open MulOpposite

/-
**MulOpposite.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.instHasDistribNeg : HasDistribNeg αᵐᵒᵖ where neg_mul _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulOpposite.instHasDistribNeg : HasDistribNeg αᵐᵒᵖ where
  neg_mul _ _ := unop_injective <| mul_neg _ _
  mul_neg _ _ := unop_injective <| neg_mul _ _

end Mul

end HasDistribNeg

section NonUnitalCommRing

variable {α : Type*} [NonUnitalCommRing α]

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
/-
**vieta_formula_quadratic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) : exists y
 : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c
参数：h : x * x - b * x + c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_neg_of_add_eq_zero_right`：∀ {α : Type u_1} [inst : SubtractionMonoid 
α] {a b : α}, a + b = 0 → b = -a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b

--- 原说明 ---
Vieta's formula for a quadratic equation, relating the coefficients of the polyn
omial with
  its roots. This particular version states that if we have a root `x` of a moni
c quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `
a_1` coefficient
  and `x * y` is the `a_0` coefficient.
-/
theorem vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine ⟨b - x, ?_, by simp, by rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]

end NonUnitalCommRing

/-
**succ_ne_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：succ_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 !
= a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem succ_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))
/-
**pred_ne_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pred_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 !
= a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pred_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h ↦
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simp [← sub_eq_add_neg, h])))

section NoZeroDivisors

variable (α)

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

/-
**isLeftRegular_iff_right_eq_zero_of_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_iff_right_eq_zero_of_mul : IsLeftRegular r ↔ forall x, r * x
 = 0 -> x = 0 where mp h r' eq
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma isLeftRegular_iff_right_eq_zero_of_mul : IsLeftRegular r ↔ ∀ x, r * x = 0 → x = 0 where
  mp h r' eq := h (by simp_rw [eq, mul_zero])
  mpr h r₁ r₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [mul_sub, eq, sub_self]
/-
**isRightRegular_iff_left_eq_zero_of_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_iff_left_eq_zero_of_mul : IsRightRegular r ↔ forall x, x * 
r = 0 -> x = 0 where mp h r' eq
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma isRightRegular_iff_left_eq_zero_of_mul : IsRightRegular r ↔ ∀ x, x * r = 0 → x = 0 where
  mp h r' eq := h (by simp_rw [eq, zero_mul])
  mpr h r₁ r₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [sub_mul, eq, sub_self]
/-
**isRegular_iff_eq_zero_of_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_iff_eq_zero_of_mul : IsRegular r ↔ (forall x, r * x = 0 -> x = 0
) ∧ (forall x, x * r = 0 -> x = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRegular_iff`：isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ I
sRightRegular c
· 使用引理 `isLeftRegular_iff_right_eq_zero_of_mul`：isLeftRegular_iff_right_eq_zero_
of_mul : IsLeftRegular r ↔ forall x, r * x = 0 -> x = 0 where mp h r' eq
· 使用引理 `isRightRegular_iff_left_eq_zero_of_mul`：isRightRegular_iff_left_eq_zero_
of_mul : IsRightRegular r ↔ forall x, x * r = 0 -> x = 0 where mp h r' eq
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_iff_eq_zero_of_mul :
    IsRegular r ↔ (∀ x, r * x = 0 → x = 0) ∧ (∀ x, x * r = 0 → x = 0) := by
  rw [isRegular_iff, isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul]

/-- A (not necessarily unital or associative) ring with no zero divisors has cancellative
multiplication on both sides. Since either left or right cancellative multiplication implies
the absence of zero divisors, the four conditions are equivalent to each other. -/
/-
**noZeroDivisors_tfae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noZeroDivisors_tfae : List.TFAE [NoZeroDivisors R, IsLeftCancelMulZero R, 
IsRightCancelMulZero R, IsCancelMulZero R]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `noZeroDivisors_iff_right_eq_zero_of_mul`：noZeroDivisors_iff_right_eq_zer
o_of_mul : NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> forall y, x * y = 0 -> y
 = 0
· 使用引理 `noZeroDivisors_iff_left_eq_zero_of_mul`：noZeroDivisors_iff_left_eq_zero_
of_mul : NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> forall y, y * x = 0 -> y =
 0
· 使用引理 `noZeroDivisors_iff_eq_zero_of_mul`：noZeroDivisors_iff_eq_zero_of_mul : N
oZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> (forall y, x * y = 0 -> y = 0) ∧ (fo
rall y, y * x = 0 -> y …
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A (not necessarily unital or associative) ring with no zero divisors has cancell
ative
multiplication on both sides. Since either left or right cancellative multiplica
tion implies
the absence of zero divisors, the four conditions are equivalent to each other.
-/
lemma noZeroDivisors_tfae : List.TFAE
    [NoZeroDivisors R, IsLeftCancelMulZero R, IsRightCancelMulZero R, IsCancelMulZero R] := by
  simp_rw [isLeftCancelMulZero_iff, isRightCancelMulZero_iff, isCancelMulZero_iff_forall_isRegular,
    isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul,
    isRegular_iff_eq_zero_of_mul]
  tfae_have 1 ↔ 2 := noZeroDivisors_iff_right_eq_zero_of_mul
  tfae_have 1 ↔ 3 := noZeroDivisors_iff_left_eq_zero_of_mul
  tfae_have 1 ↔ 4 := noZeroDivisors_iff_eq_zero_of_mul
  tfae_finish

/-- In a ring, `IsCancelMulZero` and `NoZeroDivisors` are equivalent. -/
/-
**isCancelMulZero_iff_noZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCancelMulZero_iff_noZeroDivisors : IsCancelMulZero R ↔ NoZeroDivisors R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `noZeroDivisors_tfae`：noZeroDivisors_tfae : List.TFAE [NoZeroDivisors R, 
IsLeftCancelMulZero R, IsRightCancelMulZero R, IsCancelMulZero R]

--- 原说明 ---
In a ring, `IsCancelMulZero` and `NoZeroDivisors` are equivalent.
-/
lemma isCancelMulZero_iff_noZeroDivisors : IsCancelMulZero R ↔ NoZeroDivisors R :=
  noZeroDivisors_tfae.out 3 0

variable (R) in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NoZeroDivisors.to_isCancelMulZero
    [NoZeroDivisors R] : IsCancelMulZero R :=
  isCancelMulZero_iff_noZeroDivisors.mpr ‹_›

end NonUnitalNonAssocRing

/-
**NoZeroDivisors.to_isDomain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] 
: IsDomain α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoZeroDivisors.to_isCancelMulZero`：∀ (R : Type u_3) [inst : NonUnitalNon
AssocRing R] [NoZeroDivisors R], IsCancelMulZero R
-/
lemma NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
    IsDomain α :=
  { NoZeroDivisors.to_isCancelMulZero α, h with .. }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsDomain.to_noZeroDivisors [Semiring α] [IsDomain α] :
    NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α
/-
**Subsingleton.to_isCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subsingleton.to_isCancelMulZero [Mul α] [Zero α] [Subsingleton α] : IsCanc
elMulZero α where mul_right_cancel_of_ne_zero hb
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
-/
instance Subsingleton.to_isCancelMulZero [Mul α] [Zero α] [Subsingleton α] : IsCancelMulZero α where
  mul_right_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

-- This was previously a global instance,
-- but it has been implicated in slow typeclass resolutions,
-- so we scope it to the `Subsingleton` namespace.
/-
**Subsingleton.to_noZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroD
ivisors α where eq_zero_or_eq_zero_of_mul_eq_zero _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
-/
lemma Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero _ := .inl (Subsingleton.eq_zero _)

scoped[Subsingleton] attribute [instance] Subsingleton.to_noZeroDivisors
/-
**isDomain_iff_cancelMulZero_and_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] : IsDomain α ↔ IsCa
ncelMulZero α ∧ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
lemma isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] :
    IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ {}⟩
/-
**isCancelMulZero_iff_isDomain_or_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCancelMulZero_iff_isDomain_or_subsingleton [Semiring α] : IsCancelMulZer
o α ↔ IsDomain α ∨ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
lemma isCancelMulZero_iff_isDomain_or_subsingleton [Semiring α] :
    IsCancelMulZero α ↔ IsDomain α ∨ Subsingleton α := by
  refine ⟨fun t ↦ ?_, fun h ↦ h.elim (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)⟩
  rw [or_iff_not_imp_right, not_subsingleton_iff_nontrivial]
  exact fun _ ↦ {}
/-
**isDomain_iff_noZeroDivisors_and_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isDomain_iff_noZeroDivisors_and_nontrivial [Ring α] : IsDomain α ↔ NoZeroD
ivisors α ∧ Nontrivial α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isCancelMulZero_iff_noZeroDivisors`：isCancelMulZero_iff_noZeroDivisors :
 IsCancelMulZero R ↔ NoZeroDivisors R
· 使用引理 `isDomain_iff_cancelMulZero_and_nontrivial`：isDomain_iff_cancelMulZero_an
d_nontrivial [Semiring α] : IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isDomain_iff_noZeroDivisors_and_nontrivial [Ring α] :
    IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α := by
  rw [← isCancelMulZero_iff_noZeroDivisors, isDomain_iff_cancelMulZero_and_nontrivial]
/-
**noZeroDivisors_iff_isDomain_or_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noZeroDivisors_iff_isDomain_or_subsingleton [Ring α] : NoZeroDivisors α ↔ 
IsDomain α ∨ Subsingleton α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isCancelMulZero_iff_noZeroDivisors`：isCancelMulZero_iff_noZeroDivisors :
 IsCancelMulZero R ↔ NoZeroDivisors R
· 使用引理 `isCancelMulZero_iff_isDomain_or_subsingleton`：isCancelMulZero_iff_isDoma
in_or_subsingleton [Semiring α] : IsCancelMulZero α ↔ IsDomain α ∨ Subsingleton 
α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma noZeroDivisors_iff_isDomain_or_subsingleton [Ring α] :
    NoZeroDivisors α ↔ IsDomain α ∨ Subsingleton α := by
  rw [← isCancelMulZero_iff_noZeroDivisors, isCancelMulZero_iff_isDomain_or_subsingleton]

end NoZeroDivisors

section DivisionMonoid
variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

/-
**one_div_neg_one_eq_neg_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_neg_one_eq_neg_one : (1 : R) / -1 = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_one_div_of_mul_eq_one_right`：eq_one_div_of_mul_eq_one_right (h : a * 
b = 1) : b = 1 / a
-/
lemma one_div_neg_one_eq_neg_one : (1 : R) / -1 = -1 :=
  have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)
/-
**one_div_neg_eq_neg_one_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_neg_eq_neg_one_div (a : R) : 1 / -a = -(1 / a)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `one_div_mul_one_div_rev`：one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 /
 (b * a)
· 使用引理 `one_div_neg_one_eq_neg_one`：one_div_neg_one_eq_neg_one : (1 : R) / -1 = 
-1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma one_div_neg_eq_neg_one_div (a : R) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]
/-
**div_neg_eq_neg_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用引理 `one_div_neg_eq_neg_one_div`：one_div_neg_eq_neg_one_div (a : R) : 1 / -a 
= -(1 / a)
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
-/
lemma div_neg_eq_neg_div (a b : R) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]
/-
**neg_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_div (a b : R) : -b / a = -(b / a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma neg_div (a b : R) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]
/-
**neg_div'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_div' (a b : R) : -(b / a) = -b / a
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
-/
lemma neg_div' (a b : R) : -(b / a) = -b / a := by rw [neg_div]

@[simp]
/-
**neg_div_neg_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_div_neg_eq (a b : R) : -a / -b = a / b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_neg_eq_neg_div`：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma neg_div_neg_eq (a b : R) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]
/-
**neg_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_inv : -a⁻¹ = (-a)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用引理 `div_neg_eq_neg_div`：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
-/
lemma neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]
/-
**div_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_neg (a : R) : a / -b = -(a / b)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_neg_eq_neg_div`：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
-/
lemma div_neg (a : R) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]
/-
**div_neg_eq_neg_div'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_neg_eq_neg_div' (a : R) : a / -b = -a / b
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
-/
lemma div_neg_eq_neg_div' (a : R) : a / -b = -a / b := neg_div b a ▸ div_neg _

@[simp]
/-
**inv_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_neg : (-a)⁻¹ = -a⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
-/
lemma inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]
/-
**inv_neg_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_neg_one : (-1 : R)⁻¹ = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
lemma inv_neg_one : (-1 : R)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid

