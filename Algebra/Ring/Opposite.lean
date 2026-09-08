/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Int.Cast.Basic

/-!
# Ring structures on the multiplicative opposite
-/

@[expose] public section

variable {R : Type*}

namespace MulOpposite

/-
**MulOpposite.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDistrib [Distrib R] : Distrib Rᵐᵒᵖ where left_distrib _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistrib [Distrib R] : Distrib Rᵐᵒᵖ where
  left_distrib _ _ _ := unop_injective <| add_mul _ _ _
  right_distrib _ _ _ := unop_injective <| mul_add _ _ _
/-
**MulOpposite.instNatCast** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{R : Type u_1} → [NatCast R] → NatCast Rᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instNatCast [NatCast R] : NatCast Rᵐᵒᵖ where natCast n := op n
/-
**MulOpposite.instIntCast** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{R : Type u_1} → [IntCast R] → IntCast Rᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instIntCast [IntCast R] : IntCast Rᵐᵒᵖ where intCast n := op n

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.op_natCast** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_natCast [NatCast R] (n : Nat) : op (n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_natCast [NatCast R] (n : ℕ) : op (n : R) = n :=
  rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.op_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : op (ofNat(n) : R) = ofNat(
n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    op (ofNat(n) : R) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.op_intCast** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_intCast [IntCast R] (n : Int) : op (n : R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_intCast [IntCast R] (n : ℤ) : op (n : R) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.unop_natCast** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_natCast [NatCast R] (n : Nat) : unop (n : Rᵐᵒᵖ) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_natCast [NatCast R] (n : ℕ) : unop (n : Rᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.unop_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : unop (ofNat(n) : Rᵐᵒᵖ) =
 ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    unop (ofNat(n) : Rᵐᵒᵖ) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**MulOpposite.unop_intCast** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_intCast [IntCast R] (n : Int) : unop (n : Rᵐᵒᵖ) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_intCast [IntCast R] (n : ℤ) : unop (n : Rᵐᵒᵖ) = n :=
  rfl
/-
**MulOpposite.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne Rᵐᵒᵖ where to
NatCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne Rᵐᵒᵖ where
  toNatCast := instNatCast
  toAddMonoid := instAddMonoid
  toOne := instOne
  natCast_zero := show op ((0 : ℕ) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show ∀ n, op ((n + 1 : ℕ) : R) = op ↑(n : ℕ) + 1 by simp
/-
**MulOpposite.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne R
ᵐᵒᵖ where toAddMonoidWithOne
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  __ := instAddCommMonoid
/-
**MulOpposite.instAddGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddGroupWithOne [AddGroupWithOne R] : AddGroupWithOne Rᵐᵒᵖ where toAdd
MonoidWithOne
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroupWithOne [AddGroupWithOne R] : AddGroupWithOne Rᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  toIntCast := instIntCast
  __ := instAddGroup
  intCast_ofNat n := show op ((n : ℤ) : R) = op (n : R) by rw [Int.cast_natCast]
  intCast_negSucc n := show op _ = op (-unop (op ((n + 1 : ℕ) : R))) by simp
/-
**MulOpposite.instAddCommGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵐᵒᵖ
 where toAddCommGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵐᵒᵖ where
  toAddCommGroup := instAddCommGroup
  __ := instAddGroupWithOne
/-
**MulOpposite.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposi
te`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] : NonUnitalNon
AssocSemiring Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring Rᵐᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass
/-
**MulOpposite.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵐᵒᵖ where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero
/-
**MulOpposite.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne
/-
**MulOpposite.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSemiring [Semiring R] : Semiring Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Semiring R] : Semiring Rᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero
/-
**MulOpposite.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemirin
g Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup
/-
**MulOpposite.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCommSemiring [CommSemiring R] : CommSemiring Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring R] : CommSemiring Rᵐᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid
/-
**MulOpposite.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRin
g Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵐᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring
/-
**MulOpposite.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring
/-
**MulOpposite.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne
/-
**MulOpposite.instRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instRing [Ring R] : Ring Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Ring R] : Ring Rᵐᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne
/-
**MulOpposite.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵐᵒᵖ where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring
/-
**MulOpposite.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCommRing [CommRing R] : CommRing Rᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing [CommRing R] : CommRing Rᵐᵒᵖ where
  __ := instRing
  __ := instCommMonoid
/-
**MulOpposite.instIsDomain** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `MulOpposite.instNontrivial`：∀ {α : Type u_1} [Nontrivial α], Nontrivial 
αᵐᵒᵖ
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
instance instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end MulOpposite

namespace AddOpposite

/-
**AddOpposite.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instDistrib [Distrib R] : Distrib Rᵃᵒᵖ where left_distrib _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistrib [Distrib R] : Distrib Rᵃᵒᵖ where
  left_distrib _ _ _ := unop_injective <| mul_add _ _ _
  right_distrib _ _ _ := unop_injective <| add_mul _ _ _

-- NOTE: `addMonoidWithOne R → addMonoidWithOne Rᵃᵒᵖ` does not hold
/-
**AddOpposite.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne R
ᵃᵒᵖ where toNatCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵃᵒᵖ where
  toNatCast := instNatCast
  toOne := instOne
  __ := instAddCommMonoid
  natCast_zero := show op ((0 : ℕ) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show ∀ n, op ((n + 1 : ℕ) : R) = op ↑(n : ℕ) + 1 by simp [add_comm]
/-
**AddOpposite.instAddCommGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵃᵒᵖ
 where toIntCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵃᵒᵖ where
  toIntCast := instIntCast
  toAddCommGroup := instAddCommGroup
  __ := instAddCommMonoidWithOne
  intCast_ofNat _ := congr_arg op <| Int.cast_natCast _
  intCast_negSucc _ := congr_arg op <| Int.cast_negSucc _
/-
**AddOpposite.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposi
te`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] : NonUnitalNon
AssocSemiring Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring Rᵃᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass
/-
**AddOpposite.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵃᵒᵖ where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero
/-
**AddOpposite.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne
/-
**AddOpposite.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instSemiring [Semiring R] : Semiring Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Semiring R] : Semiring Rᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero
/-
**AddOpposite.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemirin
g Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup
/-
**AddOpposite.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instCommSemiring [CommSemiring R] : CommSemiring Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring R] : CommSemiring Rᵃᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid
/-
**AddOpposite.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRin
g Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵃᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring
/-
**AddOpposite.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring
/-
**AddOpposite.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne
/-
**AddOpposite.instRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instRing [Ring R] : Ring Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Ring R] : Ring Rᵃᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne
/-
**AddOpposite.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵃᵒᵖ where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵃᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring
/-
**AddOpposite.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instCommRing [CommRing R] : CommRing Rᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing [CommRing R] : CommRing Rᵃᵒᵖ where
  __ := instRing
  __ := instCommMonoid
/-
**AddOpposite.instIsDomain** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `AddOpposite.instNontrivial`：∀ {α : Type u_1} [Nontrivial α], Nontrivial 
αᵃᵒᵖ
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
instance instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps -fullyApplied]
/-
**NonUnitalRingHom.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R] [N
onUnitalNonAssocSemiring S] (f : R ->ₙ+* S) (hf : forall x y, Commute (f x) (f y
)) : R ->ₙ+* Sᵐᵒᵖ
参数：f : R ->ₙ+* S；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y
` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`.
-/
def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps -fullyApplied]
/-
**NonUnitalRingHom.fromOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R] 
[NonUnitalNonAssocSemiring S] (f : R ->ₙ+* S) (hf : forall x y, Commute (f x) (f
 y)) : Rᵐᵒᵖ ->ₙ+* S
参数：f : R ->ₙ+* S；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y`
 for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`.
-/
def NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A non-unital ring hom `R →ₙ+* S` can equivalently be viewed as a non-unital ring hom
`Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
/-
**NonUnitalRingHom.op** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRingHom.op {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssoc
Semiring S] : (R ->ₙ+* S) ≃ (Rᵐᵒᵖ ->ₙ+* Sᵐᵒᵖ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital ring hom `R →ₙ+* S` can equivalently be viewed as a non-unital ring
 hom
`Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on mor
phisms.
-/
def NonUnitalRingHom.op {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (R →ₙ+* S) ≃ (Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }

/-- The 'unopposite' of a non-unital ring hom `Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ`. Inverse to
`NonUnitalRingHom.op`. -/
@[simp]
/-
**NonUnitalRingHom.unop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRingHom.unop {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAss
ocSemiring S] : (Rᵐᵒᵖ ->ₙ+* Sᵐᵒᵖ) ≃ (R ->ₙ+* S)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of a non-unital ring hom `Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ`. Inverse to
`NonUnitalRingHom.op`.
-/
def NonUnitalRingHom.unop {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ) ≃ (R →ₙ+* S) :=
  NonUnitalRingHom.op.symm

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps -fullyApplied]
/-
**RingHom.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S) 
(hf : forall x y, Commute (f x) (f y)) : R ->+* Sᵐᵒᵖ
参数：f : R ->+* S；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x
, y` defines
a ring homomorphism to `Sᵐᵒᵖ`.
-/
def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps -fullyApplied]
/-
**RingHom.fromOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S
) (hf : forall x y, Commute (f x) (f y)) : Rᵐᵒᵖ ->+* S
参数：f : R ->+* S；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x
, y` defines
a ring homomorphism from `Rᵐᵒᵖ`.
-/
def RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A ring hom `R →+* S` can equivalently be viewed as a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
/-
**RingHom.op** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.op {R S} [NonAssocSemiring R] [NonAssocSemiring S] : (R ->+* S) ≃ 
(Rᵐᵒᵖ ->+* Sᵐᵒᵖ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring hom `R →+* S` can equivalently be viewed as a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. T
his is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms.
-/
def RingHom.op {R S} [NonAssocSemiring R] [NonAssocSemiring S] :
    (R →+* S) ≃ (Rᵐᵒᵖ →+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }

/-- The 'unopposite' of a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. Inverse to `RingHom.op`. -/
@[simp]
/-
**RingHom.unop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.unop {R S} [NonAssocSemiring R] [NonAssocSemiring S] : (Rᵐᵒᵖ ->+* 
Sᵐᵒᵖ) ≃ (R ->+* S)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. Inverse to `RingHom.op`.
-/
def RingHom.unop {R S} [NonAssocSemiring R] [NonAssocSemiring S] : (Rᵐᵒᵖ →+* Sᵐᵒᵖ) ≃ (R →+* S) :=
  RingHom.op.symm
