/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Ring.Defs

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

public section


variable {R : Type*}

/-! ### Order dual -/

namespace OrderDual

/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Distrib R] : Distrib Rᵒᵈ := inferInstanceAs <| Distrib R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ :=
  inferInstanceAs <| LeftDistribClass R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ :=
  inferInstanceAs <| RightDistribClass R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ :=
  inferInstanceAs <| NonUnitalNonAssocSemiring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NatCast R] : NatCast Rᵒᵈ := inferInstanceAs <| NatCast R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IntCast R] : IntCast Rᵒᵈ := inferInstanceAs <| IntCast R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoidWithOne R] : AddMonoidWithOne Rᵒᵈ := inferInstanceAs <| AddMonoidWithOne R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵒᵈ :=
  inferInstanceAs <| AddCommMonoidWithOne R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroupWithOne R] : AddGroupWithOne Rᵒᵈ := inferInstanceAs <| AddGroupWithOne R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵒᵈ :=
  inferInstanceAs <| AddCommGroupWithOne R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring R] : NonUnitalSemiring Rᵒᵈ := inferInstanceAs <| NonUnitalSemiring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring R] : NonAssocSemiring Rᵒᵈ := inferInstanceAs <| NonAssocSemiring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] : Semiring Rᵒᵈ := inferInstanceAs <| Semiring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵒᵈ :=
  inferInstanceAs <| NonUnitalCommSemiring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] : CommSemiring Rᵒᵈ := inferInstanceAs <| CommSemiring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ := inferInstanceAs <| HasDistribNeg R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵒᵈ :=
  inferInstanceAs <| NonUnitalNonAssocRing R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing R] : NonUnitalRing Rᵒᵈ := inferInstanceAs <| NonUnitalRing R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing R] : NonAssocRing Rᵒᵈ := inferInstanceAs <| NonAssocRing R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] : Ring Rᵒᵈ := inferInstanceAs <| Ring R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ := inferInstanceAs <| NonUnitalCommRing R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] : CommRing Rᵒᵈ := inferInstanceAs <| CommRing R
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] [IsDomain R] : IsDomain Rᵒᵈ := inferInstanceAs <| IsDomain R

end OrderDual

open OrderDual

@[simp]
/-
**toDual_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_natCast [NatCast R] (n : Nat) : toDual (n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_natCast [NatCast R] (n : ℕ) : toDual (n : R) = n :=
  rfl

@[simp]
/-
**toDual_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : (toDual (ofNat(n) : R)
) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (toDual (ofNat(n) : R)) = ofNat(n) :=
  rfl

@[simp]
/-
**ofDual_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_natCast [NatCast R] (n : Nat) : (ofDual n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_natCast [NatCast R] (n : ℕ) : (ofDual n : R) = n :=
  rfl

@[simp]
/-
**ofDual_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : (ofDual (ofNat(n) : Rᵒ
ᵈ)) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (ofDual (ofNat(n) : Rᵒᵈ)) = ofNat(n) :=
  rfl
/-
**toDual_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : IntCast R] (n : ℤ), OrderDual.toDual ↑n = ↑n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toDual_intCast [IntCast R] (n : ℤ) : toDual (n : R) = n := rfl
/-
**ofDual_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : IntCast R] (n : ℤ), OrderDual.ofDual ↑n = ↑n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofDual_intCast [IntCast R] (n : ℤ) : (ofDual n : R) = n := rfl

/-! ### Lexicographical order -/

namespace Lex

/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Distrib R] : Distrib (Lex R) := inferInstanceAs <| Distrib R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass (Lex R) :=
  inferInstanceAs <| LeftDistribClass R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass (Lex R) :=
  inferInstanceAs <| RightDistribClass R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (Lex R) :=
  inferInstanceAs <| NonUnitalNonAssocSemiring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring R] : NonUnitalSemiring (Lex R) := inferInstanceAs <| NonUnitalSemiring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NatCast R] : NatCast (Lex R) := inferInstanceAs <| NatCast R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IntCast R] : IntCast (Lex R) := inferInstanceAs <| IntCast R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoidWithOne R] : AddMonoidWithOne (Lex R) := inferInstanceAs <| AddMonoidWithOne R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Lex R) :=
  inferInstanceAs <| AddCommMonoidWithOne R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroupWithOne R] : AddGroupWithOne (Lex R) := inferInstanceAs <| AddGroupWithOne R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroupWithOne R] : AddCommGroupWithOne (Lex R) :=
  inferInstanceAs <| AddCommGroupWithOne R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring R] : NonAssocSemiring (Lex R) := inferInstanceAs <| NonAssocSemiring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] : Semiring (Lex R) := inferInstanceAs <| Semiring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (Lex R) :=
  inferInstanceAs <| NonUnitalCommSemiring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] : CommSemiring (Lex R) := inferInstanceAs <| CommSemiring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul R] [HasDistribNeg R] : HasDistribNeg (Lex R) := inferInstanceAs <| HasDistribNeg R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Lex R) :=
  inferInstanceAs <| NonUnitalNonAssocRing R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing R] : NonUnitalRing (Lex R) := inferInstanceAs <| NonUnitalRing R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing R] : NonAssocRing (Lex R) := inferInstanceAs <| NonAssocRing R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] : Ring (Lex R) := inferInstanceAs <| Ring R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing R] : NonUnitalCommRing (Lex R) := inferInstanceAs <| NonUnitalCommRing R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] : CommRing (Lex R) := inferInstanceAs <| CommRing R
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] [IsDomain R] : IsDomain (Lex R) := inferInstanceAs <| IsDomain R

end Lex

@[simp]
/-
**toLex_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_natCast [NatCast R] (n : Nat) : toLex (n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_natCast [NatCast R] (n : ℕ) : toLex (n : R) = n :=
  rfl

@[simp]
/-
**toLex_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : toLex (ofNat(n) : R) = 
OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    toLex (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

@[simp]
/-
**ofLex_natCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_natCast [NatCast R] (n : Nat) : (ofLex n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_natCast [NatCast R] (n : ℕ) : (ofLex n : R) = n :=
  rfl

@[simp]
/-
**ofLex_ofNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : ofLex (ofNat(n) : Lex R
) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    ofLex (ofNat(n) : Lex R) = OfNat.ofNat n :=
  rfl
/-
**toLex_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : IntCast R] (n : ℤ), toLex ↑n = ↑n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLex_intCast [IntCast R] (n : ℤ) : toLex (n : R) = n := rfl
/-
**ofLex_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : IntCast R] (n : ℤ), ofLex ↑n = ↑n
参数：n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLex_intCast [IntCast R] (n : ℤ) : (ofLex n : R) = n := rfl
