/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Boolean algebra structure on idempotents in a commutative (semi)ring

We show that the idempotent in a commutative ring form a Boolean algebra, with complement given
by `a ↦ 1 - a` and infimum given by multiplication. In a commutative semiring where subtraction
is not available, it is still true that pairs of elements `(a, b)` satisfying `a * b = 0` and
`a + b = 1` form a Boolean algebra (such elements are automatically idempotents, and such a pair
is uniquely determined by either `a` or `b`).
-/

@[expose] public section

variable {R : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid R] [AddCommMonoid R] :
    Compl {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  compl a := ⟨(a.1.2, a.1.1), (mul_comm ..).trans a.2.1, (add_comm ..).trans a.2.2⟩
/-
**eq_of_mul_eq_add_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a : R) {b c : R} (mul : a * 
b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) : b = c
参数：a : R；mul : a * b = c * a；add_ab : a + b = 1；add_ac : a + c = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a : R) {b c : R}
    (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) :
    b = c :=
  calc b = (a + c) * b := by rw [add_ac, one_mul]
       _ = c * (a + b) := by rw [add_mul, mul, mul_add]
       _ = c := by rw [add_ab, mul_one]

section CommSemiring

variable [CommSemiring R] {a b : {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1}}

/-
**mul_eq_zero_add_eq_one_ext_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_eq_zero_add_eq_one_ext_left (eq : a.1.1 = b.1.1) : a = b
参数：eq : a.1.1 = b.1.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用引理 `eq_of_mul_eq_add_eq_one`：eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a
 : R) {b c : R} (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) 
: b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mul_eq_zero_add_eq_one_ext_left (eq : a.1.1 = b.1.1) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq, eq_of_mul_eq_add_eq_one a.1.1 ?_ a.2.2 ?_⟩
  · rw [a.2.1, mul_comm, eq, b.2.1]
  · rw [eq, b.2.2]
/-
**mul_eq_zero_add_eq_one_ext_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_eq_zero_add_eq_one_ext_right (eq : a.1.2 = b.1.2) : a = b
参数：eq : a.1.2 = b.1.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用引理 `eq_of_mul_eq_add_eq_one`：eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a
 : R) {b c : R} (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) 
: b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mul_eq_zero_add_eq_one_ext_right (eq : a.1.2 = b.1.2) : a = b := by
  refine Subtype.ext <| Prod.ext_iff.mpr ⟨eq_of_mul_eq_add_eq_one a.1.2 ?_ ?_ ?_, eq⟩
  · rw [mul_comm, a.2.1, eq, b.2.1]
  · rw [add_comm, a.2.2]
  · rw [add_comm, eq, b.2.2]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  le a b := a.1.1 * b.1.1 = a.1.1
  le_refl a := (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := mul_eq_zero_add_eq_one_ext_left <| by rw [← hab, mul_comm, hba]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  sup a b := ⟨(a.1.1 + a.1.2 * b.1.1, a.1.2 * b.1.2), by simp_rw [add_mul,
      mul_mul_mul_comm _ b.1.1, b.2.1, mul_zero, ← mul_assoc, a.2.1, zero_mul, add_zero], by
    simp_rw [add_assoc, ← mul_add, b.2.2, mul_one, a.2.2]⟩
  le_sup_left a b := by
    simp_rw [(· ≤ ·), mul_add, ← mul_assoc, a.2.1, zero_mul, add_zero,
      (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1.eq]
  le_sup_right a b := by
    simp_rw [(· ≤ ·), mul_add, mul_comm a.1.2, ← mul_assoc,
      (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1.eq, ← mul_add, a.2.2, mul_one]
  sup_le a b c hac hbc := by simp_rw [(· ≤ ·), add_mul, mul_assoc]; rw [hac, hbc]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanAlgebra {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  inf a b := (aᶜ ⊔ bᶜ)ᶜ
  inf_le_left a b := by simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup,
    mul_right_comm, (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1.eq]
  inf_le_right a b := by simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup,
    mul_assoc, (IsIdempotentElem.of_mul_add b.2.1 b.2.2).1.eq]
  le_inf a b c hab hac := by
    simp_rw [(· ≤ ·), (· ⊔ ·), (·ᶜ), SemilatticeSup.sup, ← mul_assoc]; rw [hab, hac]
  le_sup_inf a b c := Eq.le <| mul_eq_zero_add_eq_one_ext_right <| by
    simp_rw +instances [(· ⊔ ·), (· ⊓ ·), (·ᶜ), SemilatticeSup.sup, add_mul, mul_add,
      mul_mul_mul_comm _ b.1.1, (IsIdempotentElem.of_mul_add a.2.1 a.2.2).2.eq, ← mul_assoc, a.2.1,
      zero_mul, zero_add]
  top := ⟨(1, 0), mul_zero _, add_zero _⟩
  bot := ⟨(0, 1), zero_mul _, zero_add _⟩
  inf_compl_le_bot a := Eq.le <| mul_eq_zero_add_eq_one_ext_right <| by
    simp_rw +instances [(· ⊔ ·), (· ⊓ ·), (·ᶜ), SemilatticeSup.sup,
      (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1.eq, add_comm, a.2.2]
  top_le_sup_compl a := Eq.le <| mul_eq_zero_add_eq_one_ext_left <| by simp_rw [(· ⊔ ·), (·ᶜ),
    SemilatticeSup.sup, (IsIdempotentElem.of_mul_add a.2.1 a.2.2).2.eq, a.2.2]
  le_top _ := mul_one _
  bot_le _ := zero_mul _
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

end CommSemiring

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommSemigroup S] : SemilatticeInf {a : S // IsIdempotentElem a} where
  le a b := a.1 * b = a
  le_refl a := a.2
  le_trans a b c hab hbc := show _ = _ by rw [← hab, mul_assoc, hbc]
  le_antisymm a b hab hba := Subtype.ext <| by rw [← hab, mul_comm, hba]
  inf a b := ⟨_, a.2.mul b.2⟩
  inf_le_left a b := show _ = _ by simp_rw [mul_right_comm]; rw [a.2]
  inf_le_right a b := show _ = _ by simp_rw [mul_assoc]; rw [b.2]
  le_inf a b c hab hac := by simp_rw [← mul_assoc]; rw [hab, hac]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [CommMonoid M] : OrderTop {a : M // IsIdempotentElem a} where
  top := ⟨1, .one⟩
  le_top _ := mul_one _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M₀ : Type*} [CommMonoidWithZero M₀] : OrderBot {a : M₀ // IsIdempotentElem a} where
  bot := ⟨0, .zero⟩
  bot_le _ := zero_mul _

section CommRing

variable [CommRing R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice {a : R // IsIdempotentElem a} where
  __ : SemilatticeInf _ := inferInstance
  sup a b := ⟨_, a.2.add_sub_mul b.2⟩
  le_sup_left a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, a.2, add_sub_cancel_right]
  le_sup_right a b := show _ = _ by
    simp_rw [mul_sub, mul_add]; rw [← mul_assoc, mul_right_comm, b.2, add_sub_cancel_left]
  sup_le a b c hac hbc := show _ = _ by simp_rw [sub_mul, add_mul, mul_assoc]; rw [hbc, hac]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BooleanAlgebra {a : R // IsIdempotentElem a} where
  __ : DistribLattice _ := .ofInfSupLe fun a b c ↦ Eq.le <| Subtype.ext <| by
    simp_rw [(· ⊔ ·), (· ⊓ ·), SemilatticeSup.sup, SemilatticeInf.inf, Lattice.inf,
      SemilatticeInf.inf, mul_sub, mul_add, mul_mul_mul_comm]
    rw [a.2]
  __ : OrderTop _ := inferInstance
  __ : OrderBot _ := inferInstance
  compl a := ⟨_, a.2.one_sub⟩
  inf_compl_le_bot a := (mul_zero _).trans ((mul_one_sub ..).trans <| by rw [a.2, sub_self]).symm
  top_le_sup_compl a := (one_mul _).trans <| by
    simp_rw [(· ⊔ ·), SemilatticeSup.sup, add_sub_cancel, mul_sub, mul_one]
    rw [a.2, sub_self, sub_zero]; rfl
  sdiff_eq _ _ := rfl
  himp a b := ⟨_, (a.2.mul b.2.one_sub).one_sub⟩
  himp_eq a b := Subtype.ext <| by simp_rw [(· ⊔ ·), SemilatticeSup.sup,
    add_comm b.1, add_sub_assoc, mul_sub, mul_one, sub_sub_cancel, sub_add, mul_comm]

/-- In a commutative ring, the idempotents are in 1-1 correspondence with pairs of elements
whose product is 0 and whose sum is 1. The correspondence is given by `a ↔ (a, 1 - a)`. -/
/-
**OrderIso.isIdempotentElemMulZeroAddOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.isIdempotentElemMulZeroAddOne : {a : R // IsIdempotentElem a} ≃o 
{a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a commutative ring, the idempotents are in 1-1 correspondence with pairs of e
lements
whose product is 0 and whose sum is 1. The correspondence is given by `a ↔ (a, 1
 - a)`.
-/
def OrderIso.isIdempotentElemMulZeroAddOne :
    {a : R // IsIdempotentElem a} ≃o {a : R × R // a.1 * a.2 = 0 ∧ a.1 + a.2 = 1} where
  toFun a := ⟨(a, 1 - a), by simp_rw [mul_sub, mul_one, a.2.eq, sub_self], by rw [add_sub_cancel]⟩
  invFun a := ⟨a.1.1, (IsIdempotentElem.of_mul_add a.2.1 a.2.2).1⟩
  right_inv a := Subtype.ext <| Prod.ext rfl <| sub_eq_of_eq_add <| a.2.2.symm.trans (add_comm ..)
  map_rel_iff' := Iff.rfl

end CommRing

