/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.TermCongr

/-!
# Monoid, group etc. structures on `M × N`

In this file we define one-binop (`Monoid`, `Group` etc) structures on `M × N`.
We also prove trivial `simp` lemmas, and define the following operations on `MonoidHom`s:

* `fst M N : M × N →* M`, `snd M N : M × N →* N`: projections `Prod.fst` and `Prod.snd`
  as `MonoidHom`s;
* `inl M N : M →* M × N`, `inr M N : N →* M × N`: inclusions of first/second monoid
  into the product;
* `f.prod g` : `M →* N × P`: sends `x` to `(f x, g x)`;
* When `P` is commutative, `f.coprod g : M × N →* P` sends `(x, y)` to `f x * g y`
  (without the commutativity assumption on `P`, see `MonoidHom.noncommPiCoprod`);
* `f.prodMap g : M × N → M' × N'`: `Prod.map f g` as a `MonoidHom`,
  sends `(x, y)` to `(f x, g y)`.

## Main declarations

* `mulMulHom`/`mulMonoidHom`: Multiplication bundled as a
  multiplicative/monoid homomorphism.
* `divMonoidHom`: Division bundled as a monoid homomorphism.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered AddMonoidWithOne

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

namespace Prod

@[to_additive]
/-
**Prod.one_mk_mul_one_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：one_mk_mul_one_mk [MulOneClass M] [Mul N] (b₁ b₂ : N) : ((1 : M), b₁) * (1
, b₂) = (1, b₁ * b₂)
参数：b₁ b₂ : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_mul_mk`：mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) 
= (a₁ * a₂, b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem one_mk_mul_one_mk [MulOneClass M] [Mul N] (b₁ b₂ : N) :
    ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) := by
  rw [mk_mul_mk, mul_one]

@[to_additive]
/-
**Prod.mk_one_mul_mk_one** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_one_mul_mk_one [Mul M] [MulOneClass N] (a₁ a₂ : M) : (a₁, (1 : N)) * (a
₂, 1) = (a₁ * a₂, 1)
参数：a₁ a₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_mul_mk`：mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) 
= (a₁ * a₂, b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mk_one_mul_mk_one [Mul M] [MulOneClass N] (a₁ a₂ : M) :
    (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) := by
  rw [mk_mul_mk, mul_one]

@[to_additive]
/-
**Prod.fst_mul_snd** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1,
 p.snd) = p
参数：p : M × N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p :=
  Prod.ext (mul_one p.1) (one_mul p.2)

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveInv M] [InvolutiveInv N] : InvolutiveInv (M × N) :=
  { inv_inv := fun _ => Prod.ext (inv_inv _) (inv_inv _) }

@[to_additive]
/-
**Prod.isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：isMulCommutative [Mul M] [Mul N] [IsMulCommutative M] [IsMulCommutative N]
 : IsMulCommutative (M × N) where is_comm.comm _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
-/
instance isMulCommutative [Mul M] [Mul N] [IsMulCommutative M] [IsMulCommutative N] :
    IsMulCommutative (M × N) where
  is_comm.comm _ _ := by ext <;> apply mul_comm'

@[to_additive]
/-
**Prod.commMagma** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：commMagma [CommMagma M] [CommMagma N] : CommMagma (M × N) where mul_comm _
 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMagma [CommMagma M] [CommMagma N] : CommMagma (M × N) where
  mul_comm _ _ := by ext <;> apply mul_comm

@[to_additive]
/-
**Prod.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instSemigroup [Semigroup M] [Semigroup N] : Semigroup (M × N) where mul_as
soc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup [Semigroup M] [Semigroup N] : Semigroup (M × N) where
  mul_assoc _ _ _ := by ext <;> exact mul_assoc ..

@[to_additive]
/-
**Prod.instCommSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Prod`。
形式化陈述：{G : Type u_1} → {H : Type u_2} → [CommSemigroup G] → [CommSemigroup H] → 
CommSemigroup (G × H)
参数：G × H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup [CommSemigroup G] [CommSemigroup H] : CommSemigroup (G × H) where

@[to_additive]
/-
**Prod.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMulOneClass [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) wher
e one_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) where
  one_mul _ := by ext <;> exact one_mul _
  mul_one _ := by ext <;> exact mul_one _

@[to_additive]
/-
**Prod.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instMonoid [Monoid M] [Monoid N] : Monoid (M × N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Monoid M] [Monoid N] : Monoid (M × N) :=
  { npow := fun z a => ⟨NPow.npow z a.1, NPow.npow z a.2⟩,
    npow_zero := fun _ => Prod.ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun _ _ => Prod.ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    one_mul := by simp,
    mul_one := by simp }

@[to_additive]
/-
**Prod.instIsMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instIsMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFree M] [IsMulTors
ionFree N] : IsMulTorsionFree (M × N) where pow_left_injective n hn a b hab
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance instIsMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFree M] [IsMulTorsionFree N] :
    IsMulTorsionFree (M × N) where
  pow_left_injective n hn a b hab := by
    ext <;> apply pow_left_injective hn; exacts [congr(($hab).1), congr(($hab).2)]

@[to_additive Prod.subNegMonoid]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivInvMonoid G] [DivInvMonoid H] : DivInvMonoid (G × H) where
  div_eq_mul_inv _ _ := by ext <;> exact div_eq_mul_inv ..
  zpow z a := ⟨ZPow.zpow z a.1, ZPow.zpow z a.2⟩
  zpow_zero' _ := by ext <;> exact DivInvMonoid.zpow_zero' _
  zpow_succ' _ _ := by ext <;> exact DivInvMonoid.zpow_succ' ..
  zpow_neg' _ _ := by ext <;> exact DivInvMonoid.zpow_neg' ..

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionMonoid G] [DivisionMonoid H] : DivisionMonoid (G × H) :=
  { mul_inv_rev := fun _ _ => Prod.ext (mul_inv_rev _ _) (mul_inv_rev _ _),
    inv_eq_of_mul := fun _ _ h =>
      Prod.ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h),
    inv_inv := by simp }

@[to_additive SubtractionCommMonoid]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionCommMonoid G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H) :=
  { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mul_comm g₁, mul_comm h₁]; rfl }

@[to_additive]
/-
**Prod.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instGroup [Group G] [Group H] : Group (G × H) where inv_mul_cancel _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroup [Group G] [Group H] : Group (G × H) where
  inv_mul_cancel _ := by ext <;> exact inv_mul_cancel _

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul G] [Mul H] [IsLeftCancelMul G] [IsLeftCancelMul H] : IsLeftCancelMul (G × H) where
  mul_left_cancel _ _ _ h :=
      Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2)

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul G] [Mul H] [IsRightCancelMul G] [IsRightCancelMul H] : IsRightCancelMul (G × H) where
  mul_right_cancel _ _ _ h :=
      Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2)

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul G] [Mul H] [IsCancelMul G] [IsCancelMul H] : IsCancelMul (G × H) where

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelSemigroup G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H) :=
  { mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelSemigroup G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H) :=
  { mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelMonoid M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N) :=
  { mul_left_cancel _ _ := by simp }

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelMonoid M] [RightCancelMonoid N] : RightCancelMonoid (M × N) :=
  { mul_right_cancel _ _ := by simp }

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelMonoid M] [CancelMonoid N] : CancelMonoid (M × N) :=
  { mul_right_cancel _ _ := by simp only [mul_left_inj, imp_self, forall_const] }

@[to_additive]
/-
**Prod.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCommMonoid [CommMonoid M] [CommMonoid N] : CommMonoid (M × N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid M] [CommMonoid N] : CommMonoid (M × N) :=
  { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }

@[to_additive]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelCommMonoid M] [CancelCommMonoid N] : CancelCommMonoid (M × N) :=
  { mul_left_cancel _ _ := by simp }

@[to_additive]
/-
**Prod.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instCommGroup [CommGroup G] [CommGroup H] : CommGroup (G × H)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup [CommGroup G] [CommGroup H] : CommGroup (G × H) :=
  { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm g₁, mul_comm h₁] }

end Prod

section
variable [Mul M] [Mul N]

@[to_additive AddSemiconjBy.prod]
/-
**SemiconjBy.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemiconjBy.prod {x y z : M × N} (hm : SemiconjBy x.1 y.1 z.1) (hn : Semico
njBy x.2 y.2 z.2) : SemiconjBy x y z
参数：hm : SemiconjBy x.1 y.1 z.1；hn : SemiconjBy x.2 y.2 z.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem SemiconjBy.prod {x y z : M × N}
    (hm : SemiconjBy x.1 y.1 z.1) (hn : SemiconjBy x.2 y.2 z.2) : SemiconjBy x y z :=
  Prod.ext hm hn

@[to_additive]
/-
**Prod.semiconjBy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.semiconjBy_iff {x y z : M × N} : SemiconjBy x y z ↔ SemiconjBy x.1 y.
1 z.1 ∧ SemiconjBy x.2 y.2 z.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem Prod.semiconjBy_iff {x y z : M × N} :
    SemiconjBy x y z ↔ SemiconjBy x.1 y.1 z.1 ∧ SemiconjBy x.2 y.2 z.2 := Prod.ext_iff

@[to_additive AddCommute.prod]
/-
**Commute.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2) :
 Commute x y
参数：hm : Commute x.1 y.1；hn : Commute x.2 y.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.prod`：SemiconjBy.prod {x y z : M × N} (hm : SemiconjBy x.1 y.
1 z.1) (hn : SemiconjBy x.2 y.2 z.2) : SemiconjBy x y z
-/
theorem Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2) : Commute x y :=
  SemiconjBy.prod hm hn

@[to_additive]
/-
**Prod.commute_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prod.commute_iff {x y : M × N} : Commute x y ↔ Commute x.1 y.1 ∧ Commute x
.2 y.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.semiconjBy_iff`：Prod.semiconjBy_iff {x y z : M × N} : SemiconjBy x 
y z ↔ SemiconjBy x.1 y.1 z.1 ∧ SemiconjBy x.2 y.2 z.2
-/
theorem Prod.commute_iff {x y : M × N} :
    Commute x y ↔ Commute x.1 y.1 ∧ Commute x.2 y.2 := semiconjBy_iff

end

namespace MulHom

section Prod

variable (M N) [Mul M] [Mul N] [Mul P]

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `M`. -/
@[to_additive
      /-- Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `A` -/]
/-
**MulHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：fst : M × N ->ₙ* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fst : M × N →ₙ* M :=
  ⟨Prod.fst, fun _ _ => rfl⟩

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`. -/
@[to_additive
      /-- Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `B` -/]
/-
**MulHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：snd : M × N ->ₙ* N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def snd : M × N →ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩

variable {M N}

@[to_additive (attr := simp)]
/-
**MulHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_fst : ⇑(fst M N) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl

@[to_additive (attr := simp)]
/-
**MulHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_snd : ⇑(snd M N) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl

/-- Combine two `MonoidHom`s `f : M →ₙ* N`, `g : M →ₙ* P` into
`f.prod g : M →ₙ* (N × P)` given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod
      /-- Combine two `AddMonoidHom`s `f : AddHom M N`, `g : AddHom M P` into
      `f.prod g : AddHom M (N × P)` given by `(f.prod g) x = (f x, g x)` -/]
/-
**MulHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：{M : Type u_3} →   {N : Type u_4} →     {P : Type u_5} → [inst : Mul M] → 
[inst_1 : Mul N] → [inst_2 : Mul P] → (M →ₙ* N) → (M →ₙ* P) → M →ₙ* N × P
参数：M →ₙ* N；M →ₙ* P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def prod (f : M →ₙ* N) (g : M →ₙ* P) :
    M →ₙ* N × P where
  toFun := Function.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
/-
**MulHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_prod (f : M ->ₙ* N) (g : M ->ₙ* P) : ⇑(f.prod g) = Function.prod f g
参数：f : M ->ₙ* N；g : M ->ₙ* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : M →ₙ* N) (g : M →ₙ* P) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[to_additive (attr := simp) prod_apply]
/-
**MulHom.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：prod_apply (f : M ->ₙ* N) (g : M ->ₙ* P) (x) : f.prod g x = (f x, g x)
参数：f : M ->ₙ* N；g : M ->ₙ* P；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f : M →ₙ* N) (g : M →ₙ* P) (x) : f.prod g x = (f x, g x) :=
  rfl

@[to_additive (attr := simp) fst_comp_prod]
/-
**MulHom.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：fst_comp_prod (f : M ->ₙ* N) (g : M ->ₙ* P) : (fst N P).comp (f.prod g) = 
f
参数：f : M ->ₙ* N；g : M ->ₙ* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem fst_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
/-
**MulHom.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：snd_comp_prod (f : M ->ₙ* N) (g : M ->ₙ* P) : (snd N P).comp (f.prod g) = 
g
参数：f : M ->ₙ* N；g : M ->ₙ* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem snd_comp_prod (f : M →ₙ* N) (g : M →ₙ* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
/-
**MulHom.prod_unique** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：prod_unique (f : M ->ₙ* N × P) : ((fst N P).comp f).prod ((snd N P).comp f
) = f
参数：f : M ->ₙ* N × P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_unique (f : M →ₙ* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable {M' : Type*} {N' : Type*} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M →ₙ* M')
  (g : N →ₙ* N')

/-- `Prod.map` as a `MonoidHom`. -/
@[to_additive prodMap /-- `Prod.map` as an `AddMonoidHom` -/]
/-
**MulHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：prodMap : M × N ->ₙ* M' × N'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` as a `MonoidHom`.
-/
def prodMap : M × N →ₙ* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]
/-
**MulHom.prodMap_def** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl

@[to_additive (attr := simp) coe_prodMap]
/-
**MulHom.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coe_prodMap : ⇑(prodMap f g) = Prod.map f g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[to_additive prod_comp_prodMap]
/-
**MulHom.prod_comp_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：prod_comp_prodMap (f : P ->ₙ* M) (g : P ->ₙ* N) (f' : M ->ₙ* M') (g' : N -
>ₙ* N') : (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g)
参数：f : P ->ₙ* M；g : P ->ₙ* N；f' : M ->ₙ* M'；g' : N ->ₙ* N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp_prodMap (f : P →ₙ* M) (g : P →ₙ* N) (f' : M →ₙ* M') (g' : N →ₙ* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

section Coprod

variable [Mul M] [Mul N] [CommSemigroup P] (f : M →ₙ* P) (g : N →ₙ* P)

/-- Coproduct of two `MulHom`s with the same codomain:
  `f.coprod g (p : M × N) = f p.1 * g p.2`.
  (Commutative codomain; for the general case, see `MulHom.noncommCoprod`) -/
@[to_additive
    /-- Coproduct of two `AddHom`s with the same codomain:
    `f.coprod g (p : M × N) = f p.1 + g p.2`.
    (Commutative codomain; for the general case, see `AddHom.noncommCoprod`) -/]
/-
**MulHom.coprod** 是 Mathlib 中的一个定义，位于命名空间 `MulHom`。
形式化陈述：coprod : M × N ->ₙ* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprod : M × N →ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]
/-
**MulHom.coprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2
参数：p : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl

@[to_additive]
/-
**MulHom.comp_coprod** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：comp_coprod {Q : Type*} [CommSemigroup Q] (h : P ->ₙ* Q) (f : M ->ₙ* P) (g
 : N ->ₙ* P) : h.comp (f.coprod g) = (h.comp f).coprod (h.comp g)
参数：h : P ->ₙ* Q；f : M ->ₙ* P；g : N ->ₙ* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_coprod {Q : Type*} [CommSemigroup Q] (h : P →ₙ* Q) (f : M →ₙ* P) (g : N →ₙ* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp

end Coprod

end MulHom

namespace MonoidHom

variable (M N) [MulOneClass M] [MulOneClass N]

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `M`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `A` -/]
/-
**MonoidHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：fst : M × N ->* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fst : M × N →* M :=
  { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `B` -/]
/-
**MonoidHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：snd : M × N ->* N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def snd : M × N →* N :=
  { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `A` to `A × B`. -/]
/-
**MonoidHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：inl : M ->* M × N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inl : M →* M × N :=
  { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `B` to `A × B`. -/]
/-
**MonoidHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：inr : N ->* M × N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inr : N →* M × N :=
  { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }

variable {M N}

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_fst : ⇑(fst M N) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_snd : ⇑(snd M N) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.inl_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：inl_apply (x) : inl M N x = (x, 1)
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_apply (x) : inl M N x = (x, 1) :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.inr_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：inr_apply (y) : inr M N y = (1, y)
参数：y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_apply (y) : inr M N y = (1, y) :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：fst_comp_inl : (fst M N).comp (inl M N) = id M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：snd_comp_inl : (snd M N).comp (inl M N) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：fst_comp_inr : (fst M N).comp (inr M N) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：snd_comp_inr : (snd M N).comp (inr M N) = id N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl

@[to_additive]
/-
**MonoidHom.commute_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：commute_inl_inr (m : M) (n : N) : Commute (inl M N m) (inr M N n)
参数：m : M；n : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.prod`：Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Co
mmute x.2 y.2) : Commute x y
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
-/
theorem commute_inl_inr (m : M) (n : N) : Commute (inl M N m) (inr M N n) :=
  Commute.prod (.one_right m) (.one_left n)

section Prod

variable [MulOneClass P]

/-- Combine two `MonoidHom`s `f : M →* N`, `g : M →* P` into `f.prod g : M →* N × P`
given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod
      /-- Combine two `AddMonoidHom`s `f : M →+ N`, `g : M →+ P` into
      `f.prod g : M →+ N × P` given by `(f.prod g) x = (f x, g x)` -/]
/-
**MonoidHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：{M : Type u_3} →   {N : Type u_4} →     {P : Type u_5} →       [inst : Mul
OneClass M] → [inst_1 : MulOneClass N] → [inst_2 : MulOneClass P] → (M →* N) → (
M →* P) → M →* N × P
参数：M →* N；M →* P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def prod (f : M →* N) (g : M →* P) :
    M →* N × P where
  toFun := Function.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
/-
**MonoidHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_prod (f : M ->* N) (g : M ->* P) : ⇑(f.prod g) = Function.prod f g
参数：f : M ->* N；g : M ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : M →* N) (g : M →* P) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[to_additive (attr := simp) prod_apply]
/-
**MonoidHom.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：prod_apply (f : M ->* N) (g : M ->* P) (x) : f.prod g x = (f x, g x)
参数：f : M ->* N；g : M ->* P；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f : M →* N) (g : M →* P) (x) : f.prod g x = (f x, g x) :=
  rfl

@[to_additive (attr := simp) fst_comp_prod]
/-
**MonoidHom.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：fst_comp_prod (f : M ->* N) (g : M ->* P) : (fst N P).comp (f.prod g) = f
参数：f : M ->* N；g : M ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem fst_comp_prod (f : M →* N) (g : M →* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
/-
**MonoidHom.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：snd_comp_prod (f : M ->* N) (g : M ->* P) : (snd N P).comp (f.prod g) = g
参数：f : M ->* N；g : M ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem snd_comp_prod (f : M →* N) (g : M →* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
/-
**MonoidHom.prod_unique** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：prod_unique (f : M ->* N × P) : ((fst N P).comp f).prod ((snd N P).comp f)
 = f
参数：f : M ->* N × P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_unique (f : M →* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun _ => by simp

end Prod

section prodMap

variable {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] [MulOneClass P]
  (f : M →* M') (g : N →* N')

/-- `Prod.map` as a `MonoidHom`. -/
@[to_additive prodMap /-- `Prod.map` as an `AddMonoidHom`. -/]
/-
**MonoidHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：prodMap : M × N ->* M' × N'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` as a `MonoidHom`.
-/
def prodMap : M × N →* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]
/-
**MonoidHom.prodMap_def** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl

@[to_additive (attr := simp) coe_prodMap]
/-
**MonoidHom.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_prodMap : ⇑(prodMap f g) = Prod.map f g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[to_additive prod_comp_prodMap]
/-
**MonoidHom.prod_comp_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：prod_comp_prodMap (f : P ->* M) (g : P ->* N) (f' : M ->* M') (g' : N ->* 
N') : (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g)
参数：f : P ->* M；g : P ->* N；f' : M ->* M'；g' : N ->* N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp_prodMap (f : P →* M) (g : P →* N) (f' : M →* M') (g' : N →* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

section Coprod

variable [CommMonoid P] (f : M →* P) (g : N →* P)

/-- Coproduct of two `MonoidHom`s with the same codomain:
  `f.coprod g (p : M × N) = f p.1 * g p.2`.
  (Commutative case; for the general case, see `MonoidHom.noncommCoprod`.) -/
@[to_additive
    /-- Coproduct of two `AddMonoidHom`s with the same codomain:
    `f.coprod g (p : M × N) = f p.1 + g p.2`.
    (Commutative case; for the general case, see `AddHom.noncommCoprod`.) -/]
/-
**MonoidHom.coprod** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：coprod : M × N ->* P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprod : M × N →* P :=
  f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]
/-
**MonoidHom.coprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2
参数：p : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.coprod_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coprod_comp_inl : (f.coprod g).comp (inl M N) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]
/-
**MonoidHom.coprod_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coprod_comp_inr : (f.coprod g).comp (inr M N) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]
/-
**MonoidHom.coprod_unique** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coprod_unique (f : M × N ->* P) : (f.comp (inl M N)).coprod (f.comp (inr M
 N)) = f
参数：f : M × N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_unique (f : M × N →* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]
/-
**MonoidHom.coprod_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coprod_inl_inr {M N : Type*} [CommMonoid M] [CommMonoid N] : (inl M N).cop
rod (inr M N) = id (M × N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.coprod_unique`：coprod_unique (f : M × N ->* P) : (f.comp (inl 
M N)).coprod (f.comp (inr M N)) = f
-/
theorem coprod_inl_inr {M N : Type*} [CommMonoid M] [CommMonoid N] :
    (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id <| M × N)

@[to_additive]
/-
**MonoidHom.comp_coprod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comp_coprod {Q : Type*} [CommMonoid Q] (h : P ->* Q) (f : M ->* P) (g : N 
->* P) : h.comp (f.coprod g) = (h.comp f).coprod (h.comp g)
参数：h : P ->* Q；f : M ->* P；g : N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_coprod {Q : Type*} [CommMonoid Q] (h : P →* Q) (f : M →* P) (g : N →* P) :
    h.comp (f.coprod g) = (h.comp f).coprod (h.comp g) :=
  ext fun x => by simp

end Coprod

end MonoidHom

namespace MulEquiv

section

variable [MulOneClass M] [MulOneClass N]

/-- The equivalence between `M × N` and `N × M` given by swapping the components
is multiplicative. -/
@[to_additive prodComm
      /-- The equivalence between `M × N` and `N × M` given by swapping the
      components is additive. -/]
/-
**MulEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：prodComm : M × N ≃* N × M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodComm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodComm]
/-
**MulEquiv.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap :=
  rfl

@[to_additive (attr := simp) coe_prodComm_symm]
/-
**MulEquiv.coe_prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap :=
  rfl

variable [MulOneClass P]

/-- The equivalence between `(M × N) × P` and `M × (N × P)` is multiplicative. -/
@[to_additive prodAssoc
      /-- The equivalence between `(M × N) × P` and `M × (N × P)` is additive. -/]
/-
**MulEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：prodAssoc : (M × N) × P ≃* M × (N × P)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodAssoc : (M × N) × P ≃* M × (N × P) :=
  { Equiv.prodAssoc M N P with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodAssoc]
/-
**MulEquiv.coe_prodAssoc** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_prodAssoc : ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)) = Equiv.prodAsso
c M N P
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodAssoc : ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)) = Equiv.prodAssoc M N P :=
  rfl

@[to_additive (attr := simp) coe_prodAssoc_symm]
/-
**MulEquiv.coe_prodAssoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_prodAssoc_symm : ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)).symm = (Equ
iv.prodAssoc M N P).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodAssoc_symm :
    ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)).symm = (Equiv.prodAssoc M N P).symm :=
  rfl

variable {M' : Type*} {N' : Type*} [MulOneClass N'] [MulOneClass M']

section

variable (M N M' N')

/-- Four-way commutativity of `Prod`. The name matches `mul_mul_mul_comm`. -/
@[to_additive (attr := simps apply) prodProdProdComm
    /-- Four-way commutativity of `Prod`.
The name matches `mul_mul_mul_comm` -/]
/-
**MulEquiv.prodProdProdComm** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N' :=
  { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }

@[to_additive (attr := simp) prodProdProdComm_toEquiv]
/-
**MulEquiv.prodProdProdComm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：prodProdProdComm_toEquiv : (prodProdProdComm M N M' N' : _ ≃ _) = Equiv.pr
odProdProdComm M N M' N'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm M N M' N' : _ ≃ _) = Equiv.prodProdProdComm M N M' N' :=
  rfl

@[simp]
/-
**MulEquiv.prodProdProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：prodProdProdComm_symm : (prodProdProdComm M N M' N').symm = prodProdProdCo
mm M M' N N'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_symm : (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N' :=
  rfl

end

/-- Product of multiplicative isomorphisms; the maps come from `Equiv.prodCongr`. -/
@[to_additive prodCongr
/-- Product of additive isomorphisms; the maps come from `Equiv.prodCongr`. -/]
/-
**MulEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N'
参数：f : M ≃* M'；g : N ≃* N'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (map_mul f _ _) (map_mul g _ _) }

/-- Multiplying by the trivial monoid doesn't change the structure.

This is the `MulEquiv` version of `Equiv.uniqueProd`. -/
@[to_additive (attr := simps!) uniqueProd /-- Multiplying by the trivial monoid doesn't change the
structure.

This is the `AddEquiv` version of `Equiv.uniqueProd`. -/]
/-
**MulEquiv.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：uniqueProd [Unique N] : N × M ≃* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }

/-- Multiplying by the trivial monoid doesn't change the structure.

This is the `MulEquiv` version of `Equiv.prodUnique`. -/
@[to_additive (attr := simps!) prodUnique /-- Multiplying by the trivial monoid doesn't change the
structure.

This is the `AddEquiv` version of `Equiv.prodUnique`. -/]
/-
**MulEquiv.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：prodUnique [Unique N] : M × N ≃* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodUnique [Unique N] : M × N ≃* M :=
  { Equiv.prodUnique M N with map_mul' := fun _ _ => rfl }

end

section

variable [Monoid M] [Monoid N]

/-- The monoid equivalence between units of a product of two monoids, and the product of the
units of each monoid. -/
@[to_additive prodAddUnits
      /-- The additive monoid equivalence between additive units of a product
      of two additive monoids, and the product of the additive units of each additive monoid. -/]
/-
**MulEquiv.prodUnits** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodUnits : (M × N)ˣ ≃* Mˣ × Nˣ where
  toFun := (Units.map (MonoidHom.fst M N)).prod (Units.map (MonoidHom.snd M N))
  invFun u := ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩
  left_inv u := by
    simp only [MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_fst, MonoidHom.coe_snd,
      Prod.mk.eta, Units.coe_map_inv, Units.mk_val]
  right_inv := fun ⟨u₁, u₂⟩ => by
    simp only [Units.map, MonoidHom.coe_fst, Units.inv_eq_val_inv,
      MonoidHom.coe_snd, MonoidHom.prod_apply, Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
  map_mul' := map_mul _

@[to_additive]
/-
**MulEquiv._root_.Prod.isUnit_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Prod.isUnit_iff {x : M × N} : IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 where
  mp h := ⟨(prodUnits h.unit).1.isUnit, (prodUnits h.unit).2.isUnit⟩
  mpr h := (prodUnits.symm (h.1.unit, h.2.unit)).isUnit

@[to_additive]
/-
**MulEquiv._root_.Prod.instSubsingletonUnits** 是 Mathlib 中的一个实例，位于命名空间 `MulEquiv
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prod.instSubsingletonUnits [Subsingleton Mˣ] [Subsingleton Nˣ] :
    Subsingleton (M × N)ˣ :=
  .units_of_isUnit <| by simp [Prod.isUnit_iff, Prod.ext_iff]

end

end MulEquiv

namespace Units

open MulOpposite

/-- Canonical homomorphism of monoids from `αˣ` into `α × αᵐᵒᵖ`.
Used mainly to define the natural topology of `αˣ`. -/
@[to_additive (attr := simps)
      /-- Canonical homomorphism of additive monoids from `AddUnits α` into `α × αᵃᵒᵖ`.
      Used mainly to define the natural topology of `AddUnits α`. -/]
/-
**Units.embedProduct** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：embedProduct (α : Type*) [Monoid α] : αˣ ->* α × αᵐᵒᵖ where toFun x
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def embedProduct (α : Type*) [Monoid α] : αˣ →* α × αᵐᵒᵖ where
  toFun x := ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]

@[to_additive]
/-
**Units.embedProduct_injective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (embedP
roduct α)
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (embedProduct α) :=
  fun _ _ h => Units.ext <| (congr_arg Prod.fst h :)

end Units

/-! ### Multiplication and division as homomorphisms -/


section BundledMulDiv

variable {α : Type*}

/-- Multiplication as a multiplicative homomorphism. -/
@[to_additive (attr := simps) /-- Addition as an additive homomorphism. -/]
/-
**mulMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulMulHom [CommSemigroup α] : α × α ->ₙ* α where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication as a multiplicative homomorphism.
-/
def mulMulHom [CommSemigroup α] :
    α × α →ₙ* α where
  toFun a := a.1 * a.2
  map_mul' _ _ := mul_mul_mul_comm _ _ _ _

/-- Multiplication as a monoid homomorphism. -/
@[to_additive (attr := simps) /-- Addition as an additive monoid homomorphism. -/]
/-
**mulMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulMonoidHom [CommMonoid α] : α × α ->* α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication as a monoid homomorphism.
-/
def mulMonoidHom [CommMonoid α] : α × α →* α :=
  { mulMulHom with map_one' := mul_one _ }

/-- Division as a monoid homomorphism. -/
@[to_additive (attr := simps) /-- Subtraction as an additive monoid homomorphism. -/]
/-
**divMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：divMonoidHom [DivisionCommMonoid α] : α × α ->* α where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Division as a monoid homomorphism.
-/
def divMonoidHom [DivisionCommMonoid α] : α × α →* α where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _

end BundledMulDiv

