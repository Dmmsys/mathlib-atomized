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
/--
theorem `one_mk_mul_one_mk` / 定理 `one_mk_mul_one_mk`

English:
theorem one_mk_mul_one_mk
  given: [MulOneClass M] [Mul N] (b₁ b₂ : N)
  proof: by
  rw [mk_mul_mk]; rw [mul_one]

@[to_additive]

中文:
定理 one_mk_mul_one_mk
  条件: [MulOneClass M] [Mul N] (b₁ b₂ : N)
  证明: by
  rw [mk_mul_mk]; rw [mul_one]

@[to_additive]

Depends on / 依赖: mk_mul_mk, mul_one
-/
theorem one_mk_mul_one_mk [MulOneClass M] [Mul N] (b₁ b₂ : N) :
    ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) := by
  rw [mk_mul_mk]; rw [mul_one]

@[to_additive]
/--
theorem `mk_one_mul_mk_one` / 定理 `mk_one_mul_mk_one`

English:
theorem mk_one_mul_mk_one
  given: [Mul M] [MulOneClass N] (a₁ a₂ : M)
  proof: by
  rw [mk_mul_mk]; rw [mul_one]

@[to_additive]

中文:
定理 mk_one_mul_mk_one
  条件: [Mul M] [MulOneClass N] (a₁ a₂ : M)
  证明: by
  rw [mk_mul_mk]; rw [mul_one]

@[to_additive]

Depends on / 依赖: mk_mul_mk, mul_one
-/
theorem mk_one_mul_mk_one [Mul M] [MulOneClass N] (a₁ a₂ : M) :
    (a₁, (1 : N)) * (a₂, 1) = (a₁ * a₂, 1) := by
  rw [mk_mul_mk]; rw [mul_one]

@[to_additive]
/--
theorem `fst_mul_snd` / 定理 `fst_mul_snd`

English:
theorem fst_mul_snd
  given: [MulOneClass M] [MulOneClass N] (p : M × N)
  statement: (p.fst, 1) * (1, p.snd) = p
  proof: Prod.ext (mul_one p.1) (one_mul p.2)

@[to_additive]

中文:
定理 fst_mul_snd
  条件: [MulOneClass M] [MulOneClass N] (p : M × N)
  结论: (p.fst, 1) * (1, p.snd) = p
  证明: Prod.ext (mul_one p.1) (one_mul p.2)

@[to_additive]

Depends on / 依赖: Prod.ext, mul_one, one_mul
-/
theorem fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N) : (p.fst, 1) * (1, p.snd) = p :=
  Prod.ext (mul_one p.1) (one_mul p.2)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveInv
  signature: M] [InvolutiveInv N] : InvolutiveInv (M × N)
  body: { inv_inv := fun _ => Prod.ext (inv_inv _) (inv_inv _) }

@[to_additive]

中文:
实例 [InvolutiveInv
  签名: M] [InvolutiveInv N] : InvolutiveInv (M × N)
  定义体: { inv_inv := fun _ => Prod.ext (inv_inv _) (inv_inv _) }

@[to_additive]

Depends on / 依赖: Prod.ext, inv_inv
-/
instance [InvolutiveInv M] [InvolutiveInv N] : InvolutiveInv (M × N) :=
  { inv_inv := fun _ => Prod.ext (inv_inv _) (inv_inv _) }

@[to_additive]
/--
Instance `isMulCommutative` / 实例 `isMulCommutative`

English:
instance isMulCommutative
  signature: [Mul M] [Mul N] [IsMulCommutative M] [IsMulCommutative N]
  body: by ext <;> apply mul_comm'

@[to_additive]

中文:
实例 isMulCommutative
  签名: [Mul M] [Mul N] [IsMulCommutative M] [IsMulCommutative N]
  定义体: by ext <;> apply mul_comm'

@[to_additive]

Depends on / 依赖: mul_comm
-/
instance isMulCommutative [Mul M] [Mul N] [IsMulCommutative M] [IsMulCommutative N] :
    IsMulCommutative (M × N) where
  is_comm.comm _ _ := by ext <;> apply mul_comm'

@[to_additive]
/--
Instance `commMagma` / 实例 `commMagma`

English:
instance commMagma
  signature: [CommMagma M] [CommMagma N]
  body: by ext <;> apply mul_comm

@[to_additive]

中文:
实例 commMagma
  签名: [CommMagma M] [CommMagma N]
  定义体: by ext <;> apply mul_comm

@[to_additive]

Depends on / 依赖: mul_comm
-/
instance commMagma [CommMagma M] [CommMagma N] : CommMagma (M × N) where
  mul_comm _ _ := by ext <;> apply mul_comm

@[to_additive]
/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: [Semigroup M] [Semigroup N]
  body: by ext <;> exact mul_assoc ..

@[to_additive]

中文:
实例 instSemigroup
  签名: [Semigroup M] [Semigroup N]
  定义体: by ext <;> exact mul_assoc ..

@[to_additive]

Depends on / 依赖: mul_assoc
-/
instance instSemigroup [Semigroup M] [Semigroup N] : Semigroup (M × N) where
  mul_assoc _ _ _ := by ext <;> exact mul_assoc ..

@[to_additive]
/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: [CommSemigroup G] [CommSemigroup H]

中文:
实例 instCommSemigroup
  签名: [CommSemigroup G] [CommSemigroup H]
-/
instance instCommSemigroup [CommSemigroup G] [CommSemigroup H] : CommSemigroup (G × H) where

@[to_additive]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [MulOneClass M] [MulOneClass N]
  body: by ext <;> exact one_mul _
  mul_one _ := by ext <;> exact mul_one _

@[to_additive]

中文:
实例 instMulOneClass
  签名: [MulOneClass M] [MulOneClass N]
  定义体: by ext <;> exact one_mul _
  mul_one _ := by ext <;> exact mul_one _

@[to_additive]

Depends on / 依赖: mul_one, one_mul
-/
instance instMulOneClass [MulOneClass M] [MulOneClass N] : MulOneClass (M × N) where
  one_mul _ := by ext <;> exact one_mul _
  mul_one _ := by ext <;> exact mul_one _

@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid M] [Monoid N]
  body: { npow := fun z a => ⟨NPow.npow z a.1, NPow.npow z a.2⟩,
    npow_zero := fun _ => Prod.ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun _ _ => Prod.ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    one_mul := by simp,
    mul_one := by simp }

@[to_additive]

中文:
实例 instMonoid
  签名: [Monoid M] [Monoid N]
  定义体: { npow := fun z a => ⟨NPow.npow z a.1, NPow.npow z a.2⟩,
    npow_zero := fun _ => Prod.ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun _ _ => Prod.ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    one_mul := by simp,
    mul_one := by simp }

@[to_additive]

Depends on / 依赖: Monoid, Monoid.npow_succ, Monoid.npow_zero, NPow.npow, Prod.ext, mul_one, npow_succ, npow_zero, one_mul
-/
instance instMonoid [Monoid M] [Monoid N] : Monoid (M × N) :=
  { npow := fun z a => ⟨NPow.npow z a.1, NPow.npow z a.2⟩,
    npow_zero := fun _ => Prod.ext (Monoid.npow_zero _) (Monoid.npow_zero _),
    npow_succ := fun _ _ => Prod.ext (Monoid.npow_succ _ _) (Monoid.npow_succ _ _),
    one_mul := by simp,
    mul_one := by simp }

@[to_additive]
/--
Instance `instIsMulTorsionFree` / 实例 `instIsMulTorsionFree`

English:
instance instIsMulTorsionFree
  signature: [Monoid M] [Monoid N] [IsMulTorsionFree M] [IsMulTorsionFree N]
  body: by
    ext <;> apply pow_left_injective hn; exacts [congr(($hab).1), congr(($hab).2)]

@[to_additive Prod.subNegMonoid]

中文:
实例 instIsMulTorsionFree
  签名: [Monoid M] [Monoid N] [IsMulTorsionFree M] [IsMulTorsionFree N]
  定义体: by
    ext <;> apply pow_left_injective hn; exacts [congr(($hab).1), congr(($hab).2)]

@[to_additive Prod.subNegMonoid]

Depends on / 依赖: exacts, pow_left_injective
-/
instance instIsMulTorsionFree [Monoid M] [Monoid N] [IsMulTorsionFree M] [IsMulTorsionFree N] :
    IsMulTorsionFree (M × N) where
  pow_left_injective n hn a b hab := by
    ext <;> apply pow_left_injective hn; exacts [congr(($hab).1), congr(($hab).2)]

@[to_additive Prod.subNegMonoid]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivInvMonoid
  signature: G] [DivInvMonoid H] : DivInvMonoid (G × H) where
  body: by ext <;> exact div_eq_mul_inv ..
  zpow z a := ⟨ZPow.zpow z a.1, ZPow.zpow z a.2⟩
  zpow_zero' _ := by ext <;> exact DivInvMonoid.zpow_zero' _
  zpow_succ' _ _ := by ext <;> exact DivInvMonoid.zpow_succ' ..
  zpow_neg' _ _ := by ext <;> exact DivInvMonoid.zpow_neg' ..

@[to_additive]

中文:
实例 [DivInvMonoid
  签名: G] [DivInvMonoid H] : DivInvMonoid (G × H) where
  定义体: by ext <;> exact div_eq_mul_inv ..
  zpow z a := ⟨ZPow.zpow z a.1, ZPow.zpow z a.2⟩
  zpow_zero' _ := by ext <;> exact DivInvMonoid.zpow_zero' _
  zpow_succ' _ _ := by ext <;> exact DivInvMonoid.zpow_succ' ..
  zpow_neg' _ _ := by ext <;> exact DivInvMonoid.zpow_neg' ..

@[to_additive]

Depends on / 依赖: DivInvMonoid, DivInvMonoid.zpow_neg, DivInvMonoid.zpow_succ, DivInvMonoid.zpow_zero, ZPow.zpow, div_eq_mul_inv, zpow_neg, zpow_succ, zpow_zero
-/
instance [DivInvMonoid G] [DivInvMonoid H] : DivInvMonoid (G × H) where
  div_eq_mul_inv _ _ := by ext <;> exact div_eq_mul_inv ..
  zpow z a := ⟨ZPow.zpow z a.1, ZPow.zpow z a.2⟩
  zpow_zero' _ := by ext <;> exact DivInvMonoid.zpow_zero' _
  zpow_succ' _ _ := by ext <;> exact DivInvMonoid.zpow_succ' ..
  zpow_neg' _ _ := by ext <;> exact DivInvMonoid.zpow_neg' ..

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionMonoid
  signature: G] [DivisionMonoid H] : DivisionMonoid (G × H)
  body: { mul_inv_rev := fun _ _ => Prod.ext (mul_inv_rev _ _) (mul_inv_rev _ _),
    inv_eq_of_mul := fun _ _ h =>
      Prod.ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h),
    inv_inv := by simp }

@[to_additive SubtractionCommMonoid]

中文:
实例 [DivisionMonoid
  签名: G] [DivisionMonoid H] : DivisionMonoid (G × H)
  定义体: { mul_inv_rev := fun _ _ => Prod.ext (mul_inv_rev _ _) (mul_inv_rev _ _),
    inv_eq_of_mul := fun _ _ h =>
      Prod.ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h),
    inv_inv := by simp }

@[to_additive SubtractionCommMonoid]

Depends on / 依赖: Prod.ext, congr_arg, inv_eq_of_mul, inv_eq_of_mul_eq_one_right, inv_inv, mul_inv_rev
-/
instance [DivisionMonoid G] [DivisionMonoid H] : DivisionMonoid (G × H) :=
  { mul_inv_rev := fun _ _ => Prod.ext (mul_inv_rev _ _) (mul_inv_rev _ _),
    inv_eq_of_mul := fun _ _ h =>
      Prod.ext (inv_eq_of_mul_eq_one_right <| congr_arg fst h)
        (inv_eq_of_mul_eq_one_right <| congr_arg snd h),
    inv_inv := by simp }

@[to_additive SubtractionCommMonoid]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionCommMonoid
  signature: G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H)
  body: { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mul_comm g₁, mul_comm h₁]; rfl }

@[to_additive]

中文:
实例 [DivisionCommMonoid
  签名: G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H)
  定义体: { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mul_comm g₁, mul_comm h₁]; rfl }

@[to_additive]

Depends on / 依赖: mk_mul_mk, mul_comm
-/
instance [DivisionCommMonoid G] [DivisionCommMonoid H] : DivisionCommMonoid (G × H) :=
  { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mul_comm g₁, mul_comm h₁]; rfl }

@[to_additive]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group G] [Group H]
  body: by ext <;> exact inv_mul_cancel _

@[to_additive]

中文:
实例 instGroup
  签名: [Group G] [Group H]
  定义体: by ext <;> exact inv_mul_cancel _

@[to_additive]

Depends on / 依赖: inv_mul_cancel
-/
instance instGroup [Group G] [Group H] : Group (G × H) where
  inv_mul_cancel _ := by ext <;> exact inv_mul_cancel _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: G] [Mul H] [IsLeftCancelMul G] [IsLeftCancelMul H] : IsLeftCancelMul (G × H) where
  body: Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2)

@[to_additive]

中文:
实例 [Mul
  签名: G] [Mul H] [IsLeftCancelMul G] [IsLeftCancelMul H] : IsLeftCancelMul (G × H) where
  定义体: Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2)

@[to_additive]

Depends on / 依赖: Prod.ext, Prod.ext_iff, ext_iff, mul_left_cancel
-/
instance [Mul G] [Mul H] [IsLeftCancelMul G] [IsLeftCancelMul H] : IsLeftCancelMul (G × H) where
  mul_left_cancel _ _ _ h :=
      Prod.ext (mul_left_cancel (Prod.ext_iff.1 h).1) (mul_left_cancel (Prod.ext_iff.1 h).2)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: G] [Mul H] [IsRightCancelMul G] [IsRightCancelMul H] : IsRightCancelMul (G × H) where
  body: Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2)

@[to_additive]

中文:
实例 [Mul
  签名: G] [Mul H] [IsRightCancelMul G] [IsRightCancelMul H] : IsRightCancelMul (G × H) where
  定义体: Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2)

@[to_additive]

Depends on / 依赖: Prod.ext, Prod.ext_iff, ext_iff, mul_right_cancel
-/
instance [Mul G] [Mul H] [IsRightCancelMul G] [IsRightCancelMul H] : IsRightCancelMul (G × H) where
  mul_right_cancel _ _ _ h :=
      Prod.ext (mul_right_cancel (Prod.ext_iff.1 h).1) (mul_right_cancel (Prod.ext_iff.1 h).2)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: G] [Mul H] [IsCancelMul G] [IsCancelMul H] : IsCancelMul (G × H) where

中文:
实例 [Mul
  签名: G] [Mul H] [IsCancelMul G] [IsCancelMul H] : IsCancelMul (G × H) where
-/
instance [Mul G] [Mul H] [IsCancelMul G] [IsCancelMul H] : IsCancelMul (G × H) where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelSemigroup
  signature: G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H)
  body: { mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]

中文:
实例 [LeftCancelSemigroup
  签名: G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H)
  定义体: { mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]

Depends on / 依赖: mul_left_cancel
-/
instance [LeftCancelSemigroup G] [LeftCancelSemigroup H] : LeftCancelSemigroup (G × H) :=
  { mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelSemigroup
  signature: G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H)
  body: { mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]

中文:
实例 [RightCancelSemigroup
  签名: G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H)
  定义体: { mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]

Depends on / 依赖: mul_right_cancel
-/
instance [RightCancelSemigroup G] [RightCancelSemigroup H] : RightCancelSemigroup (G × H) :=
  { mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelMonoid
  signature: M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N)
  body: { mul_left_cancel _ _ := by simp }

@[to_additive]

中文:
实例 [LeftCancelMonoid
  签名: M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N)
  定义体: { mul_left_cancel _ _ := by simp }

@[to_additive]

Depends on / 依赖: mul_left_cancel
-/
instance [LeftCancelMonoid M] [LeftCancelMonoid N] : LeftCancelMonoid (M × N) :=
  { mul_left_cancel _ _ := by simp }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelMonoid
  signature: M] [RightCancelMonoid N] : RightCancelMonoid (M × N)
  body: { mul_right_cancel _ _ := by simp }

@[to_additive]

中文:
实例 [RightCancelMonoid
  签名: M] [RightCancelMonoid N] : RightCancelMonoid (M × N)
  定义体: { mul_right_cancel _ _ := by simp }

@[to_additive]

Depends on / 依赖: mul_right_cancel
-/
instance [RightCancelMonoid M] [RightCancelMonoid N] : RightCancelMonoid (M × N) :=
  { mul_right_cancel _ _ := by simp }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelMonoid
  signature: M] [CancelMonoid N] : CancelMonoid (M × N)
  body: { mul_right_cancel _ _ := by simp only [mul_left_inj, imp_self, forall_const] }

@[to_additive]

中文:
实例 [CancelMonoid
  签名: M] [CancelMonoid N] : CancelMonoid (M × N)
  定义体: { mul_right_cancel _ _ := by simp only [mul_left_inj, imp_self, forall_const] }

@[to_additive]

Depends on / 依赖: forall_const, imp_self, mul_left_inj, mul_right_cancel
-/
instance [CancelMonoid M] [CancelMonoid N] : CancelMonoid (M × N) :=
  { mul_right_cancel _ _ := by simp only [mul_left_inj, imp_self, forall_const] }

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid M] [CommMonoid N]
  body: { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }

@[to_additive]

中文:
实例 instCommMonoid
  签名: [CommMonoid M] [CommMonoid N]
  定义体: { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }

@[to_additive]

Depends on / 依赖: mk_mul_mk, mul_comm
-/
instance instCommMonoid [CommMonoid M] [CommMonoid N] : CommMonoid (M × N) :=
  { mul_comm := fun ⟨m₁, n₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm m₁, mul_comm n₁] }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelCommMonoid
  signature: M] [CancelCommMonoid N] : CancelCommMonoid (M × N)
  body: { mul_left_cancel _ _ := by simp }

@[to_additive]

中文:
实例 [CancelCommMonoid
  签名: M] [CancelCommMonoid N] : CancelCommMonoid (M × N)
  定义体: { mul_left_cancel _ _ := by simp }

@[to_additive]

Depends on / 依赖: mul_left_cancel
-/
instance [CancelCommMonoid M] [CancelCommMonoid N] : CancelCommMonoid (M × N) :=
  { mul_left_cancel _ _ := by simp }

@[to_additive]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup G] [CommGroup H]
  body: { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm g₁, mul_comm h₁] }

中文:
实例 instCommGroup
  签名: [CommGroup G] [CommGroup H]
  定义体: { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm g₁, mul_comm h₁] }

Depends on / 依赖: mk_mul_mk, mul_comm
-/
instance instCommGroup [CommGroup G] [CommGroup H] : CommGroup (G × H) :=
  { mul_comm := fun ⟨g₁, h₁⟩ ⟨_, _⟩ => by rw [mk_mul_mk, mk_mul_mk, mul_comm g₁, mul_comm h₁] }

end Prod

section
variable [Mul M] [Mul N]

@[to_additive AddSemiconjBy.prod]
/--
theorem `SemiconjBy.prod` / 定理 `SemiconjBy.prod`

English:
theorem SemiconjBy.prod
  statement: {x y z : M × N}
  proof: Prod.ext hm hn

@[to_additive]

中文:
定理 SemiconjBy.prod
  结论: {x y z : M × N}
  证明: Prod.ext hm hn

@[to_additive]

Depends on / 依赖: Prod.ext
-/
theorem SemiconjBy.prod {x y z : M × N}
    (hm : SemiconjBy x.1 y.1 z.1) (hn : SemiconjBy x.2 y.2 z.2) : SemiconjBy x y z :=
  Prod.ext hm hn

@[to_additive]
/--
theorem `Prod.semiconjBy_iff` / 定理 `Prod.semiconjBy_iff`

English:
theorem Prod.semiconjBy_iff
  given: {x y z : M × N}
  proof: Prod.ext_iff

@[to_additive AddCommute.prod]

中文:
定理 Prod.semiconjBy_iff
  条件: {x y z : M × N}
  证明: Prod.ext_iff

@[to_additive AddCommute.prod]

Depends on / 依赖: Prod.ext_iff, ext_iff
-/
theorem Prod.semiconjBy_iff {x y z : M × N} :
    SemiconjBy x y z ↔ SemiconjBy x.1 y.1 z.1 ∧ SemiconjBy x.2 y.2 z.2 := Prod.ext_iff

@[to_additive AddCommute.prod]
/--
theorem `Commute.prod` / 定理 `Commute.prod`

English:
theorem Commute.prod
  given: {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2)
  statement: Commute x y
  proof: SemiconjBy.prod hm hn

@[to_additive]

中文:
定理 Commute.prod
  条件: {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2)
  结论: Commute x y
  证明: SemiconjBy.prod hm hn

@[to_additive]

Depends on / 依赖: SemiconjBy, SemiconjBy.prod
-/
theorem Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2) : Commute x y :=
  SemiconjBy.prod hm hn

@[to_additive]
/--
theorem `Prod.commute_iff` / 定理 `Prod.commute_iff`

English:
theorem Prod.commute_iff
  given: {x y : M × N}
  proof: semiconjBy_iff

中文:
定理 Prod.commute_iff
  条件: {x y : M × N}
  证明: semiconjBy_iff

Depends on / 依赖: semiconjBy_iff
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
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : M × N ->ₙ* M
  body: ⟨Prod.fst, fun _ _ => rfl⟩

中文:
定义 fst
  签名: : M × N ->ₙ* M
  定义体: ⟨Prod.fst, fun _ _ => rfl⟩

Depends on / 依赖: Prod.fst
-/
def fst : M × N ->ₙ* M :=
  ⟨Prod.fst, fun _ _ => rfl⟩

/-- Given magmas `M`, `N`, the natural projection homomorphism from `M × N` to `N`. -/
@[to_additive
      /-- Given additive magmas `A`, `B`, the natural projection homomorphism
      from `A × B` to `B` -/]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : M × N ->ₙ* N
  body: ⟨Prod.snd, fun _ _ => rfl⟩

中文:
定义 snd
  签名: : M × N ->ₙ* N
  定义体: ⟨Prod.snd, fun _ _ => rfl⟩

Depends on / 依赖: Prod.snd
-/
def snd : M × N ->ₙ* N :=
  ⟨Prod.snd, fun _ _ => rfl⟩

variable {M N}

@[to_additive (attr := simp)]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ⇑(fst M N) = Prod.fst
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_fst
  结论: ⇑(fst M N) = Prod.fst
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ⇑(snd M N) = Prod.snd
  proof: rfl

中文:
定理 coe_snd
  结论: ⇑(snd M N) = Prod.snd
  证明: rfl
-/
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl

/-- Combine two `MonoidHom`s `f : M →ₙ* N`, `g : M →ₙ* P` into
`f.prod g : M →ₙ* (N × P)` given by `(f.prod g) x = (f x, g x)`. -/
@[to_additive prod
      /-- Combine two `AddMonoidHom`s `f : AddHom M N`, `g : AddHom M P` into
      `f.prod g : AddHom M (N × P)` given by `(f.prod g) x = (f x, g x)` -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : M ->ₙ* N) (g : M ->ₙ* P)
  body: Function.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]

中文:
定义 prod
  签名: (f : M ->ₙ* N) (g : M ->ₙ* P)
  定义体: Function.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
-/
protected def prod (f : M ->ₙ* N) (g : M ->ₙ* P) :
    M ->ₙ* N × P where
  toFun := Function.prod f g
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : M ->ₙ* N) (g : M ->ₙ* P)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[to_additive (attr := simp) prod_apply]

中文:
定理 coe_prod
  条件: (f : M ->ₙ* N) (g : M ->ₙ* P)
  结论: ⇑(f.prod g) = Function.prod f g
  证明: rfl

@[to_additive (attr := simp) prod_apply]
-/
theorem coe_prod (f : M ->ₙ* N) (g : M ->ₙ* P) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[to_additive (attr := simp) prod_apply]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (f : M ->ₙ* N) (g : M ->ₙ* P) (x)
  statement: f.prod g x = (f x, g x)
  proof: rfl

@[to_additive (attr := simp) fst_comp_prod]

中文:
定理 prod_apply
  条件: (f : M ->ₙ* N) (g : M ->ₙ* P) (x)
  结论: f.prod g x = (f x, g x)
  证明: rfl

@[to_additive (attr := simp) fst_comp_prod]
-/
theorem prod_apply (f : M ->ₙ* N) (g : M ->ₙ* P) (x) : f.prod g x = (f x, g x) :=
  rfl

@[to_additive (attr := simp) fst_comp_prod]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  given: (f : M ->ₙ* N) (g : M ->ₙ* P)
  statement: (fst N P).comp (f.prod g) = f
  proof: ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]

中文:
定理 fst_comp_prod
  条件: (f : M ->ₙ* N) (g : M ->ₙ* P)
  结论: (fst N P).comp (f.prod g) = f
  证明: ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
-/
theorem fst_comp_prod (f : M ->ₙ* N) (g : M ->ₙ* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  given: (f : M ->ₙ* N) (g : M ->ₙ* P)
  statement: (snd N P).comp (f.prod g) = g
  proof: ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]

中文:
定理 snd_comp_prod
  条件: (f : M ->ₙ* N) (g : M ->ₙ* P)
  结论: (snd N P).comp (f.prod g) = g
  证明: ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
-/
theorem snd_comp_prod (f : M ->ₙ* N) (g : M ->ₙ* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
/--
theorem `prod_unique` / 定理 `prod_unique`

English:
theorem prod_unique
  given: (f : M ->ₙ* N × P)
  statement: ((fst N P).comp f).prod ((snd N P).comp f) = f
  proof: ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

中文:
定理 prod_unique
  条件: (f : M ->ₙ* N × P)
  结论: ((fst N P).comp f).prod ((snd N P).comp f) = f
  证明: ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

Depends on / 依赖: coe_fst, coe_snd, comp_apply, prod_apply
-/
theorem prod_unique (f : M ->ₙ* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]

end Prod

section prodMap

variable {M' : Type*} {N' : Type*} [Mul M] [Mul N] [Mul M'] [Mul N'] [Mul P] (f : M ->ₙ* M')
  (g : N ->ₙ* N')

/-- `Prod.map` as a `MonoidHom`. -/
@[to_additive prodMap /-- `Prod.map` as an `AddMonoidHom` -/]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: : M × N ->ₙ* M' × N'
  body: (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]

中文:
定义 prodMap
  签名: : M × N ->ₙ* M' × N'
  定义体: (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]

Depends on / 依赖: f.comp, g.comp
-/
def prodMap : M × N ->ₙ* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]
/--
theorem `prodMap_def` / 定理 `prodMap_def`

English:
theorem prodMap_def
  statement: prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N))
  proof: rfl

@[to_additive (attr := simp) coe_prodMap]

中文:
定理 prodMap_def
  结论: prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N))
  证明: rfl

@[to_additive (attr := simp) coe_prodMap]
-/
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl

@[to_additive (attr := simp) coe_prodMap]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  statement: ⇑(prodMap f g) = Prod.map f g
  proof: rfl

@[to_additive prod_comp_prodMap]

中文:
定理 coe_prodMap
  结论: ⇑(prodMap f g) = Prod.map f g
  证明: rfl

@[to_additive prod_comp_prodMap]
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[to_additive prod_comp_prodMap]
/--
theorem `prod_comp_prodMap` / 定理 `prod_comp_prodMap`

English:
theorem prod_comp_prodMap
  given: (f : P ->ₙ* M) (g : P ->ₙ* N) (f' : M ->ₙ* M') (g' : N ->ₙ* N')
  proof: rfl

中文:
定理 prod_comp_prodMap
  条件: (f : P ->ₙ* M) (g : P ->ₙ* N) (f' : M ->ₙ* M') (g' : N ->ₙ* N')
  证明: rfl
-/
theorem prod_comp_prodMap (f : P ->ₙ* M) (g : P ->ₙ* N) (f' : M ->ₙ* M') (g' : N ->ₙ* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

section Coprod

variable [Mul M] [Mul N] [CommSemigroup P] (f : M ->ₙ* P) (g : N ->ₙ* P)

/-- Coproduct of two `MulHom`s with the same codomain:
  `f.coprod g (p : M × N) = f p.1 * g p.2`.
  (Commutative codomain; for the general case, see `MulHom.noncommCoprod`) -/
@[to_additive
    /-- Coproduct of two `AddHom`s with the same codomain:
    `f.coprod g (p : M × N) = f p.1 + g p.2`.
    (Commutative codomain; for the general case, see `AddHom.noncommCoprod`) -/]
/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: : M × N ->ₙ* P
  body: f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]

中文:
定义 coprod
  签名: : M × N ->ₙ* P
  定义体: f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]

Depends on / 依赖: f.comp, g.comp
-/
def coprod : M × N ->ₙ* P :=
  f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]
/--
theorem `coprod_apply` / 定理 `coprod_apply`

English:
theorem coprod_apply
  given: (p : M × N)
  statement: f.coprod g p = f p.1 * g p.2
  proof: rfl

@[to_additive]

中文:
定理 coprod_apply
  条件: (p : M × N)
  结论: f.coprod g p = f p.1 * g p.2
  证明: rfl

@[to_additive]
-/
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl

@[to_additive]
/--
theorem `comp_coprod` / 定理 `comp_coprod`

English:
theorem comp_coprod
  given: {Q : Type*} [CommSemigroup Q] (h : P ->ₙ* Q) (f : M ->ₙ* P) (g : N ->ₙ* P)
  proof: ext fun x => by simp

中文:
定理 comp_coprod
  条件: {Q : 类型} [CommSemigroup Q] (h : P ->ₙ* Q) (f : M ->ₙ* P) (g : N ->ₙ* P)
  证明: ext fun x => by simp
-/
theorem comp_coprod {Q : Type*} [CommSemigroup Q] (h : P ->ₙ* Q) (f : M ->ₙ* P) (g : N ->ₙ* P) :
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
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : M × N ->* M
  body: { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

中文:
定义 fst
  签名: : M × N ->* M
  定义体: { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

Depends on / 依赖: Prod.fst, map_mul, map_one
-/
def fst : M × N ->* M :=
  { toFun := Prod.fst,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

/-- Given monoids `M`, `N`, the natural projection homomorphism from `M × N` to `N`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural projection homomorphism
      from `A × B` to `B` -/]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : M × N ->* N
  body: { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

中文:
定义 snd
  签名: : M × N ->* N
  定义体: { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

Depends on / 依赖: Prod.snd, map_mul, map_one
-/
def snd : M × N ->* N :=
  { toFun := Prod.snd,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl }

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `M` to `M × N`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `A` to `A × B`. -/]
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : M ->* M × N
  body: { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }

中文:
定义 inl
  签名: : M ->* M × N
  定义体: { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }

Depends on / 依赖: Prod.ext, map_mul, map_one, one_mul
-/
def inl : M ->* M × N :=
  { toFun := fun x => (x, 1),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext rfl (one_mul 1).symm }

/-- Given monoids `M`, `N`, the natural inclusion homomorphism from `N` to `M × N`. -/
@[to_additive
      /-- Given additive monoids `A`, `B`, the natural inclusion homomorphism
      from `B` to `A × B`. -/]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : N ->* M × N
  body: { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }

中文:
定义 inr
  签名: : N ->* M × N
  定义体: { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }

Depends on / 依赖: Prod.ext, map_mul, map_one, one_mul
-/
def inr : N ->* M × N :=
  { toFun := fun y => (1, y),
    map_one' := rfl,
    map_mul' := fun _ _ => Prod.ext (one_mul 1).symm rfl }

variable {M N}

@[to_additive (attr := simp)]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ⇑(fst M N) = Prod.fst
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_fst
  结论: ⇑(fst M N) = Prod.fst
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_fst : ⇑(fst M N) = Prod.fst :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ⇑(snd M N) = Prod.snd
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_snd
  结论: ⇑(snd M N) = Prod.snd
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_snd : ⇑(snd M N) = Prod.snd :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inl_apply` / 定理 `inl_apply`

English:
theorem inl_apply
  given: (x)
  statement: inl M N x = (x, 1)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inl_apply
  条件: (x)
  结论: inl M N x = (x, 1)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inl_apply (x) : inl M N x = (x, 1) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inr_apply` / 定理 `inr_apply`

English:
theorem inr_apply
  given: (y)
  statement: inr M N y = (1, y)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inr_apply
  条件: (y)
  结论: inr M N y = (1, y)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inr_apply (y) : inr M N y = (1, y) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: (fst M N).comp (inl M N) = id M
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_comp_inl
  结论: (fst M N).comp (inl M N) = id M
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_comp_inl : (fst M N).comp (inl M N) = id M :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  statement: (snd M N).comp (inl M N) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_comp_inl
  结论: (snd M N).comp (inl M N) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_comp_inl : (snd M N).comp (inl M N) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  statement: (fst M N).comp (inr M N) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_comp_inr
  结论: (fst M N).comp (inr M N) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_comp_inr : (fst M N).comp (inr M N) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  statement: (snd M N).comp (inr M N) = id N
  proof: rfl

@[to_additive]

中文:
定理 snd_comp_inr
  结论: (snd M N).comp (inr M N) = id N
  证明: rfl

@[to_additive]
-/
theorem snd_comp_inr : (snd M N).comp (inr M N) = id N :=
  rfl

@[to_additive]
/--
theorem `commute_inl_inr` / 定理 `commute_inl_inr`

English:
theorem commute_inl_inr
  given: (m : M) (n : N)
  statement: Commute (inl M N m) (inr M N n)
  proof: Commute.prod (.one_right m) (.one_left n)

中文:
定理 commute_inl_inr
  条件: (m : M) (n : N)
  结论: Commute (inl M N m) (inr M N n)
  证明: Commute.prod (.one_right m) (.one_left n)

Depends on / 依赖: Commute, Commute.prod, one_left, one_right
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
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : M ->* N) (g : M ->* P)
  body: Function.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]

中文:
定义 prod
  签名: (f : M ->* N) (g : M ->* P)
  定义体: Function.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
-/
protected def prod (f : M ->* N) (g : M ->* P) :
    M ->* N × P where
  toFun := Function.prod f g
  map_one' := Prod.ext f.map_one g.map_one
  map_mul' x y := Prod.ext (f.map_mul x y) (g.map_mul x y)

@[to_additive coe_prod]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : M ->* N) (g : M ->* P)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[to_additive (attr := simp) prod_apply]

中文:
定理 coe_prod
  条件: (f : M ->* N) (g : M ->* P)
  结论: ⇑(f.prod g) = Function.prod f g
  证明: rfl

@[to_additive (attr := simp) prod_apply]

Depends on / 依赖: Encodable, Encodable.ofEquiv, H.equivOp.symm, equivOp, ofEquiv
-/
theorem coe_prod (f : M ->* N) (g : M ->* P) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[to_additive (attr := simp) prod_apply]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (f : M ->* N) (g : M ->* P) (x)
  statement: f.prod g x = (f x, g x)
  proof: rfl

@[to_additive (attr := simp) fst_comp_prod]

中文:
定理 prod_apply
  条件: (f : M ->* N) (g : M ->* P) (x)
  结论: f.prod g x = (f x, g x)
  证明: rfl

@[to_additive (attr := simp) fst_comp_prod]

Depends on / 依赖: Countable, Countable.of_equiv, H.equivOp, equivOp, of_equiv
-/
theorem prod_apply (f : M ->* N) (g : M ->* P) (x) : f.prod g x = (f x, g x) :=
  rfl

@[to_additive (attr := simp) fst_comp_prod]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  given: (f : M ->* N) (g : M ->* P)
  statement: (fst N P).comp (f.prod g) = f
  proof: ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]

中文:
定理 fst_comp_prod
  条件: (f : M ->* N) (g : M ->* P)
  结论: (fst N P).comp (f.prod g) = f
  证明: ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
-/
theorem fst_comp_prod (f : M ->* N) (g : M ->* P) : (fst N P).comp (f.prod g) = f :=
  ext fun _ => rfl

@[to_additive (attr := simp) snd_comp_prod]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  given: (f : M ->* N) (g : M ->* P)
  statement: (snd N P).comp (f.prod g) = g
  proof: ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]

中文:
定理 snd_comp_prod
  条件: (f : M ->* N) (g : M ->* P)
  结论: (snd N P).comp (f.prod g) = g
  证明: ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
-/
theorem snd_comp_prod (f : M ->* N) (g : M ->* P) : (snd N P).comp (f.prod g) = g :=
  ext fun _ => rfl

@[to_additive (attr := simp) prod_unique]
/--
theorem `prod_unique` / 定理 `prod_unique`

English:
theorem prod_unique
  given: (f : M ->* N × P)
  statement: ((fst N P).comp f).prod ((snd N P).comp f) = f
  proof: ext fun _ => by simp

中文:
定理 prod_unique
  条件: (f : M ->* N × P)
  结论: ((fst N P).comp f).prod ((snd N P).comp f) = f
  证明: ext fun _ => by simp
-/
theorem prod_unique (f : M ->* N × P) : ((fst N P).comp f).prod ((snd N P).comp f) = f :=
  ext fun _ => by simp

end Prod

section prodMap

variable {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] [MulOneClass P]
  (f : M ->* M') (g : N ->* N')

/-- `Prod.map` as a `MonoidHom`. -/
@[to_additive prodMap /-- `Prod.map` as an `AddMonoidHom`. -/]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: : M × N ->* M' × N'
  body: (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]

中文:
定义 prodMap
  签名: : M × N ->* M' × N'
  定义体: (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]

Depends on / 依赖: f.comp, g.comp
-/
def prodMap : M × N ->* M' × N' :=
  (f.comp (fst M N)).prod (g.comp (snd M N))

@[to_additive prodMap_def]
/--
theorem `prodMap_def` / 定理 `prodMap_def`

English:
theorem prodMap_def
  statement: prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N))
  proof: rfl

@[to_additive (attr := simp) coe_prodMap]

中文:
定理 prodMap_def
  结论: prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N))
  证明: rfl

@[to_additive (attr := simp) coe_prodMap]
-/
theorem prodMap_def : prodMap f g = (f.comp (fst M N)).prod (g.comp (snd M N)) :=
  rfl

@[to_additive (attr := simp) coe_prodMap]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  statement: ⇑(prodMap f g) = Prod.map f g
  proof: rfl

@[to_additive prod_comp_prodMap]

中文:
定理 coe_prodMap
  结论: ⇑(prodMap f g) = Prod.map f g
  证明: rfl

@[to_additive prod_comp_prodMap]
-/
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl

@[to_additive prod_comp_prodMap]
/--
theorem `prod_comp_prodMap` / 定理 `prod_comp_prodMap`

English:
theorem prod_comp_prodMap
  given: (f : P ->* M) (g : P ->* N) (f' : M ->* M') (g' : N ->* N')
  proof: rfl

中文:
定理 prod_comp_prodMap
  条件: (f : P ->* M) (g : P ->* N) (f' : M ->* M') (g' : N ->* N')
  证明: rfl
-/
theorem prod_comp_prodMap (f : P ->* M) (g : P ->* N) (f' : M ->* M') (g' : N ->* N') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl

end prodMap

section Coprod

variable [CommMonoid P] (f : M ->* P) (g : N ->* P)

/-- Coproduct of two `MonoidHom`s with the same codomain:
  `f.coprod g (p : M × N) = f p.1 * g p.2`.
  (Commutative case; for the general case, see `MonoidHom.noncommCoprod`.) -/
@[to_additive
    /-- Coproduct of two `AddMonoidHom`s with the same codomain:
    `f.coprod g (p : M × N) = f p.1 + g p.2`.
    (Commutative case; for the general case, see `AddHom.noncommCoprod`.) -/]
/--
Definition of `coprod` / `coprod` 的定义

English:
definition coprod
  signature: : M × N ->* P
  body: f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]

中文:
定义 coprod
  签名: : M × N ->* P
  定义体: f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]

Depends on / 依赖: f.comp, g.comp
-/
def coprod : M × N ->* P :=
  f.comp (fst M N) * g.comp (snd M N)

@[to_additive (attr := simp)]
/--
theorem `coprod_apply` / 定理 `coprod_apply`

English:
theorem coprod_apply
  given: (p : M × N)
  statement: f.coprod g p = f p.1 * g p.2
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coprod_apply
  条件: (p : M × N)
  结论: f.coprod g p = f p.1 * g p.2
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coprod_apply (p : M × N) : f.coprod g p = f p.1 * g p.2 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coprod_comp_inl` / 定理 `coprod_comp_inl`

English:
theorem coprod_comp_inl
  statement: (f.coprod g).comp (inl M N) = f
  proof: ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]

中文:
定理 coprod_comp_inl
  结论: (f.coprod g).comp (inl M N) = f
  证明: ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: coprod_apply
-/
theorem coprod_comp_inl : (f.coprod g).comp (inl M N) = f :=
  ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]
/--
theorem `coprod_comp_inr` / 定理 `coprod_comp_inr`

English:
theorem coprod_comp_inr
  statement: (f.coprod g).comp (inr M N) = g
  proof: ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]

中文:
定理 coprod_comp_inr
  结论: (f.coprod g).comp (inr M N) = g
  证明: ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: coprod_apply
-/
theorem coprod_comp_inr : (f.coprod g).comp (inr M N) = g :=
  ext fun x => by simp [coprod_apply]

@[to_additive (attr := simp)]
/--
theorem `coprod_unique` / 定理 `coprod_unique`

English:
theorem coprod_unique
  given: (f : M × N ->* P)
  statement: (f.comp (inl M N)).coprod (f.comp (inr M N)) = f
  proof: ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]

中文:
定理 coprod_unique
  条件: (f : M × N ->* P)
  结论: (f.comp (inl M N)).coprod (f.comp (inr M N)) = f
  证明: ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: coprod_apply, inl_apply, inr_apply, map_mul
-/
theorem coprod_unique (f : M × N ->* P) : (f.comp (inl M N)).coprod (f.comp (inr M N)) = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]
/--
theorem `coprod_inl_inr` / 定理 `coprod_inl_inr`

English:
theorem coprod_inl_inr
  given: {M N : Type*} [CommMonoid M] [CommMonoid N]
  proof: coprod_unique (id <| M × N)

@[to_additive]

中文:
定理 coprod_inl_inr
  条件: {M N : 类型} [CommMonoid M] [CommMonoid N]
  证明: coprod_unique (id <| M × N)

@[to_additive]

Depends on / 依赖: coprod_unique
-/
theorem coprod_inl_inr {M N : Type*} [CommMonoid M] [CommMonoid N] :
    (inl M N).coprod (inr M N) = id (M × N) :=
  coprod_unique (id <| M × N)

@[to_additive]
/--
theorem `comp_coprod` / 定理 `comp_coprod`

English:
theorem comp_coprod
  given: {Q : Type*} [CommMonoid Q] (h : P ->* Q) (f : M ->* P) (g : N ->* P)
  proof: ext fun x => by simp

中文:
定理 comp_coprod
  条件: {Q : 类型} [CommMonoid Q] (h : P ->* Q) (f : M ->* P) (g : N ->* P)
  证明: ext fun x => by simp
-/
theorem comp_coprod {Q : Type*} [CommMonoid Q] (h : P ->* Q) (f : M ->* P) (g : N ->* P) :
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
/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : M × N ≃* N × M
  body: { Equiv.prodComm M N with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodComm]

中文:
定义 prodComm
  签名: : M × N ≃* N × M
  定义体: { Equiv.prodComm M N with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodComm]

Depends on / 依赖: Equiv.prodComm, map_mul, prodComm
-/
def prodComm : M × N ≃* N × M :=
  { Equiv.prodComm M N with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodComm]
/--
theorem `coe_prodComm` / 定理 `coe_prodComm`

English:
theorem coe_prodComm
  statement: ⇑(prodComm : M × N ≃* N × M) = Prod.swap
  proof: rfl

@[to_additive (attr := simp) coe_prodComm_symm]

中文:
定理 coe_prodComm
  结论: ⇑(prodComm : M × N ≃* N × M) = Prod.swap
  证明: rfl

@[to_additive (attr := simp) coe_prodComm_symm]
-/
theorem coe_prodComm : ⇑(prodComm : M × N ≃* N × M) = Prod.swap :=
  rfl

@[to_additive (attr := simp) coe_prodComm_symm]
/--
theorem `coe_prodComm_symm` / 定理 `coe_prodComm_symm`

English:
theorem coe_prodComm_symm
  statement: ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap
  proof: rfl

中文:
定理 coe_prodComm_symm
  结论: ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap
  证明: rfl
-/
theorem coe_prodComm_symm : ⇑(prodComm : M × N ≃* N × M).symm = Prod.swap :=
  rfl

variable [MulOneClass P]

/-- The equivalence between `(M × N) × P` and `M × (N × P)` is multiplicative. -/
@[to_additive prodAssoc
      /-- The equivalence between `(M × N) × P` and `M × (N × P)` is additive. -/]
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : (M × N) × P ≃* M × (N × P)
  body: { Equiv.prodAssoc M N P with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodAssoc]

中文:
定义 prodAssoc
  签名: : (M × N) × P ≃* M × (N × P)
  定义体: { Equiv.prodAssoc M N P with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodAssoc]

Depends on / 依赖: Equiv.prodAssoc, map_mul, prodAssoc
-/
def prodAssoc : (M × N) × P ≃* M × (N × P) :=
  { Equiv.prodAssoc M N P with map_mul' := fun ⟨_, _⟩ ⟨_, _⟩ => rfl }

@[to_additive (attr := simp) coe_prodAssoc]
/--
theorem `coe_prodAssoc` / 定理 `coe_prodAssoc`

English:
theorem coe_prodAssoc
  statement: ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)) = Equiv.prodAssoc M N P
  proof: rfl

@[to_additive (attr := simp) coe_prodAssoc_symm]

中文:
定理 coe_prodAssoc
  结论: ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)) = Equiv.prodAssoc M N P
  证明: rfl

@[to_additive (attr := simp) coe_prodAssoc_symm]
-/
theorem coe_prodAssoc : ⇑(prodAssoc : (M × N) × P ≃* M × (N × P)) = Equiv.prodAssoc M N P :=
  rfl

@[to_additive (attr := simp) coe_prodAssoc_symm]
/--
theorem `coe_prodAssoc_symm` / 定理 `coe_prodAssoc_symm`

English:
theorem coe_prodAssoc_symm
  proof: rfl

中文:
定理 coe_prodAssoc_symm
  证明: rfl
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
/--
Definition of `prodProdProdComm` / `prodProdProdComm` 的定义

English:
definition prodProdProdComm
  signature: : (M × N) × M' × N' ≃* (M × M') × N × N'
  body: { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }

@[to_additive (attr := simp) prodProdProdComm_toEquiv]

中文:
定义 prodProdProdComm
  签名: : (M × N) × M' × N' ≃* (M × M') × N × N'
  定义体: { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }

@[to_additive (attr := simp) prodProdProdComm_toEquiv]

Depends on / 依赖: Equiv.prodProdProdComm, _mnmn, invFun, map_mul, prodProdProdComm
-/
def prodProdProdComm : (M × N) × M' × N' ≃* (M × M') × N × N' :=
  { Equiv.prodProdProdComm M N M' N' with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_mul' := fun _mnmn _mnmn' => rfl }

@[to_additive (attr := simp) prodProdProdComm_toEquiv]
/--
theorem `prodProdProdComm_toEquiv` / 定理 `prodProdProdComm_toEquiv`

English:
theorem prodProdProdComm_toEquiv
  proof: rfl

@[simp]

中文:
定理 prodProdProdComm_toEquiv
  证明: rfl

@[simp]
-/
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm M N M' N' : _ ≃ _) = Equiv.prodProdProdComm M N M' N' :=
  rfl

@[simp]
/--
theorem `prodProdProdComm_symm` / 定理 `prodProdProdComm_symm`

English:
theorem prodProdProdComm_symm
  statement: (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N'
  proof: rfl

中文:
定理 prodProdProdComm_symm
  结论: (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N'
  证明: rfl
-/
theorem prodProdProdComm_symm : (prodProdProdComm M N M' N').symm = prodProdProdComm M M' N N' :=
  rfl

end

/-- Product of multiplicative isomorphisms; the maps come from `Equiv.prodCongr`. -/
@[to_additive prodCongr
/-- Product of additive isomorphisms; the maps come from `Equiv.prodCongr`. -/]
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (f : M ≃* M') (g : N ≃* N')
  body: { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (map_mul f _ _) (map_mul g _ _) }

中文:
定义 prodCongr
  签名: (f : M ≃* M') (g : N ≃* N')
  定义体: { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (map_mul f _ _) (map_mul g _ _) }

Depends on / 依赖: Prod.ext, f.toEquiv.prodCongr, g.toEquiv, map_mul, prodCongr, toEquiv
-/
def prodCongr (f : M ≃* M') (g : N ≃* N') : M × N ≃* M' × N' :=
  { f.toEquiv.prodCongr g.toEquiv with
    map_mul' := fun _ _ => Prod.ext (map_mul f _ _) (map_mul g _ _) }

/-- Multiplying by the trivial monoid doesn't change the structure.

This is the `MulEquiv` version of `Equiv.uniqueProd`. -/
@[to_additive (attr := simps!) uniqueProd /-- Multiplying by the trivial monoid doesn't change the
structure.

This is the `AddEquiv` version of `Equiv.uniqueProd`. -/]
/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: [Unique N]
  body: { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }

中文:
定义 uniqueProd
  签名: [Unique N]
  定义体: { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.uniqueProd, map_mul, uniqueProd
-/
def uniqueProd [Unique N] : N × M ≃* M :=
  { Equiv.uniqueProd M N with map_mul' := fun _ _ => rfl }

/-- Multiplying by the trivial monoid doesn't change the structure.

This is the `MulEquiv` version of `Equiv.prodUnique`. -/
@[to_additive (attr := simps!) prodUnique /-- Multiplying by the trivial monoid doesn't change the
structure.

This is the `AddEquiv` version of `Equiv.prodUnique`. -/]
/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: [Unique N]
  body: { Equiv.prodUnique M N with map_mul' := fun _ _ => rfl }

中文:
定义 prodUnique
  签名: [Unique N]
  定义体: { Equiv.prodUnique M N with map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.prodUnique, map_mul, prodUnique
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
/--
Definition of `prodUnits` / `prodUnits` 的定义

English:
definition prodUnits
  signature: : (M × N)ˣ ≃* Mˣ × Nˣ where
  body: (Units.map (MonoidHom.fst M N)).prod (Units.map (MonoidHom.snd M N))
  invFun u := ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩
  left_inv u := by
    simp only [MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_fst, MonoidHom.coe_snd,
      Prod.mk.eta, Units.coe_map_inv, Units.mk_val]
  right

中文:
定义 prodUnits
  签名: : (M × N)ˣ ≃* Mˣ × Nˣ where
  定义体: (Units.map (MonoidHom.fst M N)).prod (Units.map (MonoidHom.snd M N))
  invFun u := ⟨(u.1, u.2), (↑u.1⁻¹, ↑u.2⁻¹), by simp, by simp⟩
  left_inv u := by
    simp only [MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_fst, MonoidHom.coe_snd,
      Prod.mk.eta, Units.coe_map_inv, Units.mk_val]
  right

Depends on / 依赖: MonoidHom, MonoidHom.fst, MonoidHom.snd, Units.map
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
/--
lemma `_root_.Prod.isUnit_iff` / 引理 `_root_.Prod.isUnit_iff`

English:
lemma _root_.Prod.isUnit_iff
  given: {x : M × N}
  statement: IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 where
  proof: ⟨(prodUnits h.unit).1.isUnit, (prodUnits h.unit).2.isUnit⟩
  mpr h := (prodUnits.symm (h.1.unit, h.2.unit)).isUnit

@[to_additive]

中文:
引理 _root_.Prod.isUnit_iff
  条件: {x : M × N}
  结论: IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 where
  证明: ⟨(prodUnits h.unit).1.isUnit, (prodUnits h.unit).2.isUnit⟩
  mpr h := (prodUnits.symm (h.1.unit, h.2.unit)).isUnit

@[to_additive]

Depends on / 依赖: h.unit, isUnit, prodUnits
-/
lemma _root_.Prod.isUnit_iff {x : M × N} : IsUnit x ↔ IsUnit x.1 ∧ IsUnit x.2 where
  mp h := ⟨(prodUnits h.unit).1.isUnit, (prodUnits h.unit).2.isUnit⟩
  mpr h := (prodUnits.symm (h.1.unit, h.2.unit)).isUnit

@[to_additive]
/--
Instance `_root_.Prod.instSubsingletonUnits` / 实例 `_root_.Prod.instSubsingletonUnits`

English:
instance _root_.Prod.instSubsingletonUnits
  signature: [Subsingleton Mˣ] [Subsingleton Nˣ]
  body: .units_of_isUnit by simp [Prod.isUnit_iff, Prod.ext_iff]

中文:
实例 _root_.Prod.instSubsingletonUnits
  签名: [Subsingleton Mˣ] [Subsingleton Nˣ]
  定义体: .units_of_isUnit by simp [Prod.isUnit_iff, Prod.ext_iff]

Depends on / 依赖: Prod.ext_iff, Prod.isUnit_iff, ext_iff, isUnit_iff, units_of_isUnit
-/
instance _root_.Prod.instSubsingletonUnits [Subsingleton Mˣ] [Subsingleton Nˣ] :
    Subsingleton (M × N)ˣ :=
.units_of_isUnit by simp [Prod.isUnit_iff, Prod.ext_iff]

end

end MulEquiv

namespace Units

open MulOpposite

/-- Canonical homomorphism of monoids from `αˣ` into `α × αᵐᵒᵖ`.
Used mainly to define the natural topology of `αˣ`. -/
@[to_additive (attr := simps)
      /-- Canonical homomorphism of additive monoids from `AddUnits α` into `α × αᵃᵒᵖ`.
      Used mainly to define the natural topology of `AddUnits α`. -/]
/--
Definition of `embedProduct` / `embedProduct` 的定义

English:
definition embedProduct
  signature: (α : Type*) [Monoid α]
  body: ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]

@[to_additive]

中文:
定义 embedProduct
  签名: (α : 类型) [Monoid α]
  定义体: ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]

@[to_additive]
-/
def embedProduct (α : Type*) [Monoid α] : αˣ ->* α × αᵐᵒᵖ where
  toFun x := ⟨x, op ↑x⁻¹⟩
  map_one' := by
    simp only [inv_one, Units.val_one, op_one, Prod.mk_eq_one, and_self_iff]
  map_mul' x y := by simp only [mul_inv_rev, op_mul, Units.val_mul, Prod.mk_mul_mk]

@[to_additive]
/--
theorem `embedProduct_injective` / 定理 `embedProduct_injective`

English:
theorem embedProduct_injective
  given: (α : Type*) [Monoid α]
  statement: Function.Injective (embedProduct α)
  proof: fun _ _ h => Units.ext (congr_arg Prod.fst h :)

中文:
定理 embedProduct_injective
  条件: (α : 类型) [Monoid α]
  结论: Function.Injective (embedProduct α)
  证明: fun _ _ h => Units.ext (congr_arg Prod.fst h :)

Depends on / 依赖: Prod.fst, Units.ext, congr_arg
-/
theorem embedProduct_injective (α : Type*) [Monoid α] : Function.Injective (embedProduct α) :=
fun _ _ h => Units.ext (congr_arg Prod.fst h :)

end Units

/-! ### Multiplication and division as homomorphisms -/


section BundledMulDiv

variable {α : Type*}

/-- Multiplication as a multiplicative homomorphism. -/
@[to_additive (attr := simps) /-- Addition as an additive homomorphism. -/]
/--
Definition of `mulMulHom` / `mulMulHom` 的定义

English:
definition mulMulHom
  signature: [CommSemigroup α]
  body: a.1 * a.2
  map_mul' _ _ := mul_mul_mul_comm _ _ _ _

中文:
定义 mulMulHom
  签名: [CommSemigroup α]
  定义体: a.1 * a.2
  map_mul' _ _ := mul_mul_mul_comm _ _ _ _
-/
def mulMulHom [CommSemigroup α] :
    α × α ->ₙ* α where
  toFun a := a.1 * a.2
  map_mul' _ _ := mul_mul_mul_comm _ _ _ _

/-- Multiplication as a monoid homomorphism. -/
@[to_additive (attr := simps) /-- Addition as an additive monoid homomorphism. -/]
/--
Definition of `mulMonoidHom` / `mulMonoidHom` 的定义

English:
definition mulMonoidHom
  signature: [CommMonoid α]
  body: { mulMulHom with map_one' := mul_one _ }

中文:
定义 mulMonoidHom
  签名: [CommMonoid α]
  定义体: { mulMulHom with map_one' := mul_one _ }

Depends on / 依赖: map_one, mulMulHom, mul_one
-/
def mulMonoidHom [CommMonoid α] : α × α ->* α :=
  { mulMulHom with map_one' := mul_one _ }

/-- Division as a monoid homomorphism. -/
@[to_additive (attr := simps) /-- Subtraction as an additive monoid homomorphism. -/]
/--
Definition of `divMonoidHom` / `divMonoidHom` 的定义

English:
definition divMonoidHom
  signature: [DivisionCommMonoid α]
  body: a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _

中文:
定义 divMonoidHom
  签名: [DivisionCommMonoid α]
  定义体: a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _
-/
def divMonoidHom [DivisionCommMonoid α] : α × α ->* α where
  toFun a := a.1 / a.2
  map_one' := div_one _
  map_mul' _ _ := mul_div_mul_comm _ _ _ _

end BundledMulDiv
