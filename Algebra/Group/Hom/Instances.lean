/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Instances on spaces of monoid and group morphisms

We endow the space of monoid morphisms `M →* N` with a `CommMonoid` structure when the target is
commutative, through pointwise multiplication, and with a `CommGroup` structure when the target
is a commutative group. We also prove the same instances for additive situations.

Since these structures permit morphisms of morphisms, we also provide some composition-like
operations.

Finally, we provide the `Ring` structure on `AddMonoid.End`.
-/

@[expose] public section

assert_not_exists AddMonoidWithOne Ring

universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

@[to_additive]
/--
Instance `OneHom.instPow` / 实例 `OneHom.instPow`

English:
instance OneHom.instPow
  signature: [One M] [Monoid N]
  body: { toFun := f ^ n
      map_one' := by simp }

@[to_additive]

中文:
实例 幺态射.instPow
  签名: [幺 M] [幺半群 N]
  定义体: { toFun := f ^ n
      map_one' := by simp }

@[to_additive]

Depends on / 依赖: map_one
-/
instance OneHom.instPow [One M] [Monoid N] : Pow (OneHom M N) Nat where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp }

@[to_additive]
/--
Instance `MonoidHom.instPow` / 实例 `MonoidHom.instPow`

English:
instance MonoidHom.instPow
  signature: [MulOneClass M] [CommMonoid N]
  body: { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[to_additive (attr := simp)]

中文:
实例 幺半群态射.instPow
  签名: [MulOne类 M] [交换幺半群 N]
  定义体: { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[to_additive (attr := simp)]

Depends on / 依赖: map_mul, map_one, mul_pow
-/
instance MonoidHom.instPow [MulOneClass M] [CommMonoid N] : Pow (M ->* N) Nat where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[to_additive (attr := simp)]
/--
lemma `OneHom.pow_apply` / 引理 `OneHom.pow_apply`

English:
lemma OneHom.pow_apply
  given: [One M] [Monoid N] (f : OneHom M N) (n : Nat) (x : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 幺态射.pow_apply
  条件: [幺 M] [幺半群 N] (f : 幺态射 M N) (n : 自然数) (x : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma OneHom.pow_apply [One M] [Monoid N] (f : OneHom M N) (n : Nat) (x : M) :
    (f ^ n) x = f x ^ n :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `MonoidHom.pow_apply` / 引理 `MonoidHom.pow_apply`

English:
lemma MonoidHom.pow_apply
  given: [MulOneClass M] [CommMonoid N] (f : M ->* N) (n : Nat) (x : M)
  proof: rfl

中文:
引理 幺半群态射.pow_apply
  条件: [MulOne类 M] [交换幺半群 N] (f : M ->* N) (n : 自然数) (x : M)
  证明: rfl
-/
lemma MonoidHom.pow_apply [MulOneClass M] [CommMonoid N] (f : M ->* N) (n : Nat) (x : M) :
    (f ^ n) x = f x ^ n :=
  rfl

/-- `OneHom M N` is a `Monoid` if `N` is. -/
@[to_additive /-- `ZeroHom M N` is an `AddMonoid` if `N` is. -/]
/--
Instance `OneHom.instMonoid` / 实例 `OneHom.instMonoid`

English:
instance OneHom.instMonoid
  signature: [One M] [Monoid N]
  body: fast_instance%
    DFunLike.coe_injective.monoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 幺态射.instMonoid
  签名: [幺 M] [幺半群 N]
  定义体: fast_instance%
    DFunLike.coe_injective.monoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.monoid, coe_injective, fast_instance, monoid
-/
instance OneHom.instMonoid [One M] [Monoid N] : Monoid (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.monoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- `OneHom M N` is a `CommMonoid` if `N` is commutative. -/
@[to_additive /-- `ZeroHom M N` is an `AddCommMonoid` if `N` is commutative. -/]
/--
Instance `OneHom.instCommMonoid` / 实例 `OneHom.instCommMonoid`

English:
instance OneHom.instCommMonoid
  signature: [One M] [CommMonoid N]
  body: fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 幺态射.instCommMonoid
  签名: [幺 M] [交换幺半群 N]
  定义体: fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.commMonoid, coe_injective, commMonoid, fast_instance
-/
instance OneHom.instCommMonoid [One M] [CommMonoid N] : CommMonoid (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- `(M →* N)` is a `CommMonoid` if `N` is commutative. -/
@[to_additive /-- `(M →+ N)` is an `AddCommMonoid` if `N` is commutative. -/]
/--
Instance `MonoidHom.instCommMonoid` / 实例 `MonoidHom.instCommMonoid`

English:
instance MonoidHom.instCommMonoid
  signature: [MulOneClass M] [CommMonoid N]
  body: fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 幺半群态射.instCommMonoid
  签名: [MulOne类 M] [交换幺半群 N]
  定义体: fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.commMonoid, coe_injective, commMonoid, fast_instance
-/
instance MonoidHom.instCommMonoid [MulOneClass M] [CommMonoid N] : CommMonoid (M ->* N) :=
  fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `OneHom.instZPow` / 实例 `OneHom.instZPow`

English:
instance OneHom.instZPow
  signature: [One M] [Group N]
  body: { toFun := f ^ n
      map_one' := by simp }

@[to_additive]

中文:
实例 幺态射.instZPow
  签名: [幺 M] [群 N]
  定义体: { toFun := f ^ n
      map_one' := by simp }

@[to_additive]

Depends on / 依赖: map_one
-/
instance OneHom.instZPow [One M] [Group N] : Pow (OneHom M N) Int where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp }

@[to_additive]
/--
Instance `MonoidHom.instZPow` / 实例 `MonoidHom.instZPow`

English:
instance MonoidHom.instZPow
  signature: [MulOneClass M] [CommGroup N]
  body: { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_zpow] }

@[to_additive (attr := simp)]

中文:
实例 幺半群态射.instZPow
  签名: [MulOne类 M] [交换群 N]
  定义体: { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_zpow] }

@[to_additive (attr := simp)]

Depends on / 依赖: map_mul, map_one, mul_zpow
-/
instance MonoidHom.instZPow [MulOneClass M] [CommGroup N] : Pow (M ->* N) Int where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_zpow] }

@[to_additive (attr := simp)]
/--
lemma `OneHom.zpow_apply` / 引理 `OneHom.zpow_apply`

English:
lemma OneHom.zpow_apply
  given: [One M] [Group N] (f : OneHom M N) (z : Int) (x : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 幺态射.zpow_apply
  条件: [幺 M] [群 N] (f : 幺态射 M N) (z : 整数) (x : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma OneHom.zpow_apply [One M] [Group N] (f : OneHom M N) (z : Int) (x : M) :
    (f ^ z) x = f x ^ z :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `MonoidHom.zpow_apply` / 引理 `MonoidHom.zpow_apply`

English:
lemma MonoidHom.zpow_apply
  given: [MulOneClass M] [CommGroup N] (f : M ->* N) (z : Int) (x : M)
  proof: rfl

中文:
引理 幺半群态射.zpow_apply
  条件: [MulOne类 M] [交换群 N] (f : M ->* N) (z : 整数) (x : M)
  证明: rfl
-/
lemma MonoidHom.zpow_apply [MulOneClass M] [CommGroup N] (f : M ->* N) (z : Int) (x : M) :
    (f ^ z) x = f x ^ z :=
  rfl

/-- If `G` is a group, then so is `OneHom M G`. -/
@[to_additive /-- If `G` is an additive group, then so is `ZeroHom M G`. -/]
/--
Instance `OneHom.instGroup` / 实例 `OneHom.instGroup`

English:
instance OneHom.instGroup
  signature: [One M] [Group N]
  body: fast_instance%
    DFunLike.coe_injective.group DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 幺态射.instGroup
  签名: [幺 M] [群 N]
  定义体: fast_instance%
    DFunLike.coe_injective.group DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.group, coe_injective, fast_instance
-/
instance OneHom.instGroup [One M] [Group N] : Group (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.group DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- If `G` is a commutative group, then so is `OneHom M G`. -/
@[to_additive /-- If `G` is an additive commutative group, then so is `ZeroHom M G`. -/]
/--
Instance `OneHom.instCommGroup` / 实例 `OneHom.instCommGroup`

English:
instance OneHom.instCommGroup
  signature: [One M] [CommGroup N]
  body: fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 幺态射.instCommGroup
  签名: [幺 M] [交换群 N]
  定义体: fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.commGroup, coe_injective, commGroup, fast_instance
-/
instance OneHom.instCommGroup [One M] [CommGroup N] : CommGroup (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- If `G` is a commutative group, then `M →* G` is a commutative group too. -/
@[to_additive /-- If `G` is an additive commutative group, then `M →+ G` is an additive commutative
      group too. -/]
/--
Instance `MonoidHom.instCommGroup` / 实例 `MonoidHom.instCommGroup`

English:
instance MonoidHom.instCommGroup
  signature: [MulOneClass M] [CommGroup N]
  body: fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 幺半群态射.instCommGroup
  签名: [MulOne类 M] [交换群 N]
  定义体: fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective.commGroup, coe_injective, commGroup, fast_instance
-/
instance MonoidHom.instCommGroup [MulOneClass M] [CommGroup N] : CommGroup (M ->* N) :=
  fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [MulOneClass N] [IsLeftCancelMul N] : IsLeftCancelMul (OneHom M N)
  body: DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]

中文:
实例 [幺
  签名: M] [MulOne类 N] [左乘消去 N] : 左乘消去 (幺态射 M N)
  定义体: DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.isLeftCancelMul, coe_injective, isLeftCancelMul
-/
instance [One M] [MulOneClass N] [IsLeftCancelMul N] : IsLeftCancelMul (OneHom M N) :=
  DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: M] [CommMonoid N] [IsLeftCancelMul N] : IsLeftCancelMul (M ->* N)
  body: DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]

中文:
实例 [MulOne类
  签名: M] [交换幺半群 N] [左乘消去 N] : 左乘消去 (M ->* N)
  定义体: DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.isLeftCancelMul, coe_injective, isLeftCancelMul
-/
instance [MulOneClass M] [CommMonoid N] [IsLeftCancelMul N] : IsLeftCancelMul (M ->* N) :=
  DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [MulOneClass N] [IsRightCancelMul N] : IsRightCancelMul (OneHom M N)
  body: DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]

中文:
实例 [幺
  签名: M] [MulOne类 N] [右乘消去 N] : 右乘消去 (幺态射 M N)
  定义体: DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.isRightCancelMul, coe_injective, isRightCancelMul
-/
instance [One M] [MulOneClass N] [IsRightCancelMul N] : IsRightCancelMul (OneHom M N) :=
  DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: M] [CommMonoid N] [IsRightCancelMul N] : IsRightCancelMul (M ->* N)
  body: DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]

中文:
实例 [MulOne类
  签名: M] [交换幺半群 N] [右乘消去 N] : 右乘消去 (M ->* N)
  定义体: DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.isRightCancelMul, coe_injective, isRightCancelMul
-/
instance [MulOneClass M] [CommMonoid N] [IsRightCancelMul N] : IsRightCancelMul (M ->* N) :=
  DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [MulOneClass N] [IsCancelMul N] : IsCancelMul (OneHom M N) where

中文:
实例 [幺
  签名: M] [MulOne类 N] [是消去乘法 N] : 是消去乘法 (幺态射 M N) where
-/
instance [One M] [MulOneClass N] [IsCancelMul N] : IsCancelMul (OneHom M N) where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: M] [CommMonoid N] [IsCancelMul N] : IsCancelMul (M ->* N) where

中文:
实例 [MulOne类
  签名: M] [交换幺半群 N] [是消去乘法 N] : 是消去乘法 (M ->* N) where
-/
instance [MulOneClass M] [CommMonoid N] [IsCancelMul N] : IsCancelMul (M ->* N) where

section End

/--
Instance `AddMonoid.End.instAddCommMonoid` / 实例 `AddMonoid.End.instAddCommMonoid`

English:
instance AddMonoid.End.instAddCommMonoid
  signature: [AddCommMonoid M]
  body: inferInstanceAs AddCommMonoid (M ->+ M)

@[simp]

中文:
实例 加法幺半群.End.instAddCommMonoid
  签名: [加法交换幺半群 M]
  定义体: inferInstanceAs AddCommMonoid (M ->+ M)

@[simp]

Depends on / 依赖: AddCommMonoid
-/
instance AddMonoid.End.instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (AddMonoid.End M) :=
inferInstanceAs AddCommMonoid (M ->+ M)

@[simp]
/--
theorem `AddMonoid.End.zero_apply` / 定理 `AddMonoid.End.zero_apply`

English:
theorem AddMonoid.End.zero_apply
  given: [AddCommMonoid M] (m : M)
  statement: (0 : AddMonoid.End M) m = 0
  proof: rfl

中文:
定理 加法幺半群.End.zero_apply
  条件: [加法交换幺半群 M] (m : M)
  结论: (0 : 加法幺半群.End M) m = 0
  证明: rfl
-/
theorem AddMonoid.End.zero_apply [AddCommMonoid M] (m : M) : (0 : AddMonoid.End M) m = 0 :=
  rfl

-- Note: `@[simp]` omitted because `(1 : AddMonoid.End M) = id` by `AddMonoid.End.coe_one`
/--
theorem `AddMonoid.End.one_apply` / 定理 `AddMonoid.End.one_apply`

English:
theorem AddMonoid.End.one_apply
  given: [AddZeroClass M] (m : M)
  statement: (1 : AddMonoid.End M) m = m
  proof: rfl

中文:
定理 加法幺半群.End.one_apply
  条件: [加法零类 M] (m : M)
  结论: (1 : 加法幺半群.End M) m = m
  证明: rfl
-/
theorem AddMonoid.End.one_apply [AddZeroClass M] (m : M) : (1 : AddMonoid.End M) m = m :=
  rfl

/--
Instance `AddMonoid.End.instAddCommGroup` / 实例 `AddMonoid.End.instAddCommGroup`

English:
instance AddMonoid.End.instAddCommGroup
  signature: [AddCommGroup M]
  body: inferInstanceAs AddCommGroup (M ->+ M)

中文:
实例 加法幺半群.End.instAddCommGroup
  签名: [加法交换群 M]
  定义体: inferInstanceAs AddCommGroup (M ->+ M)

Depends on / 依赖: AddCommGroup
-/
instance AddMonoid.End.instAddCommGroup [AddCommGroup M] : AddCommGroup (AddMonoid.End M) :=
inferInstanceAs AddCommGroup (M ->+ M)

/--
Instance `AddMonoid.End.instIntCast` / 实例 `AddMonoid.End.instIntCast`

English:
instance AddMonoid.End.instIntCast
  signature: [AddCommGroup M]
  body: fun z => z • 1

中文:
实例 加法幺半群.End.inst整数Cast
  签名: [加法交换群 M]
  定义体: fun z => z • 1
-/
instance AddMonoid.End.instIntCast [AddCommGroup M] : IntCast (AddMonoid.End M) where
  intCast := fun z => z • 1

/-- See also `AddMonoid.End.intCast_def`. -/
@[simp]
/--
theorem `AddMonoid.End.intCast_apply` / 定理 `AddMonoid.End.intCast_apply`

English:
theorem AddMonoid.End.intCast_apply
  given: [AddCommGroup M] (z : Int) (m : M)
  proof: rfl

中文:
定理 加法幺半群.End.intCast_apply
  条件: [加法交换群 M] (z : 整数) (m : M)
  证明: rfl
-/
theorem AddMonoid.End.intCast_apply [AddCommGroup M] (z : Int) (m : M) :
    (↑z : AddMonoid.End M) m = z • m :=
  rfl

end End

/-!
### Morphisms of morphisms

The structures above permit morphisms that themselves produce morphisms, provided the codomain
is commutative.
-/


namespace MonoidHom

@[to_additive]
/--
theorem `ext_iff₂` / 定理 `ext_iff₂`

English:
theorem ext_iff₂
  given: {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M ->* N ->* P}
  proof: DFunLike.ext_iff.trans forall_congr' fun _ => DFunLike.ext_iff

中文:
定理 ext_iff₂
  条件: {_ : MulOne类 M} {_ : MulOne类 N} {_ : 交换幺半群 P} {f g : M ->* N ->* P}
  证明: DFunLike.ext_iff.trans forall_congr' fun _ => DFunLike.ext_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, DFunLike.ext_iff.trans, ext_iff, forall_congr
-/
theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M ->* N ->* P} :
    f = g ↔ forall x y, f x y = g x y :=
DFunLike.ext_iff.trans forall_congr' fun _ => DFunLike.ext_iff

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive /-- `flip` arguments of `f : M →+ N →+ P` -/]
/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M ->* N ->* P)
  body: { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂

@[to_additive (attr := simp)]

中文:
定义 flip
  签名: {mM : MulOne类 M} {mN : MulOne类 N} {mP : 交换幺半群 P} (f : M ->* N ->* P)
  定义体: { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂

@[to_additive (attr := simp)]

Depends on / 依赖: f.map_mul, f.map_one, map_mul, map_one, mul_apply, one_apply
-/
def flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M ->* N ->* P) :
    N ->* M ->* P where
  toFun y :=
    { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂

@[to_additive (attr := simp)]
/--
theorem `flip_apply` / 定理 `flip_apply`

English:
theorem flip_apply
  statement: {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M ->* N ->* P)
  proof: rfl

@[to_additive]

中文:
定理 flip_apply
  结论: {_ : MulOne类 M} {_ : MulOne类 N} {_ : 交换幺半群 P} (f : M ->* N ->* P)
  证明: rfl

@[to_additive]
-/
theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M ->* N ->* P)
    (x : M) (y : N) : f.flip y x = f x y :=
  rfl

@[to_additive]
/--
theorem `map_one₂` / 定理 `map_one₂`

English:
theorem map_one₂
  statement: {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M ->* N ->* P)
  proof: (flip f n).map_one

@[to_additive]

中文:
定理 map_one₂
  结论: {_ : MulOne类 M} {_ : MulOne类 N} {_ : 交换幺半群 P} (f : M ->* N ->* P)
  证明: (flip f n).map_one

@[to_additive]

Depends on / 依赖: map_one
-/
theorem map_one₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M ->* N ->* P)
    (n : N) : f 1 n = 1 :=
  (flip f n).map_one

@[to_additive]
/--
theorem `map_mul₂` / 定理 `map_mul₂`

English:
theorem map_mul₂
  statement: {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M ->* N ->* P)
  proof: (flip f n).map_mul _ _

@[to_additive]

中文:
定理 map_mul₂
  结论: {_ : MulOne类 M} {_ : MulOne类 N} {_ : 交换幺半群 P} (f : M ->* N ->* P)
  证明: (flip f n).map_mul _ _

@[to_additive]

Depends on / 依赖: map_mul
-/
theorem map_mul₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M ->* N ->* P)
    (m₁ m₂ : M) (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n :=
  (flip f n).map_mul _ _

@[to_additive]
/--
theorem `map_inv₂` / 定理 `map_inv₂`

English:
theorem map_inv₂
  statement: {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M ->* N ->* P) (m : M)
  proof: (flip f n).map_inv _

@[to_additive]

中文:
定理 map_inv₂
  结论: {_ : 群 M} {_ : MulOne类 N} {_ : 交换群 P} (f : M ->* N ->* P) (m : M)
  证明: (flip f n).map_inv _

@[to_additive]

Depends on / 依赖: map_inv
-/
theorem map_inv₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M ->* N ->* P) (m : M)
    (n : N) : f m⁻¹ n = (f m n)⁻¹ :=
  (flip f n).map_inv _

@[to_additive]
/--
theorem `map_div₂` / 定理 `map_div₂`

English:
theorem map_div₂
  statement: {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M ->* N ->* P)
  proof: (flip f n).map_div _ _

中文:
定理 map_div₂
  结论: {_ : 群 M} {_ : MulOne类 N} {_ : 交换群 P} (f : M ->* N ->* P)
  证明: (flip f n).map_div _ _

Depends on / 依赖: map_div
-/
theorem map_div₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M ->* N ->* P)
    (m₁ m₂ : M) (n : N) : f (m₁ / m₂) n = f m₁ n / f m₂ n :=
  (flip f n).map_div _ _

/-- Evaluation of a `MonoidHom` at a point as a monoid homomorphism. See also `MonoidHom.apply`
for the evaluation of any function at a point. -/
@[to_additive (attr := simps!)
      /-- Evaluation of an `AddMonoidHom` at a point as an additive monoid homomorphism.
      See also `AddMonoidHom.apply` for the evaluation of any function at a point. -/]
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: [MulOneClass M] [CommMonoid N]
  body: (MonoidHom.id (M ->* N)).flip

中文:
定义 eval
  签名: [MulOne类 M] [交换幺半群 N]
  定义体: (MonoidHom.id (M ->* N)).flip

Depends on / 依赖: MonoidHom, MonoidHom.id
-/
def eval [MulOneClass M] [CommMonoid N] : M ->* (M ->* N) ->* N :=
  (MonoidHom.id (M ->* N)).flip

/-- The expression `fun g m ↦ g (f m)` as a `MonoidHom`.
Equivalently, `(fun g ↦ MonoidHom.comp g f)` as a `MonoidHom`. -/
@[to_additive (attr := simps!)
      /-- The expression `fun g m ↦ g (f m)` as an `AddMonoidHom`.
      Equivalently, `(fun g ↦ AddMonoidHom.comp g f)` as an `AddMonoidHom`.

      This also exists in a `LinearMap` version, `LinearMap.lcomp`. -/]
/--
Definition of `compHom'` / `compHom'` 的定义

English:
definition compHom'
  signature: [MulOneClass M] [MulOneClass N] [CommMonoid P] (f : M ->* N)
  body: flip eval.comp f

中文:
定义 compHom'
  签名: [MulOne类 M] [MulOne类 N] [交换幺半群 P] (f : M ->* N)
  定义体: flip eval.comp f

Depends on / 依赖: eval.comp
-/
def compHom' [MulOneClass M] [MulOneClass N] [CommMonoid P] (f : M ->* N) : (N ->* P) ->* M ->* P :=
flip eval.comp f

/-- Composition of monoid morphisms (`MonoidHom.comp`) as a monoid morphism.

Note that unlike `MonoidHom.comp_hom'` this requires commutativity of `N`. -/
@[to_additive (attr := simps)
      /-- Composition of additive monoid morphisms (`AddMonoidHom.comp`) as an additive
      monoid morphism.

      Note that unlike `AddMonoidHom.comp_hom'` this requires commutativity of `N`.

      This also exists in a `LinearMap` version, `LinearMap.llcomp`. -/]
/--
Definition of `compHom` / `compHom` 的定义

English:
definition compHom
  signature: [MulOneClass M] [CommMonoid N] [CommMonoid P]
  body: { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' g₁ g₂ := by
    ext1 f
    exact mul_comp g₁ g₂ f

中文:
定义 compHom
  签名: [MulOne类 M] [交换幺半群 N] [交换幺半群 P]
  定义体: { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' g₁ g₂ := by
    ext1 f
    exact mul_comp g₁ g₂ f

Depends on / 依赖: comp_mul, comp_one, g.comp, map_mul, map_one
-/
def compHom [MulOneClass M] [CommMonoid N] [CommMonoid P] :
    (N ->* P) ->* (M ->* N) ->* M ->* P where
  toFun g := { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' g₁ g₂ := by
    ext1 f
    exact mul_comp g₁ g₂ f

/-- Flipping arguments of monoid morphisms (`MonoidHom.flip`) as a monoid morphism. -/
@[to_additive (attr := simps)
      /-- Flipping arguments of additive monoid morphisms (`AddMonoidHom.flip`)
      as an additive monoid morphism. -/]
/--
Definition of `flipHom` / `flipHom` 的定义

English:
definition flipHom
  signature: {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P}
  body: MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 flipHom
  签名: {_ : MulOne类 M} {_ : MulOne类 N} {_ : 交换幺半群 P}
  定义体: MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: MonoidHom, MonoidHom.flip
-/
def flipHom {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} :
    (M ->* N ->* P) ->* N ->* M ->* P where
  toFun := MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The expression `fun m q ↦ f m (g q)` as a `MonoidHom`.

Note that the expression `fun q n ↦ f (g q) n` is simply `MonoidHom.comp`. -/
@[to_additive
      /-- The expression `fun m q ↦ f m (g q)` as an `AddMonoidHom`.

      Note that the expression `fun q n ↦ f (g q) n` is simply `AddMonoidHom.comp`.

      This also exists as a `LinearMap` version, `LinearMap.compl₂` -/]
/--
Definition of `compl₂` / `compl₂` 的定义

English:
definition compl₂
  signature: [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q] (f : M ->* N ->* P)
  body: (compHom' g).comp f

@[to_additive (attr := simp)]

中文:
定义 compl₂
  签名: [MulOne类 M] [MulOne类 N] [交换幺半群 P] [MulOne类 Q] (f : M ->* N ->* P)
  定义体: (compHom' g).comp f

@[to_additive (attr := simp)]

Depends on / 依赖: compHom
-/
def compl₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q] (f : M ->* N ->* P)
    (g : Q ->* N) : M ->* Q ->* P :=
  (compHom' g).comp f

@[to_additive (attr := simp)]
/--
theorem `compl₂_apply` / 定理 `compl₂_apply`

English:
theorem compl₂_apply
  statement: [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q]
  proof: rfl

中文:
定理 compl₂_apply
  结论: [MulOne类 M] [MulOne类 N] [交换幺半群 P] [MulOne类 Q]
  证明: rfl
-/
theorem compl₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q]
    (f : M ->* N ->* P) (g : Q ->* N) (m : M) (q : Q) : (compl₂ f g) m q = f m (g q) :=
  rfl

/-- The expression `fun m n ↦ g (f m n)` as a `MonoidHom`. -/
@[to_additive
      /-- The expression `fun m n ↦ g (f m n)` as an `AddMonoidHom`.

      This also exists as a `LinearMap` version, `LinearMap.compr₂` -/]
/--
Definition of `compr₂` / `compr₂` 的定义

English:
definition compr₂
  signature: [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M ->* N ->* P)
  body: (compHom g).comp f

@[to_additive (attr := simp)]

中文:
定义 compr₂
  签名: [MulOne类 M] [MulOne类 N] [交换幺半群 P] [交换幺半群 Q] (f : M ->* N ->* P)
  定义体: (compHom g).comp f

@[to_additive (attr := simp)]

Depends on / 依赖: compHom
-/
def compr₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M ->* N ->* P)
    (g : P ->* Q) : M ->* N ->* Q :=
  (compHom g).comp f

@[to_additive (attr := simp)]
/--
theorem `compr₂_apply` / 定理 `compr₂_apply`

English:
theorem compr₂_apply
  statement: [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M ->* N ->* P)
  proof: rfl

中文:
定理 compr₂_apply
  结论: [MulOne类 M] [MulOne类 N] [交换幺半群 P] [交换幺半群 Q] (f : M ->* N ->* P)
  证明: rfl
-/
theorem compr₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M ->* N ->* P)
    (g : P ->* Q) (m : M) (n : N) : (compr₂ f g) m n = g (f m n) :=
  rfl

end MonoidHom
