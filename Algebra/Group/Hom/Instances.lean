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
/-
**OneHom.instPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.instPow [One M] [Monoid N] : Pow (OneHom M N) Nat where pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OneHom.instPow [One M] [Monoid N] : Pow (OneHom M N) ℕ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp }

@[to_additive]
/-
**MonoidHom.instPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.instPow [MulOneClass M] [CommMonoid N] : Pow (M ->* N) Nat where
 pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MonoidHom.instPow [MulOneClass M] [CommMonoid N] : Pow (M →* N) ℕ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_pow] }

@[to_additive (attr := simp)]
/-
**OneHom.pow_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OneHom.pow_apply [One M] [Monoid N] (f : OneHom M N) (n : Nat) (x : M) : (
f ^ n) x = f x ^ n
参数：f : OneHom M N；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma OneHom.pow_apply [One M] [Monoid N] (f : OneHom M N) (n : ℕ) (x : M) :
    (f ^ n) x = f x ^ n :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.pow_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.pow_apply [MulOneClass M] [CommMonoid N] (f : M ->* N) (n : Nat)
 (x : M) : (f ^ n) x = f x ^ n
参数：f : M ->* N；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonoidHom.pow_apply [MulOneClass M] [CommMonoid N] (f : M →* N) (n : ℕ) (x : M) :
    (f ^ n) x = f x ^ n :=
  rfl

/-- `OneHom M N` is a `Monoid` if `N` is. -/
@[to_additive /-- `ZeroHom M N` is an `AddMonoid` if `N` is. -/]
/-
**OneHom.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.instMonoid [One M] [Monoid N] : Monoid (OneHom M N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OneHom M N` is a `Monoid` if `N` is.
-/
instance OneHom.instMonoid [One M] [Monoid N] : Monoid (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.monoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- `OneHom M N` is a `CommMonoid` if `N` is commutative. -/
@[to_additive /-- `ZeroHom M N` is an `AddCommMonoid` if `N` is commutative. -/]
/-
**OneHom.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.instCommMonoid [One M] [CommMonoid N] : CommMonoid (OneHom M N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OneHom M N` is a `CommMonoid` if `N` is commutative.
-/
instance OneHom.instCommMonoid [One M] [CommMonoid N] : CommMonoid (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- `(M →* N)` is a `CommMonoid` if `N` is commutative. -/
@[to_additive /-- `(M →+ N)` is an `AddCommMonoid` if `N` is commutative. -/]
/-
**MonoidHom.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.instCommMonoid [MulOneClass M] [CommMonoid N] : CommMonoid (M ->
* N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(M →* N)` is a `CommMonoid` if `N` is commutative.
-/
instance MonoidHom.instCommMonoid [MulOneClass M] [CommMonoid N] : CommMonoid (M →* N) :=
  fast_instance%
    DFunLike.coe_injective.commMonoid DFunLike.coe rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/-
**OneHom.instZPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.instZPow [One M] [Group N] : Pow (OneHom M N) Int where pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OneHom.instZPow [One M] [Group N] : Pow (OneHom M N) ℤ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp }

@[to_additive]
/-
**MonoidHom.instZPow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.instZPow [MulOneClass M] [CommGroup N] : Pow (M ->* N) Int where
 pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MonoidHom.instZPow [MulOneClass M] [CommGroup N] : Pow (M →* N) ℤ where
  pow f n :=
    { toFun := f ^ n
      map_one' := by simp
      map_mul' x y := by simp [mul_zpow] }

@[to_additive (attr := simp)]
/-
**OneHom.zpow_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OneHom.zpow_apply [One M] [Group N] (f : OneHom M N) (z : Int) (x : M) : (
f ^ z) x = f x ^ z
参数：f : OneHom M N；z : Int；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma OneHom.zpow_apply [One M] [Group N] (f : OneHom M N) (z : ℤ) (x : M) :
    (f ^ z) x = f x ^ z :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.zpow_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.zpow_apply [MulOneClass M] [CommGroup N] (f : M ->* N) (z : Int)
 (x : M) : (f ^ z) x = f x ^ z
参数：f : M ->* N；z : Int；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MonoidHom.zpow_apply [MulOneClass M] [CommGroup N] (f : M →* N) (z : ℤ) (x : M) :
    (f ^ z) x = f x ^ z :=
  rfl

/-- If `G` is a group, then so is `OneHom M G`. -/
@[to_additive /-- If `G` is an additive group, then so is `ZeroHom M G`. -/]
/-
**OneHom.instGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.instGroup [One M] [Group N] : Group (OneHom M N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a group, then so is `OneHom M G`.
-/
instance OneHom.instGroup [One M] [Group N] : Group (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.group DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- If `G` is a commutative group, then so is `OneHom M G`. -/
@[to_additive /-- If `G` is an additive commutative group, then so is `ZeroHom M G`. -/]
/-
**OneHom.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OneHom.instCommGroup [One M] [CommGroup N] : CommGroup (OneHom M N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is a commutative group, then so is `OneHom M G`.
-/
instance OneHom.instCommGroup [One M] [CommGroup N] : CommGroup (OneHom M N) :=
  fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- If `G` is a commutative group, then `M →* G` is a commutative group too. -/
@[to_additive /-- If `G` is an additive commutative group, then `M →+ G` is an additive commutative
      group too. -/]
/-
**MonoidHom.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonoidHom.instCommGroup [MulOneClass M] [CommGroup N] : CommGroup (M ->* N
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MonoidHom.instCommGroup [MulOneClass M] [CommGroup N] : CommGroup (M →* N) :=
  fast_instance%
    DFunLike.coe_injective.commGroup DFunLike.coe
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [MulOneClass N] [IsLeftCancelMul N] : IsLeftCancelMul (OneHom M N) :=
  DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass M] [CommMonoid N] [IsLeftCancelMul N] : IsLeftCancelMul (M →* N) :=
  DFunLike.coe_injective.isLeftCancelMul _ fun _ _ => rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [MulOneClass N] [IsRightCancelMul N] : IsRightCancelMul (OneHom M N) :=
  DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass M] [CommMonoid N] [IsRightCancelMul N] : IsRightCancelMul (M →* N) :=
  DFunLike.coe_injective.isRightCancelMul _ fun _ _ => rfl

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [MulOneClass N] [IsCancelMul N] : IsCancelMul (OneHom M N) where

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass M] [CommMonoid N] [IsCancelMul N] : IsCancelMul (M →* N) where

section End

/-
**AddMonoid.End.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.End.instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (AddMono
id.End M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddMonoid.End.instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (AddMonoid.End M) :=
  inferInstanceAs <| AddCommMonoid (M →+ M)

@[simp]
/-
**AddMonoid.End.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.End.zero_apply [AddCommMonoid M] (m : M) : (0 : AddMonoid.End M)
 m = 0
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoid.End.zero_apply [AddCommMonoid M] (m : M) : (0 : AddMonoid.End M) m = 0 :=
  rfl

-- Note: `@[simp]` omitted because `(1 : AddMonoid.End M) = id` by `AddMonoid.End.coe_one`
/-
**AddMonoid.End.one_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.End.one_apply [AddZeroClass M] (m : M) : (1 : AddMonoid.End M) m
 = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoid.End.one_apply [AddZeroClass M] (m : M) : (1 : AddMonoid.End M) m = m :=
  rfl
/-
**AddMonoid.End.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.End.instAddCommGroup [AddCommGroup M] : AddCommGroup (AddMonoid.
End M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddMonoid.End.instAddCommGroup [AddCommGroup M] : AddCommGroup (AddMonoid.End M) :=
  inferInstanceAs <| AddCommGroup (M →+ M)
/-
**AddMonoid.End.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.End.instIntCast [AddCommGroup M] : IntCast (AddMonoid.End M) whe
re intCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AddMonoid.End.instIntCast [AddCommGroup M] : IntCast (AddMonoid.End M) where
  intCast := fun z => z • 1

/-- See also `AddMonoid.End.intCast_def`. -/
@[simp]
/-
**AddMonoid.End.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoid.End.intCast_apply [AddCommGroup M] (z : Int) (m : M) : (↑z : Add
Monoid.End M) m = z • m
参数：z : Int；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `AddMonoid.End.intCast_def`.
-/
theorem AddMonoid.End.intCast_apply [AddCommGroup M] (z : ℤ) (m : M) :
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
/-
**MonoidHom.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [inst_1 : MulOne N] {f g
 : M →* N}, f = g ↔ ∀ (x : M), f x = g x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M →* N →* P} :
    f = g ↔ ∀ x y, f x y = g x y :=
  DFunLike.ext_iff.trans <| forall_congr' fun _ => DFunLike.ext_iff

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive /-- `flip` arguments of `f : M →+ N →+ P` -/]
/-
**MonoidHom.flip** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M 
->* N ->* P) : N ->* M ->* P where toFun y
参数：f : M ->* N ->* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`flip` arguments of `f : M →* N →* P`
-/
def flip {mM : MulOneClass M} {mN : MulOneClass N} {mP : CommMonoid P} (f : M →* N →* P) :
    N →* M →* P where
  toFun y :=
    { toFun := fun x => f x y,
      map_one' := by simp [f.map_one, one_apply],
      map_mul' := fun x₁ x₂ => by simp [f.map_mul, mul_apply] }
  map_one' := ext fun x => (f x).map_one
  map_mul' y₁ y₂ := ext fun x => (f x).map_mul y₁ y₂

@[to_additive (attr := simp)]
/-
**MonoidHom.flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f :
 M ->* N ->* P) (x : M) (y : N) : f.flip y x = f x y
参数：f : M ->* N ->* P；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (x : M) (y : N) : f.flip y x = f x y :=
  rfl

@[to_additive]
/-
**MonoidHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [inst_1 : MulOne N] (f :
 M →* N), f 1 = 1
参数：f : M →* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
-/
theorem map_one₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (n : N) : f 1 n = 1 :=
  (flip f n).map_one

@[to_additive]
/-
**MonoidHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [inst_1 : MulOne N] (f :
 M →* N) (a b : M), f (a * b) = f a * f b
参数：f : M →* N；a b : M；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
-/
theorem map_mul₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n :=
  (flip f n).map_mul _ _

@[to_additive]
/-
**MonoidHom.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : DivisionMonoid 
β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
参数：f : α →* β；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
theorem map_inv₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M →* N →* P) (m : M)
    (n : N) : f m⁻¹ n = (f m n)⁻¹ :=
  (flip f n).map_inv _

@[to_additive]
/-
**MonoidHom.map_div** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : DivisionMonoid 
β] (f : α →* β) (g h : α),   f (g / h) = f g / f h
参数：f : α →* β；g h : α；g / h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
-/
theorem map_div₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ / m₂) n = f m₁ n / f m₂ n :=
  (flip f n).map_div _ _

/-- Evaluation of a `MonoidHom` at a point as a monoid homomorphism. See also `MonoidHom.apply`
for the evaluation of any function at a point. -/
@[to_additive (attr := simps!)
      /-- Evaluation of an `AddMonoidHom` at a point as an additive monoid homomorphism.
      See also `AddMonoidHom.apply` for the evaluation of any function at a point. -/]
/-
**MonoidHom.eval** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：eval [MulOneClass M] [CommMonoid N] : M ->* (M ->* N) ->* N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def eval [MulOneClass M] [CommMonoid N] : M →* (M →* N) →* N :=
  (MonoidHom.id (M →* N)).flip

/-- The expression `fun g m ↦ g (f m)` as a `MonoidHom`.
Equivalently, `(fun g ↦ MonoidHom.comp g f)` as a `MonoidHom`. -/
@[to_additive (attr := simps!)
      /-- The expression `fun g m ↦ g (f m)` as an `AddMonoidHom`.
      Equivalently, `(fun g ↦ AddMonoidHom.comp g f)` as an `AddMonoidHom`.

      This also exists in a `LinearMap` version, `LinearMap.lcomp`. -/]
/-
**MonoidHom.compHom'** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：compHom' [MulOneClass M] [MulOneClass N] [CommMonoid P] (f : M ->* N) : (N
 ->* P) ->* M ->* P
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compHom' [MulOneClass M] [MulOneClass N] [CommMonoid P] (f : M →* N) : (N →* P) →* M →* P :=
  flip <| eval.comp f

/-- Composition of monoid morphisms (`MonoidHom.comp`) as a monoid morphism.

Note that unlike `MonoidHom.comp_hom'` this requires commutativity of `N`. -/
@[to_additive (attr := simps)
      /-- Composition of additive monoid morphisms (`AddMonoidHom.comp`) as an additive
      monoid morphism.

      Note that unlike `AddMonoidHom.comp_hom'` this requires commutativity of `N`.

      This also exists in a `LinearMap` version, `LinearMap.llcomp`. -/]
/-
**MonoidHom.compHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：compHom [MulOneClass M] [CommMonoid N] [CommMonoid P] : (N ->* P) ->* (M -
>* N) ->* M ->* P where toFun g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.comp_mul`：comp_mul [CommMonoid P] (g : N ->* P) (f₁ f₂ : M ->*
 N) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂
-/
def compHom [MulOneClass M] [CommMonoid N] [CommMonoid P] :
    (N →* P) →* (M →* N) →* M →* P where
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
/-
**MonoidHom.flipHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：flipHom {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} : (M ->
* N ->* P) ->* N ->* M ->* P where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def flipHom {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} :
    (M →* N →* P) →* N →* M →* P where
  toFun := MonoidHom.flip
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The expression `fun m q ↦ f m (g q)` as a `MonoidHom`.

Note that the expression `fun q n ↦ f (g q) n` is simply `MonoidHom.comp`. -/
@[to_additive
      /-- The expression `fun m q ↦ f m (g q)` as an `AddMonoidHom`.

      Note that the expression `fun q n ↦ f (g q) n` is simply `AddMonoidHom.comp`.

      This also exists as a `LinearMap` version, `LinearMap.compl₂` -/]
/-
**MonoidHom.compl** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compl₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q] (f : M →* N →* P)
    (g : Q →* N) : M →* Q →* P :=
  (compHom' g).comp f

@[to_additive (attr := simp)]
/-
**MonoidHom.compl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q]
    (f : M →* N →* P) (g : Q →* N) (m : M) (q : Q) : (compl₂ f g) m q = f m (g q) :=
  rfl

/-- The expression `fun m n ↦ g (f m n)` as a `MonoidHom`. -/
@[to_additive
      /-- The expression `fun m n ↦ g (f m n)` as an `AddMonoidHom`.

      This also exists as a `LinearMap` version, `LinearMap.compr₂` -/]
/-
**MonoidHom.compr** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compr₂ [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M →* N →* P)
    (g : P →* Q) : M →* N →* Q :=
  (compHom g).comp f

@[to_additive (attr := simp)]
/-
**MonoidHom.compr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compr₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M →* N →* P)
    (g : P →* Q) (m : M) (n : N) : (compr₂ f g) m n = g (f m n) :=
  rfl

end MonoidHom

