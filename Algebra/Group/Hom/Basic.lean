/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Additional lemmas about monoid and group homomorphisms

-/

@[expose] public section

-- `NeZero` cannot be additivised, hence its theory should be developed outside of the
-- `Algebra.Group` folder.
assert_not_imported Mathlib.Algebra.NeZero

variable {α M N P : Type*}

-- monoids
variable {G : Type*} {H : Type*}

-- groups
variable {F : Type*}

section CommMonoid
variable [CommMonoid α]

/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive (attr := simps) /-- Multiplication by a natural `n` on a commutative additive monoid,
considered as a morphism of additive monoids. -/]
/--
Definition of `powMonoidHom` / `powMonoidHom` 的定义

English:
definition powMonoidHom
  signature: (n : Nat)
  body: (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n

中文:
定义 powMonoidHom
  签名: (n : 自然数)
  定义体: (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n
-/
def powMonoidHom (n : Nat) : α ->* α where
  toFun := (· ^ n)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b n

end CommMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive (attr := simps) /-- Multiplication by an integer `n` on a commutative additive group,
considered as an additive group homomorphism. -/]
/--
Definition of `zpowGroupHom` / `zpowGroupHom` 的定义

English:
definition zpowGroupHom
  signature: (n : Int)
  body: (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n

中文:
定义 zpowGroupHom
  签名: (n : 整数)
  定义体: (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n
-/
def zpowGroupHom (n : Int) : α ->* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive /-- Negation on a commutative additive group, considered as an additive monoid
homomorphism. -/]
/--
Definition of `invMonoidHom` / `invMonoidHom` 的定义

English:
definition invMonoidHom
  signature: : α ->* α where
  body: Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv

@[to_additive (attr := simp)]

中文:
定义 invMonoidHom
  签名: : α ->* α where
  定义体: Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv

@[to_additive (attr := simp)]

Depends on / 依赖: Inv.inv
-/
def invMonoidHom : α ->* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv

@[to_additive (attr := simp)]
/--
theorem `coe_invMonoidHom` / 定理 `coe_invMonoidHom`

English:
theorem coe_invMonoidHom
  statement: (invMonoidHom : α -> α) = Inv.inv
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_invMonoidHom
  结论: (invMonoidHom : α -> α) = Inv.inv
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_invMonoidHom : (invMonoidHom : α -> α) = Inv.inv := rfl

@[to_additive (attr := simp)]
/--
theorem `invMonoidHom_apply` / 定理 `invMonoidHom_apply`

English:
theorem invMonoidHom_apply
  given: (a : α)
  statement: invMonoidHom a = a⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 invMonoidHom_apply
  条件: (a : α)
  结论: invMonoidHom a = a⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `invMonoidHom_comp_invMonoidHom` / 定理 `invMonoidHom_comp_invMonoidHom`

English:
theorem invMonoidHom_comp_invMonoidHom
  statement: (invMonoidHom (α := α)).comp invMonoidHom = .id _
  proof: by
  ext; simp

中文:
定理 invMonoidHom_comp_invMonoidHom
  结论: (invMonoidHom (α := α)).comp invMonoidHom = .id _
  证明: by
  ext; simp

Depends on / 依赖: invMonoidHom
-/
theorem invMonoidHom_comp_invMonoidHom : (invMonoidHom (α := α)).comp invMonoidHom = .id _ := by
  ext; simp

end DivisionCommMonoid

namespace OneHom

/-- Given two one-preserving morphisms `f`, `g`,
`f * g` is the one-preserving morphism sending `x` to `f x * g x`. -/
@[to_additive /-- Given two zero-preserving morphisms `f`, `g`,
`f + g` is the zero-preserving morphism sending `x` to `f x + g x`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [MulOneClass N] : Mul (OneHom M N) where
  body: { toFun m := f m * g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]

中文:
实例 [One
  签名: M] [MulOneClass N] : Mul (OneHom M N) where
  定义体: { toFun m := f m * g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]

Depends on / 依赖: map_one
-/
instance [One M] [MulOneClass N] : Mul (OneHom M N) where
  mul f g :=
    { toFun m := f m * g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: {M N} [One M] [MulOneClass N] (f g : OneHom M N)
  statement: ⇑(f * g) = ⇑f * ⇑g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mul
  条件: {M N} [One M] [MulOneClass N] (f g : OneHom M N)
  结论: ⇑(f * g) = ⇑f * ⇑g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mul {M N} [One M] [MulOneClass N] (f g : OneHom M N) : ⇑(f * g) = ⇑f * ⇑g := rfl

@[to_additive (attr := simp)]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 mul_apply
  条件: {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) :
    (f * g) x = f x * g x := rfl

@[to_additive]
/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  given: [One M] [One N] [MulOneClass P] (g₁ g₂ : OneHom N P) (f : OneHom M N)
  proof: rfl

中文:
定理 mul_comp
  条件: [One M] [One N] [MulOneClass P] (g₁ g₂ : OneHom N P) (f : OneHom M N)
  证明: rfl
-/
theorem mul_comp [One M] [One N] [MulOneClass P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

/-- Given a one-preserving morphism `f`,
`f⁻¹` is the one-preserving morphism sending `x` to `(f x)⁻¹`. -/
@[to_additive /-- Given a zero-preserving morphism `f`,
`-f` is the zero-preserving morphism sending `x` to `-f x`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [InvOneClass N] : Inv (OneHom M N) where
  body: { toFun m := (f m)⁻¹
      map_one' := by simp }

@[to_additive (attr := norm_cast)]

中文:
实例 [One
  签名: M] [InvOneClass N] : Inv (OneHom M N) where
  定义体: { toFun m := (f m)⁻¹
      map_one' := by simp }

@[to_additive (attr := norm_cast)]

Depends on / 依赖: map_one
-/
instance [One M] [InvOneClass N] : Inv (OneHom M N) where
  inv f :=
    { toFun m := (f m)⁻¹
      map_one' := by simp }

@[to_additive (attr := norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: {M N} [One M] [InvOneClass N] (f : OneHom M N)
  statement: ⇑(f⁻¹) = (⇑f)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_inv
  条件: {M N} [One M] [InvOneClass N] (f : OneHom M N)
  结论: ⇑(f⁻¹) = (⇑f)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_inv {M N} [One M] [InvOneClass N] (f : OneHom M N) : ⇑(f⁻¹) = (⇑f)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 inv_apply
  条件: {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem inv_apply {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M) :
    f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive]
/--
theorem `inv_comp` / 定理 `inv_comp`

English:
theorem inv_comp
  given: [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N)
  proof: rfl

中文:
定理 inv_comp
  条件: [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N)
  证明: rfl
-/
theorem inv_comp [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N) :
    (g⁻¹).comp f = (g.comp f)⁻¹ := rfl

/-- Given two one-preserving morphisms `f`, `g`,
`f / g` is the one-preserving morphism sending `x` to `f x / g x`. -/
@[to_additive /-- Given two zero-preserving morphisms `f`, `g`,
`f - g` is the additive morphism sending `x` to `f x - g x`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: M] [DivisionMonoid N] : Div (OneHom M N) where
  body: { toFun m := f m / g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]

中文:
实例 [One
  签名: M] [DivisionMonoid N] : Div (OneHom M N) where
  定义体: { toFun m := f m / g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]

Depends on / 依赖: map_one
-/
instance [One M] [DivisionMonoid N] : Div (OneHom M N) where
  div f g :=
    { toFun m := f m / g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: {M N} [One M] [DivisionMonoid N] (f g : OneHom M N)
  statement: ⇑(f / g) = ⇑f / ⇑g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_div
  条件: {M N} [One M] [DivisionMonoid N] (f g : OneHom M N)
  结论: ⇑(f / g) = ⇑f / ⇑g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_div {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) : ⇑(f / g) = ⇑f / ⇑g := rfl

@[to_additive (attr := simp)]
/--
theorem `div_apply` / 定理 `div_apply`

English:
theorem div_apply
  given: {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 div_apply
  条件: {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem div_apply {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) (x : M) :
    (f / g) x = f x / g x := rfl

@[to_additive]
/--
theorem `div_comp` / 定理 `div_comp`

English:
theorem div_comp
  given: [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneHom M N)
  proof: rfl

中文:
定理 div_comp
  条件: [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneHom M N)
  证明: rfl
-/
theorem div_comp [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ / g₂).comp f = g₁.comp f / g₂.comp f := rfl

end OneHom

namespace MulHom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive /-- Given two additive morphisms `f`, `g` to an additive commutative semigroup,
`f + g` is the additive morphism sending `x` to `f x + g x`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: M] [CommSemigroup N] : Mul (M ->ₙ* N)
  body: ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul]; rw [g.map_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_comm (f x)] }⟩

@[to_additive (attr := simp)]

中文:
实例 [Mul
  签名: M] [CommSemigroup N] : Mul (M ->ₙ* N)
  定义体: ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul]; rw [g.map_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_comm (f x)] }⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.map_mul, g.map_mul, map_mul, mul_assoc, mul_right_comm
-/
instance [Mul M] [CommSemigroup N] : Mul (M ->ₙ* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul]; rw [g.map_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_comm (f x)] }⟩

@[to_additive (attr := simp)]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: {M N} [Mul M] [CommSemigroup N] (f g : M ->ₙ* N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 mul_apply
  条件: {M N} [Mul M] [CommSemigroup N] (f g : M ->ₙ* N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M ->ₙ* N) (x : M) :
    (f * g) x = f x * g x := rfl

@[to_additive]
/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  given: [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N ->ₙ* P) (f : M ->ₙ* N)
  proof: rfl

@[to_additive]

中文:
定理 mul_comp
  条件: [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N ->ₙ* P) (f : M ->ₙ* N)
  证明: rfl

@[to_additive]
-/
theorem mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N ->ₙ* P) (f : M ->ₙ* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
/--
theorem `comp_mul` / 定理 `comp_mul`

English:
theorem comp_mul
  given: [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N ->ₙ* P) (f₁ f₂ : M ->ₙ* N)
  proof: by
  ext
  simp

中文:
定理 comp_mul
  条件: [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N ->ₙ* P) (f₁ f₂ : M ->ₙ* N)
  证明: by
  ext
  simp
-/
theorem comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N ->ₙ* P) (f₁ f₂ : M ->ₙ* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp

end MulHom

namespace MonoidHom
section Group
variable [Group G]

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`. -/
@[to_additive
  /-- A homomorphism from an additive group to an additive monoid is injective iff
  its kernel is trivial. For the iff statement on the triviality of the kernel,
  see `injective_iff_map_eq_zero'`. -/]
/--
theorem `_root_.injective_iff_map_eq_one` / 定理 `_root_.injective_iff_map_eq_one`

English:
theorem _root_.injective_iff_map_eq_one
  statement: {G H} [Group G] [MulOneClass H]
  proof: ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
mul_inv_eq_one.1 h _ by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

中文:
定理 _root_.injective_iff_map_eq_one
  结论: {G H} [Group G] [MulOneClass H]
  证明: ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
mul_inv_eq_one.1 h _ by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

Depends on / 依赖: map_eq_one_iff, map_mul, map_one, mul_inv_cancel, mul_inv_eq_one
-/
theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ forall a, f a = 1 -> a = 1 :=
  ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
mul_inv_eq_one.1 h _ by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive
  /-- A homomorphism from an additive group to an additive monoid is injective iff its
  kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see
  `injective_iff_map_eq_zero`. -/]
/--
theorem `_root_.injective_iff_map_eq_one'` / 定理 `_root_.injective_iff_map_eq_one'`

English:
theorem _root_.injective_iff_map_eq_one'
  statement: {G H} [Group G] [MulOneClass H]
  proof: (injective_iff_map_eq_one f).trans
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

中文:
定理 _root_.injective_iff_map_eq_one'
  结论: {G H} [Group G] [MulOneClass H]
  证明: (injective_iff_map_eq_one f).trans
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

Depends on / 依赖: H.symm, Iff.mp, forall_congr, injective_iff_map_eq_one, map_one
-/
theorem _root_.injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ forall a, f a = 1 ↔ a = 1 :=
(injective_iff_map_eq_one f).trans
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

/-- Makes a group homomorphism from a proof that the map preserves right division
`fun x y => x * y⁻¹`. See also `MonoidHom.of_map_div` for a version using `fun x y => x / y`.
-/
@[to_additive
  /-- Makes an additive group homomorphism from a proof that the map preserves
  the operation `fun a b => a + -b`. See also `AddMonoidHom.ofMapSub` for a version using
  `fun a b => a - b`. -/]
/--
Definition of `ofMapMulInv` / `ofMapMulInv` 的定义

English:
definition ofMapMulInv
  signature: {H : Type*} [Group H] (f : G -> H)
  body: (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_inv_cancel, one_mul, inv_inv] }

@[to_additive (attr := simp)]

中文:
定义 ofMapMulInv
  签名: {H : 类型} [Group H] (f : G -> H)
  定义体: (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_inv_cancel, one_mul, inv_inv] }

@[to_additive (attr := simp)]

Depends on / 依赖: inv_inv, inv_one, map_div, mul_inv_cancel, one_mul
-/
def ofMapMulInv {H : Type*} [Group H] (f : G -> H)
    (map_div : forall a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G ->* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_inv_cancel, one_mul, inv_inv] }

@[to_additive (attr := simp)]
/--
theorem `coe_of_map_mul_inv` / 定理 `coe_of_map_mul_inv`

English:
theorem coe_of_map_mul_inv
  statement: {H : Type*} [Group H] (f : G -> H)
  proof: rfl

中文:
定理 coe_of_map_mul_inv
  结论: {H : 类型} [Group H] (f : G -> H)
  证明: rfl
-/
theorem coe_of_map_mul_inv {H : Type*} [Group H] (f : G -> H)
    (map_div : forall a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : ↑(ofMapMulInv f map_div) = f :=
  rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive /-- Define a morphism of additive groups given a map which respects difference. -/]
/--
Definition of `ofMapDiv` / `ofMapDiv` 的定义

English:
definition ofMapDiv
  signature: {H : Type*} [Group H] (f : G -> H) (hf : forall x y, f (x / y) = f x / f y)
  body: ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)

@[to_additive (attr := simp)]

中文:
定义 ofMapDiv
  签名: {H : 类型} [Group H] (f : G -> H) (hf : 对任意 x y, f (x / y) = f x / f y)
  定义体: ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, ofMapMulInv
-/
def ofMapDiv {H : Type*} [Group H] (f : G -> H) (hf : forall x y, f (x / y) = f x / f y) : G ->* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)

@[to_additive (attr := simp)]
/--
theorem `coe_of_map_div` / 定理 `coe_of_map_div`

English:
theorem coe_of_map_div
  given: {H : Type*} [Group H] (f : G -> H) (hf : forall x y, f (x / y) = f x / f y)
  proof: rfl

中文:
定理 coe_of_map_div
  条件: {H : 类型} [Group H] (f : G -> H) (hf : 对任意 x y, f (x / y) = f x / f y)
  证明: rfl
-/
theorem coe_of_map_div {H : Type*} [Group H] (f : G -> H) (hf : forall x y, f (x / y) = f x / f y) :
    ↑(ofMapDiv f hf) = f := rfl

end Group

section Mul
variable [MulOneClass M] [CommMonoid N]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul (M ->* N)
  body: ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := by simp,
      map_mul' := fun x y => by
        rw [f.map_mul]; rw [g.map_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_comm (f x)] }⟩

中文:
实例 mul
  签名: : Mul (M ->* N)
  定义体: ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := by simp,
      map_mul' := fun x y => by
        rw [f.map_mul]; rw [g.map_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_comm (f x)] }⟩

Depends on / 依赖: f.map_mul, g.map_mul, map_mul, map_one, mul_assoc, mul_right_comm
-/
instance mul : Mul (M ->* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := by simp,
      map_mul' := fun x y => by
        rw [f.map_mul]; rw [g.map_mul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,
`f + g` is the additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.add

/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (f g : M ->* N) (x : M)
  statement: (f * g) x = f x * g x
  proof: rfl

@[to_additive]

中文:
引理 mul_apply
  条件: (f g : M ->* N) (x : M)
  结论: (f * g) x = f x * g x
  证明: rfl

@[to_additive]
-/
@[to_additive (attr := simp)] lemma mul_apply (f g : M ->* N) (x : M) : (f * g) x = f x * g x := rfl

@[to_additive]
/--
lemma `mul_comp` / 引理 `mul_comp`

English:
lemma mul_comp
  given: [MulOneClass P] (g₁ g₂ : M ->* N) (f : P ->* M)
  proof: rfl

@[to_additive]

中文:
引理 mul_comp
  条件: [MulOneClass P] (g₁ g₂ : M ->* N) (f : P ->* M)
  证明: rfl

@[to_additive]
-/
lemma mul_comp [MulOneClass P] (g₁ g₂ : M ->* N) (f : P ->* M) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
/--
lemma `comp_mul` / 引理 `comp_mul`

English:
lemma comp_mul
  given: [CommMonoid P] (g : N ->* P) (f₁ f₂ : M ->* N)
  proof: by
  ext
  simp

中文:
引理 comp_mul
  条件: [CommMonoid P] (g : N ->* P) (f₁ f₂ : M ->* N)
  证明: by
  ext
  simp
-/
lemma comp_mul [CommMonoid P] (g : N ->* P) (f₁ f₂ : M ->* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp

end Mul

section InvDiv
variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive /-- If `f` is an additive monoid homomorphism to an additive commutative group,
then `-f` is the homomorphism sending `x` to `-(f x)`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (M ->* G)
  body: mk' (fun g => (f g)⁻¹) fun a b => by simp_rw [← mul_inv, f.map_mul]

中文:
实例 :
  签名: Inv (M ->* G)
  定义体: mk' (fun g => (f g)⁻¹) fun a b => by simp_rw [← mul_inv, f.map_mul]

Depends on / 依赖: f.map_mul, map_mul, mul_inv, simp_rw
-/
instance : Inv (M ->* G) where
  inv f := mk' (fun g => (f g)⁻¹) fun a b => by simp_rw [← mul_inv, f.map_mul]

/--
lemma `inv_apply` / 引理 `inv_apply`

English:
lemma inv_apply
  given: (f : M ->* G) (x : M)
  statement: f⁻¹ x = (f x)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 inv_apply
  条件: (f : M ->* G) (x : M)
  结论: f⁻¹ x = (f x)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma inv_apply (f : M ->* G) (x : M) : f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `inv_comp` / 定理 `inv_comp`

English:
theorem inv_comp
  given: (φ : N ->* G) (ψ : M ->* N)
  statement: φ⁻¹.comp ψ = (φ.comp ψ)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_comp
  条件: (φ : N ->* G) (ψ : M ->* N)
  结论: φ⁻¹.comp ψ = (φ.comp ψ)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_comp (φ : N ->* G) (ψ : M ->* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `comp_inv` / 定理 `comp_inv`

English:
theorem comp_inv
  given: (φ : G ->* H) (ψ : M ->* G)
  statement: φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹
  proof: by
  ext
  simp

中文:
定理 comp_inv
  条件: (φ : G ->* H) (ψ : M ->* G)
  结论: φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹
  证明: by
  ext
  simp
-/
theorem comp_inv (φ : G ->* H) (ψ : M ->* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive /-- If `f` and `g` are monoid homomorphisms to an additive commutative group,
then `f - g` is the homomorphism sending `x` to `(f x) - (g x)`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (M ->* G)
  body: mk' (fun x => f x / g x) fun a b => by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

中文:
实例 :
  签名: Div (M ->* G)
  定义体: mk' (fun x => f x / g x) fun a b => by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

Depends on / 依赖: div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm
-/
instance : Div (M ->* G) where
  div f g := mk' (fun x => f x / g x) fun a b => by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
lemma `div_apply` / 引理 `div_apply`

English:
lemma div_apply
  given: (f g : M ->* G) (x : M)
  statement: (f / g) x = f x / g x
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 div_apply
  条件: (f g : M ->* G) (x : M)
  结论: (f / g) x = f x / g x
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma div_apply (f g : M ->* G) (x : M) : (f / g) x = f x / g x := rfl

@[to_additive (attr := simp)]
/--
lemma `div_comp` / 引理 `div_comp`

English:
lemma div_comp
  given: (f g : N ->* G) (h : M ->* N)
  statement: (f / g).comp h = f.comp h / g.comp h
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 div_comp
  条件: (f g : N ->* G) (h : M ->* N)
  结论: (f / g).comp h = f.comp h / g.comp h
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma div_comp (f g : N ->* G) (h : M ->* N) : (f / g).comp h = f.comp h / g.comp h := rfl

@[to_additive (attr := simp)]
/--
lemma `comp_div` / 引理 `comp_div`

English:
lemma comp_div
  given: (f : G ->* H) (g h : M ->* G)
  statement: f.comp (g / h) = f.comp g / f.comp h
  proof: by
  ext
  simp

中文:
引理 comp_div
  条件: (f : G ->* H) (g h : M ->* G)
  结论: f.comp (g / h) = f.comp g / f.comp h
  证明: by
  ext
  simp
-/
lemma comp_div (f : G ->* H) (g h : M ->* G) : f.comp (g / h) = f.comp g / f.comp h := by
  ext
  simp

end InvDiv

/-- If `H` is commutative and `G →* H` is injective, then `G` is commutative. -/
@[instance_reducible]
/--
Definition of `commGroupOfInjective` / `commGroupOfInjective` 的定义

English:
definition commGroupOfInjective
  signature: [Group G] [CommGroup H] (f : G ->* H) (hf : Function.Injective f)
  body: ⟨by simp_rw [← hf.eq_iff, map_mul, mul_comm, implies_true]⟩

中文:
定义 commGroupOfInjective
  签名: [Group G] [CommGroup H] (f : G ->* H) (hf : Function.Injective f)
  定义体: ⟨by simp_rw [← hf.eq_iff, map_mul, mul_comm, implies_true]⟩

Depends on / 依赖: eq_iff, hf.eq_iff, implies_true, map_mul, mul_comm, simp_rw
-/
def commGroupOfInjective [Group G] [CommGroup H] (f : G ->* H) (hf : Function.Injective f) :
    CommGroup G :=
  ⟨by simp_rw [← hf.eq_iff, map_mul, mul_comm, implies_true]⟩

/-- If `G` is commutative and `G →* H` is surjective, then `H` is commutative. -/
@[instance_reducible]
/--
Definition of `commGroupOfSurjective` / `commGroupOfSurjective` 的定义

English:
definition commGroupOfSurjective
  signature: [CommGroup G] [Group H] (f : G ->* H) (hf : Function.Surjective f)
  body: ⟨by simp_rw [hf.forall₂, ← map_mul, mul_comm, implies_true]⟩

中文:
定义 commGroupOfSurjective
  签名: [CommGroup G] [Group H] (f : G ->* H) (hf : Function.Surjective f)
  定义体: ⟨by simp_rw [hf.forall₂, ← map_mul, mul_comm, implies_true]⟩

Depends on / 依赖: hf.forall, implies_true, map_mul, mul_comm, simp_rw
-/
def commGroupOfSurjective [CommGroup G] [Group H] (f : G ->* H) (hf : Function.Surjective f) :
    CommGroup H :=
  ⟨by simp_rw [hf.forall₂, ← map_mul, mul_comm, implies_true]⟩

end MonoidHom
