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
/-
**powMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powMonoidHom (n : Nat) : α ->* α where toFun
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
def powMonoidHom (n : ℕ) : α →* α where
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
/-
**zpowGroupHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：zpowGroupHom (n : Int) : α ->* α where toFun
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
-/
def zpowGroupHom (n : ℤ) : α →* α where
  toFun := (· ^ n)
  map_one' := one_zpow n
  map_mul' a b := mul_zpow a b n

/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive /-- Negation on a commutative additive group, considered as an additive monoid
homomorphism. -/]
/-
**invMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invMonoidHom : α ->* α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
-/
def invMonoidHom : α →* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv

@[to_additive (attr := simp)]
/-
**coe_invMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_invMonoidHom : (invMonoidHom : α -> α) = Inv.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_invMonoidHom : (invMonoidHom : α → α) = Inv.inv := rfl

@[to_additive (attr := simp)]
/-
**invMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**invMonoidHom_comp_invMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invMonoidHom_comp_invMonoidHom : (invMonoidHom (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invMonoidHom_comp_invMonoidHom : (invMonoidHom (α := α)).comp invMonoidHom = .id _ := by
  ext; simp

end DivisionCommMonoid

namespace OneHom

/-- Given two one-preserving morphisms `f`, `g`,
`f * g` is the one-preserving morphism sending `x` to `f x * g x`. -/
@[to_additive /-- Given two zero-preserving morphisms `f`, `g`,
`f + g` is the zero-preserving morphism sending `x` to `f x + g x`. -/]
/-
**OneHom.** 是 Mathlib 中的一个实例，位于命名空间 `OneHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [MulOneClass N] : Mul (OneHom M N) where
  mul f g :=
    { toFun m := f m * g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]
/-
**OneHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：coe_mul {M N} [One M] [MulOneClass N] (f g : OneHom M N) : ⇑(f * g) = ⇑f *
 ⇑g
参数：f g : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul {M N} [One M] [MulOneClass N] (f g : OneHom M N) : ⇑(f * g) = ⇑f * ⇑g := rfl

@[to_additive (attr := simp)]
/-
**OneHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) : (f * 
g) x = f x * g x
参数：f g : OneHom M N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) :
    (f * g) x = f x * g x := rfl

@[to_additive]
/-
**OneHom.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：mul_comp [One M] [One N] [MulOneClass P] (g₁ g₂ : OneHom N P) (f : OneHom 
M N) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
参数：g₁ g₂ : OneHom N P；f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_comp [One M] [One N] [MulOneClass P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

/-- Given a one-preserving morphism `f`,
`f⁻¹` is the one-preserving morphism sending `x` to `(f x)⁻¹`. -/
@[to_additive /-- Given a zero-preserving morphism `f`,
`-f` is the zero-preserving morphism sending `x` to `-f x`. -/]
/-
**OneHom.** 是 Mathlib 中的一个实例，位于命名空间 `OneHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [InvOneClass N] : Inv (OneHom M N) where
  inv f :=
    { toFun m := (f m)⁻¹
      map_one' := by simp }

@[to_additive (attr := norm_cast)]
/-
**OneHom.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：coe_inv {M N} [One M] [InvOneClass N] (f : OneHom M N) : ⇑(f⁻¹) = (⇑f)⁻¹
参数：f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv {M N} [One M] [InvOneClass N] (f : OneHom M N) : ⇑(f⁻¹) = (⇑f)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**OneHom.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：inv_apply {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M) : f⁻¹ x =
 (f x)⁻¹
参数：f : OneHom M N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply {M N} [One M] [InvOneClass N] (f : OneHom M N) (x : M) :
    f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive]
/-
**OneHom.inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：inv_comp [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N)
 : (g⁻¹).comp f = (g.comp f)⁻¹
参数：g : OneHom N P；f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_comp [One M] [One N] [InvOneClass P] (g : OneHom N P) (f : OneHom M N) :
    (g⁻¹).comp f = (g.comp f)⁻¹ := rfl

/-- Given two one-preserving morphisms `f`, `g`,
`f / g` is the one-preserving morphism sending `x` to `f x / g x`. -/
@[to_additive /-- Given two zero-preserving morphisms `f`, `g`,
`f - g` is the additive morphism sending `x` to `f x - g x`. -/]
/-
**OneHom.** 是 Mathlib 中的一个实例，位于命名空间 `OneHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One M] [DivisionMonoid N] : Div (OneHom M N) where
  div f g :=
    { toFun m := f m / g m
      map_one' := by simp }

@[to_additive (attr := norm_cast)]
/-
**OneHom.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：coe_div {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) : ⇑(f / g) = ⇑
f / ⇑g
参数：f g : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) : ⇑(f / g) = ⇑f / ⇑g := rfl

@[to_additive (attr := simp)]
/-
**OneHom.div_apply** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：div_apply {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) (x : M) : (f
 / g) x = f x / g x
参数：f g : OneHom M N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_apply {M N} [One M] [DivisionMonoid N] (f g : OneHom M N) (x : M) :
    (f / g) x = f x / g x := rfl

@[to_additive]
/-
**OneHom.div_comp** 是 Mathlib 中的一个定理，位于命名空间 `OneHom`。
形式化陈述：div_comp [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneH
om M N) : (g₁ / g₂).comp f = g₁.comp f / g₂.comp f
参数：g₁ g₂ : OneHom N P；f : OneHom M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_comp [One M] [One N] [DivisionMonoid P] (g₁ g₂ : OneHom N P) (f : OneHom M N) :
    (g₁ / g₂).comp f = g₁.comp f / g₂.comp f := rfl

end OneHom

namespace MulHom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive /-- Given two additive morphisms `f`, `g` to an additive commutative semigroup,
`f + g` is the additive morphism sending `x` to `f x + g x`. -/]
/-
**MulHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul M] [CommSemigroup N] : Mul (M →ₙ* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_mul' := fun x y => by
        show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

@[to_additive (attr := simp)]
/-
**MulHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M ->ₙ* N) (x : M) : (f * 
g) x = f x * g x
参数：f g : M ->ₙ* N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
    (f * g) x = f x * g x := rfl

@[to_additive]
/-
**MulHom.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N ->ₙ* P) (f : M ->ₙ* 
N) : (g₁ * g₂).comp f = g₁.comp f * g₂.comp f
参数：g₁ g₂ : N ->ₙ* P；f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N →ₙ* P) (f : M →ₙ* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
/-
**MulHom.comp_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulHom`。
形式化陈述：comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N ->ₙ* P) (f₁ f₂
 : M ->ₙ* N) : g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂
参数：g : N ->ₙ* P；f₁ f₂ : M ->ₙ* N。
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
theorem comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N →ₙ* P) (f₁ f₂ : M →ₙ* N) :
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
/-
**MonoidHom._root_.injective_iff_map_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <| h _ <| by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive
  /-- A homomorphism from an additive group to an additive monoid is injective iff its
  kernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see
  `injective_iff_map_eq_zero`. -/]
/-
**MonoidHom._root_.injective_iff_map_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHo
m`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  (injective_iff_map_eq_one f).trans <|
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

/-- Makes a group homomorphism from a proof that the map preserves right division
`fun x y => x * y⁻¹`. See also `MonoidHom.of_map_div` for a version using `fun x y => x / y`.
-/
@[to_additive
  /-- Makes an additive group homomorphism from a proof that the map preserves
  the operation `fun a b => a + -b`. See also `AddMonoidHom.ofMapSub` for a version using
  `fun a b => a - b`. -/]
/-
**MonoidHom.ofMapMulInv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ofMapMulInv {H : Type*} [Group H] (f : G -> H) (map_div : forall a b : G, 
f (a * b⁻¹) = f a * (f b)⁻¹) : G ->* H
参数：f : G -> H；map_div : forall a b : G, f (a * b⁻¹) = f a * (f b)⁻¹。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofMapMulInv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  (mk' f) fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        { simp only [one_mul, inv_one, ← map_div, inv_inv] }
      _ = f x * f y := by
        { simp only [map_div]
          simp only [mul_inv_cancel, one_mul, inv_inv] }

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_of_map_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_of_map_mul_inv {H : Type*} [Group H] (f : G -> H) (map_div : forall a 
b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : ↑(ofMapMulInv f map_div) = f
参数：f : G -> H；map_div : forall a b : G, f (a * b⁻¹) = f a * (f b)⁻¹。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of_map_mul_inv {H : Type*} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : ↑(ofMapMulInv f map_div) = f :=
  rfl

/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive /-- Define a morphism of additive groups given a map which respects difference. -/]
/-
**MonoidHom.ofMapDiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ofMapDiv {H : Type*} [Group H] (f : G -> H) (hf : forall x y, f (x / y) = 
f x / f y) : G ->* H
参数：f : G -> H；hf : forall x y, f (x / y) = f x / f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a morphism of additive groups given a map which respects ratios.
-/
def ofMapDiv {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_of_map_div** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_of_map_div {H : Type*} [Group H] (f : G -> H) (hf : forall x y, f (x /
 y) = f x / f y) : ↑(ofMapDiv f hf) = f
参数：f : G -> H；hf : forall x y, f (x / y) = f x / f y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of_map_div {H : Type*} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
    ↑(ofMapDiv f hf) = f := rfl

end Group

section Mul
variable [MulOneClass M] [CommMonoid N]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
/-
**MonoidHom.mul** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
形式化陈述：mul : Mul (M ->* N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the mono
id morphism
sending `x` to `f x * g x`.
-/
instance mul : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m,
      map_one' := by simp,
      map_mul' := fun x y => by
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,
`f + g` is the additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.add

/-
**MonoidHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_2} {N : Type u_3} [inst : MulOneClass M] [inst_1 : CommMonoi
d N] (f g : M →* N) (x : M),   (f * g) x = f x * g x
参数：f g : M →* N；x : M；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma mul_apply (f g : M →* N) (x : M) : (f * g) x = f x * g x := rfl

@[to_additive]
/-
**MonoidHom.mul_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：mul_comp [MulOneClass P] (g₁ g₂ : M ->* N) (f : P ->* M) : (g₁ * g₂).comp 
f = g₁.comp f * g₂.comp f
参数：g₁ g₂ : M ->* N；f : P ->* M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_comp [MulOneClass P] (g₁ g₂ : M →* N) (f : P →* M) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

@[to_additive]
/-
**MonoidHom.comp_mul** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：comp_mul [CommMonoid P] (g : N ->* P) (f₁ f₂ : M ->* N) : g.comp (f₁ * f₂)
 = g.comp f₁ * g.comp f₂
参数：g : N ->* P；f₁ f₂ : M ->* N。
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
lemma comp_mul [CommMonoid P] (g : N →* P) (f₁ f₂ : M →* N) :
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
/-
**MonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (M →* G) where
  inv f := mk' (fun g ↦ (f g)⁻¹) fun a b ↦ by simp_rw [← mul_inv, f.map_mul]
/-
**MonoidHom.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_2} {G : Type u_5} [inst : MulOneClass M] [inst_1 : CommGroup
 G] (f : M →* G) (x : M), f⁻¹ x = (f x)⁻¹
参数：f : M →* G；x : M；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma inv_apply (f : M →* G) (x : M) : f⁻¹ x = (f x)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：inv_comp (φ : N ->* G) (ψ : M ->* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹
参数：φ : N ->* G；ψ : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_comp (φ : N →* G) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comp_inv (φ : G ->* H) (ψ : M ->* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹
参数：φ : G ->* H；ψ : M ->* G。
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
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_inv (φ : G →* H) (ψ : M →* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive /-- If `f` and `g` are monoid homomorphisms to an additive commutative group,
then `f - g` is the homomorphism sending `x` to `(f x) - (g x)`. -/]
/-
**MonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (M →* G) where
  div f g := mk' (fun x ↦ f x / g x) fun a b ↦ by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
/-
**MonoidHom.div_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {M : Type u_2} {G : Type u_5} [inst : MulOneClass M] [inst_1 : CommGroup
 G] (f g : M →* G) (x : M),   (f / g) x = f x / g x
参数：f g : M →* G；x : M；f / g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma div_apply (f g : M →* G) (x : M) : (f / g) x = f x / g x := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.div_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：div_comp (f g : N ->* G) (h : M ->* N) : (f / g).comp h = f.comp h / g.com
p h
参数：f g : N ->* G；h : M ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_comp (f g : N →* G) (h : M →* N) : (f / g).comp h = f.comp h / g.comp h := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.comp_div** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：comp_div (f : G ->* H) (g h : M ->* G) : f.comp (g / h) = f.comp g / f.com
p h
参数：f : G ->* H；g h : M ->* G。
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
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_div (f : G →* H) (g h : M →* G) : f.comp (g / h) = f.comp g / f.comp h := by
  ext
  simp

end InvDiv

/-- If `H` is commutative and `G →* H` is injective, then `G` is commutative. -/
@[instance_reducible]
/-
**MonoidHom.commGroupOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：commGroupOfInjective [Group G] [CommGroup H] (f : G ->* H) (hf : Function.
Injective f) : CommGroup G
参数：f : G ->* H；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H` is commutative and `G →* H` is injective, then `G` is commutative.
-/
def commGroupOfInjective [Group G] [CommGroup H] (f : G →* H) (hf : Function.Injective f) :
    CommGroup G :=
  ⟨by simp_rw [← hf.eq_iff, map_mul, mul_comm, implies_true]⟩

/-- If `G` is commutative and `G →* H` is surjective, then `H` is commutative. -/
@[instance_reducible]
/-
**MonoidHom.commGroupOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：commGroupOfSurjective [CommGroup G] [Group H] (f : G ->* H) (hf : Function
.Surjective f) : CommGroup H
参数：f : G ->* H；hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is commutative and `G →* H` is surjective, then `H` is commutative.
-/
def commGroupOfSurjective [CommGroup G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    CommGroup H :=
  ⟨by simp_rw [hf.forall₂, ← map_mul, mul_comm, implies_true]⟩

end MonoidHom

