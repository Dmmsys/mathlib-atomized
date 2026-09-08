/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Monoid homomorphisms and units

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `Units` that depend on `MonoidHom`.

## Main declarations

* `Units.map`: Turn a homomorphism from `α` to `β` monoids into a homomorphism from `αˣ` to `βˣ`.
* `MonoidHom.toHomUnits`: Turn a homomorphism from a group `α` to `β` into a homomorphism from
  `α` to `βˣ`.
* `IsLocalHom`: A predicate on monoid maps, requiring that it maps
  nonunits to nonunits. For the local rings, that is, applied to their
  multiplicative monoids, this means that the image of the unique
  maximal ideal is again contained in the unique maximal ideal. This
  is developed earlier, and in the generality of monoids, as it allows
  its use in non-local-ring related contexts, but it does have the
  strange consequence that it does not require local rings, or even rings.

## TODO

The results that don't mention homomorphisms should be proved (earlier?) in a different file and be
used to golf the basic `Group` lemmas.

Add a `@[to_additive]` version of `IsLocalHom`.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

open Function

universe u v w

section MonoidHomClass

/-- If two homomorphisms from a division monoid to a monoid are equal at a unit `x`, then they are
equal at `x⁻¹`. -/
@[to_additive
  /-- If two homomorphisms from a subtraction monoid to an additive monoid are equal at an
  additive unit `x`, then they are equal at `-x`. -/]
/-
**IsUnit.eq_on_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N] [Mo
noidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = 
g x⁻¹
参数：hx : IsUnit x；f g : F；h : f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `map_mul_eq_one`：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} 
(h : a * b = 1) : f a * f b = 1
· 使用定理 `IsUnit.inv_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a⁻¹ * a = 1
· 使用定理 `IsUnit.mul_inv_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a * a⁻¹ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N]
    [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
    /-- If two homomorphism from an additive group to an additive monoid are equal at `x`,
    then they are equal at `-x`. -/]
/-
**eq_on_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G
 M] (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹
参数：f g : F；h : f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.eq_on_inv`：IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N]
 [FunLike F G N] [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f
 x = g…
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
    (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  (Group.isUnit x).eq_on_inv f g h

end MonoidHomClass

namespace Units

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

/-- The group homomorphism on units induced by a `MonoidHom`. -/
@[to_additive /-- The additive homomorphism on `AddUnit`s induced by an `AddMonoidHom`. -/]
/-
**Units.map** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：map (f : M ->* N) : Mˣ ->* Nˣ
参数：f : M ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism on units induced by a `MonoidHom`.
-/
def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk' (fun u => ⟨f u.val, f u.inv, by simp [← map_mul], by simp [← map_mul]⟩)
    fun _ _ => ext <| by simp

@[to_additive (attr := simp)]
/-
**Units.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_map (f : M ->* N) (x : Mˣ) : ↑(map f x) = f x
参数：f : M ->* N；x : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x := rfl

@[to_additive (attr := simp)]
/-
**Units.coe_map_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_map_inv (f : M ->* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹
参数：f : M ->* N；u : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**Units.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：map_mk (f : M ->* N) (val inv : M) (val_inv inv_val) : map f (mk val inv v
al_inv inv_val) = mk (f val) (f inv) (by simp [← map_mul, val_inv]) (by simp [← 
map_mul, inv_val])
参数：f : M ->* N；val inv : M；val_inv inv_val。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (f : M →* N) (val inv : M) (val_inv inv_val) :
    map f (mk val inv val_inv inv_val) =
      mk (f val) (f inv) (by simp [← map_mul, val_inv]) (by simp [← map_mul, inv_val]) := rfl

@[to_additive (attr := simp)]
/-
**Units.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：map_comp (f : M ->* N) (g : N ->* P) : map (g.comp f) = (map g).comp (map 
f)
参数：f : M ->* N；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) := rfl

@[to_additive]
/-
**Units.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：map_injective {f : M ->* N} (hf : Function.Injective f) : Function.Injecti
ve (map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem map_injective {f : M →* N} (hf : Function.Injective f) :
    Function.Injective (map f) := fun _ _ e => ext (hf (congr_arg val e))

@[to_additive]
/-
**Units.map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：map_bijective {f : M ->* N} (hf : Function.Bijective f) : Function.Bijecti
ve map f
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.map_injective`：map_injective {f : M ->* N} (hf : Function.Injectiv
e f) : Function.Injective (map f)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem map_bijective {f : M →* N} (hf : Function.Bijective f) : Function.Bijective <| map f := by
  refine ⟨map_injective hf.injective, ?_⟩
  rintro ⟨u, v, uv, vu⟩
  rcases hf.surjective u, hf.surjective v with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact ⟨⟨u, v, hf.injective <| by simpa, hf.injective <| by simpa⟩, rfl⟩

variable (M)

@[to_additive (attr := simp)]
/-
**Units.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by ext; rfl

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive /-- Coercion `AddUnits M → M` as an AddMonoid homomorphism. -/]
/-
**Units.coeHom** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：coeHom : Mˣ ->* M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b

--- 原说明 ---
Coercion `Mˣ → M` as a monoid homomorphism.
-/
def coeHom : Mˣ →* M where
  toFun := Units.val; map_one' := val_one; map_mul' := val_mul

variable {M}

@[to_additive (attr := simp)]
/-
**Units.coeHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coeHom_apply (x : Mˣ) : coeHom M x = ↑x
参数：x : Mˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeHom_apply (x : Mˣ) : coeHom M x = ↑x := rfl

@[to_additive]
/-
**Units.coeHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coeHom_injective : Function.Injective (coeHom M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
theorem coeHom_injective : Function.Injective (coeHom M) := Units.val_injective

section DivisionMonoid

variable {α : Type*} [DivisionMonoid α]

@[to_additive (attr := simp, norm_cast)]
/-
**Units.val_zpow_eq_zpow_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_zpow_eq_zpow_val : forall (u : αˣ) (n : Int), ((u ^ n : αˣ) : α) = (u 
: α) ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
-/
theorem val_zpow_eq_zpow_val : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = (u : α) ^ n :=
  (Units.coeHom α).map_zpow

@[to_additive (attr := simp)]
/-
**Units._root_.map_units_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.map_units_inv {F : Type*} [FunLike F M α] [MonoidHomClass F M α]
    (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ := ((f : M →* α).comp (Units.coeHom M)).map_inv u

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
  /-- If a map `g : M → AddUnits N` agrees with a homomorphism `f : M →+ N`, then this map
  is an AddMonoid homomorphism too. -/]
/-
**Units.liftRight** 是 Mathlib 中的一个定义，位于命名空间 `Units`。
形式化陈述：liftRight (f : M ->* N) (g : M -> Nˣ) (h : forall x, ↑(g x) = f x) : M ->*
 Nˣ where toFun
参数：f : M ->* N；g : M -> Nˣ；h : forall x, ↑(g x) = f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ where
  toFun := g
  map_one' := by ext; rw [h 1]; exact f.map_one
  map_mul' x y := Units.ext <| by simp only [h, val_mul, f.map_mul]

@[to_additive (attr := simp)]
/-
**Units.coe_liftRight** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：coe_liftRight {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x)
 : (liftRight f g h x : N) = f x
参数：h : forall x, ↑(g x) = f x；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftRight {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    (liftRight f g h x : N) = f x := h x

@[to_additive (attr := simp)]
/-
**Units.mul_liftRight_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_liftRight_inv {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x)
 (x) : f x * ↑(liftRight f g h x)⁻¹ = 1
参数：h : forall x, ↑(g x) = f x；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ 
= c ↔ a = c * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Units.coe_liftRight`：coe_liftRight {f : M ->* N} {g : M -> Nˣ} (h : fora
ll x, ↑(g x) = f x) (x) : (liftRight f g h x : N) = f x
-/
theorem mul_liftRight_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    f x * ↑(liftRight f g h x)⁻¹ = 1 := by
  rw [Units.mul_inv_eq_iff_eq_mul, one_mul, coe_liftRight]

@[to_additive (attr := simp)]
/-
**Units.liftRight_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：liftRight_inv_mul {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x)
 (x) : ↑(liftRight f g h x)⁻¹ * f x = 1
参数：h : forall x, ↑(g x) = f x；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.coe_liftRight`：coe_liftRight {f : M ->* N} {g : M -> Nˣ} (h : fora
ll x, ↑(g x) = f x) (x) : (liftRight f g h x : N) = f x
-/
theorem liftRight_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    ↑(liftRight f g h x)⁻¹ * f x = 1 := by
  rw [Units.inv_mul_eq_iff_eq_mul, mul_one, coe_liftRight]

end Units

namespace MonoidHom
variable {G M : Type*} [Group G]

section Monoid
variable [Monoid M]

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.toHomUnits` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
  /-- If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,
  then its image lies in the `AddUnits` of `M`,
  and `f.toHomUnits` is the corresponding homomorphism from `G` to `AddUnits M`. -/]
/-
**MonoidHom.toHomUnits** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：toHomUnits (f : G ->* M) : G ->* Mˣ
参数：f : G ->* M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toHomUnits (f : G →* M) : G →* Mˣ :=
  Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_cancel _),
    map_mul_eq_one f (inv_mul_cancel _)⟩)
    fun _ => rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_toHomUnits** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_toHomUnits (f : G ->* M) (g : G) : (f.toHomUnits g : M) = f g
参数：f : G ->* M；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomUnits (f : G →* M) (g : G) : (f.toHomUnits g : M) = f g := rfl

end Monoid

variable [CommMonoid M]

/-
**MonoidHom.toHomUnits_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} {M : Type u_2} [inst : Group G] [inst_1 : CommMonoid M] (
f g : G →* M),   (f * g).toHomUnits = f.toHomUnits * g.toHomUnits
参数：f g : G →* M；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
@[simp] lemma toHomUnits_mul (f g : G →* M) : (f * g).toHomUnits = f.toHomUnits * g.toHomUnits := by
  ext; rfl

/-- `MonoidHom.toHomUnits` as a `MulEquiv`. -/
/-
**MonoidHom.toHomUnitsMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：{G : Type u_1} → {M : Type u_2} → [inst : Group G] → [inst_1 : CommMonoid 
M] → (G →* M) ≃* (G →* Mˣ)
参数：G →* M；G →* Mˣ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidHom.toHomUnits` as a `MulEquiv`.
-/
@[simps] def toHomUnitsMulEquiv : (G →* M) ≃* (G →* Mˣ) where
  toFun := toHomUnits
  invFun f := (Units.coeHom _).comp f
  map_mul' := by simp

end MonoidHom

namespace IsUnit

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive]
/-
**IsUnit.map** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x)
参数：f : F；h : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M →* N) y).isUnit

@[to_additive]
/-
**IsUnit.unit_map** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : (h.map f)
.unit = f h.unit
参数：f : F；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
theorem unit_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    (h.map f).unit = f h.unit :=
  rfl

@[to_additive]
/-
**IsUnit.unit_inv_map** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：unit_inv_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : (h.ma
p f).unit⁻¹ = f ↑h.unit⁻¹
参数：f : F；h : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_eq_of_mul_eq_one_left`：∀ {α : Type u} [inst : Monoid α] {u : α
ˣ} {a : α}, a * ↑u = 1 → ↑u⁻¹ = a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_inv_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    (h.map f).unit⁻¹ = f ↑h.unit⁻¹ :=
  Units.inv_eq_of_mul_eq_one_left <| by simp [← map_mul]

@[to_additive]
/-
**IsUnit.of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：of_leftInverse [MonoidHomClass G N M] {f : F} {x : M} (g : G) (hfg : Funct
ion.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x
参数：g : G；hfg : Function.LeftInverse g f；h : IsUnit (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
theorem of_leftInverse [MonoidHomClass G N M] {f : F} {x : M} (g : G)
    (hfg : Function.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x := by
  simpa only [hfg x] using h.map g

/-- Prefer `IsLocalHom.of_leftInverse`, but we can't get rid of this because of `ToAdditive`. -/
@[to_additive]
/-
**IsUnit._root_.isUnit_map_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prefer `IsLocalHom.of_leftInverse`, but we can't get rid of this because of `ToA
dditive`.
-/
theorem _root_.isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M]
    {f : F} {x : M} (g : G) (hfg : Function.LeftInverse g f) :
    IsUnit (f x) ↔ IsUnit x := ⟨of_leftInverse g hfg, map _⟩

/-- If a homomorphism `f : M →* N` sends each element to an `IsUnit`, then it can be lifted
to `f : M →* Nˣ`. See also `Units.liftRight` for a computable version. -/
@[to_additive
  /-- If a homomorphism `f : M →+ N` sends each element to an `IsAddUnit`, then it can be
  lifted to `f : M →+ AddUnits N`. See also `AddUnits.liftRight` for a computable version. -/]
/-
**IsUnit.liftRight** 是 Mathlib 中的一个定义，位于命名空间 `IsUnit`。
形式化陈述：liftRight (f : M ->* N) (hf : forall x, IsUnit (f x)) : M ->* Nˣ
参数：f : M ->* N；hf : forall x, IsUnit (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).unit) fun _ => rfl

@[to_additive]
/-
**IsUnit.coe_liftRight** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：coe_liftRight (f : M ->* N) (hf : forall x, IsUnit (f x)) (x) : (IsUnit.li
ftRight f hf x : N) = f x
参数：f : M ->* N；hf : forall x, IsUnit (f x)；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x) :
    (IsUnit.liftRight f hf x : N) = f x := rfl

@[to_additive (attr := simp)]
/-
**IsUnit.mul_liftRight_inv** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_liftRight_inv (f : M ->* N) (h : forall x, IsUnit (f x)) (x) : f x * ↑
(IsUnit.liftRight f h x)⁻¹ = 1
参数：f : M ->* N；h : forall x, IsUnit (f x)；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_liftRight_inv`：mul_liftRight_inv {f : M ->* N} {g : M -> Nˣ} (
h : forall x, ↑(g x) = f x) (x) : f x * ↑(liftRight f g h x)⁻¹ = 1
-/
theorem mul_liftRight_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 := Units.mul_liftRight_inv (by intro; rfl) x

@[to_additive (attr := simp)]
/-
**IsUnit.liftRight_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：liftRight_inv_mul (f : M ->* N) (h : forall x, IsUnit (f x)) (x) : ↑(IsUni
t.liftRight f h x)⁻¹ * f x = 1
参数：f : M ->* N；h : forall x, IsUnit (f x)；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.liftRight_inv_mul`：liftRight_inv_mul {f : M ->* N} {g : M -> Nˣ} (
h : forall x, ↑(g x) = f x) (x) : ↑(liftRight f g h x)⁻¹ * f x = 1
-/
theorem liftRight_inv_mul (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 := Units.liftRight_inv_mul (by intro; rfl) x

@[to_additive]
/-
**IsUnit.liftRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：liftRight_apply (f : M ->* N) (hf : forall x, IsUnit (f x)) (x : M) : IsUn
it.liftRight f hf x = (hf x).unit
参数：f : M ->* N；hf : forall x, IsUnit (f x)；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftRight_apply (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x : M) :
    IsUnit.liftRight f hf x = (hf x).unit :=
  rfl

end Monoid
end IsUnit

section IsLocalHom

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

/-- A map `f` between monoids is *local* if any `a` in the domain is a unit
  whenever `f a` is a unit. See `IsLocalRing.local_hom_TFAE` for other equivalent
  definitions in the local ring case - from where this concept originates, but it is useful in
  other contexts, so we allow this generalisation in mathlib. -/
/-
**IsLocalHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_2} → {S : Type u_3} → {F : Type u_5} → [Monoid R] → [Monoid S]
 → [FunLike F R S] → F → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` between monoids is *local* if any `a` in the domain is a unit
  whenever `f a` is a unit. See `IsLocalRing.local_hom_TFAE` for other equivalen
t
  definitions in the local ring case - from where this concept originates, but i
t is useful in
  other contexts, so we allow this generalisation in mathlib.
-/
class IsLocalHom (f : F) : Prop where
  /-- A local homomorphism `f : R ⟶ S` will send nonunits of `R` to nonunits of `S`. -/
  map_nonunit : ∀ a, IsUnit (f a) → IsUnit a
/-
**IsUnit.of_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit (f a)) : IsUnit a
参数：f : F；a : R；h : IsUnit (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
theorem IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit (f a)) : IsUnit a :=
  IsLocalHom.map_nonunit a h

-- TODO : remove alias, change the parenthesis of `f` and `a`
alias isUnit_of_map_unit := IsUnit.of_map

variable [MonoidHomClass F R S]

@[simp]
/-
**isUnit_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (f a) ↔ IsUnit a
参数：f : F；a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
theorem isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (f a) ↔ IsUnit a :=
  ⟨IsLocalHom.map_nonunit a, IsUnit.map f⟩
/-
**isLocalHom_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_of_leftInverse [FunLike G S R] [MonoidHomClass G S R] {f : F} (
g : G) (hfg : Function.LeftInverse g f) : IsLocalHom f where map_nonunit a ha
参数：g : G；hfg : Function.LeftInverse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUnit_map_of_leftInverse`：∀ {F : Type u_1} {G : Type u_2} {M : Type u_3
} {N : Type u_4} [inst : FunLike F M N] [inst_1 : FunLike G N M]   [inst_2 : Mon
oid M] [inst_3 …
-/
theorem isLocalHom_of_leftInverse [FunLike G S R] [MonoidHomClass G S R]
    {f : F} (g : G) (hfg : Function.LeftInverse g f) : IsLocalHom f where
  map_nonunit a ha := by rwa [isUnit_map_of_leftInverse g hfg] at ha

@[instance]
/-
**MonoidHom.isLocalHom_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isLocalHom_comp (g : S ->* T) (f : R ->* S) [IsLocalHom g] [IsLo
calHom f] : IsLocalHom (g.comp f) where map_nonunit a
参数：g : S ->* T；f : R ->* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
theorem MonoidHom.isLocalHom_comp (g : S →* T) (f : R →* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

-- see note [lower instance priority]
@[instance 100]
/-
**isLocalHom_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalHom_toMonoidHom (f : F) [IsLocalHom f] : IsLocalHom (f : R ->* S)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.map_nonunit`：∀ {R : Type u_2} {S : Type u_3} {F : Type u_5} {
inst : Monoid R} {inst_1 : Monoid S} {inst_2 : FunLike F R S} {f : F}   [self : 
IsLocalHom f…
-/
theorem isLocalHom_toMonoidHom (f : F) [IsLocalHom f] :
    IsLocalHom (f : R →* S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩
/-
**MonoidHom.isLocalHom_of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.isLocalHom_of_comp (f : R ->* S) (g : S ->* T) [IsLocalHom (g.co
mp f)] : IsLocalHom f
参数：f : R ->* S；g : S ->* T；g.comp f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
theorem MonoidHom.isLocalHom_of_comp (f : R →* S) (g : S →* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (ha.map g)⟩

end IsLocalHom

