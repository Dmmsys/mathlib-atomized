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
/--
theorem `IsUnit.eq_on_inv` / 定理 `IsUnit.eq_on_inv`

English:
theorem IsUnit.eq_on_inv
  statement: {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N]
  proof: left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

中文:
定理 是单位.eq_on_inv
  结论: {F G N} [Division幺半群 G] [幺半群 N] [函数状 F G N]
  证明: left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

Depends on / 依赖: h.symm, hx.inv_mul_cancel, hx.mul_inv_cancel, inv_mul_cancel, left_inv_eq_right_inv, map_mul_eq_one, mul_inv_cancel
-/
theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N]
    [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
    /-- If two homomorphism from an additive group to an additive monoid are equal at `x`,
    then they are equal at `-x`. -/]
/--
theorem `eq_on_inv` / 定理 `eq_on_inv`

English:
theorem eq_on_inv
  statement: {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
  proof: (Group.isUnit x).eq_on_inv f g h

中文:
定理 eq_on_inv
  结论: {F G M} [群 G] [幺半群 M] [函数状 F G M] [幺半群态射类 F G M]
  证明: (Group.isUnit x).eq_on_inv f g h

Depends on / 依赖: Group.isUnit, eq_on_inv, isUnit
-/
theorem eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
    (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  (Group.isUnit x).eq_on_inv f g h

end MonoidHomClass

namespace Units

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

/-- The group homomorphism on units induced by a `MonoidHom`. -/
@[to_additive /-- The additive homomorphism on `AddUnit`s induced by an `AddMonoidHom`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->* N)
  body: MonoidHom.mk' (fun u => ⟨f u.val, f u.inv, by simp [← map_mul], by simp [← map_mul]⟩)
fun _ _ => ext by simp

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : M ->* N)
  定义体: MonoidHom.mk' (fun u => ⟨f u.val, f u.inv, by simp [← map_mul], by simp [← map_mul]⟩)
fun _ _ => ext by simp

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.mk, map_mul, u.inv, u.val
-/
def map (f : M ->* N) : Mˣ ->* Nˣ :=
  MonoidHom.mk' (fun u => ⟨f u.val, f u.inv, by simp [← map_mul], by simp [← map_mul]⟩)
fun _ _ => ext by simp

@[to_additive (attr := simp)]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : M ->* N) (x : Mˣ)
  statement: ↑(map f x) = f x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_map
  条件: (f : M ->* N) (x : Mˣ)
  结论: ↑(map f x) = f x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_map (f : M ->* N) (x : Mˣ) : ↑(map f x) = f x := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_map_inv` / 定理 `coe_map_inv`

English:
theorem coe_map_inv
  given: (f : M ->* N) (u : Mˣ)
  statement: ↑(map f u)⁻¹ = f ↑u⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_map_inv
  条件: (f : M ->* N) (u : Mˣ)
  结论: ↑(map f u)⁻¹ = f ↑u⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_map_inv (f : M ->* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (f : M ->* N) (val inv : M) (val_inv inv_val)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_mk
  条件: (f : M ->* N) (val inv : M) (val_inv inv_val)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_mk (f : M ->* N) (val inv : M) (val_inv inv_val) :
    map f (mk val inv val_inv inv_val) =
      mk (f val) (f inv) (by simp [← map_mul, val_inv]) (by simp [← map_mul, inv_val]) := rfl

@[to_additive (attr := simp)]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : M ->* N) (g : N ->* P)
  statement: map (g.comp f) = (map g).comp (map f)
  proof: rfl

@[to_additive]

中文:
定理 map_comp
  条件: (f : M ->* N) (g : N ->* P)
  结论: map (g.comp f) = (map g).comp (map f)
  证明: rfl

@[to_additive]
-/
theorem map_comp (f : M ->* N) (g : N ->* P) : map (g.comp f) = (map g).comp (map f) := rfl

@[to_additive]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : M ->* N} (hf : Function.Injective f)
  proof: fun _ _ e => ext (hf (congr_arg val e))

@[to_additive]

中文:
定理 map_injective
  条件: {f : M ->* N} (hf : 函数.单射 f)
  证明: fun _ _ e => ext (hf (congr_arg val e))

@[to_additive]

Depends on / 依赖: congr_arg
-/
theorem map_injective {f : M ->* N} (hf : Function.Injective f) :
    Function.Injective (map f) := fun _ _ e => ext (hf (congr_arg val e))

@[to_additive]
/--
theorem `map_bijective` / 定理 `map_bijective`

English:
theorem map_bijective
  given: {f : M ->* N} (hf : Function.Bijective f)
  statement: Function.Bijective map f
  proof: by
  refine ⟨map_injective hf.injective, ?_⟩
  rintro ⟨u, v, uv, vu⟩
  rcases hf.surjective u, hf.surjective v with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
exact ⟨⟨u, v, hf.injective by simpa, hf.injective by simpa⟩, rfl⟩

中文:
定理 map_bijective
  条件: {f : M ->* N} (hf : 函数.双射 f)
  结论: 函数.双射 map f
  证明: by
  refine ⟨map_injective hf.injective, ?_⟩
  rintro ⟨u, v, uv, vu⟩
  rcases hf.surjective u, hf.surjective v with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
exact ⟨⟨u, v, hf.injective by simpa, hf.injective by simpa⟩, rfl⟩

Depends on / 依赖: hf.injective, hf.surjective, injective, map_injective, surjective
-/
theorem map_bijective {f : M ->* N} (hf : Function.Bijective f) : Function.Bijective map f := by
  refine ⟨map_injective hf.injective, ?_⟩
  rintro ⟨u, v, uv, vu⟩
  rcases hf.surjective u, hf.surjective v with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
exact ⟨⟨u, v, hf.injective by simpa, hf.injective by simpa⟩, rfl⟩

variable (M)

@[to_additive (attr := simp)]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (MonoidHom.id M) = MonoidHom.id Mˣ
  proof: by ext; rfl

中文:
定理 map_id
  结论: map (幺半群态射.id M) = 幺半群态射.id Mˣ
  证明: by ext; rfl
-/
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by ext; rfl

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive /-- Coercion `AddUnits M → M` as an AddMonoid homomorphism. -/]
/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : Mˣ ->* M where
  body: Units.val; map_one' := val_one; map_mul' := val_mul

中文:
定义 coeHom
  签名: : Mˣ ->* M where
  定义体: Units.val; map_one' := val_one; map_mul' := val_mul

Depends on / 依赖: Units.val, map_mul, map_one, val_mul, val_one
-/
def coeHom : Mˣ ->* M where
  toFun := Units.val; map_one' := val_one; map_mul' := val_mul

variable {M}

@[to_additive (attr := simp)]
/--
theorem `coeHom_apply` / 定理 `coeHom_apply`

English:
theorem coeHom_apply
  given: (x : Mˣ)
  statement: coeHom M x = ↑x
  proof: rfl

@[to_additive]

中文:
定理 coeHom_apply
  条件: (x : Mˣ)
  结论: coeHom M x = ↑x
  证明: rfl

@[to_additive]
-/
theorem coeHom_apply (x : Mˣ) : coeHom M x = ↑x := rfl

@[to_additive]
/--
theorem `coeHom_injective` / 定理 `coeHom_injective`

English:
theorem coeHom_injective
  statement: Function.Injective (coeHom M)
  proof: Units.val_injective

中文:
定理 coeHom_injective
  结论: 函数.单射 (coeHom M)
  证明: Units.val_injective

Depends on / 依赖: Units.val_injective, val_injective
-/
theorem coeHom_injective : Function.Injective (coeHom M) := Units.val_injective

section DivisionMonoid

variable {α : Type*} [DivisionMonoid α]

@[to_additive (attr := simp, norm_cast)]
/--
theorem `val_zpow_eq_zpow_val` / 定理 `val_zpow_eq_zpow_val`

English:
theorem val_zpow_eq_zpow_val
  statement: forall (u : αˣ) (n : Int), ((u ^ n : αˣ) : α) = (u : α) ^ n
  proof: (Units.coeHom α).map_zpow

@[to_additive (attr := simp)]

中文:
定理 val_zpow_eq_zpow_val
  结论: 对任意 (u : αˣ) (n : 整数), ((u ^ n : αˣ) : α) = (u : α) ^ n
  证明: (Units.coeHom α).map_zpow

@[to_additive (attr := simp)]

Depends on / 依赖: Units.coeHom, coeHom, map_zpow
-/
theorem val_zpow_eq_zpow_val : forall (u : αˣ) (n : Int), ((u ^ n : αˣ) : α) = (u : α) ^ n :=
  (Units.coeHom α).map_zpow

@[to_additive (attr := simp)]
/--
theorem `_root_.map_units_inv` / 定理 `_root_.map_units_inv`

English:
theorem _root_.map_units_inv
  statement: {F : Type*} [FunLike F M α] [MonoidHomClass F M α]
  proof: ((f : M ->* α).comp (Units.coeHom M)).map_inv u

中文:
定理 _root_.map_units_inv
  结论: {F : 类型} [函数状 F M α] [幺半群态射类 F M α]
  证明: ((f : M ->* α).comp (Units.coeHom M)).map_inv u

Depends on / 依赖: Units.coeHom, coeHom, map_inv
-/
theorem _root_.map_units_inv {F : Type*} [FunLike F M α] [MonoidHomClass F M α]
    (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ := ((f : M ->* α).comp (Units.coeHom M)).map_inv u

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
  /-- If a map `g : M → AddUnits N` agrees with a homomorphism `f : M →+ N`, then this map
  is an AddMonoid homomorphism too. -/]
/--
Definition of `liftRight` / `liftRight` 的定义

English:
definition liftRight
  signature: (f : M ->* N) (g : M -> Nˣ) (h : forall x, ↑(g x) = f x)
  body: g
  map_one' := by ext; rw [h 1]; exact f.map_one
map_mul' x y := Units.ext by simp only [h, val_mul, f.map_mul]

@[to_additive (attr := simp)]

中文:
定义 liftRight
  签名: (f : M ->* N) (g : M -> Nˣ) (h : 对任意 x, ↑(g x) = f x)
  定义体: g
  map_one' := by ext; rw [h 1]; exact f.map_one
map_mul' x y := Units.ext by simp only [h, val_mul, f.map_mul]

@[to_additive (attr := simp)]
-/
def liftRight (f : M ->* N) (g : M -> Nˣ) (h : forall x, ↑(g x) = f x) : M ->* Nˣ where
  toFun := g
  map_one' := by ext; rw [h 1]; exact f.map_one
map_mul' x y := Units.ext by simp only [h, val_mul, f.map_mul]

@[to_additive (attr := simp)]
/--
theorem `coe_liftRight` / 定理 `coe_liftRight`

English:
theorem coe_liftRight
  given: {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x)
  proof: h x

@[to_additive (attr := simp)]

中文:
定理 coe_liftRight
  条件: {f : M ->* N} {g : M -> Nˣ} (h : 对任意 x, ↑(g x) = f x) (x)
  证明: h x

@[to_additive (attr := simp)]
-/
theorem coe_liftRight {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x) :
    (liftRight f g h x : N) = f x := h x

@[to_additive (attr := simp)]
/--
theorem `mul_liftRight_inv` / 定理 `mul_liftRight_inv`

English:
theorem mul_liftRight_inv
  given: {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x)
  proof: by
  rw [Units.mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [coe_liftRight]

@[to_additive (attr := simp)]

中文:
定理 mul_liftRight_inv
  条件: {f : M ->* N} {g : M -> Nˣ} (h : 对任意 x, ↑(g x) = f x) (x)
  证明: by
  rw [Units.mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [coe_liftRight]

@[to_additive (attr := simp)]

Depends on / 依赖: Units.mul_inv_eq_iff_eq_mul, coe_liftRight, mul_inv_eq_iff_eq_mul, one_mul
-/
theorem mul_liftRight_inv {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x) :
    f x * ↑(liftRight f g h x)⁻¹ = 1 := by
  rw [Units.mul_inv_eq_iff_eq_mul]; rw [one_mul]; rw [coe_liftRight]

@[to_additive (attr := simp)]
/--
theorem `liftRight_inv_mul` / 定理 `liftRight_inv_mul`

English:
theorem liftRight_inv_mul
  given: {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x)
  proof: by
  rw [Units.inv_mul_eq_iff_eq_mul]; rw [mul_one]; rw [coe_liftRight]

中文:
定理 liftRight_inv_mul
  条件: {f : M ->* N} {g : M -> Nˣ} (h : 对任意 x, ↑(g x) = f x) (x)
  证明: by
  rw [Units.inv_mul_eq_iff_eq_mul]; rw [mul_one]; rw [coe_liftRight]

Depends on / 依赖: Units.inv_mul_eq_iff_eq_mul, coe_liftRight, inv_mul_eq_iff_eq_mul, mul_one
-/
theorem liftRight_inv_mul {f : M ->* N} {g : M -> Nˣ} (h : forall x, ↑(g x) = f x) (x) :
    ↑(liftRight f g h x)⁻¹ * f x = 1 := by
  rw [Units.inv_mul_eq_iff_eq_mul]; rw [mul_one]; rw [coe_liftRight]

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
/--
Definition of `toHomUnits` / `toHomUnits` 的定义

English:
definition toHomUnits
  signature: (f : G ->* M)
  body: Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_cancel _),
    map_mul_eq_one f (inv_mul_cancel _)⟩)
    fun _ => rfl

@[to_additive (attr := simp)]

中文:
定义 toHomUnits
  签名: (f : G ->* M)
  定义体: Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_cancel _),
    map_mul_eq_one f (inv_mul_cancel _)⟩)
    fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Units.liftRight, inv_mul_cancel, liftRight, map_mul_eq_one, mul_inv_cancel
-/
def toHomUnits (f : G ->* M) : G ->* Mˣ :=
  Units.liftRight f (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_cancel _),
    map_mul_eq_one f (inv_mul_cancel _)⟩)
    fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `coe_toHomUnits` / 定理 `coe_toHomUnits`

English:
theorem coe_toHomUnits
  given: (f : G ->* M) (g : G)
  statement: (f.toHomUnits g : M) = f g
  proof: rfl

中文:
定理 coe_toHomUnits
  条件: (f : G ->* M) (g : G)
  结论: (f.toHomUnits g : M) = f g
  证明: rfl
-/
theorem coe_toHomUnits (f : G ->* M) (g : G) : (f.toHomUnits g : M) = f g := rfl

end Monoid

variable [CommMonoid M]

/--
lemma `toHomUnits_mul` / 引理 `toHomUnits_mul`

English:
lemma toHomUnits_mul
  given: (f g : G ->* M)
  statement: (f * g).toHomUnits = f.toHomUnits * g.toHomUnits
  proof: by
  ext; rfl

中文:
引理 toHomUnits_mul
  条件: (f g : G ->* M)
  结论: (f * g).toHomUnits = f.toHomUnits * g.toHomUnits
  证明: by
  ext; rfl
-/
@[simp] lemma toHomUnits_mul (f g : G ->* M) : (f * g).toHomUnits = f.toHomUnits * g.toHomUnits := by
  ext; rfl

/--
Definition of `toHomUnitsMulEquiv` / `toHomUnitsMulEquiv` 的定义

English:
definition toHomUnitsMulEquiv
  signature: : (G ->* M) ≃* (G ->* Mˣ) where
  body: toHomUnits
  invFun f := (Units.coeHom _).comp f
  map_mul' := by simp

中文:
定义 toHomUnitsMulEquiv
  签名: : (G ->* M) ≃* (G ->* Mˣ) where
  定义体: toHomUnits
  invFun f := (Units.coeHom _).comp f
  map_mul' := by simp
-/
@[simps] def toHomUnitsMulEquiv : (G ->* M) ≃* (G ->* Mˣ) where
  toFun := toHomUnits
  invFun f := (Units.coeHom _).comp f
  map_mul' := by simp

end MonoidHom

namespace IsUnit

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive]
/--
theorem `map` / 定理 `map`

English:
theorem map
  given: [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x)
  statement: IsUnit (f x)
  proof: by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M ->* N) y).isUnit

@[to_additive]

中文:
定理 map
  条件: [幺半群态射类 F M N] (f : F) {x : M} (h : 是单位 x)
  结论: 是单位 (f x)
  证明: by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M ->* N) y).isUnit

@[to_additive]

Depends on / 依赖: GroupWithZero, GroupWithZero.noZeroDivisors, NoZeroDivisors, Units.map, isUnit, noZeroDivisors
-/
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M ->* N) y).isUnit

@[to_additive]
/--
theorem `unit_map` / 定理 `unit_map`

English:
theorem unit_map
  given: [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x)
  proof: rfl

@[to_additive]

中文:
定理 unit_map
  条件: [幺半群态射类 F M N] (f : F) {x : M} (h : 是单位 x)
  证明: rfl

@[to_additive]
-/
theorem unit_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    (h.map f).unit = f h.unit :=
  rfl

@[to_additive]
/--
theorem `unit_inv_map` / 定理 `unit_inv_map`

English:
theorem unit_inv_map
  given: [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x)
  proof: Units.inv_eq_of_mul_eq_one_left by simp [← map_mul]

@[to_additive]

中文:
定理 unit_inv_map
  条件: [幺半群态射类 F M N] (f : F) {x : M} (h : 是单位 x)
  证明: Units.inv_eq_of_mul_eq_one_left by simp [← map_mul]

@[to_additive]

Depends on / 依赖: Units.inv_eq_of_mul_eq_one_left, inv_eq_of_mul_eq_one_left, map_mul
-/
theorem unit_inv_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    (h.map f).unit⁻¹ = f ↑h.unit⁻¹ :=
Units.inv_eq_of_mul_eq_one_left by simp [← map_mul]

@[to_additive]
/--
theorem `of_leftInverse` / 定理 `of_leftInverse`

English:
theorem of_leftInverse
  statement: [MonoidHomClass G N M] {f : F} {x : M} (g : G)
  proof: by
  simpa only [hfg x] using h.map g

中文:
定理 of_leftInverse
  结论: [幺半群态射类 G N M] {f : F} {x : M} (g : G)
  证明: by
  simpa only [hfg x] using h.map g

Depends on / 依赖: h.map
-/
theorem of_leftInverse [MonoidHomClass G N M] {f : F} {x : M} (g : G)
    (hfg : Function.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x := by
  simpa only [hfg x] using h.map g

/-- Prefer `IsLocalHom.of_leftInverse`, but we can't get rid of this because of `ToAdditive`. -/
@[to_additive]
/--
theorem `_root_.isUnit_map_of_leftInverse` / 定理 `_root_.isUnit_map_of_leftInverse`

English:
theorem _root_.isUnit_map_of_leftInverse
  statement: [MonoidHomClass F M N] [MonoidHomClass G N M]
  proof: ⟨of_leftInverse g hfg, map _⟩

中文:
定理 _root_.isUnit_map_of_leftInverse
  结论: [幺半群态射类 F M N] [幺半群态射类 G N M]
  证明: ⟨of_leftInverse g hfg, map _⟩

Depends on / 依赖: of_leftInverse
-/
theorem _root_.isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M]
    {f : F} {x : M} (g : G) (hfg : Function.LeftInverse g f) :
    IsUnit (f x) ↔ IsUnit x := ⟨of_leftInverse g hfg, map _⟩

/-- If a homomorphism `f : M →* N` sends each element to an `IsUnit`, then it can be lifted
to `f : M →* Nˣ`. See also `Units.liftRight` for a computable version. -/
@[to_additive
  /-- If a homomorphism `f : M →+ N` sends each element to an `IsAddUnit`, then it can be
  lifted to `f : M →+ AddUnits N`. See also `AddUnits.liftRight` for a computable version. -/]
/--
Definition of `liftRight` / `liftRight` 的定义

English:
definition liftRight
  signature: (f : M ->* N) (hf : forall x, IsUnit (f x))
  body: (Units.liftRight f fun x => (hf x).unit) fun _ => rfl

@[to_additive]

中文:
定义 liftRight
  签名: (f : M ->* N) (hf : 对任意 x, 是单位 (f x))
  定义体: (Units.liftRight f fun x => (hf x).unit) fun _ => rfl

@[to_additive]

Depends on / 依赖: Units.liftRight, liftRight
-/
noncomputable def liftRight (f : M ->* N) (hf : forall x, IsUnit (f x)) : M ->* Nˣ :=
  (Units.liftRight f fun x => (hf x).unit) fun _ => rfl

@[to_additive]
/--
theorem `coe_liftRight` / 定理 `coe_liftRight`

English:
theorem coe_liftRight
  given: (f : M ->* N) (hf : forall x, IsUnit (f x)) (x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_liftRight
  条件: (f : M ->* N) (hf : 对任意 x, 是单位 (f x)) (x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_liftRight (f : M ->* N) (hf : forall x, IsUnit (f x)) (x) :
    (IsUnit.liftRight f hf x : N) = f x := rfl

@[to_additive (attr := simp)]
/--
theorem `mul_liftRight_inv` / 定理 `mul_liftRight_inv`

English:
theorem mul_liftRight_inv
  given: (f : M ->* N) (h : forall x, IsUnit (f x)) (x)
  proof: Units.mul_liftRight_inv (by intro; rfl) x

@[to_additive (attr := simp)]

中文:
定理 mul_liftRight_inv
  条件: (f : M ->* N) (h : 对任意 x, 是单位 (f x)) (x)
  证明: Units.mul_liftRight_inv (by intro; rfl) x

@[to_additive (attr := simp)]

Depends on / 依赖: Units.mul_liftRight_inv, mul_liftRight_inv
-/
theorem mul_liftRight_inv (f : M ->* N) (h : forall x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 := Units.mul_liftRight_inv (by intro; rfl) x

@[to_additive (attr := simp)]
/--
theorem `liftRight_inv_mul` / 定理 `liftRight_inv_mul`

English:
theorem liftRight_inv_mul
  given: (f : M ->* N) (h : forall x, IsUnit (f x)) (x)
  proof: Units.liftRight_inv_mul (by intro; rfl) x

@[to_additive]

中文:
定理 liftRight_inv_mul
  条件: (f : M ->* N) (h : 对任意 x, 是单位 (f x)) (x)
  证明: Units.liftRight_inv_mul (by intro; rfl) x

@[to_additive]

Depends on / 依赖: Units.liftRight_inv_mul, liftRight_inv_mul
-/
theorem liftRight_inv_mul (f : M ->* N) (h : forall x, IsUnit (f x)) (x) :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 := Units.liftRight_inv_mul (by intro; rfl) x

@[to_additive]
/--
theorem `liftRight_apply` / 定理 `liftRight_apply`

English:
theorem liftRight_apply
  given: (f : M ->* N) (hf : forall x, IsUnit (f x)) (x : M)
  proof: rfl

中文:
定理 liftRight_apply
  条件: (f : M ->* N) (hf : 对任意 x, 是单位 (f x)) (x : M)
  证明: rfl
-/
theorem liftRight_apply (f : M ->* N) (hf : forall x, IsUnit (f x)) (x : M) :
    IsUnit.liftRight f hf x = (hf x).unit :=
  rfl

end Monoid
end IsUnit

section IsLocalHom

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

/--
Definition of `IsLocalHom` / `IsLocalHom` 的定义

English:
class IsLocalHom
  parameters: (f : F)
  axioms and operations (1):
    - map_nonunit : forall a, IsUnit (f a) -> IsUnit a

中文:
类 是Local态射
  参数: (f : F)
  公理与运算 (1 个):
    - map_nonunit : 对任意 a, 是单位 (f a) -> 是单位 a
-/
class IsLocalHom (f : F) : Prop where
  /-- A local homomorphism `f : R ⟶ S` will send nonunits of `R` to nonunits of `S`. -/
  map_nonunit : forall a, IsUnit (f a) -> IsUnit a

/--
theorem `IsUnit.of_map` / 定理 `IsUnit.of_map`

English:
theorem IsUnit.of_map
  given: (f : F) [IsLocalHom f] (a : R) (h : IsUnit (f a))
  statement: IsUnit a
  proof: IsLocalHom.map_nonunit a h

中文:
定理 是单位.of_map
  条件: (f : F) [是Local态射 f] (a : R) (h : 是单位 (f a))
  结论: 是单位 a
  证明: IsLocalHom.map_nonunit a h

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, map_nonunit
-/
theorem IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit (f a)) : IsUnit a :=
  IsLocalHom.map_nonunit a h

-- TODO : remove alias, change the parenthesis of `f` and `a`
alias isUnit_of_map_unit := IsUnit.of_map

variable [MonoidHomClass F R S]

@[simp]
/--
theorem `isUnit_map_iff` / 定理 `isUnit_map_iff`

English:
theorem isUnit_map_iff
  given: (f : F) [IsLocalHom f] (a : R)
  statement: IsUnit (f a) ↔ IsUnit a
  proof: ⟨IsLocalHom.map_nonunit a, IsUnit.map f⟩

中文:
定理 isUnit_map_iff
  条件: (f : F) [是Local态射 f] (a : R)
  结论: 是单位 (f a) ↔ 是单位 a
  证明: ⟨IsLocalHom.map_nonunit a, IsUnit.map f⟩

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, IsUnit, IsUnit.map, map_nonunit
-/
theorem isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (f a) ↔ IsUnit a :=
  ⟨IsLocalHom.map_nonunit a, IsUnit.map f⟩

/--
theorem `isLocalHom_of_leftInverse` / 定理 `isLocalHom_of_leftInverse`

English:
theorem isLocalHom_of_leftInverse
  statement: [FunLike G S R] [MonoidHomClass G S R]
  proof: by rwa [isUnit_map_of_leftInverse g hfg] at ha

@[instance]

中文:
定理 isLocalHom_of_leftInverse
  结论: [函数状 G S R] [幺半群态射类 G S R]
  证明: by rwa [isUnit_map_of_leftInverse g hfg] at ha

@[instance]

Depends on / 依赖: isUnit_map_of_leftInverse
-/
theorem isLocalHom_of_leftInverse [FunLike G S R] [MonoidHomClass G S R]
    {f : F} (g : G) (hfg : Function.LeftInverse g f) : IsLocalHom f where
  map_nonunit a ha := by rwa [isUnit_map_of_leftInverse g hfg] at ha

@[instance]
/--
theorem `MonoidHom.isLocalHom_comp` / 定理 `MonoidHom.isLocalHom_comp`

English:
theorem MonoidHom.isLocalHom_comp
  statement: (g : S ->* T) (f : R ->* S) [IsLocalHom g]
  proof: IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

中文:
定理 幺半群态射.isLocalHom_comp
  结论: (g : S ->* T) (f : R ->* S) [是Local态射 g]
  证明: IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, map_nonunit
-/
theorem MonoidHom.isLocalHom_comp (g : S ->* T) (f : R ->* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

-- see note [lower instance priority]
@[instance 100]
/--
theorem `isLocalHom_toMonoidHom` / 定理 `isLocalHom_toMonoidHom`

English:
theorem isLocalHom_toMonoidHom
  given: (f : F) [IsLocalHom f]
  proof: ⟨IsLocalHom.map_nonunit (f := f)⟩

中文:
定理 isLocalHom_toMonoidHom
  条件: (f : F) [是Local态射 f]
  证明: ⟨IsLocalHom.map_nonunit (f := f)⟩

Depends on / 依赖: IsLocalHom, IsLocalHom.map_nonunit, map_nonunit
-/
theorem isLocalHom_toMonoidHom (f : F) [IsLocalHom f] :
    IsLocalHom (f : R ->* S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

/--
theorem `MonoidHom.isLocalHom_of_comp` / 定理 `MonoidHom.isLocalHom_of_comp`

English:
theorem MonoidHom.isLocalHom_of_comp
  given: (f : R ->* S) (g : S ->* T) [IsLocalHom (g.comp f)]
  proof: ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (ha.map g)⟩

中文:
定理 幺半群态射.isLocalHom_of_comp
  条件: (f : R ->* S) (g : S ->* T) [是Local态射 (g.comp f)]
  证明: ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (ha.map g)⟩

Depends on / 依赖: g.comp, ha.map, isUnit_map_iff
-/
theorem MonoidHom.isLocalHom_of_comp (f : R ->* S) (g : S ->* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (ha.map g)⟩

end IsLocalHom
