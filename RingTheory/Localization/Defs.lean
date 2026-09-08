/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.MonoidLocalization.Divisibility
public import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.Tactic.Ring

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

* `IsLocalization (M : Submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
  localization of `R` at `M`, i.e. the canonical map `algebraMap R S : R →+* S` is a
  localization map (satisfying the above properties).
* `IsLocalization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
* `IsLocalization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
  which maps elements of `M` to invertible elements of the codomain.
* `IsLocalization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
  of `M` to elements of `T`
* `IsLocalization.ringEquivOfRingEquiv`: if `R` and `P` are isomorphic by an isomorphism
  sending `M` to `T`, then `S` and `Q` are isomorphic

## Main results

* `Localization M S`, a construction of the localization as a quotient type, defined in
  `GroupTheory.MonoidLocalization`, has `CommRing`, `Algebra R` and `IsLocalization M`
  instances if `R` is a ring. `Localization.Away`, `Localization.AtPrime` and `FractionRing`
  are abbreviations for `Localization`s and have their corresponding `IsLocalization` instances

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists AlgHom Ideal

open Function

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

/-- An auxiliary typeclass to avoid auto-generated declarations
under the `IsLocalization` namespace. -/
/-
**IsLocalization'** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] → Submonoid R → (S : Type u_2) 
→ [inst_1 : CommSemiring S] → [Algebra R S] → Prop
参数：S : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary typeclass to avoid auto-generated declarations
under the `IsLocalization` namespace.
-/
class IsLocalization' : Prop extends M.IsLocalizationMap (algebraMap R S)

/-- The typeclass `IsLocalization (M : Submonoid R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
/-
**IsLocalization** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsLocalization
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass `IsLocalization (M : Submonoid R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`.
-/
abbrev IsLocalization := @IsLocalization'
/-
**isLocalization_iff_isLocalizationMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalization_iff_isLocalizationMap : IsLocalization M S ↔ M.IsLocalizati
onMap (algebraMap R S)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalization_iff_isLocalizationMap :
    IsLocalization M S ↔ M.IsLocalizationMap (algebraMap R S) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
/-
**isLocalization_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalization_iff : IsLocalization M S ↔ (forall y : M, IsUnit (algebraMa
p R S y)) ∧ (forall z : S, exists x : R × M, z * algebraMap R S x.2 = algebraMap
 R S x.1) ∧ forall {x y : R}, algebraMap R S x = algebraMap R S y -> exists c : 
M, c * x = c * y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocalization_iff_isLocalizationMap`：isLocalization_iff_isLocalizationM
ap : IsLocalization M S ↔ M.IsLocalizationMap (algebraMap R S)
· 使用定理 `Submonoid.isLocalizationMap_iff`：∀ {M : Type u_1} [inst : CommMonoid M] 
{N : Type u_2} [inst_1 : CommMonoid N] (S : Submonoid M) (f : M → N),   S.IsLoca
lizationMap f ↔     (…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLocalization_iff : IsLocalization M S ↔
    (∀ y : M, IsUnit (algebraMap R S y)) ∧
    (∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1) ∧
    ∀ {x y : R}, algebraMap R S x = algebraMap R S y → ∃ c : M, c * x = c * y := by
  rw [isLocalization_iff_isLocalizationMap, Submonoid.isLocalizationMap_iff]

variable {M}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

section

/-- Everything in the image of `algebraMap` is a unit. -/
/-
**IsLocalization.map_units** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_units : forall y : M, IsUnit (algebraMap R S y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.map_units`：∀ {M : Type u_1} [inst : CommMono
id M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.
IsLocalizationMap f → ∀ (y …
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…

--- 原说明 ---
Everything in the image of `algebraMap` is a unit.
-/
theorem map_units : ∀ y : M, IsUnit (algebraMap R S y) :=
  IsLocalization'.toIsLocalizationMap.map_units

variable (M) {S}
/-- Every element in the localization can be expressed as a quotient of an element in the
range of `algebraMap` by the image of an element of the submonoid. -/
/-
**IsLocalization.surj** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：surj : forall z : S, exists x : R × M, z * algebraMap R S x.2 = algebraMap
 R S x.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…

--- 原说明 ---
Every element in the localization can be expressed as a quotient of an element i
n the
range of `algebraMap` by the image of an element of the submonoid.
-/
theorem surj : ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1 :=
  IsLocalization'.toIsLocalizationMap.surj

variable {M} in
/-
**IsLocalization.exists_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：exists_of_eq {x y : R} : algebraMap R S x = algebraMap R S y -> exists c :
 M, c * x = c * y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.exists_of_eq`：∀ {M : Type u_1} [inst : CommM
onoid M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},  
 S.IsLocalizationMap f → ∀ {x …
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…
-/
theorem exists_of_eq {x y : R} : algebraMap R S x = algebraMap R S y → ∃ c : M, c * x = c * y :=
  IsLocalization'.toIsLocalizationMap.exists_of_eq

variable (S)

variable {M} in
/-
**IsLocalization.smul_bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：smul_bijective (m : M) : Bijective fun s : S => m • s
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsUnit.smul_bijective`：smul_bijective {m : α} (hm : IsUnit m) : Function
.Bijective (fun (a : β) => m • a)
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
-/
theorem smul_bijective (m : M) : Bijective fun s : S ↦ m • s := by
  simpa only [Submonoid.smul_def, Algebra.smul_def] using! (map_units S m).smul_bijective

/-- `IsLocalization.toLocalizationMap M S` shows `S` is the monoid localization of `R` at `M`. -/
/-
**IsLocalization.toLocalizationMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsLocalization`。
形式化陈述：toLocalizationMap : M.LocalizationMap S where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…

--- 原说明 ---
`IsLocalization.toLocalizationMap M S` shows `S` is the monoid localization of `
R` at `M`.
-/
abbrev toLocalizationMap : M.LocalizationMap S where
  __ := algebraMap R S
  toFun := algebraMap R S
  isLocalizationMap := IsLocalization'.toIsLocalizationMap

@[simp]
/-
**IsLocalization.toLocalizationMap_toMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `IsLoca
lization`。
形式化陈述：toLocalizationMap_toMonoidHom : (toLocalizationMap M S).toMonoidHom = (.of
Class (algebraMap R S) : R ->*₀ S)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLocalizationMap_toMonoidHom :
    (toLocalizationMap M S).toMonoidHom = (.ofClass (algebraMap R S) : R →*₀ S) := rfl
/-
**IsLocalization.coe_toLocalizationMap** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
, ⇑(IsLocalization.toLocalizationMap M S) = ⇑(algebraMap R S)
参数：M : Submonoid R；S : Type u_2；IsLocalization.toLocalizationMap M S；algebraMap 
R S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLocalizationMap : ⇑(toLocalizationMap M S) = algebraMap R S := rfl
/-
**IsLocalization.toLocalizationMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizati
on`。
形式化陈述：toLocalizationMap_apply (x) : toLocalizationMap M S x = algebraMap R S x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLocalizationMap_apply (x) : toLocalizationMap M S x = algebraMap R S x := rfl
/-
**IsLocalization.surj** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：surj : forall z : S, exists x : R × M, z * algebraMap R S x.2 = algebraMap
 R S x.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `IsLocalization'.toIsLocalizationMap`：∀ {R : Type u_1} {inst : CommSemiri
ng R} {M : Submonoid R} {S : Type u_2} {inst_1 : CommSemiring S}   {inst_2 : Alg
ebra R S} [self : IsLocal…
-/
theorem surj₂ : ∀ z w : S, ∃ z' w' : R, ∃ d : M,
    (z * algebraMap R S d = algebraMap R S z') ∧ (w * algebraMap R S d = algebraMap R S w') :=
  (toLocalizationMap M S).surj₂

/-- The kernel of `algebraMap` is equal to the annihilator by `map_units'` -/
/-
**IsLocalization.eq_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：eq_iff_exists {x y} : algebraMap R S x = algebraMap R S y ↔ exists c : M, 
↑c * x = ↑c * y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y

--- 原说明 ---
The kernel of `algebraMap` is equal to the annihilator by `map_units'`
-/
theorem eq_iff_exists {x y} : algebraMap R S x = algebraMap R S y ↔ ∃ c : M, ↑c * x = ↑c * y :=
  (toLocalizationMap M S).eq_iff_exists

variable {S}
/-
**IsLocalization.injective_iff_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：injective_iff_isRegular : Injective (algebraMap R S) ↔ forall c : M, IsReg
ular (c : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submonoid.LocalizationMap.injective_iff`：∀ {M : Type u_1} {N : Type u_2}
 [inst : CommMonoid M] {S : Submonoid M} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N), Function.Inject…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem injective_iff_isRegular : Injective (algebraMap R S) ↔ ∀ c : M, IsRegular (c : R) :=
  (toLocalizationMap M S).injective_iff.trans <| .symm Subtype.forall
/-
**IsLocalization.of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：of_le (N : Submonoid R) (h₁ : M <= N) (h₂ : forall r in N, IsUnit (algebra
Map R S r)) : IsLocalization N S where map_units r
参数：N : Submonoid R；h₁ : M <= N；h₂ : forall r in N, IsUnit (algebraMap R S r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
-/
theorem of_le (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ r ∈ N, IsUnit (algebraMap R S r)) :
    IsLocalization N S where
  map_units r := h₂ r r.2
  surj s :=
    have ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
    ⟨⟨x, y, h₁ hy⟩, H⟩
  exists_of_eq {x y} := by
    rw [IsLocalization.eq_iff_exists M]
    rintro ⟨c, hc⟩
    exact ⟨⟨c, h₁ c.2⟩, hc⟩
/-
**IsLocalization.of_le_of_exists_dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：of_le_of_exists_dvd (N : Submonoid R) (h₁ : M <= N) (h₂ : forall n in N, e
xists m in M, n ∣ m) : IsLocalization N S
参数：N : Submonoid R；h₁ : M <= N；h₂ : forall n in N, exists m in M, n ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.of_le`：of_le (N : Submonoid R) (h₁ : M <= N) (h₂ : forall
 r in N, IsUnit (algebraMap R S r)) : IsLocalization N S where map_units r
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
-/
theorem of_le_of_exists_dvd (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ n ∈ N, ∃ m ∈ M, n ∣ m) :
    IsLocalization N S :=
  of_le M N h₁ fun n hn ↦ have ⟨m, hm, dvd⟩ := h₂ n hn
    isUnit_of_dvd_unit (map_dvd _ dvd) (map_units S ⟨m, hm⟩)
/-
**IsLocalization.algebraMap_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：algebraMap_isUnit_iff {x : R} : IsUnit (algebraMap R S x) ↔ exists m in M,
 x ∣ m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_isUnit_iff`：∀ {M : Type u_1} {N : Type u_2
} [inst : CommMonoid M] {S : Submonoid M} [inst_1 : CommMonoid N]   (f : S.Local
izationMap N) {m : M}, IsUnit …
-/
theorem algebraMap_isUnit_iff {x : R} : IsUnit (algebraMap R S x) ↔ ∃ m ∈ M, x ∣ m :=
  (toLocalizationMap M S).map_isUnit_iff

end

variable (M) {S}

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
/-
**IsLocalization.sec** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：sec (z : S) : R × M
参数：z : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1

--- 原说明 ---
Given a localization map `f : M →* N`, a section function sending `z : N` to som
e
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`.
-/
noncomputable def sec (z : S) : R × M :=
  Classical.choose <| IsLocalization.surj _ z

@[simp]
/-
**IsLocalization.toLocalizationMap_sec** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：toLocalizationMap_sec : (toLocalizationMap M S).sec = sec M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLocalizationMap_sec : (toLocalizationMap M S).sec = sec M :=
  rfl

/-- Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
/-
**IsLocalization.sec_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：sec_spec (z : S) : z * algebraMap R S (IsLocalization.sec M z).2 = algebra
Map R S (IsLocalization.sec M z).1
参数：z : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1

--- 原说明 ---
Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M`
 such
that `z * f y = f x` (so this lemma is true by definition).
-/
theorem sec_spec (z : S) :
    z * algebraMap R S (IsLocalization.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1 :=
  Classical.choose_spec <| IsLocalization.surj _ z

/-- Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
/-
**IsLocalization.sec_spec'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：sec_spec' (z : S) : algebraMap R S (IsLocalization.sec M z).1 = algebraMap
 R S (IsLocalization.sec M z).2 * z
参数：z : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.sec_spec`：sec_spec (z : S) : z * algebraMap R S (IsLocali
zation.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1

--- 原说明 ---
Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M`
 such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativit
y.
-/
theorem sec_spec' (z : S) :
    algebraMap R S (IsLocalization.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2 * z := by
  rw [mul_comm, sec_spec]

variable {M}

/-- If `M` contains `0` then the localization at `M` is trivial. -/
/-
**IsLocalization.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：subsingleton (h : 0 in M) : Subsingleton S
参数：h : 0 in M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.subsingleton`：∀ {M : Type u_1} [inst : CommMon
oidWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N] 
  (f : S.LocalizationMap N),…

--- 原说明 ---
If `M` contains `0` then the localization at `M` is trivial.
-/
theorem subsingleton (h : 0 ∈ M) : Subsingleton S := (toLocalizationMap M S).subsingleton h
/-
**IsLocalization.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLocalization M S], Subsing
leton S ↔ 0 ∈ M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.subsingleton_iff`：∀ {M : Type u_1} [inst : Com
mMonoidWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero
 N]   (f : S.LocalizationMap N),…
-/
protected theorem subsingleton_iff : Subsingleton S ↔ 0 ∈ M :=
  (toLocalizationMap M S).subsingleton_iff
/-
**IsLocalization.map_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_right_cancel {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R 
S (c * y)) : algebraMap R S x = algebraMap R S y
参数：h : algebraMap R S (c * x) = algebraMap R S (c * y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_right_cancel`：map_right_cancel {x y} {c : 
S} (h : f (c * x) = f (c * y)) : f x = f y
-/
theorem map_right_cancel {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_right_cancel h
/-
**IsLocalization.map_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_left_cancel {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S
 (y * c)) : algebraMap R S x = algebraMap R S y
参数：h : algebraMap R S (x * c) = algebraMap R S (y * c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_left_cancel`：map_left_cancel {x y} {c : S}
 (h : f (x * c) = f (y * c)) : f x = f y
-/
theorem map_left_cancel {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_left_cancel h
/-
**IsLocalization.eq_zero_of_fst_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizatio
n`。
形式化陈述：eq_zero_of_fst_eq_zero {z x} {y : M} (h : z * algebraMap R S y = algebraMa
p R S x) (hx : x = 0) : z = 0
参数：h : z * algebraMap R S y = algebraMap R S x；hx : x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_left_eq_zero`：mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a
 * b = 0 ↔ a = 0
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem eq_zero_of_fst_eq_zero {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
    (hx : x = 0) : z = 0 := by
  rw [hx, (algebraMap R S).map_zero] at h
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h

variable (M S)
/-
**IsLocalization.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_eq_zero_iff (r : R) : algebraMap R S r = 0 ↔ exists m : M, ↑m * r = 0
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_eq_zero_iff`：map_eq_zero_iff (f : Localiza
tionMap S N) {m : M} : f m = 0 ↔ exists s : S, s * m = 0
-/
theorem map_eq_zero_iff (r : R) : algebraMap R S r = 0 ↔ ∃ m : M, ↑m * r = 0 :=
  (toLocalizationMap M S).map_eq_zero_iff

variable {M}

/-- `IsLocalization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
/-
**IsLocalization.mk'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization (Algebra.algebraMapSu
bmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x ⟨_, Algebra.mem_algeb
raMapSubmonoid_of_mem s⟩ = IsLocalizedModule.mk' (IsScalarTower.toAlgHom R A Aₛ)
.toLinearMap x s
参数：Algebra.algebraMapSubmonoid A S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsLocalization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`.
-/
noncomputable def mk' (x : R) (y : M) : S :=
  (toLocalizationMap M S).mk' x y

@[simp]
/-
**IsLocalization.mk'_sec** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (z : S),   IsLocalization.mk' S (IsLocalization.sec M z).1 (IsLocalization.sec 
M z).2 = z
参数：S : Type u_2；z : S；IsLocalization.sec M z；IsLocalization.sec M z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_sec`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (z : N), f.mk' (…
-/
theorem mk'_sec (z : S) : mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z :=
  (toLocalizationMap M S).mk'_sec _
/-
**IsLocalization.mk'_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x₁ x₂ : R) (y₁ y₂ : ↥M),   IsLocalization.mk' S (x₁ * x₂) (y₁ * y₂) = IsLocali
zation.mk' S x₁ y₁ * IsLocalization.mk' S x₂ y₂
参数：S : Type u_2；x₁ x₂ : R；y₁ y₂ : ↥M；x₁ * x₂；y₁ * y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_mul`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (x₁ x₂ : M) (y₁ …
-/
theorem mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) : mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
  (toLocalizationMap M S).mk'_mul _ _ _ _
/-
**IsLocalization.mk'_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R), IsLocalization.mk' S x 1 = (algebraMap R S) x
参数：S : Type u_2；x : R；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_one`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (x : M), f.mk' x…
-/
theorem mk'_one (x) : mk' S x (1 : M) = algebraMap R S x :=
  (toLocalizationMap M S).mk'_one _

@[simp]
/-
**IsLocalization.mk'_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M),   IsLocalization.mk' S x y * (algebraMap R S) ↑y = (algebraMa
p R S) x
参数：S : Type u_2；x : R；y : ↥M；algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_spec`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
-/
theorem mk'_spec (x) (y : M) : mk' S x y * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec _ _

@[simp]
/-
**IsLocalization.mk'_spec'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M),   (algebraMap R S) ↑y * IsLocalization.mk' S x y = (algebraMa
p R S) x
参数：S : Type u_2；x : R；y : ↥M；algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_spec'`：∀ {M : Type u_1} [inst : CommMonoid
 M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizati
onMap N) (x : M) (y : ↥S)…
-/
theorem mk'_spec' (x) (y : M) : algebraMap R S y * mk' S x y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec' _ _

@[simp]
/-
**IsLocalization.mk'_spec_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x y : R) (hy : y ∈ M),   IsLocalization.mk' S x ⟨y, hy⟩ * (algebraMap R S) y =
 (algebraMap R S) x
参数：S : Type u_2；x y : R；hy : y ∈ M；algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem mk'_spec_mk (x) (y : R) (hy : y ∈ M) :
    mk' S x ⟨y, hy⟩ * algebraMap R S y = algebraMap R S x :=
  mk'_spec S x ⟨y, hy⟩

@[simp]
/-
**IsLocalization.mk'_spec'_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x y : R) (hy : y ∈ M),   (algebraMap R S) y * IsLocalization.mk' S x ⟨y, hy⟩ =
 (algebraMap R S) x
参数：S : Type u_2；x y : R；hy : y ∈ M；algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
-/
theorem mk'_spec'_mk (x) (y : R) (hy : y ∈ M) :
    algebraMap R S y * mk' S x ⟨y, hy⟩ = algebraMap R S x :=
  mk'_spec' S x ⟨y, hy⟩

variable {S}
/-
**IsLocalization.eq_mk'_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} {y : ↥M} {z : S},   z = IsLocalization.mk' S x y ↔ z * (algebraMap R S)
 ↑y = (algebraMap R S) x
参数：algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq_mk'_iff_mul_eq`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) {x : M} {y : ↥S}…
-/
theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
    z = mk' S x y ↔ z * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).eq_mk'_iff_mul_eq
/-
**IsLocalization.eq_mk'_of_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} {y : ↥M} {z : R},   z * ↑y = x → (algebraMap R S) z = IsLocalization.mk
' S x y
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem eq_mk'_of_mul_eq {x : R} {y : M} {z : R} (h : z * y = x) : (algebraMap R S) z = mk' S x y :=
  eq_mk'_iff_mul_eq.mpr (by rw [← h, map_mul])
/-
**IsLocalization.mk'_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} {y : ↥M} {z : S},   IsLocalization.mk' S x y = z ↔ (algebraMap R S) x =
 z * (algebraMap R S) ↑y
参数：algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq_mul`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) {x : M} {y : ↥S}…
-/
theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
    mk' S x y = z ↔ algebraMap R S x = z * algebraMap R S y :=
  (toLocalizationMap M S).mk'_eq_iff_eq_mul
/-
**IsLocalization.mk'_add_eq_iff_add_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} {y : ↥M} {z₁ z₂ : S},   IsLocalization.mk' S x y + z₁ = z₂ ↔ (algebraMa
p R S) x + z₁ * (algebraMap R S) ↑y = z₂ * (algebraMap R S) ↑y
参数：algebraMap R S；algebraMap R S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk'_add_eq_iff_add_mul_eq_mul {x} {y : M} {z₁ z₂} :
    mk' S x y + z₁ = z₂ ↔ algebraMap R S x + z₁ * algebraMap R S y = z₂ * algebraMap R S y := by
  rw [← mk'_spec S x y, ← IsUnit.mul_left_inj (IsLocalization.map_units S y), right_distrib]
/-
**IsLocalization.mk'_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M) (n : ℕ),   IsLocalization.mk' S (x ^ n) (y ^ n) = IsLocalizati
on.mk' S x y ^ n
参数：x : R；y : ↥M；n : ℕ；x ^ n；y ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk'_pow (x : R) (y : M) (n : ℕ) : mk' S (x ^ n) (y ^ n) = mk' S x y ^ n := by
  simp_rw [IsLocalization.mk'_eq_iff_eq_mul, SubmonoidClass.coe_pow, map_pow, ← mul_pow]
  simp

variable (M)
/-
**IsLocalization.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
,   Function.Surjective fun x =>     match x with     | (r, m) => IsLocalization
.mk' S r m
参数：M : Submonoid R；r, m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
-/
theorem mk'_surjective : Surjective fun ((r, m) : R × M) ↦ mk' S r m := fun z ↦
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r, (eq_mk'_iff_mul_eq.2 hr).symm⟩
/-
**IsLocalization.exists_mk'_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (z : S), ∃ x y, IsLocalization.mk' S x y = z
参数：M : Submonoid R；z : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
-/
theorem exists_mk'_eq (z : S) : ∃ (x : R) (y : M), mk' S x y = z :=
  let ⟨⟨r, m⟩, hz⟩ := mk'_surjective M z; ⟨r, m, hz⟩

variable (S) in
/-- The localization of a `Fintype` is a `Fintype`. Cannot be an instance. -/
@[instance_reducible]
/-
**IsLocalization.fintype'** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：fintype' [Fintype R] : Fintype S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…

--- 原说明 ---
The localization of a `Fintype` is a `Fintype`. Cannot be an instance.
-/
noncomputable def fintype' [Fintype R] : Fintype S :=
  have := Classical.propDecidable
  .ofSurjective (Function.uncurry <| IsLocalization.mk' S) <| mk'_surjective M

variable {M}

/-- Localizing at a submonoid with 0 inside it leads to the trivial ring. -/
@[instance_reducible]
/-
**IsLocalization.uniqueOfZeroMem** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：uniqueOfZeroMem (h : (0 : R) in M) : Unique S
参数：h : (0 : R) in M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Localizing at a submonoid with 0 inside it leads to the trivial ring.
-/
def uniqueOfZeroMem (h : (0 : R) ∈ M) : Unique S :=
  uniqueOfZeroEqOne <| by simpa using IsLocalization.map_units S ⟨0, h⟩
/-
**IsLocalization.mk'_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x₁ x₂ : R} {y₁ y₂ : ↥M},   IsLocalization.mk' S x₁ y₁ = IsLocalization.mk' S x
₂ y₂ ↔ (algebraMap R S) (↑y₂ * x₁) = (algebraMap R S) (↑y₁ * x₂)
参数：algebraMap R S；↑y₂ * x₁；algebraMap R S；↑y₁ * x₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {x₁ x₂ : M} {y₁ …
-/
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (y₂ * x₁) = algebraMap R S (y₁ * x₂) :=
  (toLocalizationMap M S).mk'_eq_iff_eq
/-
**IsLocalization.mk'_eq_iff_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x₁ x₂ : R} {y₁ y₂ : ↥M},   IsLocalization.mk' S x₁ y₁ = IsLocalization.mk' S x
₂ y₂ ↔ (algebraMap R S) (x₁ * ↑y₂) = (algebraMap R S) (x₂ * ↑y₁)
参数：algebraMap R S；x₁ * ↑y₂；algebraMap R S；x₂ * ↑y₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq'`：∀ {M : Type u_1} [inst : CommM
onoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Local
izationMap N) {x₁ x₂ : M} {y₁ …
-/
theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (x₁ * y₂) = algebraMap R S (x₂ * y₁) :=
  (toLocalizationMap M S).mk'_eq_iff_eq'
/-
**IsLocalization.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {a₁ b₁ : R} {a₂ b₂ : ↥M},   IsLocalization.mk' S a₁ a₂ = IsLocalization.mk' S b
₁ b₂ ↔ ∃ c, ↑c * (↑b₂ * a₁) = ↑c * (↑a₂ * b₁)
参数：↑b₂ * a₁；↑a₂ * b₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq`：∀ {M : Type u_1} [inst : CommMonoid M] {S 
: Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.LocalizationMap N
) {a₁ b₁ : M} {a₂ …
-/
protected theorem eq {a₁ b₁} {a₂ b₂ : M} :
    mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  (toLocalizationMap M S).eq
/-
**IsLocalization.mk'_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (s : ↥M), IsLocalization.mk' S x s = 0 ↔ ∃ m, ↑m * x = 0
参数：x : R；s : ↥M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_zero_iff`：∀ {M : Type u_1} [inst : Comm
MonoidWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero 
N]   (f : S.LocalizationMap N) …
-/
theorem mk'_eq_zero_iff (x : R) (s : M) : mk' S x s = 0 ↔ ∃ m : M, ↑m * x = 0 :=
  (toLocalizationMap M S).mk'_eq_zero_iff x s

@[simp]
/-
**IsLocalization.mk'_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (s : ↥M), IsLocalization.mk' S 0 s = 0
参数：s : ↥M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_zero`：∀ {M : Type u_1} [inst : CommMonoidW
ithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   (f
 : S.LocalizationMap N) …
-/
theorem mk'_zero (s : M) : IsLocalization.mk' S 0 s = 0 :=
  (toLocalizationMap M S).mk'_zero s
/-
**IsLocalization.ne_zero_of_mk'_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizatio
n`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} {y : ↥M}, IsLocalization.mk' S x y ≠ 0 → x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : IsLocalization.mk' S x y ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)

/-- If we localise a ring `R` at a submonoid `M` made of regular elements, then `r / m : R[1/M]` is
regular iff `r : R` is. -/
/-
**IsLocalization.isRegular_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
,   (∀ m ∈ M, IsRegular m) → ∀ {r : R} {m : ↥M}, IsRegular (IsLocalization.mk' S
 r m) ↔ IsRegular r
参数：∀ m ∈ M, IsRegular m；IsLocalization.mk' S r m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S

--- 原说明 ---
If we localise a ring `R` at a submonoid `M` made of regular elements, then `r /
 m : R[1/M]` is
regular iff `r : R` is.
-/
@[simp] lemma isRegular_mk' (hM : ∀ m ∈ M, IsRegular m) {r : R} {m : M} :
    IsRegular (IsLocalization.mk' S r m) ↔ IsRegular r := by
  have (n : M) (x y : R) : n * x = n * y ↔ x = y := (hM _ n.2).1.eq_iff
  simp +contextual only [← isLeftRegular_iff_isRegular, IsLeftRegular, Function.Injective,
    (mk'_surjective M).forall, ← mk'_mul, Prod.forall, Subtype.forall, IsLocalization.eq,
    Submonoid.coe_mul, this, exists_const, mul_assoc]
  simp_rw [← mul_left_comm r]
  exact ⟨fun h a b ↦ by simpa using h a 1 M.one_mem b 1 M.one_mem, fun h ha s hs b t ht ↦ @h _ _⟩

include M in
variable (M) in
/-- Any localization of a commutative semiring without zero-divisors also has no zero-divisors. -/
/-
**IsLocalization.noZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.noZeroDivisors`：noZeroDivisors (f : Localizati
onMap S N) [NoZeroDivisors M] : NoZeroDivisors N

--- 原说明 ---
Any localization of a commutative semiring without zero-divisors also has no zer
o-divisors.
-/
theorem noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors S :=
  (toLocalizationMap M S).noZeroDivisors
/-
**IsLocalization.sec_fst_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：sec_fst_ne_zero {x : S} (hx : x != 0) : (sec M x).fst != 0
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_sec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem sec_fst_ne_zero {x : S} (hx : x ≠ 0) : (sec M x).fst ≠ 0 :=
  mt (fun h ↦ by rw [← mk'_sec (M := M) S x, h, mk'_zero]) hx

section Ext

/-
**IsLocalization.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：eq_iff_eq [Algebra R P] [IsLocalization M P] {x y} : algebraMap R S x = al
gebraMap R S y ↔ algebraMap R P x = algebraMap R P y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq_iff_eq`：eq_iff_eq (g : LocalizationMap S P)
 {x y} : f x = f y ↔ g x = g y
-/
theorem eq_iff_eq [Algebra R P] [IsLocalization M P] {x y} :
    algebraMap R S x = algebraMap R S y ↔ algebraMap R P x = algebraMap R P y :=
  (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)
/-
**IsLocalization.mk'_eq_iff_mk'_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] {P : Type u_3} [inst_3 : Comm
Semiring P] [inst_4 : IsLocalization M S] [inst_5 : Algebra R P]   [inst_6 : IsL
ocalization M P] {x₁ x₂ : R} {y₁ y₂ : ↥M},   IsLocalization.mk' S x₁ y₁ = IsLoca
lization.mk' S x₂ y₂ ↔ IsLocalization.mk' P x₁ y₁ = IsLocalization.mk' P x₂ y₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_mk'_eq`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N] {P : Type u
_3}   [inst_2 : CommMonoid P] (f …
-/
theorem mk'_eq_iff_mk'_eq [Algebra R P] [IsLocalization M P] {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
  (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)
/-
**IsLocalization.mk'_eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {a₁ b₁ : R} {a₂ b₂ : ↥M},   ↑a₂ * b₁ = ↑b₂ * a₁ → IsLocalization.mk' S a₁ a₂ = 
IsLocalization.mk' S b₁ b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_of_eq`：∀ {M : Type u_1} [inst : CommMon
oid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localiz
ationMap N) {a₁ b₁ : M} {a₂ …
-/
theorem mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq H
/-
**IsLocalization.mk'_eq_of_eq'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {a₁ b₁ : R} {a₂ b₂ : ↥M},   b₁ * ↑a₂ = a₁ * ↑b₂ → IsLocalization.mk' S a₁ a₂ = 
IsLocalization.mk' S b₁ b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_of_eq'`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {a₁ b₁ : M} {a₂ …
-/
theorem mk'_eq_of_eq' {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq' H
/-
**IsLocalization.mk'_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (a : R) (b c : ↥M),   IsLocalization.mk' S (a * ↑c) (b * c) = IsLocalization.mk
' S a b
参数：a : R；b c : ↥M；a * ↑c；b * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_cancel`：∀ {M : Type u_1} [inst : CommMonoi
d M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizat
ionMap N) (a : M) (b c : ↥…
-/
theorem mk'_cancel (a : R) (b c : M) :
    mk' S (a * c) (b * c) = mk' S a b := (toLocalizationMap M S).mk'_cancel _ _ _

variable (S)

@[simp]
/-
**IsLocalization.mk'_self** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} (hx : x ∈ M), IsLocalization.mk' S x ⟨x, hx⟩ = 1
参数：S : Type u_2；hx : x ∈ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_self`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (H : x ∈…
-/
theorem mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
  (toLocalizationMap M S).mk'_self _ hx

@[simp]
/-
**IsLocalization.mk'_self'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : ↥M}, IsLocalization.mk' S (↑x) x = 1
参数：S : Type u_2；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_self'`：∀ {M : Type u_1} [inst : CommMonoid
 M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizati
onMap N) (y : ↥S), f.mk' …
-/
theorem mk'_self' {x : M} : mk' S (x : R) x = 1 :=
  (toLocalizationMap M S).mk'_self' _
/-
**IsLocalization.mk'_self''** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : ↥M}, IsLocalization.mk' S (↑x) x = 1
参数：S : Type u_2；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.mk'_self'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
-/
theorem mk'_self'' {x : M} : mk' S x.1 x = 1 :=
  mk'_self' _

end Ext

/-
**IsLocalization.mul_mk'_eq_mk'_of_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x y : R) (z : ↥M),   (algebraMap R S) x * IsLocalization.mk' S y z = IsLocaliz
ation.mk' S (x * y) z
参数：x y : R；z : ↥M；algebraMap R S；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mul_mk'_eq_mk'_of_mul`：∀ {M : Type u_1} [inst 
: CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : 
S.LocalizationMap N) (x₁ x₂ : M) (y :…
-/
theorem mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
    (algebraMap R S) x * mk' S y z = mk' S (x * y) z :=
  (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _
/-
**IsLocalization.mk'_eq_mul_mk'_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M),   IsLocalization.mk' S x y = (algebraMap R S) x * IsLocalizat
ion.mk' S 1 y
参数：x : R；y : ↥M；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mul_mk'_one_eq_mk'`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.L
ocalizationMap N) (x : M) (y : ↥S)…
-/
theorem mk'_eq_mul_mk'_one (x : R) (y : M) : mk' S x y = (algebraMap R S) x * mk' S 1 y :=
  ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm

@[simp]
/-
**IsLocalization.mk'_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M),   IsLocalization.mk' S (↑y * x) y = (algebraMap R S) x
参数：x : R；y : ↥M；↑y * x；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_mul_cancel_left`：∀ {M : Type u_1} [inst : 
CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.
LocalizationMap N) (x : M) (y : ↥S)…
-/
theorem mk'_mul_cancel_left (x : R) (y : M) : mk' S (y * x : R) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_left _ _
/-
**IsLocalization.mk'_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`
。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M),   IsLocalization.mk' S (x * ↑y) y = (algebraMap R S) x
参数：x : R；y : ↥M；x * ↑y；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_mul_cancel_right`：∀ {M : Type u_1} [inst :
 CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S
.LocalizationMap N) (x : M) (y : ↥S)…
-/
theorem mk'_mul_cancel_right (x : R) (y : M) : mk' S (x * y) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_right _ _

@[simp]
/-
**IsLocalization.mk'_mul_mk'_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x y : ↥M),   IsLocalization.mk' S (↑x) y * IsLocalization.mk' S (↑y) x = 1
参数：x y : ↥M；↑x；↑y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem mk'_mul_mk'_eq_one (x y : M) : mk' S (x : R) y * mk' S (y : R) x = 1 := by
  rw [← mk'_mul, mul_comm]; exact mk'_self _ _
/-
**IsLocalization.mk'_mul_mk'_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (y : ↥M) (h : x ∈ M),   IsLocalization.mk' S x y * IsLocalization.mk' S
 ↑y ⟨x, h⟩ = 1
参数：x : R；y : ↥M；h : x ∈ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.mk'_mul_mk'_eq_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
-/
theorem mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) : mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
  mk'_mul_mk'_eq_one ⟨x, h⟩ _
/-
**IsLocalization.smul_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：smul_mk' (x y : R) (m : M) : x • mk' S y m = mk' S (x * y) m
参数：x y : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsLocalization.mk'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem smul_mk' (x y : R) (m : M) : x • mk' S y m = mk' S (x * y) m := by
  nth_rw 2 [← one_mul m]
  rw [mk'_mul, mk'_one, Algebra.smul_def]
/-
**IsLocalization.smul_mk'_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x : R) (m : ↥M),   x • IsLocalization.mk' S 1 m = IsLocalization.mk' S x m
参数：x : R；m : ↥M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.smul_mk'`：smul_mk' (x y : R) (m : M) : x • mk' S y m = mk
' S (x * y) m
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] theorem smul_mk'_one (x : R) (m : M) : x • mk' S 1 m = mk' S x m := by
  rw [smul_mk', mul_one]
/-
**IsLocalization.smul_mk'_self** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {m : ↥M} {r : R},   ↑m • IsLocalization.mk' S r m = (algebraMap R S) r
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.smul_mk'`：smul_mk' (x y : R) (m : M) : x • mk' S y m = mk
' S (x * y) m
· 使用定理 `IsLocalization.mk'_mul_cancel_left`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
-/
@[simp] lemma smul_mk'_self {m : M} {r : R} :
    (m : R) • mk' S r m = algebraMap R S r := by
  rw [smul_mk', mk'_mul_cancel_left]

@[simps]
/-
**IsLocalization.invertible_mk'_one** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {M : Submonoid R} →      
 {S : Type u_2} →         [inst_1 : CommSemiring S] →           [inst_2 : Algebr
a R S] → [inst_3 : IsLocalization M S] → (s : ↥M) → Invertible (IsLocalization.m
k' S 1 s)
参数：s : ↥M；IsLocalization.mk' S 1 s。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
-/
noncomputable instance invertible_mk'_one (s : M) :
    Invertible (IsLocalization.mk' S (1 : R) s) where
  invOf := algebraMap R S s
  invOf_mul_self := by simp
  mul_invOf_self := by simp

section

variable (M)

/-
**IsLocalization.isUnit_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isUnit_comp (j : S ->+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y)
参数：j : S ->+* P；y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.isUnit_comp`：isUnit_comp (j : N ->* P) (y : S)
 : IsUnit (j.comp f.toMonoidHom y)
-/
theorem isUnit_comp (j : S →+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y) :=
  (toLocalizationMap M S).isUnit_comp j.toMonoidHom _

end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →+* P` such that `g(M) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : R`. -/
/-
**IsLocalization.eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：eq_of_eq {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) {x y} (h : (alge
braMap R S) x = (algebraMap R S) y) : g x = g y
参数：hg : forall y : M, IsUnit (g y)；h : (algebraMap R S) x = (algebraMap R S) y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq_of_eq`：eq_of_eq (hg : forall y : S, IsUnit 
(g y)) {x y} (h : f x = f y) : g x = g y

--- 原说明 ---
Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `Com
mSemiring`s
`g : R →+* P` such that `g(M) ⊆ Units P`, `f x = f y → g x = g y` for all `x y :
 R`.
-/
theorem eq_of_eq {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) {x y}
    (h : (algebraMap R S) x = (algebraMap R S) y) : g x = g y :=
  Submonoid.LocalizationMap.eq_of_eq (toLocalizationMap M S) (g := g.toMonoidHom) hg h
/-
**IsLocalization.mk'_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (x₁ x₂ : R) (y₁ y₂ : ↥M),   IsLocalization.mk' S (x₁ * ↑y₂ + x₂ * ↑y₁) (y₁ * y₂
) = IsLocalization.mk' S x₁ y₁ + IsLocalization.mk' S x₂ y₂
参数：x₁ x₂ : R；y₁ y₂ : ↥M；x₁ * ↑y₂ + x₂ * ↑y₁；y₁ * y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `IsLocalization.mul_mk'_eq_mk'_of_mul`：∀ {R : Type u_1} [inst : CommSemir
ing R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Al
gebra R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_add_eq_iff_add_mul_eq_mul`：∀ {R : Type u_1} [inst : C
ommSemiring R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [ins
t_2 : Algebra R S] [inst_3 : IsLoc…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 40 条，此处仅展示前 30 条）
-/
theorem mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
  mk'_eq_iff_eq_mul.2 <|
    Eq.symm
      (by
        rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, mk'_add_eq_iff_add_mul_eq_mul,
          mul_comm (_ * _), ← mul_assoc, add_comm, ← map_mul, mul_mk'_eq_mk'_of_mul,
          mk'_add_eq_iff_add_mul_eq_mul]
        simp only [map_add, Submonoid.coe_mul, map_mul]
        ring)

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalization.mul_add_inv_left** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：mul_add_inv_left {g : R ->+* P} (h : forall y : M, IsUnit (g y)) (y : M) (
w z₁ z₂ : P) : w * ↑(IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y)⁻¹ + z₁ 
= z₂ ↔ w + g y * z₁ = g y * z₂
参数：h : forall y : M, IsUnit (g y)；y : M；w z₁ z₂ : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `IsUnit.coe_liftRight`：coe_liftRight (f : M ->* N) (hf : forall x, IsUnit
 (f x)) (x) : (IsUnit.liftRight f hf x : N) = f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_add_inv_left {g : R →+* P} (h : ∀ y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P) :
    w * ↑(IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y)⁻¹ + z₁ =
    z₂ ↔ w + g y * z₁ = g y * z₂ := by
  rw [mul_comm, ← one_mul z₁, ← Units.inv_mul (IsUnit.liftRight (g.toMonoidHom.domRestrict M) h y),
    mul_assoc, ← mul_add, Units.inv_mul_eq_iff_eq_mul, Units.inv_mul_cancel_left,
    IsUnit.coe_liftRight]
  simp [RingHom.toMonoidHom_eq_coe, MonoidHom.domRestrict_apply]
/-
**IsLocalization.lift_spec_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_spec_mul_add {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) (z w w'
 v) : ((toLocalizationMap M S).lift hg) z * w + w' = v ↔ g ((toLocalizationMap M
 S).sec z).1 * w + g ((toLocalizationMap M S).sec z).2 * w' = g ((toLocalization
Map M S).sec z).2 * v
参数：hg : forall y : M, IsUnit (g y)；z w w' v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `Submonoid.LocalizationMap.lift_apply`：lift_apply (z) : f.lift hg z = g (
f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsLocalization.mul_add_inv_left`：mul_add_inv_left {g : R ->+* P} (h : fo
rall y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P) : w * ↑(IsUnit.liftRight (g.toMo
noidHom.domRestrict M…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_spec_mul_add {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) (z w w' v) :
    ((toLocalizationMap M S).lift hg) z * w + w' = v ↔
      g ((toLocalizationMap M S).sec z).1 * w + g ((toLocalizationMap M S).sec z).2 * w' =
        g ((toLocalizationMap M S).sec z).2 * v := by
  rw [mul_comm, Submonoid.LocalizationMap.lift_apply, ← mul_assoc, mul_add_inv_left hg,
    mul_comm]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
/-
**IsLocalization.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：lift {g : R ->+* P} (hg : forall y : M, IsUnit (g y)) : S ->+* P
参数：hg : forall y : M, IsUnit (g y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `Com
mSemiring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism in
duced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such t
hat
`z = f x * (f y)⁻¹`.
-/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) : S →+* P :=
  { (toLocalizationMap M S).lift₀ g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      dsimp
      rw [(toLocalizationMap M S).lift₀_def, (toLocalizationMap M S).lift_spec,
        mul_add, mul_comm, eq_comm, lift_spec_mul_add, add_comm, mul_comm, mul_assoc, mul_comm,
        mul_assoc, lift_spec_mul_add]
      simp_rw [← mul_assoc]
      change g _ * g _ * g _ + g _ * g _ * g _ = g _ * g _ * g _
      simp_rw [← map_mul g, ← map_add g]
      apply eq_of_eq (S := S) hg
      simp only [sec_spec', toLocalizationMap_sec, map_add, map_mul]
      ring }

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
/-
**IsLocalization.lift_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_mk' (x y) : lift hg (mk' S x y) = g x * ↑(IsUnit.liftRight (g.toMonoi
dHom.domRestrict M) hg y)⁻¹
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹

--- 原说明 ---
Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `Com
mSemiring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism ind
uced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`.
-/
theorem lift_mk' (x y) :
    lift hg (mk' S x y) = g x * ↑(IsUnit.liftRight (g.toMonoidHom.domRestrict M) hg y)⁻¹ :=
  (toLocalizationMap M S).lift_mk' _ _ _
/-
**IsLocalization.lift_mk'_spec** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] {P : Type u_3} [inst_3 : Comm
Semiring P] [inst_4 : IsLocalization M S] {g : R →+* P}   (hg : ∀ (y : ↥M), IsUn
it (g ↑y)) (x : R) (v : P) (y : ↥M),   (IsLocalization.lift hg) (IsLocalization.
mk' S x y) = v ↔ g x = g ↑y * v
参数：hg : ∀ (y : ↥M), IsUnit (g ↑y)；x : R；v : P；y : ↥M；IsLocalization.lift hg；IsLo
calization.mk' S x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_mk'_spec`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N] {P : Type u_3} 
  [inst_2 : CommMonoid P] (f …
-/
theorem lift_mk'_spec (x v) (y : M) : lift hg (mk' S x y) = v ↔ g x = g y * v :=
  (toLocalizationMap M S).lift_mk'_spec _ _ _ _

@[simp]
/-
**IsLocalization.lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
-/
theorem lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x :=
  (toLocalizationMap M S).lift_eq _ _
/-
**IsLocalization.lift_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_eq_iff {x y : R × M} : lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y
.2) ↔ g (x.1 * y.2) = g (y.1 * x.2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_eq_iff`：lift_eq_iff {x y : M × S} : f.lif
t hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2)
-/
theorem lift_eq_iff {x y : R × M} :
    lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
  (toLocalizationMap M S).lift_eq_iff _

@[simp]
/-
**IsLocalization.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_comp : (lift hg).comp (algebraMap R S) = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Submonoid.LocalizationMap.lift_comp`：lift_comp : (f.lift hg).comp f.toMo
noidHom = g
-/
theorem lift_comp : (lift hg).comp (algebraMap R S) = g :=
  RingHom.ext <| (DFunLike.ext_iff (F := MonoidHom _ _)).1 <| (toLocalizationMap M S).lift_comp _

@[simp]
/-
**IsLocalization.lift_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_of_comp (j : S ->+* P) : lift (isUnit_comp M j) = j
参数：j : S ->+* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsLocalization.isUnit_comp`：isUnit_comp (j : S ->+* P) (y : M) : IsUnit 
(j.comp (algebraMap R S) y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Submonoid.LocalizationMap.lift_of_comp`：lift_of_comp (j : N ->* P) : f.l
ift (f.isUnit_comp j) = j
-/
theorem lift_of_comp (j : S →+* P) : lift (isUnit_comp M j) = j :=
  RingHom.ext <| (DFunLike.ext_iff (F := MonoidHom _ _)).1 <|
    (toLocalizationMap M S).lift_of_comp j.toMonoidHom

variable (M)

section
include M

/-- See note [partially-applied ext lemmas] -/
/-
**IsLocalization.monoidHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：monoidHom_ext {P : Type*} [Monoid P] ⦃j k : S ->* P⦄ (h : j.comp (algebraM
ap R S : R ->* S) = k.comp (algebraMap R S)) : j = k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.LocalizationMap.epic_of_localizationMap`：epic_of_localizationM
ap {P : Type*} [Monoid P] {j k : N ->* P} (h : j.comp f.toMonoidHom = k.comp f.t
oMonoidHom) : j = k

--- 原说明 ---
See note [partially-applied ext lemmas]
-/
theorem monoidHom_ext {P : Type*} [Monoid P] ⦃j k : S →* P⦄
    (h : j.comp (algebraMap R S : R →* S) = k.comp (algebraMap R S)) : j = k :=
  (toLocalizationMap M S).epic_of_localizationMap h

/-- See note [partially-applied ext lemmas] -/
/-
**IsLocalization.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：ringHom_ext {P : Type*} [Semiring P] ⦃j k : S ->+* P⦄ (h : j.comp (algebra
Map R S) = k.comp (algebraMap R S)) : j = k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.coe_monoidHom_injective`：coe_monoidHom_injective : Injective (fu
n f : α ->+* β => (f : α ->* β))
· 使用定理 `IsLocalization.monoidHom_ext`：monoidHom_ext {P : Type*} [Monoid P] ⦃j k 
: S ->* P⦄ (h : j.comp (algebraMap R S : R ->* S) = k.comp (algebraMap R S)) : j
 = k
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2

--- 原说明 ---
See note [partially-applied ext lemmas]
-/
theorem ringHom_ext {P : Type*} [Semiring P] ⦃j k : S →+* P⦄
    (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) :
    j = k :=
  RingHom.coe_monoidHom_injective <| monoidHom_ext M <| MonoidHom.ext <| RingHom.congr_fun h

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
/-
**IsLocalization.ext** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLocalization M S] {P : Typ
e u_4} [inst_4 : Monoid P] (j k : S → P),   j 1 = 1 →     k 1 = 1 →       (∀ (a 
b : S), j (a * b) = j a * j b) →         (∀ (a b : S), k (a * b) = k a * k b) → 
(∀ (a : R), j ((algebraMap R S) a) = k ((algebraMap R S) a)) → j = k
参数：M : Submonoid R；j k : S → P；∀ (a b : S), j (a * b) = j a * j b；∀ (a b : S), k
 (a * b) = k a * k b；∀ (a : R), j ((algebraMap R S) a) = k ((algebraMap R S) a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.monoidHom_ext`：monoidHom_ext {P : Type*} [Monoid P] ⦃j k 
: S ->* P⦄ (h : j.comp (algebraMap R S : R ->* S) = k.comp (algebraMap R S)) : j
 = k
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
To show `j` and `k` agree on the whole localization, it suffices to show they ag
ree
on the image of the base ring, if they preserve `1` and `*`.
-/
protected theorem ext {P : Type*} [Monoid P] (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
    (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
    (h : ∀ a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]
end

variable {M}

/-
**IsLocalization.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_unique {j : S ->+* P} (hj : forall x, j ((algebraMap R S) x) = g x) :
 lift hg = j
参数：hj : forall x, j ((algebraMap R S) x) = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Submonoid.LocalizationMap.lift_unique`：lift_unique {j : N ->* P} (hj : f
orall x, j (f x) = g x) : f.lift hg = j
-/
theorem lift_unique {j : S →+* P} (hj : ∀ x, j ((algebraMap R S) x) = g x) : lift hg = j :=
  RingHom.ext <|
    (DFunLike.ext_iff (F := MonoidHom _ _)).1 <|
      Submonoid.LocalizationMap.lift_unique (toLocalizationMap M S) (g := g.toMonoidHom) hg
        (j := j.toMonoidHom) hj

@[simp]
/-
**IsLocalization.lift_id** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_id (x) : lift (map_units S : forall _ : M, IsUnit _) x = x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_id`：lift_id (x) : f.lift f.map_units x = 
x
-/
theorem lift_id (x) : lift (map_units S : ∀ _ : M, IsUnit _) x = x :=
  (toLocalizationMap M S).lift_id _
/-
**IsLocalization.lift_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_surjective_iff : Surjective (lift hg : S -> P) ↔ forall v : P, exists
 x : R × M, v * g x.2 = g x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_surjective_iff`：lift_surjective_iff : Fun
ction.Surjective (f.lift hg) ↔ forall v : P, exists x : M × S, v * g x.2 = g x.1
-/
theorem lift_surjective_iff :
    Surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
  (toLocalizationMap M S).lift_surjective_iff hg
/-
**IsLocalization.lift_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_injective_iff : Injective (lift hg : S -> P) ↔ forall x y, algebraMap
 R S x = algebraMap R S y ↔ g x = g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_injective_iff`：lift_injective_iff : Funct
ion.Injective (f.lift hg) ↔ forall x y, f x = f y ↔ g x = g y
-/
theorem lift_injective_iff :
    Injective (lift hg : S → P) ↔ ∀ x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (toLocalizationMap M S).lift_injective_iff hg

variable (M) in
include M in
/-
**IsLocalization.injective_iff_map_algebraMap_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsLo
calization`。
形式化陈述：injective_iff_map_algebraMap_eq {T} [CommSemiring T] (f : S ->+* T) : Func
tion.Injective f ↔ forall x y, algebraMap R S x = algebraMap R S y ↔ f (algebraM
ap R S x) = f (algebraMap R S y)
参数：f : S ->+* T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isUnit_comp`：isUnit_comp (j : S ->+* P) (y : M) : IsUnit 
(j.comp (algebraMap R S) y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.lift_of_comp`：lift_of_comp (j : S ->+* P) : lift (isUnit_
comp M j) = j
· 使用定理 `IsLocalization.lift_injective_iff`：lift_injective_iff : Injective (lift 
hg : S -> P) ↔ forall x y, algebraMap R S x = algebraMap R S y ↔ g x = g y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma injective_iff_map_algebraMap_eq {T} [CommSemiring T] (f : S →+* T) :
    Function.Injective f ↔ ∀ x y,
      algebraMap R S x = algebraMap R S y ↔ f (algebraMap R S x) = f (algebraMap R S y) := by
  rw [← IsLocalization.lift_of_comp (M := M) f, IsLocalization.lift_injective_iff]
  simp

section Map

variable {T : Submonoid P} {Q : Type*} [CommSemiring Q]
variable [Algebra P Q] [IsLocalization T Q]

section

variable (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebraMap P Q (g x) * (algebraMap P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
/-
**IsLocalization.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：map (g : R ->+* P) (hy : M <= T.comap g) : S ->+* Q
参数：g : R ->+* P；hy : M <= T.comap g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebraMap P Q (g x) * (algebraMap P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`.
-/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

end

section
variable (hy : M ≤ T.comap g)
include hy

@[simp]
/-
**IsLocalization.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x)
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]
/-
**IsLocalization.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.lift_comp`：lift_comp : (lift hg).comp (algebraMap R S) = 
g
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp fun y => map_units _ ⟨g y, hy y.2⟩
/-
**IsLocalization.map_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩
参数：x；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.LocalizationMap.map_mk'`：map_mk' (x) (y : S) : f.map hy k (f.m
k' x y) = k.mk' (g x) ⟨g y, hy y⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  Submonoid.LocalizationMap.map_mk' (toLocalizationMap M S) (g := g.toMonoidHom)
    (fun y => hy y.2) (k := toLocalizationMap T Q) ..
/-
**IsLocalization.map_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_unique (j : S ->+* Q) (hj : forall x : R, j (algebraMap R S x) = algeb
raMap P Q (g x)) : map Q g hy = j
参数：j : S ->+* Q；hj : forall x : R, j (algebraMap R S x) = algebraMap P Q (g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.lift_unique`：lift_unique {j : S ->+* P} (hj : forall x, j
 ((algebraMap R S) x) = g x) : lift hg = j
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_unique (j : S →+* Q) (hj : ∀ x : R, j (algebraMap R S x) = algebraMap P Q (g x)) :
    map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
/-
**IsLocalization.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_comp_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemir
ing W] [Algebra A W] [IsLocalization U W] {l : P ->+* A} (hl : T <= U.comap l) :
 (map W l hl).comp (map Q g hy : S ->+* _) = map W (l.comp g) fun _ hx => hl (hy
 hx)
参数：hl : T <= U.comap l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Submonoid.LocalizationMap.map_map`：map_map {A : Type*} [CommMonoid A] {U
 : Submonoid A} {R} [CommMonoid R] (j : LocalizationMap U R) {l : P ->* A} (hl :
 forall w : T, l w in U…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, 
the composition
of the induced maps equals the map of localizations induced by `l ∘ g`.
-/
theorem map_comp_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
    [Algebra A W] [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
    (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) fun _ hx => hl (hy hx) :=
  RingHom.ext fun x =>
    Submonoid.LocalizationMap.map_map (P := P) (toLocalizationMap M S) (fun y => hy y.2)
      (toLocalizationMap U W) (fun w => hl w.2) x

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
/-
**IsLocalization.map_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W
] [Algebra A W] [IsLocalization U W] {l : P ->+* A} (hl : T <= U.comap l) (x : S
) : map W l hl (map Q g hy x) = map W (l.comp g) (fun _ hx => hl (hy hx)) x
参数：hl : T <= U.comap l；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.map_comp_map`：map_comp_map {A : Type*} [CommSemiring A] {
U : Submonoid A} {W} [CommSemiring W] [Algebra A W] [IsLocalization U W] {l : P 
->+* A} (hl : T <…

--- 原说明 ---
If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, 
the composition
of the induced maps equals the map of localizations induced by `l ∘ g`.
-/
theorem map_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
    [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
    map W l hl (map Q g hy x) = map W (l.comp g) (fun _ hx => hl (hy hx)) x := by
  rw [← map_comp_map (Q := Q) hy hl]; rfl
/-
**IsLocalization.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] {P : Type u_3} [inst_3 : Comm
Semiring P] [inst_4 : IsLocalization M S] {g : R →+* P}   {T : Submonoid P} {Q :
 Type u_4} [inst_5 : CommSemiring Q] [inst_6 : Algebra P Q] [inst_7 : IsLocaliza
tion T Q]   (hy : M ≤ Submonoid.comap g T) (x : S) (z : R),   (IsLocalization.ma
p Q g hy) (z • x) = g z • (IsLocalization.map Q g hy) x
参数：hy : M ≤ Submonoid.comap g T；x : S；z : R；IsLocalization.map Q g hy；z • x；IsLo
calization.map Q g hy。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
-/
protected theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_eq]

end

@[simp]
/-
**IsLocalization.map_id_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_id_mk' {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]
 (x) (y : M) : map Q (RingHom.id R) (le_refl M) (mk' S x y) = mk' Q x y
参数：x；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_id_mk' {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q] (x) (y : M) :
    map Q (RingHom.id R) (le_refl M) (mk' S x y) = mk' Q x y :=
  map_mk' ..

@[simp]
/-
**IsLocalization.map_id** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_id (z : S) (h : M <= M.comap (RingHom.id R)
参数：z : S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.lift_id`：lift_id (x) : lift (map_units S : forall _ : M, 
IsUnit _) x = x
-/
theorem map_id (z : S) (h : M ≤ M.comap (RingHom.id R) := le_refl M) :
    map S (RingHom.id _) h z = z :=
  lift_id _

section

variable (S Q)

set_option backward.isDefEq.respectTransparency false in
/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps apply]
/-
**IsLocalization.ringEquivOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`
。
形式化陈述：ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q
参数：h : R ≃+* P；H : M.map h.toMonoidHom = T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, 
an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localiz
ations
`S ≃+* Q`.
-/
noncomputable def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id, ← H, Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp
    right_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp }

end

/-
**IsLocalization.ringEquivOfRingEquiv_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation`。
形式化陈述：ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) : 
(ringEquivOfRingEquiv S Q j H : S ->+* Q) = map Q (j : R ->+* P) (M.le_comap_of_
map_le (le_of_eq H))
参数：H : M.map j.toMonoidHom = T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) :
    (ringEquivOfRingEquiv S Q j H : S →+* Q) =
      map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl
/-
**IsLocalization.ringEquivOfRingEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizati
on`。
形式化陈述：ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) : 
ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x)
参数：H : M.map j.toMonoidHom = T；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.ringEquivOfRingEquiv_apply`：∀ {R : Type u_1} [inst : Comm
Semiring R] {M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] {P : Type u_3} …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
    ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) := by
  simp
/-
**IsLocalization.ringEquivOfRingEquiv_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : 
R) (y : M) : ringEquivOfRingEquiv S Q j H (mk' S x y) = mk' Q (j x) ⟨j y, show j
 y in T from H ▸ Set.mem_image_of_mem j y.2⟩
参数：H : M.map j.toMonoidHom = T；x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.ringEquivOfRingEquiv_apply`：∀ {R : Type u_1} [inst : Comm
Semiring R] {M : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] {P : Type u_3} …
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M) :
    ringEquivOfRingEquiv S Q j H (mk' S x y) =
      mk' Q (j x) ⟨j y, show j y ∈ T from H ▸ Set.mem_image_of_mem j y.2⟩ := by
  simp [map_mk']

@[simp]
/-
**IsLocalization.ringEquivOfRingEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion`。
形式化陈述：ringEquivOfRingEquiv_symm {j : R ≃+* P} (H : M.map j = T) : (ringEquivOfRi
ngEquiv S Q j H).symm = ringEquivOfRingEquiv Q S j.symm (show T.map (j : R ≃* P)
.symm = M by rw [← H]; rw [← Submonoid.comap_equiv_eq_map_symm]; rw [← Submonoid
.map_coe_toMulEquiv]; rw [Submonoid.comap_map_eq_of_injective (j : R ≃* P).injec
tive])
参数：H : M.map j = T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem ringEquivOfRingEquiv_symm {j : R ≃+* P} (H : M.map j = T) :
    (ringEquivOfRingEquiv S Q j H).symm =
      ringEquivOfRingEquiv Q S j.symm (show T.map (j : R ≃* P).symm = M by
        rw [← H, ← Submonoid.comap_equiv_eq_map_symm, ← Submonoid.map_coe_toMulEquiv,
          Submonoid.comap_map_eq_of_injective (j : R ≃* P).injective]) := rfl

end Map

section

variable (M S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

/-- Injectivity of a map descends to the map induced on localizations. -/
/-
**IsLocalization.map_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
ation`。
形式化陈述：map_injective_of_injective (h : Function.Injective g) [IsLocalization (M.m
ap g) Q] : Function.Injective (map Q g M.le_comap_map : S -> Q)
参数：h : Function.Injective g；M.map g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.LocalizationMap.map_injective_of_injective`：map_injective_of_i
njective (hg : Injective g) (k : LocalizationMap (S.map g) Q) : Injective (map f
 (apply_coe_mem_map g S) k)

--- 原说明 ---
Injectivity of a map descends to the map induced on localizations.
-/
theorem map_injective_of_injective (h : Function.Injective g) [IsLocalization (M.map g) Q] :
    Function.Injective (map Q g M.le_comap_map : S → Q) :=
  (toLocalizationMap M S).map_injective_of_injective h (toLocalizationMap (M.map g) Q)

/-- Surjectivity of a map descends to the map induced on localizations. -/
/-
**IsLocalization.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
ization`。
形式化陈述：map_surjective_of_surjective (h : Function.Surjective g) [IsLocalization (
M.map g) Q] : Function.Surjective (map Q g M.le_comap_map : S -> Q)
参数：h : Function.Surjective g；M.map g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.LocalizationMap.map_surjective_of_surjective`：map_surjective_o
f_surjective (hg : Surjective g) (k : LocalizationMap (S.map g) Q) : Surjective 
(map f (apply_coe_mem_map g S) k)

--- 原说明 ---
Surjectivity of a map descends to the map induced on localizations.
-/
theorem map_surjective_of_surjective (h : Function.Surjective g) [IsLocalization (M.map g) Q] :
    Function.Surjective (map Q g M.le_comap_map : S → Q) :=
  (toLocalizationMap M S).map_surjective_of_surjective h (toLocalizationMap (M.map g) Q)

end

end IsLocalization

section

variable (M)

/-
**isLocalization_of_base_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalization_of_base_ringEquiv [IsLocalization M S] (h : R ≃+* P) :
    haveI := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
    IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  constructor; constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert! IsLocalization.map_units S ⟨y, hy⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    exact congr_arg _ (h.symm_apply_apply _)
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M y
    refine ⟨⟨h x, _, _, s.prop, rfl⟩, ?_⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at e ⊢
    convert! e <;> exact h.symm_apply_apply _
  · intro x y
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply,
      IsLocalization.eq_iff_exists M S]
    simp [← h.toEquiv.apply_eq_iff_eq]
/-
**isLocalization_iff_of_base_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isLocalization_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsLocalization M S ↔
      haveI := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
      IsLocalization (M.map h) S := by
  let : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  refine ⟨fun _ => isLocalization_of_base_ringEquiv M S h, ?_⟩
  intro (H : IsLocalization (Submonoid.map (h : R ≃* P) M) S)
  convert! isLocalization_of_base_ringEquiv (Submonoid.map (h : R ≃* P) M) S h.symm
  · rw [← Submonoid.map_coe_toMulEquiv, RingEquiv.coe_toMulEquiv_symm, ←
      Submonoid.comap_equiv_eq_map_symm, Submonoid.comap_map_eq_of_injective]
    exact h.toEquiv.injective
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc]
  simp only [RingHom.comp_id, RingEquiv.symm_symm, RingEquiv.symm_toRingHom_comp_toRingHom]
  apply Algebra.algebra_ext
  intro r
  rw [RingHom.algebraMap_toAlgebra]
/-
**of_ringEquiv_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_ringEquiv_left {S : Type*} [CommSemiring S] {K : Type*} [CommSemiring K]
    [Algebra R K] (e : R ≃+* S) [Algebra S K] {M₁ : Submonoid S} {M₂ : Submonoid R}
    (hM : M₂.map e = M₁) (h : ∀ x, algebraMap R K x = algebraMap S K (e x)) [IsLocalization M₁ K] :
    IsLocalization M₂ K := by
  rw [IsLocalization.isLocalization_iff_of_base_ringEquiv _ _ e, hM]
  convert! (inferInstance : IsLocalization M₁ K)
  exact Algebra.algebra_ext _ _ (by simp [RingHom.algebraMap_toAlgebra, h])

end

variable (M)

/-
**nonZeroDivisors_le_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonZeroDivisors_le_comap [IsLocalization M S] :
    nonZeroDivisors R ≤ (nonZeroDivisors S).comap (algebraMap R S) :=
  (toLocalizationMap M S).nonZeroDivisors_le_comap
/-
**map_nonZeroDivisors_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_nonZeroDivisors_le [IsLocalization M S] :
    (nonZeroDivisors R).map (algebraMap R S) ≤ nonZeroDivisors S :=
  (toLocalizationMap M S).map_nonZeroDivisors_le

end IsLocalization

namespace Localization

open IsLocalization

/-! ### Constructing a localization at a given submonoid -/

section

/-
**Localization.instUniqueLocalization** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：instUniqueLocalization [Subsingleton R] : Unique (Localization M) where un
iq a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniqueLocalization [Subsingleton R] : Unique (Localization M) where
  uniq a := by
    with_unfolding_all change a = mk 1 1
    exact Localization.induction_on a fun _ => by
      congr <;> apply Subsingleton.elim
/-
**Localization.add_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：add_mk (a b c d) : (mk a b : Localization M) + mk c d = mk ((b : R) * c + 
(d : R) * a) (b * d)
参数：a b c d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `OreLocalization.oreDiv_add_oreDiv`：oreDiv_add_oreDiv {r r' : X} {s s' : 
S} : r /ₒ s + r' /ₒ s' = (oreDenom (s : R) s' • r + oreNum (s : R) s' • r') /ₒ (
oreDenom (s : R) s' * s…
-/
theorem add_mk (a b c d) : (mk a b : Localization M) + mk c d =
    mk ((b : R) * c + (d : R) * a) (b * d) := by
  rw [add_comm (b * c) (d * a), mul_comm b d]
  exact OreLocalization.oreDiv_add_oreDiv
/-
**Localization.add_mk_self** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：add_mk_self (a b c) : (mk a b : Localization M) + mk c b = mk (a + c) b
参数：a b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.add_mk`：add_mk (a b c d) : (mk a b : Localization M) + mk c
 d = mk ((b : R) * c + (d : R) * a) (b * d)
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
· 使用定理 `Localization.r_eq_r'`：r_eq_r' : r S = r' S
· 使用定理 `Con.symm`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y : M}, c x y →
 c y x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
-/
theorem add_mk_self (a b c) : (mk a b : Localization M) + mk c b = mk (a + c) b := by
  rw [add_mk, mk_eq_mk_iff, r_eq_r']
  refine (r' M).symm ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  ring

/-- For any given denominator `b : M`, the map `a ↦ a / b` is an `AddMonoidHom` from `R` to
  `Localization M`. -/
@[simps]
/-
**Localization.mkAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：mkAddMonoidHom (b : M) : R ->+ Localization M where toFun a
参数：b : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any given denominator `b : M`, the map `a ↦ a / b` is an `AddMonoidHom` from
 `R` to
  `Localization M`.
-/
def mkAddMonoidHom (b : M) : R →+ Localization M where
  toFun a := mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm
/-
**Localization.mk_sum** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_sum {ι : Type*} (f : ι -> R) (s : Finset ι) (b : M) : mk (∑ i in s, f i
) b = ∑ i in s, mk (f i) b
参数：f : ι -> R；s : Finset ι；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem mk_sum {ι : Type*} (f : ι → R) (s : Finset ι) (b : M) :
    mk (∑ i ∈ s, f i) b = ∑ i ∈ s, mk (f i) b :=
  map_sum (mkAddMonoidHom b) f s
/-
**Localization.mk_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_list_sum (l : List R) (b : M) : mk l.sum b = (l.map fun a => mk a b).su
m
参数：l : List R；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem mk_list_sum (l : List R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  map_list_sum (mkAddMonoidHom b) l
/-
**Localization.mk_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_multiset_sum (l : Multiset R) (b : M) : mk l.sum b = (l.map fun a => mk
 a b).sum
参数：l : Multiset R；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_multiset_sum`：∀ {M : Type u_5} {N : Type u_6} [inst : A
ddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N) (s : Multiset M),   f s.
sum = (Multiset.map…
-/
theorem mk_multiset_sum (l : Multiset R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  (mkAddMonoidHom b).map_multiset_sum l
/-
**Localization.isLocalization** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：isLocalization : IsLocalization M (Localization M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
-/
instance isLocalization : IsLocalization M (Localization M) :=
  ⟨(Localization.monoidOf M).isLocalizationMap⟩
/-
**Localization.** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors R] : NoZeroDivisors (Localization M) := IsLocalization.noZeroDivisors M

end

@[simp]
/-
**Localization.toLocalizationMap_eq_monoidOf** 是 Mathlib 中的一个定理，位于命名空间 `Localiza
tion`。
形式化陈述：toLocalizationMap_eq_monoidOf : toLocalizationMap M (Localization M) = mon
oidOf M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLocalizationMap_eq_monoidOf : toLocalizationMap M (Localization M) = monoidOf M :=
  rfl
/-
**Localization.monoidOf_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：monoidOf_eq_algebraMap (x) : monoidOf M x = algebraMap R (Localization M) 
x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monoidOf_eq_algebraMap (x) : monoidOf M x = algebraMap R (Localization M) x :=
  rfl
/-
**Localization.mk_one_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_one_eq_algebraMap (x) : mk x 1 = algebraMap R (Localization M) x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one_eq_algebraMap (x) : mk x 1 = algebraMap R (Localization M) x :=
  rfl
/-
**Localization.mk_eq_mk'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (x : R) (y : ↥M
),   Localization.mk x y = IsLocalization.mk' (Localization M) x y
参数：x : R；y : ↥M；Localization M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_monoidOf_mk'_apply`：∀ {M : Type u_1} [inst : CommMono
id M] {S : Submonoid M} (x : M) (y : ↥S),   Localization.mk x y = (Localization.
monoidOf S).mk' x y
· 使用定理 `IsLocalization.mk'.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `Localization.toLocalizationMap_eq_monoidOf`：toLocalizationMap_eq_monoidO
f : toLocalizationMap M (Localization M) = monoidOf M
-/
theorem mk_eq_mk'_apply (x y) : mk x y = IsLocalization.mk' (Localization M) x y := by
  rw [mk_eq_monoidOf_mk'_apply, mk', toLocalizationMap_eq_monoidOf]
/-
**Localization.mk_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.mk' (Localization M) x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mk_eq_monoidOf_mk'`：mk_eq_monoidOf_mk'_apply (x y) : mk x y
 = (monoidOf S).mk' x y
-/
theorem mk_eq_mk' : (mk : R → M → Localization M) = IsLocalization.mk' (Localization M) :=
  mk_eq_monoidOf_mk'
/-
**Localization.mk_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] (m : A) : mk (alg
ebraMap A R m) 1 = algebraMap A (Localization M) m
参数：m : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Submonoid.coe_one`：coe_one : ((1 : S) : M) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mk_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] (m : A) :
    mk (algebraMap A R m) 1 = algebraMap A (Localization M) m := by
  rw [mk_eq_mk', mk'_eq_iff_eq_mul, Submonoid.coe_one, map_one, mul_one]; rfl

end Localization

namespace IsLocalization

variable [IsLocalization M S]

/-
**IsLocalization.to_map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：to_map_eq_zero_iff {x : R} (hM : M <= nonZeroDivisors R) : algebraMap R S 
x = 0 ↔ x = 0
参数：hM : M <= nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem to_map_eq_zero_iff {x : R} (hM : M ≤ nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0 := by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := (map_eq_zero_iff M _ _).mp h
    exact (hM c.2).1 x hc
  · rw [h, map_zero]
/-
**IsLocalization.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Submonoid R} (S : Type u_2) [ins
t_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocalization M S], M ≤ nonZeroDivi
sors R → Function.Injective ⇑(algebraMap R S)
参数：S : Type u_2；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.injectiveₛ`：∀ {R : Type u_1} [inst : CommSemiring R] {M :
 Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] 
[IsLocalization…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰
-/
protected theorem injectiveₛ (hM : ∀ m ∈ M, IsRegular m) : Injective (algebraMap R S) :=
  (toLocalizationMap M S).injective_iff.mpr hM
/-
**IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间
 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLocalization M S] [Nontriv
ial R],   M ≤ nonZeroDivisors R → ∀ {x : R}, x ∈ nonZeroDivisors R → (algebraMap
 R S) x ≠ 0
参数：S : Type u_2；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `IsLocalization.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} (hM : M <=
 nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
-/
protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] (hM : M ≤ nonZeroDivisors R)
    {x : R} (hx : x ∈ nonZeroDivisors R) : algebraMap R S x ≠ 0 := by
  rw [Ne, to_map_eq_zero_iff S hM]
  exact nonZeroDivisors.ne_zero hx

variable {S}
/-
**IsLocalization.sec_snd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：sec_snd_ne_zero [Nontrivial R] (hM : M <= nonZeroDivisors R) (x : S) : ((s
ec M x).snd : R) != 0
参数：hM : M <= nonZeroDivisors R；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sec_snd_ne_zero [Nontrivial R] (hM : M ≤ nonZeroDivisors R) (x : S) :
    ((sec M x).snd : R) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩

variable [IsDomain R]

variable (S) in
/-- A `CommRing` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain. -/
/-
**IsLocalization.isDomain_of_le_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alization`。
形式化陈述：isDomain_of_le_nonZeroDivisors (hM : M <= nonZeroDivisors R) : IsDomain S 
where __ : IsCancelMulZero S
参数：hM : M <= nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.isCancelMulZero`：isCancelMulZero (f : Localiza
tionMap S N) [IsCancelMulZero M] : IsCancelMulZero N
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Submonoid.LocalizationMap.nontrivial`：∀ {M : Type u_1} [inst : CommMonoi
dWithZero M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoidWithZero N]   
(f : S.LocalizationMap N),…
· 使用定理 `zero_notMem_nonZeroDivisors`：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
A `CommRing` `S` which is the localization of an integral domain `R` at a subset
 of
non-zero elements is an integral domain.
-/
theorem isDomain_of_le_nonZeroDivisors (hM : M ≤ nonZeroDivisors R) : IsDomain S where
  __ : IsCancelMulZero S := (toLocalizationMap M S).isCancelMulZero
  __ : Nontrivial S := (toLocalizationMap M S).nontrivial fun h ↦ zero_notMem_nonZeroDivisors (hM h)

/-- The localization of an integral domain to a set of non-zero elements is an integral domain. -/
/-
**IsLocalization.isDomain_localization** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization
`。
形式化陈述：isDomain_localization {M : Submonoid R} (hM : M <= nonZeroDivisors R) : Is
Domain (Localization M)
参数：hM : M <= nonZeroDivisors R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S

--- 原说明 ---
The localization of an integral domain to a set of non-zero elements is an integ
ral domain.
-/
theorem isDomain_localization {M : Submonoid R} (hM : M ≤ nonZeroDivisors R) :
    IsDomain (Localization M) :=
  isDomain_of_le_nonZeroDivisors _ hM

end IsLocalization

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace Localization

/-
**Localization.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：neg_mk (a b) : -(mk a b : Localization M) = mk (-a) b
参数：a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.neg_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddGroup X]
 [inst_3 : Di…
-/
theorem neg_mk (a b) : -(mk a b : Localization M) = mk (-a) b := OreLocalization.neg_def _ _
/-
**Localization.sub_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：sub_mk (a c) (b d) : (mk a b : Localization M) - mk c d = mk ((d : R) * a 
- b * c) (b * d)
参数：a c；b d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Localization.neg_mk`：neg_mk (a b) : -(mk a b : Localization M) = mk (-a)
 b
· 使用定理 `Localization.add_mk`：add_mk (a b c d) : (mk a b : Localization M) + mk c
 d = mk ((b : R) * c + (d : R) * a) (b * d)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sub_mk (a c) (b d) : (mk a b : Localization M) - mk c d =
    mk ((d : R) * a - b * c) (b * d) := by
  rw [sub_eq_add_neg, neg_mk, add_mk, add_comm, mul_neg, ← sub_eq_add_neg]

end Localization

namespace IsLocalization

variable [IsLocalization M S]

/-
**IsLocalization.mk'_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Submonoid R} (S : Type u_2) [ins
t_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : IsLocalization M S] (x : R)
 (y : ↥M), IsLocalization.mk' S (-x) y = -IsLocalization.mk' S x y
参数：S : Type u_2；x : R；y : ↥M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem mk'_neg (x : R) (y : M) :
    mk' S (-x) y = -mk' S x y := by
  rw [eq_comm, eq_mk'_iff_mul_eq, neg_mul, map_neg, mk'_spec]
/-
**IsLocalization.mk'_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Submonoid R} (S : Type u_2) [ins
t_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : IsLocalization M S] (x₁ x₂ 
: R) (y₁ y₂ : ↥M),   IsLocalization.mk' S (x₁ * ↑y₂ - x₂ * ↑y₁) (y₁ * y₂) = IsLo
calization.mk' S x₁ y₁ - IsLocalization.mk' S x₂ y₂
参数：S : Type u_2；x₁ x₂ : R；y₁ y₂ : ↥M；x₁ * ↑y₂ - x₂ * ↑y₁；y₁ * y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_neg`：∀ {R : Type u_1} [inst : CommRing R] {M : Submon
oid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : I
sLocalizatio…
· 使用定理 `IsLocalization.mk'_add`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem mk'_sub (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ - x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ - mk' S x₂ y₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← mk'_neg, ← mk'_add, neg_mul]

include M in
/-
**IsLocalization.injective_of_map_algebraMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsL
ocalization`。
形式化陈述：injective_of_map_algebraMap_zero {T} [CommRing T] (f : S ->+* T) (h : fora
ll x, f (algebraMap R S x) = 0 -> algebraMap R S x = 0) : Function.Injective f
参数：f : S ->+* T；h : forall x, f (algebraMap R S x) = 0 -> algebraMap R S x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalization.injective_iff_map_algebraMap_eq`：injective_iff_map_algebr
aMap_eq {T} [CommSemiring T] (f : S ->+* T) : Function.Injective f ↔ forall x y,
 algebraMap R S x = algebraMap R S y…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma injective_of_map_algebraMap_zero {T} [CommRing T] (f : S →+* T)
    (h : ∀ x, f (algebraMap R S x) = 0 → algebraMap R S x = 0) :
    Function.Injective f := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq M]
  refine fun x y ↦ ⟨fun hz ↦ hz ▸ rfl, fun hz ↦ ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← map_sub] at hz
  apply h at hz
  rwa [map_sub, sub_eq_zero] at hz
/-
**IsLocalization.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Submonoid R} (S : Type u_2) [ins
t_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocalization M S], M ≤ nonZeroDivi
sors R → Function.Injective ⇑(algebraMap R S)
参数：S : Type u_2；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.injectiveₛ`：∀ {R : Type u_1} [inst : CommSemiring R] {M :
 Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] 
[IsLocalization…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰
-/
protected theorem injective (hM : M ≤ nonZeroDivisors R) : Injective (algebraMap R S) :=
  IsLocalization.injectiveₛ S fun _x hx ↦ isRegular_iff_mem_nonZeroDivisors.mpr (hM hx)

end IsLocalization

end CommRing

