/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.GroupTheory.OreLocalization.Basic

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M` such that `f x = f y`, there exists `c ∈ S` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

Given such a localization map `f : M →* N`, we can define the surjection
`Submonoid.LocalizationMap.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`. Mapping properties
of the localization (e.g. extending a map from `M → P` to `N` if the image of `S` is contained in
the units) are treated in a later file `Mathlib.GroupTheory.MonoidLocalization.Maps`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, `Localization`, but the majority of
subsequent lemmas in the file are given in terms of localizations up to isomorphism, using maps
which satisfy the characteristic predicate.

The Grothendieck group construction corresponds to localizing at the top submonoid, namely making
every element invertible.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To reason about the localization as a quotient type, use `mk_eq_monoidOf_mk'` and associated
lemmas. These show the quotient map `mk : M → S → Localization S` equals the
surjection `LocalizationMap.mk'` induced by the map
`Localization.monoidOf : Submonoid.LocalizationMap S (Localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoidOf_mk'` hence gives you access to the results in the rest of the file, which are about
the `LocalizationMap.mk'` induced by any localization map.

## TODO

* Show that the localization at the top monoid is a group.
* Generalise to (nonempty) subsemigroups.
* If we acquire more bundlings, we can make `Localization.mkOrderEmbedding` be an ordered monoid
  embedding.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/

@[expose] public section

assert_not_exists MonoidWithZero Ring

open Function
namespace AddSubmonoid

variable {M : Type*} [AddCommMonoid M] (S : AddSubmonoid M) (N : Type*) [AddCommMonoid N]

variable {N} in
/-- A predicate characterizing homomorphisms between additive monoids `M` and `N` that form a
commutative triangle with the canonical map from `M` to its localization at `S` and
some isomorphism between `N` and the localization. -/
/-
**AddSubmonoid.IsLocalizationMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddSubmonoid`。
形式化陈述：{M : Type u_1} → [inst : AddCommMonoid M] → {N : Type u_2} → [AddCommMonoi
d N] → AddSubmonoid M → (M → N) → Prop
参数：M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate characterizing homomorphisms between additive monoids `M` and `N` th
at form a
commutative triangle with the canonical map from `M` to its localization at `S` 
and
some isomorphism between `N` and the localization.
-/
structure IsLocalizationMap (S : AddSubmonoid M) (f : M → N) where
  map_addUnits (y : S) : IsAddUnit (f y)
  surj (z : N) : ∃ x : M × S, z + f x.2 = f x.1
  exists_of_eq {x y} : f x = f y → ∃ c : S, c + x = c + y

/-- The type of AddMonoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
/-
**AddSubmonoid.LocalizationMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddSubmonoid`。
形式化陈述：{M : Type u_1} → [inst : AddCommMonoid M] → AddSubmonoid M → (N : Type u_2
) → [AddCommMonoid N] → Type (max u_1 u_2)
参数：N : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of AddMonoid homomorphisms satisfying the characteristic predicate: if 
`f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `
S`.
-/
structure LocalizationMap extends M →ₙ+ N where
  isLocalizationMap : IsLocalizationMap S toFun

/-- The additive homomorphism underlying a `LocalizationMap` of `AddCommMonoid`s. -/
add_decl_doc LocalizationMap.toAddHom

end AddSubmonoid

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

namespace Submonoid

variable {N} in
/-- A predicate characterizing homomorphisms between monoids `M` and `N` that form a
commutative triangle with the canonical map from `M` to its localization at `S` and
some isomorphism between `N` and the localization. -/
@[to_additive (attr := mk_iff)]
/-
**Submonoid.IsLocalizationMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submonoid`。
形式化陈述：{M : Type u_1} → [inst : CommMonoid M] → {N : Type u_2} → [CommMonoid N] →
 Submonoid M → (M → N) → Prop
参数：M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate characterizing homomorphisms between monoids `M` and `N` that form a
commutative triangle with the canonical map from `M` to its localization at `S` 
and
some isomorphism between `N` and the localization.
-/
structure IsLocalizationMap (S : Submonoid M) (f : M → N) where
  map_units (y : S) : IsUnit (f y)
  surj (z : N) : ∃ x : M × S, z * f x.2 = f x.1
  exists_of_eq {x y} : f x = f y → ∃ c : S, c * x = c * y

/-- The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
/-
**Submonoid.LocalizationMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submonoid`。
形式化陈述：{M : Type u_1} → [inst : CommMonoid M] → Submonoid M → (N : Type u_2) → [C
ommMonoid N] → Type (max u_1 u_2)
参数：N : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of monoid homomorphisms satisfying the characteristic predicate: if `f 
: M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `
S`.
-/
@[to_additive] structure LocalizationMap extends M →ₙ* N where
  isLocalizationMap : IsLocalizationMap S toFun

/-- The multiplicative homomorphism underlying a `LocalizationMap`. -/
add_decl_doc LocalizationMap.toMulHom

end Submonoid

namespace Localization

/- Ensure that `@[to_additive]` uses the right namespace before the definition of `Localization`. -/
insert_to_additive_translation Localization AddLocalization

/-- The congruence relation on `M × S`, `M` a `CommMonoid` and `S` a submonoid of `M`, whose
quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive
/-- The congruence relation on `M × S`, `M` an `AddCommMonoid` and `S` an `AddSubmonoid` of `M`,
whose quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/]
/-
**Localization.r** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：r (S : Submonoid M) : Con (M × S)
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def r (S : Submonoid M) : Con (M × S) :=
  sInf { c | ∀ y : S, c 1 (y, y) }

/-- An alternate form of the congruence relation on `M × S`, `M` a `CommMonoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
@[to_additive
/-- An alternate form of the congruence relation on `M × S`, `M` a `CommMonoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/]
/-
**Localization.r'** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：r' : Con (M × S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def r' : Con (M × S) := by
  -- note we multiply by `c` on the left so that we can later generalize to `•`
  refine
    { r := fun a b : M × S ↦ ∃ c : S, ↑c * (↑b.2 * a.1) = c * (a.2 * b.1)
      iseqv := ⟨fun a ↦ ⟨1, rfl⟩, fun ⟨c, hc⟩ ↦ ⟨c, hc.symm⟩, ?_⟩
      mul' := ?_ }
  · rintro a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₂ * t₁ * b.2
    simp only [Submonoid.coe_mul]
    calc
      (t₂ * t₁ * b.2 : M) * (c.2 * a.1) = t₂ * c.2 * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = t₁ * a.2 * (t₂ * (c.2 * b.1)) := by rw [ht₁]; ac_rfl
      _ = t₂ * t₁ * b.2 * (a.2 * c.1) := by rw [ht₂]; ac_rfl
  · rintro a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₂ * t₁
    calc
      (t₂ * t₁ : M) * (b.2 * d.2 * (a.1 * c.1)) = t₂ * (d.2 * c.1) * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = (t₂ * t₁ : M) * (a.2 * c.2 * (b.1 * d.1)) := by rw [ht₁, ht₂]; ac_rfl

/-- The congruence relation used to localize a `CommMonoid` at a submonoid can be expressed
equivalently as an infimum (see `Localization.r`) or explicitly
(see `Localization.r'`). -/
@[to_additive
/-- The additive congruence relation used to localize an `AddCommMonoid` at a submonoid can be
expressed equivalently as an infimum (see `AddLocalization.r`) or explicitly
(see `AddLocalization.r'`). -/]
/-
**Localization.r_eq_r'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：r_eq_r' : r S = r' S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Con.trans`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y z : M}, c x 
y → c y z → c x z
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
· 使用定理 `Con.refl`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) (x : M), c x x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Con.symm`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y : M}, c x y →
 c y x
-/
theorem r_eq_r' : r S = r' S :=
  le_antisymm (sInf_le fun _ ↦ ⟨1, by simp⟩) <|
    le_sInf fun b H ⟨p, q⟩ ⟨x, y⟩ ⟨t, ht⟩ ↦ by
      rw [← one_mul (p, q), ← one_mul (x, y)]
      refine b.trans (b.mul (H (t * y)) (b.refl _)) ?_
      convert! b.symm (b.mul (H (t * q)) (b.refl (x, y))) using 1
      dsimp only [Prod.mk_mul_mk, Submonoid.coe_mul] at ht ⊢
      simp_rw [mul_assoc, ht, mul_comm y q]

variable {S}

@[to_additive]
/-
**Localization.r_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：r_iff_exists {x y : M × S} : r S x y ↔ exists c : S, ↑c * (↑y.2 * x.1) = c
 * (x.2 * y.1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.r_eq_r'`：r_eq_r' : r S = r' S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, ↑c * (↑y.2 * x.1) = c * (x.2 * y.1) := by
  simp only [r_eq_r' S, r', Con.rel_mk]

@[to_additive]
/-
**Localization.r_iff_oreEqv_r** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：r_iff_oreEqv_r {x y : M × S} : r S x y ↔ (OreLocalization.oreEqv S M).r x 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Setoid.mk.congr_simp`：∀ {α : Sort u} (r r_1 : α → α → Prop) (e_r : r = r
_1) (iseqv : Equivalence r),   { r := r, iseqv := iseqv } = { r := r_1, iseqv :=
 ⋯ }
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem r_iff_oreEqv_r {x y : M × S} : r S x y ↔ (OreLocalization.oreEqv S M).r x y := by
  simp +instances only [r_iff_exists, Subtype.exists, exists_prop, OreLocalization.oreEqv,
    smul_eq_mul, Submonoid.mk_smul]
  constructor
  · rintro ⟨u, hu, e⟩
    exact ⟨_, mul_mem hu x.2.2, u * y.2, by rw [mul_assoc, mul_assoc, ← e], mul_right_comm _ _ _⟩
  · rintro ⟨u, hu, v, e₁, e₂⟩
    exact ⟨u, hu, by rw [← mul_assoc, e₂, mul_right_comm, ← e₁, mul_assoc, mul_comm y.1]⟩

end Localization

set_option linter.translateOverwrite false in
/-- The localization of a `CommMonoid` at one of its submonoids (as a quotient type). -/
@[to_additive AddLocalization
/-- The localization of an `AddCommMonoid` at one of its submonoids (as a quotient type). -/]
/-
**Localization** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Localization
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Localization := OreLocalization S M

namespace Localization

variable {S}

/-- Given a `CommMonoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
/-
**Localization.of** 是 Mathlib 中的一个类，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class of `(x, y)` in the localization of `M` at `S`. -/
@[to_additive
/-- Given an `AddCommMonoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to
the equivalence class of `(x, y)` in the localization of `M` at `S`. -/]
/-
**Localization.mk** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：mk (x : M) (y : S) : Localization S
参数：x : M；y : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk (x : M) (y : S) : Localization S := x /ₒ y

@[to_additive]
/-
**Localization.mk_eq_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_eq_mk_iff {a c : M} {b d : S} : mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩ := by
  simp +instances only [mk, OreLocalization.oreDiv_eq_iff, r_iff_oreEqv_r, OreLocalization.oreEqv]

universe u

/-- Dependent recursion principle for `Localizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (with the correct coercions),
then `f` is defined on the whole `Localization S`. -/
@[to_additive (attr := elab_as_elim)
/-- Dependent recursion principle for `AddLocalizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (with the correct coercions),
then `f` is defined on the whole `AddLocalization S`. -/]
/-
**Localization.rec** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：rec {p : Localization S -> Sort u} (f : forall (a : M) (b : S), p (mk a b)
) (H : forall {a c : M} {b d : S} (h : r S (a, b) (c, d)), (Eq.ndrec (f a b) (mk
_eq_mk_iff.mpr h) : p (mk c d)) = f c d) (x) : p x
参数：f : forall (a : M) (b : S), p (mk a b)；H : forall {a c : M} {b d : S} (h : r 
S (a, b) (c, d)), (Eq.ndrec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d；x
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rec {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b))
    (H : ∀ {a c : M} {b d : S} (h : r S (a, b) (c, d)),
      (Eq.ndrec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d) (x) : p x :=
  Quot.rec (fun y ↦ f y.1 y.2)
    (fun y z h ↦ by cases y; cases z; exact H (r_iff_oreEqv_r.mpr h)) x

/-- Copy of `Quotient.recOnSubsingleton₂` for `Localization` -/
@[to_additive (attr := elab_as_elim)
/-- Copy of `Quotient.recOnSubsingleton₂` for `AddLocalization` -/]
/-
**Localization.recOnSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def recOnSubsingleton₂ {r : Localization S → Localization S → Sort u}
    [h : ∀ (a c : M) (b d : S), Subsingleton (r (mk a b) (mk c d))] (x y : Localization S)
    (f : ∀ (a c : M) (b d : S), r (mk a b) (mk c d)) : r x y :=
  @Quotient.recOnSubsingleton₂' _ _ _ _ r (Prod.rec fun _ _ => Prod.rec fun _ _ => h _ _ _ _) x y
    (Prod.rec fun _ _ => Prod.rec fun _ _ => f _ _ _ _)

@[to_additive]
/-
**Localization.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (a * c) (b * d)
参数：a c : M；b d : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `OreLocalization.oreDiv_mul_oreDiv`：oreDiv_mul_oreDiv {r₁ : R} {r₂ : R} {
s₁ s₂ : S} : (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = oreNum r₁ s₂ * r₂ /ₒ (oreDenom r₁ s₂ * s₁
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (a * c) (b * d) :=
  mul_comm b d ▸ OreLocalization.oreDiv_mul_oreDiv

unseal OreLocalization.one in
@[to_additive]
/-
**Localization.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_one : mk 1 (1 : S) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.one_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] [inst_3 :…
-/
theorem mk_one : mk 1 (1 : S) = 1 := OreLocalization.one_def

@[to_additive]
/-
**Localization.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_pow (n : Nat) (a : M) (b : S) : mk a b ^ n = mk (a ^ n) (b ^ n)
参数：n : Nat；a : M；b : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.oreDiv_pow`：oreDiv_pow (r : R) (s : S) (n : Nat) (h : Co
mmute r (s : R)) : (r /ₒ s) ^ n = (r ^ n) /ₒ (s ^ n)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem mk_pow (n : ℕ) (a : M) (b : S) : mk a b ^ n = mk (a ^ n) (b ^ n) :=
  OreLocalization.oreDiv_pow _ _ _ <| .all _ _

@[to_additive]
/-
**Localization.mk_prod** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_prod {ι} (t : Finset ι) (f : ι -> M) (s : ι -> S) : ∏ i in t, mk (f i) 
(s i) = mk (∏ i in t, f i) (∏ i in t, s i)
参数：t : Finset ι；f : ι -> M；s : ι -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_one`：mk_one : mk 1 (1 : S) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
-/
theorem mk_prod {ι} (t : Finset ι) (f : ι → M) (s : ι → S) :
    ∏ i ∈ t, mk (f i) (s i) = mk (∏ i ∈ t, f i) (∏ i ∈ t, s i) := by
  classical
  induction t using Finset.induction_on <;> simp [mk_one, Finset.prod_insert, *, mk_mul]

@[to_additive (attr := simp)]
/-
**Localization.ndrec_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：ndrec_mk {p : Localization S -> Sort u} (f : forall (a : M) (b : S), p (mk
 a b)) (H) (a : M) (b : S) : (rec f H (mk a b) : p (mk a b)) = f a b
参数：f : forall (a : M) (b : S), p (mk a b)；H；a : M；b : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
-/
theorem ndrec_mk {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b)) (H) (a : M)
    (b : S) : (rec f H (mk a b) : p (mk a b)) = f a b := rfl

/-- Non-dependent recursion principle for localizations: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `Localization S`. -/
@[to_additive
/-- Non-dependent recursion principle for `AddLocalization`s: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `Localization S`. -/]
/-
**Localization.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：liftOn {p : Sort u} (x : Localization S) (f : M -> S -> p) (H : forall {a 
c : M} {b d : S}, r S (a, b) (c, d) -> f a b = f c d) : p
参数：x : Localization S；f : M -> S -> p；H : forall {a c : M} {b d : S}, r S (a, b)
 (c, d) -> f a b = f c d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftOn {p : Sort u} (x : Localization S) (f : M → S → p)
    (H : ∀ {a c : M} {b d : S}, r S (a, b) (c, d) → f a b = f c d) : p :=
  rec f (fun h ↦ (by simpa only [eq_rec_constant] using H h)) x

@[to_additive]
/-
**Localization.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：liftOn_mk {p : Sort u} (f : M -> S -> p) (H) (a : M) (b : S) : liftOn (mk 
a b) f H = f a b
参数：f : M -> S -> p；H；a : M；b : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn_mk {p : Sort u} (f : M → S → p) (H) (a : M) (b : S) :
    liftOn (mk a b) f H = f a b := rfl

@[to_additive (attr := elab_as_elim, induction_eliminator, cases_eliminator)]
/-
**Localization.ind** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：ind {p : Localization S -> Prop} (H : forall y : M × S, p (mk y.1 y.2)) (x
) : p x
参数：H : forall y : M × S, p (mk y.1 y.2)；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
-/
theorem ind {p : Localization S → Prop} (H : ∀ y : M × S, p (mk y.1 y.2)) (x) : p x :=
  rec (fun a b ↦ H (a, b)) (fun _ ↦ rfl) x

@[to_additive (attr := elab_as_elim)]
/-
**Localization.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：induction_on {p : Localization S -> Prop} (x) (H : forall y : M × S, p (mk
 y.1 y.2)) : p x
参数：x；H : forall y : M × S, p (mk y.1 y.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.ind`：ind {p : Localization S -> Prop} (H : forall y : M × S
, p (mk y.1 y.2)) (x) : p x
-/
theorem induction_on {p : Localization S → Prop} (x) (H : ∀ y : M × S, p (mk y.1 y.2)) : p x :=
  ind H x

/-- Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `Localization S`. -/
@[to_additive
/-- Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `Localization S`. -/]
/-
**Localization.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：liftOn {p : Sort u} (x : Localization S) (f : M -> S -> p) (H : forall {a 
c : M} {b d : S}, r S (a, b) (c, d) -> f a b = f c d) : p
参数：x : Localization S；f : M -> S -> p；H : forall {a c : M} {b d : S}, r S (a, b)
 (c, d) -> f a b = f c d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftOn₂ {p : Sort u} (x y : Localization S) (f : M → S → M → S → p)
    (H : ∀ {a a' b b' c c' d d'}, r S (a, b) (a', b') → r S (c, d) (c', d') →
      f a b c d = f a' b' c' d') : p :=
  liftOn x (fun a b ↦ liftOn y (f a b) fun hy ↦ H ((r S).refl _) hy) fun hx ↦
    induction_on y fun ⟨_, _⟩ ↦ H hx ((r S).refl _)

@[to_additive]
/-
**Localization.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：liftOn {p : Sort u} (x : Localization S) (f : M -> S -> p) (H : forall {a 
c : M} {b d : S}, r S (a, b) (c, d) -> f a b = f c d) : p
参数：x : Localization S；f : M -> S -> p；H : forall {a c : M} {b d : S}, r S (a, b)
 (c, d) -> f a b = f c d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_mk {p : Sort*} (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
    liftOn₂ (mk a b) (mk c d) f H = f a b c d := rfl

@[to_additive (attr := elab_as_elim)]
/-
**Localization.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：induction_on {p : Localization S -> Prop} (x) (H : forall y : M × S, p (mk
 y.1 y.2)) : p x
参数：x；H : forall y : M × S, p (mk y.1 y.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.ind`：ind {p : Localization S -> Prop} (H : forall y : M × S
, p (mk y.1 y.2)) (x) : p x
-/
theorem induction_on₂ {p : Localization S → Localization S → Prop} (x y)
    (H : ∀ x y : M × S, p (mk x.1 x.2) (mk y.1 y.2)) : p x y :=
  induction_on x fun x ↦ induction_on y <| H x

@[to_additive (attr := elab_as_elim)]
/-
**Localization.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：induction_on {p : Localization S -> Prop} (x) (H : forall y : M × S, p (mk
 y.1 y.2)) : p x
参数：x；H : forall y : M × S, p (mk y.1 y.2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.ind`：ind {p : Localization S -> Prop} (H : forall y : M × S
, p (mk y.1 y.2)) (x) : p x
-/
theorem induction_on₃ {p : Localization S → Localization S → Localization S → Prop} (x y z)
    (H : ∀ x y z : M × S, p (mk x.1 x.2) (mk y.1 y.2) (mk z.1 z.2)) : p x y z :=
  induction_on₂ x y fun x y ↦ induction_on z <| H x y

@[to_additive]
/-
**Localization.one_rel** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：one_rel (y : S) : r S 1 (y, y)
参数：y : S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_rel (y : S) : r S 1 (y, y) := fun _ hb ↦ hb y

@[to_additive]
/-
**Localization.r_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：r_of_eq {x y : M × S} (h : ↑y.2 * x.1 = ↑x.2 * y.1) : r S x y
参数：h : ↑y.2 * x.1 = ↑x.2 * y.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Localization.r_iff_exists`：r_iff_exists {x y : M × S} : r S x y ↔ exists
 c : S, ↑c * (↑y.2 * x.1) = c * (x.2 * y.1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem r_of_eq {x y : M × S} (h : ↑y.2 * x.1 = ↑x.2 * y.1) : r S x y :=
  r_iff_exists.2 ⟨1, by rw [h]⟩

@[to_additive]
/-
**Localization.mk_self** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_self (a : S) : mk (a : M) a = 1
参数：a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_one`：mk_one : mk 1 (1 : S) = 1
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
· 使用定理 `Localization.one_rel`：one_rel (y : S) : r S 1 (y, y)
-/
theorem mk_self (a : S) : mk (a : M) a = 1 := by
  symm
  rw [← mk_one, mk_eq_mk_iff]
  exact one_rel a

@[to_additive (attr := simp)]
/-
**Localization.mk_self_mk** 是 Mathlib 中的一个引理，位于命名空间 `Localization`。
形式化陈述：mk_self_mk (a : M) (haS : a in S) : mk a ⟨a, haS⟩ = 1
参数：a : M；haS : a in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mk_self`：mk_self (a : S) : mk (a : M) a = 1
-/
lemma mk_self_mk (a : M) (haS : a ∈ S) : mk a ⟨a, haS⟩ = 1 :=
  mk_self ⟨a, haS⟩

/-- `Localization.mk` as a monoid hom. -/
@[to_additive (attr := simps) /-- `Localization.mk` as a monoid hom. -/]
/-
**Localization.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：mkHom : M × S ->* Localization S where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mk_one`：mk_one : mk 1 (1 : S) = 1

--- 原说明 ---
`Localization.mk` as a monoid hom.
-/
def mkHom : M × S →* Localization S where
  toFun x := mk x.1 x.2
  map_one' := mk_one
  map_mul' _ _ := (mk_mul ..).symm

@[to_additive]
/-
**Localization.mkHom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Localization`。
形式化陈述：mkHom_surjective : Surjective (mkHom (S
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkHom_surjective : Surjective (mkHom (S := S)) := by rintro ⟨x, y⟩; exact ⟨⟨x, y⟩, rfl⟩

section Scalar

variable {R R₁ R₂ : Type*}

/-
**Localization.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (a b) : c • (mk a b : Loc
alization S) = mk (c • a) b
参数：c : R；a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk.eq_1`：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submon
oid M} (x : M) (y : ↥S), Localization.mk x y = x /ₒ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OreLocalization.smul_one_oreDiv_one_smul`：smul_one_oreDiv_one_smul (r : 
R) (x : X[S⁻¹]) : ((r • 1 : M) /ₒ (1 : S)) • x = r • x
· 使用定理 `OreLocalization.oreDiv_smul_oreDiv`：oreDiv_smul_oreDiv {r₁ : R} {r₂ : X}
 {s₁ s₂ : S} : (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * 
s₁)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (a b) :
    c • (mk a b : Localization S) = mk (c • a) b := by
  rw [mk, mk, ← OreLocalization.smul_one_oreDiv_one_smul, OreLocalization.oreDiv_smul_oreDiv]
  change (c • 1) • a /ₒ (b * 1) = _
  rw [smul_assoc, one_smul, mul_one]

-- Note: Previously there was a `MulDistribMulAction R (Localization S)`.
-- It was removed as it is not the correct action.

end Scalar

end Localization

variable {S N}

namespace MonoidHom

/-- Makes a localization map from a `CommMonoid` hom satisfying the characteristic predicate. -/
@[to_additive /-- Makes a localization map from an `AddCommMonoid` hom satisfying the
characteristic predicate. -/]
/-
**MonoidHom.toLocalizationMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：toLocalizationMap (f : M ->* N) (H1 : forall y : S, IsUnit (f y)) (H2 : fo
rall z, exists x : M × S, z * f x.2 = f x.1) (H3 : forall x y, f x = f y -> exis
ts c : S, ↑c * x = ↑c * y) : Submonoid.LocalizationMap S N where __
参数：f : M ->* N；H1 : forall y : S, IsUnit (f y)；H2 : forall z, exists x : M × S, 
z * f x.2 = f x.1；H3 : forall x y, f x = f y -> exists c : S, ↑c * x = ↑c * y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toLocalizationMap (f : M →* N) (H1 : ∀ y : S, IsUnit (f y))
    (H2 : ∀ z, ∃ x : M × S, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y → ∃ c : S, ↑c * x = ↑c * y) :
    Submonoid.LocalizationMap S N where
  __ := f
  isLocalizationMap :=
  { map_units := H1
    surj := H2
    exists_of_eq := H3 _ _ }

end MonoidHom

namespace Submonoid

namespace IsLocalizationMap

/-
**Submonoid.IsLocalizationMap.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.IsLoc
alizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N] {F : Type u_4}   [inst_2 : FunLike F M N] [MulHomClass F M
 N] {f : F}, S.IsLocalizationMap ⇑f → f 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `Submonoid.IsLocalizationMap.map_units`：∀ {M : Type u_1} [inst : CommMono
id M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.
IsLocalizationMap f → ∀ (y …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
@[to_additive] protected theorem map_one {F : Type*} [FunLike F M N] [MulHomClass F M N]
    {f : F} (hf : IsLocalizationMap S f) : f 1 = 1 := by
  rw [← (hf.map_units 1).mul_right_inj, mul_one]
  exact (map_mul ..).symm.trans congr(f $(mul_one _))
/-
**Submonoid.IsLocalizationMap.mulEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
.IsLocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N] {P : Type u_3}   [inst_2 : CommMonoid P] {f : M → N},   S.
IsLocalizationMap f →     ∀ {E : Type u_4} [inst_3 : EquivLike E N P] [MulEquivC
lass E N P] (e : E), S.IsLocalizationMap (⇑e ∘ f)
参数：e : E；⇑e ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `Submonoid.IsLocalizationMap.map_units`：∀ {M : Type u_1} [inst : CommMono
id M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.
IsLocalizationMap f → ∀ (y …
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquivClass.coe_symm_apply_apply`：∀ {α : Type u_9} {β : Type u_10} [in
st : Mul α] [inst_1 : Mul β] {F : Type u_11} [inst_2 : EquivLike F α β]   [inst_
3 : MulEquivClass F α β]…
· 使用定理 `Submonoid.IsLocalizationMap.exists_of_eq`：∀ {M : Type u_1} [inst : CommM
onoid M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},  
 S.IsLocalizationMap f → ∀ {x …
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
@[to_additive] theorem mulEquiv_comp {f : M → N} (hf : IsLocalizationMap S f)
    {E} [EquivLike E N P] [MulEquivClass E N P] (e : E) : IsLocalizationMap S (e ∘ f) where
  map_units x := (hf.map_units x).map e
  surj y := let e : N ≃* P := e
    have ⟨x, eq⟩ := hf.surj (e.symm y)
    ⟨x, e.symm.injective (by simpa [e])⟩
  exists_of_eq eq := hf.exists_of_eq (EquivLike.injective e eq)

end IsLocalizationMap

namespace LocalizationMap

/-- A localization map between monoids automatically preserves 1 and therefore
is a monoid homomorphism. -/
@[to_additive /-- A localization map between additive monoids automatically preserves 0 and
therefore is an additive monoid homomorphism. -/]
/-
**Submonoid.LocalizationMap.toMonoidHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：toMonoidHom (f : LocalizationMap S N) : M ->* N where __
参数：f : LocalizationMap S N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev toMonoidHom (f : LocalizationMap S N) : M →* N where
  __ := f
  map_one' := f.isLocalizationMap.map_one (f := f.toMulHom)

@[to_additive]
/-
**Submonoid.LocalizationMap.toMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.LocalizationMap`。
形式化陈述：toMonoidHom_injective : Injective (toMonoidHom : LocalizationMap S N -> M 
->* N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : LocalizationMap S N → M →* N) :=
  fun f g ↦ by cases f; congr! with eq; ext; exact congr($eq _)
/-
**Submonoid.LocalizationMap.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid.LocalizationMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : FunLike (LocalizationMap S N) M N where
  coe f := f.toMonoidHom
  coe_injective := DFunLike.coe_injective.comp toMonoidHom_injective
/-
**Submonoid.LocalizationMap.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid.LocalizationMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : MonoidHomClass (LocalizationMap S N) M N where
  map_one f := f.toMonoidHom.map_one
  map_mul f := f.map_mul
/-
**Submonoid.LocalizationMap.toMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M), f.toMonoidHom x = f x
参数：f : S.LocalizationMap N；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma toMonoidHom_apply (f : LocalizationMap S N) (x : M) :
    f.toMonoidHom x = f x := rfl

@[to_additive (attr := ext)]
/-
**Submonoid.LocalizationMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localizatio
nMap`。
形式化陈述：ext {f g : LocalizationMap S N} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : LocalizationMap S N} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

@[to_additive]
/-
**Submonoid.LocalizationMap.map_units** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：map_units (f : LocalizationMap S N) (y : S) : IsUnit (f y)
参数：f : LocalizationMap S N；y : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.map_units`：∀ {M : Type u_1} [inst : CommMono
id M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.
IsLocalizationMap f → ∀ (y …
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
-/
theorem map_units (f : LocalizationMap S N) (y : S) : IsUnit (f y) :=
  f.2.1 y

@[to_additive]
/-
**Submonoid.LocalizationMap.surj** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localizati
onMap`。
形式化陈述：surj (f : LocalizationMap S N) (z : N) : exists x : M × S, z * f x.2 = f x
.1
参数：f : LocalizationMap S N；z : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
-/
theorem surj (f : LocalizationMap S N) (z : N) : ∃ x : M × S, z * f x.2 = f x.1 :=
  f.2.2 z

@[to_additive]
/-
**Submonoid.LocalizationMap.exists_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：exists_of_eq (f : LocalizationMap S N) {x y : M} : f x = f y -> exists c :
 S, c * x = c * y
参数：f : LocalizationMap S N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.exists_of_eq`：∀ {M : Type u_1} [inst : CommM
onoid M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},  
 S.IsLocalizationMap f → ∀ {x …
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
-/
theorem exists_of_eq (f : LocalizationMap S N) {x y : M} : f x = f y → ∃ c : S, c * x = c * y :=
  f.2.3

/-- Given a localization map `f : M →* N`, and `z w : N`, there exist `z' w' : M` and `d : S`
such that `f z' / f d = z` and `f w' / f d = w`. -/
@[to_additive
/-- Given a localization map `f : M →+ N`, and `z w : N`, there exist `z' w' : M` and `d : S`
such that `f z' - f d = z` and `f w' - f d = w`. -/]
/-
**Submonoid.LocalizationMap.surj** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localizati
onMap`。
形式化陈述：surj (f : LocalizationMap S N) (z : N) : exists x : M × S, z * f x.2 = f x
.1
参数：f : LocalizationMap S N；z : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
-/
theorem surj₂ (f : LocalizationMap S N) (z w : N) : ∃ z' w' : M, ∃ d : S,
    (z * f d = f z') ∧ (w * f d = f w') := by
  let ⟨a, ha⟩ := surj f z
  let ⟨b, hb⟩ := surj f w
  refine ⟨a.1 * b.2, a.2 * b.1, a.2 * b.2, ?_, ?_⟩
  · simp_rw [mul_def, map_mul, ← ha]
    exact (mul_assoc z _ _).symm
  · simp_rw [mul_def, map_mul, ← hb]
    exact mul_left_comm w _ _

@[to_additive]
/-
**Submonoid.LocalizationMap.eq_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：eq_iff_exists (f : LocalizationMap S N) {x y} : f x = f y ↔ exists c : S, 
c * x = c * y
参数：f : LocalizationMap S N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.exists_of_eq`：∀ {M : Type u_1} [inst : CommM
onoid M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},  
 S.IsLocalizationMap f → ∀ {x …
· 使用定理 `Submonoid.LocalizationMap.isLocalizationMap`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (self : S
.LocalizationMap N), S.IsLocaliza…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
-/
theorem eq_iff_exists (f : LocalizationMap S N) {x y} :
    f x = f y ↔ ∃ c : S, c * x = c * y := Iff.intro f.2.3
  fun ⟨c, h⟩ ↦ by
    replace h := congr_arg f h
    rw [map_mul, map_mul] at h
    exact (f.map_units c).mul_right_inj.mp h

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
@[to_additive
/-- Given a localization map `f : M →+ N`, a section function sending `z : N`
to some `(x, y) : M × S` such that `f x - f y = z`. -/]
/-
**Submonoid.LocalizationMap.sec** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizatio
nMap`。
形式化陈述：sec (f : LocalizationMap S N) (z : N) : M × S
参数：f : LocalizationMap S N；z : N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
-/
noncomputable def sec (f : LocalizationMap S N) (z : N) : M × S := Classical.choose <| f.surj z

@[to_additive]
/-
**Submonoid.LocalizationMap.sec_spec** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：sec_spec {f : LocalizationMap S N} (z : N) : z * f (f.sec z).2 = f (f.sec 
z).1
参数：z : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
-/
theorem sec_spec {f : LocalizationMap S N} (z : N) :
    z * f (f.sec z).2 = f (f.sec z).1 := Classical.choose_spec <| f.surj z

@[to_additive]
/-
**Submonoid.LocalizationMap.sec_spec'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：sec_spec' {f : LocalizationMap S N} (z : N) : f (f.sec z).1 = f (f.sec z).
2 * z
参数：z : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.sec_spec`：sec_spec {f : LocalizationMap S N} (
z : N) : z * f (f.sec z).2 = f (f.sec z).1
-/
theorem sec_spec' {f : LocalizationMap S N} (z : N) :
    f (f.sec z).1 = f (f.sec z).2 * z := by rw [mul_comm, sec_spec]

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`w, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that `f(S) ⊆ AddUnits N`, for all
`w, z : N` and `y ∈ S`, we have `w - f y = z ↔ w = f y + z`. -/]
/-
**Submonoid.LocalizationMap.mul_inv_left** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：mul_inv_left {f : M ->* N} (h : forall y : S, IsUnit (f y)) (y : S) (w z :
 N) : w * (IsUnit.liftRight (f.domRestrict S) h y)⁻¹ = z ↔ w = f y * z
参数：h : forall y : S, IsUnit (f y)；y : S；w z : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
-/
theorem mul_inv_left {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) (w z : N) :
    w * (IsUnit.liftRight (f.domRestrict S) h y)⁻¹ = z ↔ w = f y * z := by
  rw [mul_comm]
  exact Units.inv_mul_eq_iff_eq_mul (IsUnit.liftRight (f.domRestrict S) h y)

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`w, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that `f(S) ⊆ AddUnits N`, for all
`w, z : N` and `y ∈ S`, we have `z = w - f y ↔ z + f y = w`. -/]
/-
**Submonoid.LocalizationMap.mul_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：mul_inv_right {f : M ->* N} (h : forall y : S, IsUnit (f y)) (y : S) (w z 
: N) : z = w * (IsUnit.liftRight (f.domRestrict S) h y)⁻¹ ↔ z * f y = w
参数：h : forall y : S, IsUnit (f y)；y : S；w z : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_right {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) (w z : N) :
    z = w * (IsUnit.liftRight (f.domRestrict S) h y)⁻¹ ↔ z * f y = w := by
  rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ Nˣ`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[to_additive (attr := simp)
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ - f y₁ = f x₂ - f y₂ ↔ f (x₁ + y₂) = f (x₂ + y₁)`. -/]
/-
**Submonoid.LocalizationMap.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：mul_inv {f : M ->* N} (h : forall y : S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S}
 : f x₁ * (IsUnit.liftRight (f.domRestrict S) h y₁)⁻¹ = f x₂ * (IsUnit.liftRight
 (f.domRestrict S) h y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)
参数：h : forall y : S, IsUnit (f y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mul_inv_right`：mul_inv_right {f : M ->* N} (h 
: forall y : S, IsUnit (f y)) (y : S) (w z : N) : z = w * (IsUnit.liftRight (f.d
omRestrict S) h y)⁻¹ ↔ z * f …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} :
    f x₁ * (IsUnit.liftRight (f.domRestrict S) h y₁)⁻¹ =
        f x₂ * (IsUnit.liftRight (f.domRestrict S) h y₂)⁻¹ ↔
      f (x₁ * y₂) = f (x₂ * y₁) := by
  rw [mul_inv_right h, mul_assoc, mul_comm _ (f y₂), ← mul_assoc, mul_inv_left h, mul_comm x₂,
    f.map_mul, f.map_mul]

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `y, z ∈ S`, we have `- (f y) = - (f z) → f y = f z`. -/]
/-
**Submonoid.LocalizationMap.inv_inj** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：inv_inj {f : M ->* N} (hf : forall y : S, IsUnit (f y)) {y z : S} (h : (Is
Unit.liftRight (f.domRestrict S) hf y)⁻¹ = (IsUnit.liftRight (f.domRestrict S) h
f z)⁻¹) : f y = f z
参数：hf : forall y : S, IsUnit (f y)；h : (IsUnit.liftRight (f.domRestrict S) hf y)
⁻¹ = (IsUnit.liftRight (f.domRestrict S) hf z)⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
theorem inv_inj {f : M →* N} (hf : ∀ y : S, IsUnit (f y)) {y z : S}
    (h : (IsUnit.liftRight (f.domRestrict S) hf y)⁻¹ =
      (IsUnit.liftRight (f.domRestrict S) hf z)⁻¹) : f y = f z := by
  rw [← mul_one (f y), eq_comm, ← mul_inv_left hf y (f z) 1, h]
  exact Units.inv_mul (IsUnit.liftRight (f.domRestrict S) hf z)⁻¹

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`y ∈ S`, `(f y)⁻¹` is unique. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `y ∈ S`, `- (f y)` is unique. -/]
/-
**Submonoid.LocalizationMap.inv_unique** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loca
lizationMap`。
形式化陈述：inv_unique {f : M ->* N} (h : forall y : S, IsUnit (f y)) {y : S} {z : N} 
(H : f y * z = 1) : (IsUnit.liftRight (f.domRestrict S) h y)⁻¹ = z
参数：h : forall y : S, IsUnit (f y)；H : f y * z = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
-/
theorem inv_unique {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {y : S} {z : N} (H : f y * z = 1) :
    (IsUnit.liftRight (f.domRestrict S) h y)⁻¹ = z := by
  rw [← one_mul _⁻¹, Units.val_mul, mul_inv_left]
  exact H.symm

variable (f : LocalizationMap S N)

@[to_additive]
/-
**Submonoid.LocalizationMap.map_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Submonoi
d.LocalizationMap`。
形式化陈述：map_right_cancel {x y} {c : S} (h : f (c * x) = f (c * y)) : f x = f y
参数：h : f (c * x) = f (c * y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.mul_right_inj`：mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a 
* c ↔ b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
-/
theorem map_right_cancel {x y} {c : S} (h : f (c * x) = f (c * y)) :
    f x = f y := by
  rw [map_mul, map_mul] at h
  let ⟨u, hu⟩ := f.map_units c
  rw [← hu] at h
  exact (Units.mul_right_inj u).1 h

@[to_additive]
/-
**Submonoid.LocalizationMap.map_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
.LocalizationMap`。
形式化陈述：map_left_cancel {x y} {c : S} (h : f (x * c) = f (y * c)) : f x = f y
参数：h : f (x * c) = f (y * c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_right_cancel`：map_right_cancel {x y} {c : 
S} (h : f (c * x) = f (c * y)) : f x = f y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem map_left_cancel {x y} {c : S} (h : f (x * c) = f (y * c)) :
    f x = f y :=
  f.map_right_cancel (c := c) <| by rw [mul_comm _ x, mul_comm _ y, h]

/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
`f x * (f y)⁻¹`. -/
@[to_additive
/-- Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S` to
`f x - f y`. -/]
/-
**Submonoid.LocalizationMap.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizatio
nMap`。
形式化陈述：mk' (f : LocalizationMap S N) (x : M) (y : S) : N
参数：f : LocalizationMap S N；x : M；y : S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
noncomputable def mk' (f : LocalizationMap S N) (x : M) (y : S) : N :=
  f x * ↑(IsUnit.liftRight (f.toMonoidHom.domRestrict S) f.map_units y)⁻¹

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x₁ x₂ : M) (y₁ y₂ : ↥S), f.mk
' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂
参数：f : S.LocalizationMap N；x₁ x₂ : M；y₁ y₂ : ↥S；x₁ * x₂；y₁ * y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) : f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ := by
  refine (mul_inv_left f.map_units _ _ _).2 ?_
  simp only [map_mul, coe_mul, toMonoidHom_apply, mk', IsUnit.liftRight, Units.liftRight,
    MonoidHom.domRestrict_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_mul_mul_comm (f x₁), mul_left_comm, mul_mul_mul_comm (f y₁)]
  simp

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_one** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M), f.mk' x 1 = f x
参数：f : S.LocalizationMap N；x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mk'.eq_1`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mk'_one (x) : f.mk' x (1 : S) = f x := by
  rw [mk', map_one]
  exact mul_one _

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
`x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[to_additive (attr := simp)
/-- Given a localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, for all `z : N`
we have that if `x : M, y ∈ S` are such that `z + f y = f x`, then `f x - f y = z`. -/]
/-
**Submonoid.LocalizationMap.mk'_sec** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (z : N), f.mk' (f.sec z).1 (f.
sec z).2 = z
参数：f : S.LocalizationMap N；z : N；f.sec z；f.sec z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.sec_spec`：sec_spec {f : LocalizationMap S N} (
z : N) : z * f (f.sec z).2 = f (f.sec z).1
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mk'_sec (z : N) : f.mk' (f.sec z).1 (f.sec z).2 = z :=
  show _ * _ = _ by rw [← sec_spec, mul_inv_left, mul_comm]; dsimp

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.
LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (z : N), ∃ x y, f.mk' x y = z
参数：f : S.LocalizationMap N；z : N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_sec`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (z : N), f.mk' (…
-/
theorem mk'_surjective (z : N) : ∃ (x : _) (y : S), f.mk' x y = z :=
  ⟨(f.sec z).1, (f.sec z).2, f.mk'_sec z⟩

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_spec** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M) (y : ↥S), f.mk' x y * 
f ↑y = f x
参数：f : S.LocalizationMap N；x : M；y : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
-/
theorem mk'_spec (x) (y : S) : f.mk' x y * f y = f x :=
  show _ * _ * _ = _ by rw [mul_assoc, mul_comm _ (f y), ← mul_assoc, mul_inv_left, mul_comm]; dsimp

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_spec'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M) (y : ↥S), f ↑y * f.mk'
 x y = f x
参数：f : S.LocalizationMap N；x : M；y : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.mk'_spec`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
-/
theorem mk'_spec' (x) (y : S) : f y * f.mk' x y = f x := by rw [mul_comm, mk'_spec]

@[to_additive]
/-
**Submonoid.LocalizationMap.eq_mk'_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {x : M} {y : ↥S} {z : N}, z = 
f.mk' x y ↔ z * f ↑y = f x
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mk'_spec`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.mk'.eq_1`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_right`：mul_inv_right {f : M ->* N} (h 
: forall y : S, IsUnit (f y)) (y : S) (w z : N) : z = w * (IsUnit.liftRight (f.d
omRestrict S) h y)⁻¹ ↔ z * f …
-/
theorem eq_mk'_iff_mul_eq {x} {y : S} {z} : z = f.mk' x y ↔ z * f y = f x :=
  ⟨fun H ↦ by rw [H, mk'_spec], fun H ↦ by rwa [mk', mul_inv_right]⟩

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {x : M} {y : ↥S} {z : N}, f.mk
' x y = z ↔ f x = z * f ↑y
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submonoid.LocalizationMap.eq_mk'_iff_mul_eq`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) {x : M} {y : ↥S}…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk'_eq_iff_eq_mul {x} {y : S} {z} : f.mk' x y = z ↔ f x = z * f y := by
  rw [eq_comm, eq_mk'_iff_mul_eq, eq_comm]

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {x₁ x₂ : M} {y₁ y₂ : ↥S}, f.mk
' x₁ y₁ = f.mk' x₂ y₂ ↔ f (↑y₂ * x₁) = f (↑y₁ * x₂)
参数：f : S.LocalizationMap N；↑y₂ * x₁；↑y₁ * x₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq_mul`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) {x : M} {y : ↥S}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.LocalizationMap.mk'_spec'`：∀ {M : Type u_1} [inst : CommMonoid
 M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizati
onMap N) (x : M) (y : ↥S)…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.mk'.eq_1`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_right`：mul_inv_right {f : M ->* N} (h 
: forall y : S, IsUnit (f y)) (y : S) (w z : N) : z = w * (IsUnit.liftRight (f.d
omRestrict S) h y)⁻¹ ↔ z * f …
· 使用定理 `Submonoid.LocalizationMap.toMonoidHom_apply`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) (x : M), f.toMon…
-/
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f (y₂ * x₁) = f (y₁ * x₂) where
  mp H := by
    rw [map_mul f, map_mul f, f.mk'_eq_iff_eq_mul.1 H, ← mul_assoc, mk'_spec', mul_comm (f x₂)]
  mpr H := by
    rw [mk'_eq_iff_eq_mul, mk', mul_assoc, mul_comm _ (f y₁), ← mul_assoc, ← map_mul f, mul_comm x₂,
      ← H, ← mul_comm x₁, map_mul f, mul_inv_right f.map_units, toMonoidHom_apply]

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_iff_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.
LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {x₁ x₂ : M} {y₁ y₂ : ↥S}, f.mk
' x₁ y₁ = f.mk' x₂ y₂ ↔ f (x₁ * ↑y₂) = f (x₂ * ↑y₁)
参数：f : S.LocalizationMap N；x₁ * ↑y₂；x₂ * ↑y₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {x₁ x₂ : M} {y₁ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f (x₁ * y₂) = f (x₂ * y₁) := by
  simp only [f.mk'_eq_iff_eq, mul_comm]

@[to_additive]
/-
**Submonoid.LocalizationMap.eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localization
Map`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {a₁ b₁ : M} {a₂ b₂ : ↥S}, f.mk
' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c, ↑c * (↑b₂ * a₁) = ↑c * (↑a₂ * b₁)
参数：f : S.LocalizationMap N；↑b₂ * a₁；↑a₂ * b₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {x₁ x₂ : M} {y₁ …
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y
-/
protected theorem eq {a₁ b₁} {a₂ b₂ : S} :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : S, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  f.mk'_eq_iff_eq.trans <| f.eq_iff_exists

@[to_additive]
/-
**Submonoid.LocalizationMap.eq'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localizatio
nMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {a₁ b₁ : M} {a₂ b₂ : ↥S}, f.mk
' a₁ a₂ = f.mk' b₁ b₂ ↔ (Localization.r S) (a₁, a₂) (b₁, b₂)
参数：f : S.LocalizationMap N；Localization.r S；a₁, a₂；b₁, b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.eq`：∀ {M : Type u_1} [inst : CommMonoid M] {S 
: Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.LocalizationMap N
) {a₁ b₁ : M} {a₂ …
· 使用定理 `Localization.r_iff_exists`：r_iff_exists {x y : M × S} : r S x y ↔ exists
 c : S, ↑c * (↑y.2 * x.1) = c * (x.2 * y.1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem eq' {a₁ b₁} {a₂ b₂ : S} :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ Localization.r S (a₁, a₂) (b₁, b₂) := by
  rw [f.eq, Localization.r_iff_exists]

@[to_additive]
/-
**Submonoid.LocalizationMap.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：eq_iff_eq (g : LocalizationMap S P) {x y} : f x = f y ↔ g x = g y
参数：g : LocalizationMap S P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem eq_iff_eq (g : LocalizationMap S P) {x y} : f x = f y ↔ g x = g y :=
  f.eq_iff_exists.trans g.eq_iff_exists.symm

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_iff_mk'_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N] {P : Type u_3}   [inst_2 : CommMonoid P] (f : S.Localizati
onMap N) (g : S.LocalizationMap P) {x₁ x₂ : M} {y₁ y₂ : ↥S},   f.mk' x₁ y₁ = f.m
k' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂
参数：f : S.LocalizationMap N；g : S.LocalizationMap P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submonoid.LocalizationMap.eq'`：∀ {M : Type u_1} [inst : CommMonoid M] {S
 : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.LocalizationMap 
N) {a₁ b₁ : M} {a₂ …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem mk'_eq_iff_mk'_eq (g : LocalizationMap S P) {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
  f.eq'.trans g.eq'.symm

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, for all `x₁ : M`
and `y₁ ∈ S`, if `x₂ : M, y₂ ∈ S` are such that `(f x₁ - f y₁) + f y₂ = f x₂`, then there exists
`c ∈ S` such that `x₁ + y₂ + c = x₂ + y₁ + c`. -/]
/-
**Submonoid.LocalizationMap.exists_of_sec_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：exists_of_sec_mk' (x) (y : S) : exists c : S, ↑c * (↑(f.sec <| f.mk' x y).
2 * x) = c * (y * (f.sec <| f.mk' x y).1)
参数：x；y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {x₁ x₂ : M} {y₁ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mk'_sec`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (z : N), f.mk' (…
-/
theorem exists_of_sec_mk' (x) (y : S) :
    ∃ c : S, ↑c * (↑(f.sec <| f.mk' x y).2 * x) = c * (y * (f.sec <| f.mk' x y).1) :=
  f.eq_iff_exists.1 <| f.mk'_eq_iff_eq.1 <| (mk'_sec _ _).symm

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {a₁ b₁ : M} {a₂ b₂ : ↥S}, ↑a₂ 
* b₁ = ↑b₂ * a₁ → f.mk' a₁ a₂ = f.mk' b₁ b₂
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {x₁ x₂ : M} {y₁ …
-/
theorem mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_iff_eq.2 <| H ▸ rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_of_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {a₁ b₁ : M} {a₂ b₂ : ↥S}, b₁ *
 ↑a₂ = a₁ * ↑b₂ → f.mk' a₁ a₂ = f.mk' b₁ b₂
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_of_eq`：∀ {M : Type u_1} [inst : CommMon
oid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localiz
ationMap N) {a₁ b₁ : M} {a₂ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mk'_eq_of_eq' {a₁ b₁ : M} {a₂ b₂ : S} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_of_eq <| by simpa only [mul_comm] using H

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loca
lizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (a : M) (b c : ↥S), f.mk' (a *
 ↑c) (b * c) = f.mk' a b
参数：f : S.LocalizationMap N；a : M；b c : ↥S；a * ↑c；b * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_of_eq'`：∀ {M : Type u_1} [inst : CommMo
noid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {a₁ b₁ : M} {a₂ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem mk'_cancel (a : M) (b c : S) :
    f.mk' (a * c) (b * c) = f.mk' a b :=
  mk'_eq_of_eq' f (by rw [Submonoid.coe_mul, mul_comm (b : M), mul_assoc])

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_eq_of_same** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.
LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {a b : M} {d : ↥S}, f.mk' a d 
= f.mk' b d ↔ ∃ c, ↑c * a = ↑c * b
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mk'_eq_iff_eq'`：∀ {M : Type u_1} [inst : CommM
onoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Local
izationMap N) {x₁ x₂ : M} {y₁ …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem mk'_eq_of_same {a b} {d : S} :
    f.mk' a d = f.mk' b d ↔ ∃ c : S, c * a = c * b := by
  rw [mk'_eq_iff_eq', map_mul, map_mul, ← eq_iff_exists f]
  exact (map_units f d).mul_left_inj

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mk'_self'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (y : ↥S), f.mk' (↑y) y = 1
参数：f : S.LocalizationMap N；y : ↥S；↑y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mk'_self' (y : S) : f.mk' (y : M) y = 1 :=
  show _ * _ = _ by rw [mul_inv_left, mul_one]; dsimp

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mk'_self** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M) (H : x ∈ S), f.mk' x ⟨
x, H⟩ = 1
参数：f : S.LocalizationMap N；x : M；H : x ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_self'`：∀ {M : Type u_1} [inst : CommMonoid
 M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizati
onMap N) (y : ↥S), f.mk' …
-/
theorem mk'_self (x) (H : x ∈ S) : f.mk' x ⟨x, H⟩ = 1 := mk'_self' f ⟨x, H⟩

@[to_additive]
/-
**Submonoid.LocalizationMap.mul_mk'_eq_mk'_of_mul** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x₁ x₂ : M) (y : ↥S), f x₁ * f
.mk' x₂ y = f.mk' (x₁ * x₂) y
参数：f : S.LocalizationMap N；x₁ x₂ : M；y : ↥S；x₁ * x₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mk'_one`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (x : M), f.mk' x…
· 使用定理 `Submonoid.LocalizationMap.mk'_mul`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (x₁ x₂ : M) (y₁ …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_mk'_eq_mk'_of_mul (x₁ x₂) (y : S) : f x₁ * f.mk' x₂ y = f.mk' (x₁ * x₂) y := by
  rw [← mk'_one, ← mk'_mul, one_mul]

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_mul_eq_mk'_of_mul** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x₁ x₂ : M) (y : ↥S), f.mk' x₂
 y * f x₁ = f.mk' (x₁ * x₂) y
参数：f : S.LocalizationMap N；x₁ x₂ : M；y : ↥S；x₁ * x₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.mul_mk'_eq_mk'_of_mul`：∀ {M : Type u_1} [inst 
: CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : 
S.LocalizationMap N) (x₁ x₂ : M) (y :…
-/
theorem mk'_mul_eq_mk'_of_mul (x₁ x₂) (y : S) : f.mk' x₂ y * f x₁ = f.mk' (x₁ * x₂) y := by
  rw [mul_comm, mul_mk'_eq_mk'_of_mul]

@[to_additive]
/-
**Submonoid.LocalizationMap.mul_mk'_one_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Submon
oid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M) (y : ↥S), f x * f.mk' 
1 y = f.mk' x y
参数：f : S.LocalizationMap N；x : M；y : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mul_mk'_eq_mk'_of_mul`：∀ {M : Type u_1} [inst 
: CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : 
S.LocalizationMap N) (x₁ x₂ : M) (y :…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_mk'_one_eq_mk' (x) (y : S) : f x * f.mk' 1 y = f.mk' x y := by
  rw [mul_mk'_eq_mk'_of_mul, mul_one]

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mk'_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Subm
onoid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M) (y : ↥S), f.mk' (x * ↑
y) y = f x
参数：f : S.LocalizationMap N；x : M；y : ↥S；x * ↑y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mul_mk'_one_eq_mk'`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.L
ocalizationMap N) (x : M) (y : ↥S)…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.LocalizationMap.mk'_self'`：∀ {M : Type u_1} [inst : CommMonoid
 M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizati
onMap N) (y : ↥S), f.mk' …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mk'_mul_cancel_right (x : M) (y : S) : f.mk' (x * y) y = f x := by
  rw [← mul_mk'_one_eq_mk', map_mul, mul_assoc, mul_mk'_one_eq_mk', mk'_self', mul_one]

@[to_additive]
/-
**Submonoid.LocalizationMap.mk'_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Submo
noid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) (x : M) (y : ↥S), f.mk' (↑y * 
x) y = f x
参数：f : S.LocalizationMap N；x : M；y : ↥S；↑y * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.mk'_mul_cancel_right`：∀ {M : Type u_1} [inst :
 CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S
.LocalizationMap N) (x : M) (y : ↥S)…
-/
theorem mk'_mul_cancel_left (x) (y : S) : f.mk' ((y : M) * x) y = f x := by
  rw [mul_comm, mk'_mul_cancel_right]

@[to_additive]
/-
**Submonoid.LocalizationMap.isUnit_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loc
alizationMap`。
形式化陈述：isUnit_comp (j : N ->* P) (y : S) : IsUnit (j.comp f.toMonoidHom y)
参数：j : N ->* P；y : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsUnit.coe_liftRight`：coe_liftRight (f : M ->* N) (hf : forall x, IsUnit
 (f x)) (x) : (IsUnit.liftRight f hf x : N) = f x
-/
theorem isUnit_comp (j : N →* P) (y : S) : IsUnit (j.comp f.toMonoidHom y) :=
  ⟨Units.map j <| IsUnit.liftRight (f.toMonoidHom.domRestrict S) f.map_units y, show j _ = j _ from
      congr_arg j (IsUnit.coe_liftRight (f.toMonoidHom.domRestrict S) f.map_units _)⟩

@[to_additive]
/-
**Submonoid.LocalizationMap.epic_of_localizationMap** 是 Mathlib 中的一个定理，位于命名空间 `S
ubmonoid.LocalizationMap`。
形式化陈述：epic_of_localizationMap {P : Type*} [Monoid P] {j k : N ->* P} (h : j.comp
 f.toMonoidHom = k.comp f.toMonoidHom) : j = k
参数：h : j.comp f.toMonoidHom = k.comp f.toMonoidHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
-/
theorem epic_of_localizationMap {P : Type*} [Monoid P] {j k : N →* P}
    (h : j.comp f.toMonoidHom = k.comp f.toMonoidHom) : j = k := by
  ext n
  obtain ⟨⟨m, s⟩, hn : n * f s = f m⟩ := f.surj n
  replace h (a) : j (f a) = k (f a) := congr($h a)
  exact ((f.map_units s).map j).mul_left_inj.mp <| by rw [← j.map_mul, h, ← k.map_mul, hn, h m]

end LocalizationMap

end Submonoid

namespace Localization

variable (S) in
/-- Natural homomorphism sending `x : M`, `M` a `CommMonoid`, to the equivalence class of
`(x, 1)` in the Localization of `M` at a Submonoid. -/
@[to_additive
/-- Natural homomorphism sending `x : M`, `M` an `AddCommMonoid`, to the equivalence class of
`(x, 0)` in the Localization of `M` at a Submonoid. -/]
/-
**Localization.monoidOf** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：monoidOf : Submonoid.LocalizationMap S (Localization S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidOf : Submonoid.LocalizationMap S (Localization S) :=
  { (r S).mk'.comp <| MonoidHom.inl M S with
    toFun := fun x ↦ mk x 1
    map_mul' := fun x y ↦ by rw [mk_mul, mul_one]
    isLocalizationMap :=
    { map_units y :=
        isUnit_iff_exists_inv.2 ⟨mk 1 y, by rw [mk_mul, mul_one, one_mul, mk_self]⟩
      surj z := induction_on z fun x ↦
        ⟨x, by rw [mk_mul, mul_comm x.fst, ← mk_mul, mk_self, one_mul]⟩
      exists_of_eq := Iff.mp <| mk_eq_mk_iff.trans <| r_iff_exists.trans <| by simp } }

@[to_additive]
/-
**Localization.mk_one_eq_monoidOf_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_one_eq_monoidOf_mk (x) : mk x 1 = monoidOf S x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one_eq_monoidOf_mk (x) : mk x 1 = monoidOf S x := rfl

@[to_additive]
/-
**Localization.mk_eq_monoidOf_mk'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Localization`
。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} (x : M) (y : ↥S),
   Localization.mk x y = (Localization.monoidOf S).mk' x y
参数：x : M；y : ↥S；Localization.monoidOf S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_right`：mul_inv_right {f : M ->* N} (h 
: forall y : S, IsUnit (f y)) (y : S) (w z : N) : z = w * (IsUnit.liftRight (f.d
omRestrict S) h y)⁻¹ ↔ z * f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.mk_one_eq_monoidOf_mk`：mk_one_eq_monoidOf_mk (x) : mk x 1 =
 monoidOf S x
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Localization.mk_eq_mk_iff`：mk_eq_mk_iff {a c : M} {b d : S} : mk a b = m
k c d ↔ r S ⟨a, b⟩ ⟨c, d⟩
· 使用定理 `Con.symm`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y : M}, c x y →
 c y x
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
· 使用定理 `Con.refl`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) (x : M), c x x
· 使用定理 `Localization.one_rel`：one_rel (y : S) : r S 1 (y, y)
-/
theorem mk_eq_monoidOf_mk'_apply (x y) : mk x y = (monoidOf S).mk' x y :=
  show _ = _ * _ from
    (Submonoid.LocalizationMap.mul_inv_right (monoidOf S).map_units _ _ _).2 <| by
      dsimp
      rw [← mk_one_eq_monoidOf_mk, ← mk_one_eq_monoidOf_mk, mk_mul x y y 1, mul_comm y 1]
      conv => rhs; rw [← mul_one 1]; rw [← mul_one x]
      exact mk_eq_mk_iff.2 (Con.symm _ <| (Localization.r S).mul (Con.refl _ (x, 1)) <| one_rel _)

@[to_additive]
/-
**Localization.mk_eq_monoidOf_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_eq_monoidOf_mk'_apply (x y) : mk x y = (monoidOf S).mk' x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Localization.mk_eq_monoidOf_mk'_apply`：∀ {M : Type u_1} [inst : CommMono
id M] {S : Submonoid M} (x : M) (y : ↥S),   Localization.mk x y = (Localization.
monoidOf S).mk' x y
-/
theorem mk_eq_monoidOf_mk' : mk = (monoidOf S).mk' :=
  funext fun _ ↦ funext fun _ ↦ mk_eq_monoidOf_mk'_apply _ _

universe u

@[to_additive (attr := simp)]
/-
**Localization.liftOn_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：liftOn_mk' {p : Sort u} (f : M -> S -> p) (H) (a : M) (b : S) : liftOn ((m
onoidOf S).mk' a b) f H = f a b
参数：f : M -> S -> p；H；a : M；b : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.mk_eq_monoidOf_mk'`：mk_eq_monoidOf_mk'_apply (x y) : mk x y
 = (monoidOf S).mk' x y
· 使用定理 `Localization.liftOn_mk`：liftOn_mk {p : Sort u} (f : M -> S -> p) (H) (a 
: M) (b : S) : liftOn (mk a b) f H = f a b
-/
theorem liftOn_mk' {p : Sort u} (f : M → S → p) (H) (a : M) (b : S) :
    liftOn ((monoidOf S).mk' a b) f H = f a b := by rw [← mk_eq_monoidOf_mk', liftOn_mk]

@[to_additive (attr := simp)]
/-
**Localization.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：liftOn {p : Sort u} (x : Localization S) (f : M -> S -> p) (H : forall {a 
c : M} {b d : S}, r S (a, b) (c, d) -> f a b = f c d) : p
参数：x : Localization S；f : M -> S -> p；H : forall {a c : M} {b d : S}, r S (a, b)
 (c, d) -> f a b = f c d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_mk' {p : Sort*} (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
    liftOn₂ ((monoidOf S).mk' a b) ((monoidOf S).mk' c d) f H = f a b c d := by
  rw [← mk_eq_monoidOf_mk', liftOn₂_mk]

/-- The localization of a torsion-free monoid is torsion-free. -/
@[to_additive /-- The localization of a torsion-free monoid is torsion-free. -/]
/-
**Localization.instIsMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：instIsMulTorsionFree [IsMulTorsionFree M] : IsMulTorsionFree Localization 
S where pow_left_injective n hn
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Localization.mk_pow`：mk_pow (n : Nat) (a : M) (b : S) : mk a b ^ n = mk 
(a ^ n) (b ^ n)
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
The localization of a torsion-free monoid is torsion-free.
-/
instance instIsMulTorsionFree [IsMulTorsionFree M] : IsMulTorsionFree <| Localization S where
  pow_left_injective n hn := by
    rintro ⟨a⟩ ⟨b⟩ (hab : mk a.1 a.2 ^ n = mk b.1 b.2 ^ n)
    change mk a.1 a.2 = mk b.1 b.2
    simp only [mk_pow, mk_eq_mk_iff, r_iff_exists, SubmonoidClass.coe_pow, Subtype.exists,
      exists_prop] at hab ⊢
    obtain ⟨c, hc, hab⟩ := hab
    refine ⟨c, hc, pow_left_injective hn ?_⟩
    obtain _ | n := n
    · simp
    · simp [mul_pow, pow_succ c, mul_assoc, hab]

end Localization

end CommMonoid

namespace Localization

variable {α : Type*} [CommMonoid α] [IsCancelMul α] {s : Submonoid α} {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
/-
**Localization.mk_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_left_injective (b : s) : Injective fun a => mk a b
参数：b : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem mk_left_injective (b : s) : Injective fun a => mk a b := fun c d h => by
  simpa [mk_eq_mk_iff, r_iff_exists] using h

@[to_additive]
/-
**Localization.mk_eq_mk_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_eq_mk_iff' : mk a₁ a₂ = mk b₁ b₂ ↔ ↑b₂ * a₁ = a₂ * b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_eq_mk_iff' : mk a₁ a₂ = mk b₁ b₂ ↔ ↑b₂ * a₁ = a₂ * b₁ := by
  simp_rw [mk_eq_mk_iff, r_iff_exists, mul_left_cancel_iff, exists_const]

@[to_additive]
/-
**Localization.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：decidableEq [DecidableEq α] : DecidableEq (Localization s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mk_eq_mk_iff'`：mk_eq_mk_iff' : mk a₁ a₂ = mk b₁ b₂ ↔ ↑b₂ * 
a₁ = a₂ * b₁
-/
instance decidableEq [DecidableEq α] : DecidableEq (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_eq_mk_iff'

end Localization

namespace OreLocalization

variable (R) [CommMonoid R] (S : Submonoid R)

/-- The morphism `numeratorHom` is a monoid localization map in the case of commutative `R`. -/
/-
**OreLocalization.localizationMap** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：(R : Type u_1) → [inst : CommMonoid R] → (S : Submonoid R) → S.Localizatio
nMap (OreLocalization S R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `numeratorHom` is a monoid localization map in the case of commutat
ive `R`.
-/
protected def localizationMap : S.LocalizationMap R[S⁻¹] := Localization.monoidOf S

/-- If `R` is commutative, Ore localization and monoid localization are isomorphic. -/
/-
**OreLocalization.equivMonoidLocalization** 是 Mathlib 中的一个定义，位于命名空间 `OreLocaliza
tion`。
形式化陈述：(R : Type u_1) → [inst : CommMonoid R] → (S : Submonoid R) → Localization 
S ≃* OreLocalization S R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is commutative, Ore localization and monoid localization are isomorphic.
-/
protected noncomputable def equivMonoidLocalization : Localization S ≃* R[S⁻¹] := MulEquiv.refl _

end OreLocalization

section Group

variable {M G F : Type*} [CommMonoid M] [CommGroup G]

/-
**Submonoid.isLocalizationMap_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid
`。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} {F : Type u_3} [inst : CommMonoid M] [inst
_1 : CommGroup G] {S : Submonoid G}   [inst_2 : FunLike F G M] [MulHomClass F G 
M] {f : F}, S.IsLocalizationMap ⇑f ↔ Function.Bijective ⇑f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsLocalizationMap.exists_of_eq`：∀ {M : Type u_1} [inst : CommM
onoid M] {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},  
 S.IsLocalizationMap f → ∀ {x …
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Submonoid.IsLocalizationMap.surj`：∀ {M : Type u_1} [inst : CommMonoid M]
 {N : Type u_2} [inst_1 : CommMonoid N] {S : Submonoid M} {f : M → N},   S.IsLoc
alizationMap f → ∀ (z …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Submonoid.IsLocalizationMap.map_one`：∀ {M : Type u_1} [inst : CommMonoid
 M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N] {F : Type u_4}   [i
nst_2 : FunLike F M N] [M…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulEquiv.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOneClass M]
 [inst_1 : MulOneClass N] (h : M ≃* N), h 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
@[to_additive] theorem Submonoid.isLocalizationMap_iff_bijective {S : Submonoid G}
    [FunLike F G M] [MulHomClass F G M] {f : F} :
    S.IsLocalizationMap f ↔ Bijective f where
  mp h := by
    refine ⟨fun g g' eq ↦ ?_, fun m ↦ ?_⟩
    · have ⟨c, eq⟩ := h.exists_of_eq eq
      exact mul_left_cancel eq
    · have ⟨x, eq⟩ := h.surj m
      use x.1 / x.2
      rw [div_eq_mul_inv, map_mul, ← eq, mul_assoc, ← map_mul, mul_inv_cancel, h.map_one, mul_one]
  mpr h := let e : G ≃* M := ⟨Equiv.ofBijective f h, map_mul f⟩
  { map_units _ := (Group.isUnit _).map e
    surj m := have ⟨g, eq⟩ := h.2 m
      ⟨⟨g, 1⟩, congr(m * $e.map_one).trans <| (mul_one _).trans eq.symm⟩
    exists_of_eq eq := by simp [h.1 eq] }
/-
**Submonoid.isLocalizationMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {G : Type u_2} [inst : CommGroup G] (S : Submonoid G), S.IsLocalizationM
ap id
参数：S : Submonoid G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.isLocalizationMap_iff_bijective`：∀ {M : Type u_1} {G : Type u_
2} {F : Type u_3} [inst : CommMonoid M] [inst_1 : CommGroup G] {S : Submonoid G}
   [inst_2 : FunLike F G M] [Mu…
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
@[to_additive] theorem Submonoid.isLocalizationMap_id (S : Submonoid G) :
    S.IsLocalizationMap (@id G) :=
  S.isLocalizationMap_iff_bijective (f := MulHom.id _).mpr bijective_id
/-
**Submonoid.isLocalizationMap_of_group** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_1} {G : Type u_2} [inst : CommMonoid M] [inst_1 : CommGroup 
G] {S : Submonoid M} {f : M → G},   Function.Injective f → (∀ (g : G), ∃ x, ∃ y 
∈ S, g = f x / f y) → S.IsLocalizationMap f
参数：∀ (g : G), ∃ x, ∃ y ∈ S, g = f x / f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
@[to_additive] theorem Submonoid.isLocalizationMap_of_group {S : Submonoid M}
    {f : M → G} (hf : f.Injective) (surj : ∀ g : G, ∃ x : M, ∃ y ∈ S, g = f x / f y) :
    S.IsLocalizationMap f where
  map_units _ := Group.isUnit _
  surj g := have ⟨x, y, hy, eq⟩ := surj g; ⟨⟨x, y, hy⟩, by simp [eq]⟩
  exists_of_eq eq := by simp [hf eq]
/-
**AddSubmonoid.isLocalizationMap_nat_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.isLocalizationMap_nat_int (S : AddSubmonoid Nat) (hS : S != ⊥
) : S.IsLocalizationMap ((↑) : Nat -> Int)
参数：S : AddSubmonoid Nat；hS : S != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.isLocalizationMap_of_addGroup`：∀ {M : Type u_1} {G : Type u
_2} [inst : AddCommMonoid M] [inst_1 : AddCommGroup G] {S : AddSubmonoid M} {f :
 M → G},   Function.Injective f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `AddSubmonoid.bot_or_exists_ne_zero`：∀ {M : Type u_1} [inst : AddZeroClas
s M] (S : AddSubmonoid M), S = ⊥ ∨ ∃ x ∈ S, x ≠ 0
· 使用定理 `Nat.lt_mul_div_succ`：∀ {b : ℕ} (a : ℕ), 0 < b → a < b * (a / b + 1)
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
-/
theorem AddSubmonoid.isLocalizationMap_nat_int (S : AddSubmonoid ℕ) (hS : S ≠ ⊥) :
    S.IsLocalizationMap ((↑) : ℕ → ℤ) :=
  S.isLocalizationMap_of_addGroup (fun _ _ ↦ Int.natCast_inj.mp) fun z ↦ by
    obtain ⟨z, rfl | rfl⟩ := z.eq_nat_or_neg
    · exact ⟨z, 0, zero_mem _, by lia⟩
    have ⟨n, hnS, hn0⟩ := S.bot_or_exists_ne_zero.resolve_left hS
    have key : z < n * (z / n + 1) := Nat.lt_mul_div_succ _ <| Nat.pos_of_ne_zero hn0
    exact ⟨(z / n + 1) * n - z, (z / n + 1) * n, nsmul_mem hnS _, by lia⟩
/-
**AddSubmonoid.isLocalizationMap_top_nat_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.isLocalizationMap_top_nat_int : (⊤ : AddSubmonoid Nat).IsLoca
lizationMap ((↑) : Nat -> Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.isLocalizationMap_nat_int`：AddSubmonoid.isLocalizationMap_n
at_int (S : AddSubmonoid Nat) (hS : S != ⊥) : S.IsLocalizationMap ((↑) : Nat -> 
Int)
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `AddSubmonoid.instNontrivial`：∀ {M : Type u_1} [inst : AddZeroClass M] [N
ontrivial M], Nontrivial (AddSubmonoid M)
-/
theorem AddSubmonoid.isLocalizationMap_top_nat_int :
    (⊤ : AddSubmonoid ℕ).IsLocalizationMap ((↑) : ℕ → ℤ) :=
  AddSubmonoid.isLocalizationMap_nat_int _ top_ne_bot

end Group

namespace Submonoid.LocalizationMap

variable {M N : Type*} [CommMonoid M] {S : Submonoid M} [CommMonoid N]

/-
**Submonoid.LocalizationMap.injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : CommMonoid M] {S : Submonoid M} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N), Function.Injective ⇑f ↔ ∀ ⦃x 
: M⦄, x ∈ S → IsRegular x
参数：f : S.LocalizationMap N。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Commute.isRegular_iff`：Commute.isRegular_iff {a : R} (ca : forall b, Com
mute a b) : IsRegular a ↔ IsLeftRegular a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
@[to_additive] theorem injective_iff (f : LocalizationMap S N) :
    Injective f ↔ ∀ ⦃x⦄, x ∈ S → IsRegular x := by
  simp_rw [Commute.isRegular_iff (Commute.all _), IsLeftRegular,
    Injective, LocalizationMap.eq_iff_exists, exists_imp, Subtype.forall]
  exact forall₂_comm
/-
**Submonoid.LocalizationMap.top_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : CommMonoid M] [inst_1 : CommMonoid
 N] (f : ⊤.LocalizationMap N),   Function.Injective ⇑f ↔ IsCancelMul M
参数：f : ⊤.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] theorem top_injective_iff (f : (⊤ : Submonoid M).LocalizationMap N) :
    Injective f ↔ IsCancelMul M := by
  simp [injective_iff, isCancelMul_iff_forall_isRegular]
/-
**Submonoid.LocalizationMap.map_isRegular** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : CommMonoid M] {S : Submonoid M} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) {m : M}, IsRegular m → IsRegul
ar (f m)
参数：f : S.LocalizationMap N；f m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Commute.isRegular_iff`：Commute.isRegular_iff {a : R} (ca : forall b, Com
mute a b) : IsRegular a ↔ IsLeftRegular a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_additive] theorem map_isRegular (f : LocalizationMap S N) {m : M}
    (hm : IsRegular m) : IsRegular (f m) := by
  refine (Commute.isRegular_iff (Commute.all _)).mpr fun n₁ n₂ eq ↦ ?_
  have ⟨ms₁, eq₁⟩ := f.surj n₁
  have ⟨ms₂, eq₂⟩ := f.surj n₂
  rw [← (f.map_units (ms₁.2 * ms₂.2)).mul_left_inj, Submonoid.coe_mul]
  replace eq := congr($eq * f (ms₁.2 * ms₂.2))
  simp_rw [mul_assoc] at eq
  rw [map_mul, ← mul_assoc n₁, eq₁, ← mul_assoc n₂, mul_right_comm n₂, eq₂] at eq ⊢
  simp_rw [← map_mul, eq_iff_exists] at eq ⊢
  simp_rw [mul_left_comm _ m] at eq
  exact eq.imp fun _ ↦ (hm.1 ·)
/-
**Submonoid.LocalizationMap.isCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loc
alizationMap`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : CommMonoid M] {S : Submonoid M} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) [IsCancelMul M], IsCancelMul N
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Commute.isRegular_iff`：Commute.isRegular_iff {a : R} (ca : forall b, Com
mute a b) : IsRegular a ↔ IsLeftRegular a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.isRightRegular_iff`：∀ {R : Type u_1} [inst : Mul R] {a : R}, (∀ 
(b : R), Commute a b) → (IsRightRegular a ↔ IsLeftRegular a)
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `IsRightRegular.of_mul`：IsRightRegular.of_mul (ab : IsRightRegular (b * a
)) : IsRightRegular b
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `Submonoid.LocalizationMap.map_isRegular`：∀ {M : Type u_1} {N : Type u_2}
 [inst : CommMonoid M] {S : Submonoid M} [inst_1 : CommMonoid N]   (f : S.Locali
zationMap N) {m : M}, IsRegul…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCancelMul_iff_forall_isRegular`：∀ {R : Type u_2} [inst : Mul R], IsCan
celMul R ↔ ∀ (r : R), IsRegular r
-/
@[to_additive] theorem isCancelMul (f : LocalizationMap S N) [IsCancelMul M] : IsCancelMul N := by
  simp_rw [isCancelMul_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n
  have ⟨ms, eq⟩ := f.surj n
  exact (eq ▸ f.map_isRegular (isCancelMul_iff_forall_isRegular.mp ‹_› ms.1)).2.of_mul
/-
**Submonoid.LocalizationMap.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid.LocalizationMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [IsCancelMul M] : IsCancelMul (Localization S) :=
  (Localization.monoidOf S).isCancelMul
/-
**Submonoid.LocalizationMap.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid.LocalizationMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [IsCancelMul M] [Nontrivial M] : Nontrivial (Localization S) :=
  (injective_iff <| Localization.monoidOf S).mpr (fun _ _ ↦ .all _) |>.nontrivial

/-- Any localization of a cancellative commutative monoid is cancellative. -/
@[to_additive
/-- Any localization of a cancellative commutative additive monoid is cancellative. -/]
/-
**Submonoid.LocalizationMap.cancelCommMonoid** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submon
oid.LocalizationMap`。
形式化陈述：cancelCommMonoid {M N} [CancelCommMonoid M] {S : Submonoid M} [CommMonoid 
N] (f : S.LocalizationMap N) : CancelCommMonoid N where mul_left_cancel
参数：f : S.LocalizationMap N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev cancelCommMonoid {M N} [CancelCommMonoid M] {S : Submonoid M}
    [CommMonoid N] (f : S.LocalizationMap N) : CancelCommMonoid N where
  mul_left_cancel := f.isCancelMul.mul_left_cancel
/-
**Submonoid.LocalizationMap.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid.LocalizationMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance {M} [CancelCommMonoid M] (S : Submonoid M) :
    CancelCommMonoid (Localization S) :=
  (Localization.monoidOf S).cancelCommMonoid
/-
**Submonoid.LocalizationMap.subsingleton_of_subsingleton** 是 Mathlib 中的一个定理，位于命名
空间 `Submonoid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : CommMonoid M] {S : Submonoid M} [i
nst_1 : CommMonoid N]   (f : S.LocalizationMap N) [Subsingleton M], Subsingleton
 N
参数：f : S.LocalizationMap N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_surjective`：∀ {M : Type u_1} [inst : CommM
onoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Local
izationMap N) (z : N), ∃ x y, …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
-/
@[to_additive] theorem subsingleton_of_subsingleton (f : LocalizationMap S N) [Subsingleton M] :
    Subsingleton N where
  allEq x y := by
    obtain ⟨mx, sx, rfl⟩ := f.mk'_surjective x
    obtain ⟨my, sy, rfl⟩ := f.mk'_surjective y
    exact congr(f.mk' $(Subsingleton.elim ..) $(Subsingleton.elim ..))
/-
**Submonoid.LocalizationMap.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid.LocalizationMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Subsingleton (Localization S) :=
  (Localization.monoidOf S).subsingleton_of_subsingleton

end Submonoid.LocalizationMap

