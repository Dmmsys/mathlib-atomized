/-
Copyright (c) 2025 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Maps

/-!
# Grothendieck group

The Grothendieck group of a commutative monoid `M` is the "smallest" commutative group `G`
containing `M`, in the sense that monoid homs `M → H` are in bijection with monoid homs `G → H` for
any commutative group `H`.

Note that "Grothendieck group" also refers to the analogous construction in an abelian category
obtained by formally making the last term of each short exact sequence invertible.

### References

* [*Grothendieck group*, Wikipedia](https://en.wikipedia.org/wiki/Grothendieck_group#Grothendieck_group_of_a_commutative_monoid)
-/

@[expose] public section

open Function Localization

namespace Algebra
variable {M G : Type*} [CommMonoid M] [CommGroup G]

variable (M) in
/-- The Grothendieck group of a monoid `M` is the localization at its top submonoid. -/
@[to_additive
/-- The Grothendieck group of an additive monoid `M` is the localization at its top submonoid. -/]
/--
Definition of `GrothendieckGroup` / `GrothendieckGroup` 的定义

English:
abbreviation GrothendieckGroup
  signature: : Type _
  body: Localization (⊤ : Submonoid M)

中文:
缩写 GrothendieckGroup
  签名: : 类型 _
  定义体: Localization (⊤ : Submonoid M)

Depends on / 依赖: Localization, Submonoid
-/
abbrev GrothendieckGroup : Type _ := Localization (⊤ : Submonoid M)

namespace GrothendieckGroup

/-- The inclusion from a commutative monoid `M` to its Grothendieck group.

Note that this is only injective if `M` is cancellative. -/
@[to_additive
/-- The inclusion from an additive commutative monoid `M` to its Grothendieck group.

Note that this is only injective if `M` is cancellative. -/]
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : M ->* GrothendieckGroup M
  body: (monoidOf ⊤).toMonoidHom

@[to_additive]

中文:
缩写 of
  签名: : M ->* GrothendieckGroup M
  定义体: (monoidOf ⊤).toMonoidHom

@[to_additive]

Depends on / 依赖: monoidOf, toMonoidHom
-/
abbrev of : M ->* GrothendieckGroup M := (monoidOf ⊤).toMonoidHom

@[to_additive]
/--
lemma `of_injective` / 引理 `of_injective`

English:
lemma of_injective
  given: [IsCancelMul M]
  statement: Injective (of (M := M))
  proof: fun m₁ m₂ => by simp [of, ← mk_one_eq_monoidOf_mk, mk_eq_mk_iff']

@[to_additive]

中文:
引理 of_injective
  条件: [是消去乘法 M]
  结论: 单射 (of (M := M))
  证明: fun m₁ m₂ => by simp [of, ← mk_one_eq_monoidOf_mk, mk_eq_mk_iff']

@[to_additive]
-/
lemma of_injective [IsCancelMul M] : Injective (of (M := M)) :=
  fun m₁ m₂ => by simp [of, ← mk_one_eq_monoidOf_mk, mk_eq_mk_iff']

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (GrothendieckGroup M)
  body: rec (fun m s => (.mk s ⟨m, Submonoid.mem_top m⟩ : GrothendieckGroup M))
    fun {m₁ m₂ s₁ s₂} h => by simpa [r_iff_exists, mk_eq_mk_iff, eq_comm, mul_comm] using h

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 取逆 (GrothendieckGroup M)
  定义体: rec (fun m s => (.mk s ⟨m, Submonoid.mem_top m⟩ : GrothendieckGroup M))
    fun {m₁ m₂ s₁ s₂} h => by simpa [r_iff_exists, mk_eq_mk_iff, eq_comm, mul_comm] using h

@[to_additive (attr := simp)]

Depends on / 依赖: GrothendieckGroup, Submonoid, Submonoid.mem_top, mem_top
-/
instance : Inv (GrothendieckGroup M) where
  inv := rec (fun m s => (.mk s ⟨m, Submonoid.mem_top m⟩ : GrothendieckGroup M))
    fun {m₁ m₂ s₁ s₂} h => by simpa [r_iff_exists, mk_eq_mk_iff, eq_comm, mul_comm] using h

@[to_additive (attr := simp)]
/--
lemma `inv_mk` / 引理 `inv_mk`

English:
lemma inv_mk
  given: (m : M) (s : (⊤ : Submonoid M))
  statement: (mk m s)⁻¹ = .mk s ⟨m, Submonoid.mem_top _⟩
  proof: rfl

中文:
引理 inv_mk
  条件: (m : M) (s : (⊤ : 子幺半群 M))
  结论: (mk m s)⁻¹ = .mk s ⟨m, 子幺半群.mem_top _⟩
  证明: rfl
-/
lemma inv_mk (m : M) (s : (⊤ : Submonoid M)) : (mk m s)⁻¹ = .mk s ⟨m, Submonoid.mem_top _⟩ := rfl

/-- The Grothendieck group is a group. -/
@[to_additive /-- The Grothendieck group is a group. -/]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: : CommGroup (GrothendieckGroup M) where
  body: inferInstance
  inv_mul_cancel a := by
    cases a using ind
    rw [inv_mk]; rw [mk_eq_monoidOf_mk']; rw [← Submonoid.LocalizationMap.mk'_mul]
    convert! Submonoid.LocalizationMap.mk'_self' _ _
    rw [mul_comm]; rw [Submonoid.coe_mul]

@[to_additive (attr := simp)]

中文:
实例 instCommGroup
  签名: : 交换群 (GrothendieckGroup M) where
  定义体: inferInstance
  inv_mul_cancel a := by
    cases a using ind
    rw [inv_mk]; rw [mk_eq_monoidOf_mk']; rw [← Submonoid.LocalizationMap.mk'_mul]
    convert! Submonoid.LocalizationMap.mk'_self' _ _
    rw [mul_comm]; rw [Submonoid.coe_mul]

@[to_additive (attr := simp)]
-/
instance instCommGroup : CommGroup (GrothendieckGroup M) where
  __ : CommMonoid (GrothendieckGroup M) := inferInstance
  inv_mul_cancel a := by
    cases a using ind
    rw [inv_mk]; rw [mk_eq_monoidOf_mk']; rw [← Submonoid.LocalizationMap.mk'_mul]
    convert! Submonoid.LocalizationMap.mk'_self' _ _
    rw [mul_comm]; rw [Submonoid.coe_mul]

@[to_additive (attr := simp)]
/--
lemma `mk_div_mk` / 引理 `mk_div_mk`

English:
lemma mk_div_mk
  given: (m₁ m₂ : M) (s₁ s₂ : (⊤ : Submonoid M))
  proof: by
  simp [div_eq_mul_inv, mk_mul]; rfl

中文:
引理 mk_div_mk
  条件: (m₁ m₂ : M) (s₁ s₂ : (⊤ : 子幺半群 M))
  证明: by
  simp [div_eq_mul_inv, mk_mul]; rfl

Depends on / 依赖: div_eq_mul_inv, mk_mul
-/
lemma mk_div_mk (m₁ m₂ : M) (s₁ s₂ : (⊤ : Submonoid M)) :
    mk m₁ s₁ / mk m₂ s₂ = .mk (m₁ * s₂) ⟨s₁ * m₂, Submonoid.mem_top _⟩ := by
  simp [div_eq_mul_inv, mk_mul]; rfl

/-- A monoid homomorphism from a monoid `M` to a group `G` lifts to a group homomorphism from the
Grothendieck group of `M` to `G`. -/
@[to_additive (attr := simps symm_apply)
/-- A monoid homomorphism from a monoid `M` to a group `G` lifts to a group homomorphism from the
Grothendieck group of `M` to `G`. -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (M ->* G) ≃ (GrothendieckGroup M ->* G) where
  body: (monoidOf ⊤).lift (g := f) fun _ => Group.isUnit _
  invFun f := f.comp of
  left_inv f := by ext; simp
  right_inv f := by ext; simp

中文:
定义 lift
  签名: : (M ->* G) ≃ (GrothendieckGroup M ->* G) where
  定义体: (monoidOf ⊤).lift (g := f) fun _ => Group.isUnit _
  invFun f := f.comp of
  left_inv f := by ext; simp
  right_inv f := by ext; simp

Depends on / 依赖: Group.isUnit, isUnit, monoidOf
-/
noncomputable def lift : (M ->* G) ≃ (GrothendieckGroup M ->* G) where
  toFun f := (monoidOf ⊤).lift (g := f) fun _ => Group.isUnit _
  invFun f := f.comp of
  left_inv f := by ext; simp
  right_inv f := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
lemma `lift_apply` / 引理 `lift_apply`

English:
lemma lift_apply
  given: (f : M ->* G) (x : GrothendieckGroup M)
  proof: by
  simp [lift, (monoidOf ⊤).lift_apply, div_eq_mul_inv]; congr

中文:
引理 lift_apply
  条件: (f : M ->* G) (x : GrothendieckGroup M)
  证明: by
  simp [lift, (monoidOf ⊤).lift_apply, div_eq_mul_inv]; congr

Depends on / 依赖: div_eq_mul_inv, lift_apply, monoidOf
-/
lemma lift_apply (f : M ->* G) (x : GrothendieckGroup M) :
    lift f x = f ((monoidOf ⊤).sec x).1 / f ((monoidOf ⊤).sec x).2 := by
  simp [lift, (monoidOf ⊤).lift_apply, div_eq_mul_inv]; congr

end Algebra.GrothendieckGroup
