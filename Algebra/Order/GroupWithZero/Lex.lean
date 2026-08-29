/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.GroupWithZero.ProdHom
public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Monoid.Lex
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Data.Prod.Lex

/-!
# Order homomorphisms for products of linearly ordered groups with zero

This file defines order homomorphisms for products of linearly ordered groups with zero,
which is identified with the `WithZero` of the lexicographic product of the units of the groups.

The product of linearly ordered groups with zero `WithZero (αˣ ×ₗ βˣ)` is a
linearly ordered group with zero itself with natural inclusions but only one projection.
One has to work with the lexicographic product of the units `αˣ ×ₗ βˣ` since otherwise,
the plain product `αˣ × βˣ` would not be linearly ordered.

## TODO

Create the "LinOrdCommGrpWithZero" category.

-/

@[expose] public section

namespace MonoidWithZeroHom

variable {M₀ N₀ : Type*}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inl_mono` / 引理 `inl_mono`

English:
lemma inl_mono
  statement: [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
  proof: by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

中文:
引理 inl_mono
  结论: [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
  证明: by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, MonoidHom, MonoidHom.inl_mono, WithZero, WithZero.map, WithZero.withZeroUnitsEquiv, _mono, eq_zero_or_unit, inl_mono, withZeroUnitsEquiv
-/
lemma inl_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
    [DecidablePred fun x : M₀ => x = 0] : Monotone (inl M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

/--
lemma `inl_strictMono` / 引理 `inl_strictMono`

English:
lemma inl_strictMono
  statement: [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
  proof: inl_mono.strictMono_of_injective inl_injective

中文:
引理 inl_strictMono
  结论: [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
  证明: inl_mono.strictMono_of_injective inl_injective

Depends on / 依赖: inl_injective, inl_mono, inl_mono.strictMono_of_injective, strictMono_of_injective
-/
lemma inl_strictMono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
    [DecidablePred fun x : M₀ => x = 0] : StrictMono (inl M₀ N₀) :=
  inl_mono.strictMono_of_injective inl_injective

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inr_mono` / 引理 `inr_mono`

English:
lemma inr_mono
  statement: [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
  proof: by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

中文:
引理 inr_mono
  结论: [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
  证明: by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, MonoidHom, MonoidHom.inr_mono, WithZero, WithZero.map, WithZero.withZeroUnitsEquiv, _mono, eq_zero_or_unit, inr_mono, withZeroUnitsEquiv
-/
lemma inr_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ => x = 0] : Monotone (inr M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]

/--
lemma `inr_strictMono` / 引理 `inr_strictMono`

English:
lemma inr_strictMono
  statement: [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
  proof: inr_mono.strictMono_of_injective inr_injective

中文:
引理 inr_strictMono
  结论: [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
  证明: inr_mono.strictMono_of_injective inr_injective

Depends on / 依赖: RingCone, inr_injective, inr_mono, inr_mono.strictMono_of_injective, ofSetLike, strictMono_of_injective
-/
lemma inr_strictMono [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ => x = 0] : StrictMono (inr M₀ N₀) :=
  inr_mono.strictMono_of_injective inr_injective

/--
lemma `fst_mono` / 引理 `fst_mono`

English:
lemma fst_mono
  given: [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
  proof: by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]

中文:
引理 fst_mono
  条件: [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
  证明: by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]

Depends on / 依赖: Prod.le_def, WithZero, WithZero.forall, WithZero.forall.mpr, contextual, le_def
-/
lemma fst_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀] :
    Monotone (fst M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]


/--
lemma `snd_mono` / 引理 `snd_mono`

English:
lemma snd_mono
  given: [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
  proof: by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]

中文:
引理 snd_mono
  条件: [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
  证明: by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]

Depends on / 依赖: Prod.le_def, WithZero, WithZero.forall, WithZero.forall.mpr, le_def
-/
lemma snd_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀] :
    Monotone (snd M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]

end MonoidWithZeroHom

namespace LinearOrderedCommGroupWithZero

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

open MonoidWithZeroHom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
M to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inl : α ->*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inl α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inl_mono

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
N to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inr : β ->*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inr α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inr_mono

set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural projection ordered homomorphism from
`WithZero (Mˣ ×ₗ Nˣ)` to M, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def fst : WithZero (αˣ ×ₗ βˣ) ->*₀o α where
  __ := (fst α β).comp (WithZero.map' (toLexMulEquiv (αˣ × βˣ)).symm.toMonoidHom)
  monotone' := by
    -- this can't rely on `Monotone.comp` since `ofLex` is not monotone
    intro x y
    cases x <;>
    cases y
    · simp
    · simp
    · simp
    · simpa using Prod.Lex.monotone_fst _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: (fst _ _).comp (inl α β) = .id α
  proof: by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

中文:
定理 fst_comp_inl
  结论: (fst _ _).comp (inl α β) = .id α
  证明: by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

Depends on / 依赖: GroupWithZero, GroupWithZero.eq_zero_or_unit, eq_zero_or_unit
-/
theorem fst_comp_inl : (fst _ _).comp (inl α β) = .id α := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

variable {α β}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inl_eq_coe_inlₗ` / 引理 `inl_eq_coe_inlₗ`

English:
lemma inl_eq_coe_inlₗ
  given: {m : α} (hm : m != 0)
  proof: by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

中文:
引理 inl_eq_coe_inlₗ
  条件: {m : α} (hm : m != 0)
  证明: by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

Depends on / 依赖: isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr
-/
lemma inl_eq_coe_inlₗ {m : α} (hm : m != 0) :
    inl α β m = OrderMonoidHom.inlₗ αˣ βˣ (Units.mk0 _ hm) := by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inr_eq_coe_inrₗ` / 引理 `inr_eq_coe_inrₗ`

English:
lemma inr_eq_coe_inrₗ
  given: {n : β} (hn : n != 0)
  proof: by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp

中文:
引理 inr_eq_coe_inrₗ
  条件: {n : β} (hn : n != 0)
  证明: by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp

Depends on / 依赖: isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr
-/
lemma inr_eq_coe_inrₗ {n : β} (hn : n != 0) :
    inr α β n = OrderMonoidHom.inrₗ αˣ βˣ (Units.mk0 _ hn) := by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp

/--
theorem `inl_mul_inr_eq_coe_toLex` / 定理 `inl_mul_inr_eq_coe_toLex`

English:
theorem inl_mul_inr_eq_coe_toLex
  given: {m : α} {n : β} (hm : m != 0) (hn : n != 0)
  proof: by
  rw [inl_eq_coe_inlₗ hm]; rw [inr_eq_coe_inrₗ hn]; rw [← WithZero.coe_mul]; rw [OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

中文:
定理 inl_mul_inr_eq_coe_toLex
  条件: {m : α} {n : β} (hm : m != 0) (hn : n != 0)
  证明: by
  rw [inl_eq_coe_inlₗ hm]; rw [inr_eq_coe_inrₗ hn]; rw [← WithZero.coe_mul]; rw [OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

Depends on / 依赖: OrderMonoidHom, OrderMonoidHom.inl, WithZero, WithZero.coe_mul, coe_mul
-/
theorem inl_mul_inr_eq_coe_toLex {m : α} {n : β} (hm : m != 0) (hn : n != 0) :
    inl α β m * inr α β n = toLex (Units.mk0 _ hm, Units.mk0 _ hn) := by
  rw [inl_eq_coe_inlₗ hm]; rw [inr_eq_coe_inrₗ hn]; rw [← WithZero.coe_mul]; rw [OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

end LinearOrderedCommGroupWithZero
