/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# More lemmas about irreducible elements
-/

public section

assert_not_exists MonoidWithZero IsOrderedMonoid Multiset

variable {F M N : Type*}

section Monoid
variable [Monoid M] [Monoid N] {f : F} {x y : M}

@[to_additive]
/--
lemma `not_irreducible_pow` / 引理 `not_irreducible_pow`

English:
lemma not_irreducible_pow
  statement: forall {n : Nat}, n != 1 -> ¬ Irreducible (x ^ n)
  proof: h₂ (pow_succ _ _)
    rw [isUnit_pow_iff n.succ_ne_zero]; rw [or_self] at this
    exact h₁ (this.pow _)

@[to_additive]

中文:
引理 not_irreducible_pow
  结论: 对任意 {n : 自然数}, n != 1 -> ¬ 不可约 (x ^ n)
  证明: h₂ (pow_succ _ _)
    rw [isUnit_pow_iff n.succ_ne_zero]; rw [or_self] at this
    exact h₁ (this.pow _)

@[to_additive]

Depends on / 依赖: pow_succ
-/
lemma not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬ Irreducible (x ^ n)
  | 0, _ => by simp
  | n + 2, _ => by
    intro ⟨h₁, h₂⟩
    have := h₂ (pow_succ _ _)
    rw [isUnit_pow_iff n.succ_ne_zero]; rw [or_self] at this
    exact h₁ (this.pow _)

@[to_additive]
/--
lemma `irreducible_units_mul` / 引理 `irreducible_units_mul`

English:
lemma irreducible_units_mul
  given: (u : Mˣ)
  statement: Irreducible (u * y) ↔ Irreducible y
  proof: by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_units_mul]
    apply h
    rw [mul_assoc]; rw [← HAB]
  · rw [← u⁻¹.isUnit_units_mul]
    apply h
    rw [mul_assoc]; rw [← HAB]; rw [Units.inv_mul_cancel_left]

@[to_additive]

中文:
引理 irreducible_units_mul
  条件: (u : Mˣ)
  结论: 不可约 (u * y) ↔ 不可约 y
  证明: by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_units_mul]
    apply h
    rw [mul_assoc]; rw [← HAB]
  · rw [← u⁻¹.isUnit_units_mul]
    apply h
    rw [mul_assoc]; rw [← HAB]; rw [Units.inv_mul_cancel_left]

@[to_additive]

Depends on / 依赖: Units.inv_mul_cancel_left, Units.isUnit_units_mul, and_congr_right_iff, inv_mul_cancel_left, irreducible_iff, isUnit_units_mul, mul_assoc, u.isUnit_units_mul
-/
lemma irreducible_units_mul (u : Mˣ) : Irreducible (u * y) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_units_mul]
    apply h
    rw [mul_assoc]; rw [← HAB]
  · rw [← u⁻¹.isUnit_units_mul]
    apply h
    rw [mul_assoc]; rw [← HAB]; rw [Units.inv_mul_cancel_left]

@[to_additive]
/--
lemma `irreducible_isUnit_mul` / 引理 `irreducible_isUnit_mul`

English:
lemma irreducible_isUnit_mul
  given: (h : IsUnit x)
  statement: Irreducible (x * y) ↔ Irreducible y
  proof: let ⟨x, ha⟩ := h
  ha ▸ irreducible_units_mul x

@[to_additive]

中文:
引理 irreducible_isUnit_mul
  条件: (h : 是单位 x)
  结论: 不可约 (x * y) ↔ 不可约 y
  证明: let ⟨x, ha⟩ := h
  ha ▸ irreducible_units_mul x

@[to_additive]

Depends on / 依赖: irreducible_units_mul
-/
lemma irreducible_isUnit_mul (h : IsUnit x) : Irreducible (x * y) ↔ Irreducible y :=
  let ⟨x, ha⟩ := h
  ha ▸ irreducible_units_mul x

@[to_additive]
/--
lemma `irreducible_mul_units` / 引理 `irreducible_mul_units`

English:
lemma irreducible_mul_units
  given: (u : Mˣ)
  statement: Irreducible (y * u) ↔ Irreducible y
  proof: by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_mul_units B]
    apply h
    rw [← mul_assoc]; rw [← HAB]
  · rw [← u⁻¹.isUnit_mul_units B]
    apply h
    rw [← mul_assoc]; rw [← HAB]; rw [Units.mul_inv_cancel_right]

@[to_additive]

中文:
引理 irreducible_mul_units
  条件: (u : Mˣ)
  结论: 不可约 (y * u) ↔ 不可约 y
  证明: by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_mul_units B]
    apply h
    rw [← mul_assoc]; rw [← HAB]
  · rw [← u⁻¹.isUnit_mul_units B]
    apply h
    rw [← mul_assoc]; rw [← HAB]; rw [Units.mul_inv_cancel_right]

@[to_additive]

Depends on / 依赖: Units.isUnit_mul_units, Units.mul_inv_cancel_right, and_congr_right_iff, irreducible_iff, isUnit_mul_units, mul_assoc, mul_inv_cancel_right, u.isUnit_mul_units
-/
lemma irreducible_mul_units (u : Mˣ) : Irreducible (y * u) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_mul_units B]
    apply h
    rw [← mul_assoc]; rw [← HAB]
  · rw [← u⁻¹.isUnit_mul_units B]
    apply h
    rw [← mul_assoc]; rw [← HAB]; rw [Units.mul_inv_cancel_right]

@[to_additive]
/--
lemma `irreducible_mul_isUnit` / 引理 `irreducible_mul_isUnit`

English:
lemma irreducible_mul_isUnit
  given: (h : IsUnit x)
  statement: Irreducible (y * x) ↔ Irreducible y
  proof: let ⟨x, hx⟩ := h
  hx ▸ irreducible_mul_units x

@[to_additive]

中文:
引理 irreducible_mul_isUnit
  条件: (h : 是单位 x)
  结论: 不可约 (y * x) ↔ 不可约 y
  证明: let ⟨x, hx⟩ := h
  hx ▸ irreducible_mul_units x

@[to_additive]

Depends on / 依赖: irreducible_mul_units
-/
lemma irreducible_mul_isUnit (h : IsUnit x) : Irreducible (y * x) ↔ Irreducible y :=
  let ⟨x, hx⟩ := h
  hx ▸ irreducible_mul_units x

@[to_additive]
/--
lemma `irreducible_mul_iff` / 引理 `irreducible_mul_iff`

English:
lemma irreducible_mul_iff
  proof: by
  constructor
  · refine fun h => Or.imp (fun h' => ⟨?_, h'⟩) (fun h' => ⟨?_, h'⟩) (h.isUnit_or_isUnit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]

中文:
引理 irreducible_mul_iff
  证明: by
  constructor
  · refine fun h => Or.imp (fun h' => ⟨?_, h'⟩) (fun h' => ⟨?_, h'⟩) (h.isUnit_or_isUnit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]

Depends on / 依赖: Or.imp, h.isUnit_or_isUnit, irreducible_isUnit_mul, irreducible_mul_isUnit, isUnit_or_isUnit
-/
lemma irreducible_mul_iff :
    Irreducible (x * y) ↔ Irreducible x ∧ IsUnit y ∨ Irreducible y ∧ IsUnit x := by
  constructor
  · refine fun h => Or.imp (fun h' => ⟨?_, h'⟩) (fun h' => ⟨?_, h'⟩) (h.isUnit_or_isUnit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]

section MulEquivClass
variable [EquivLike F M N] [MulEquivClass F M N] (f : F)

@[to_additive]
/--
lemma `MulEquiv.irreducible_iff` / 引理 `MulEquiv.irreducible_iff`

English:
lemma MulEquiv.irreducible_iff
  statement: Irreducible (f x) ↔ Irreducible x
  proof: by
  simp [_root_.irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, -isUnit_map_iff]

中文:
引理 乘法等价.irreducible_iff
  结论: 不可约 (f x) ↔ 不可约 x
  证明: by
  simp [_root_.irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, -isUnit_map_iff]

Depends on / 依赖: EquivLike, EquivLike.surjective, _root_, _root_.irreducible_iff, irreducible_iff, isUnit_map_iff, map_mul, surjective
-/
lemma MulEquiv.irreducible_iff : Irreducible (f x) ↔ Irreducible x := by
  simp [_root_.irreducible_iff, (EquivLike.surjective f).forall, ← map_mul, -isUnit_map_iff]

/-- Irreducibility is preserved by multiplicative equivalences.

Note that surjective + local hom is not enough. Consider the additive monoids `M = ℕ ⊕ ℕ`, `N = ℕ`,
with x surjective local (additive) hom `f : M →+ N` sending `(m, n)` to `2m + n`.
It is local because the only add unit in `N` is `0`, with preimage `{(0, 0)}` also an add unit.
Then `x = (1, 0)` is irreducible in `M`, but `f x = 2 = 1 + 1` is not irreducible in `N`. -/
@[to_additive /-- Irreducibility is preserved by additive equivalences. -/]
alias ⟨_, Irreducible.map⟩ := MulEquiv.irreducible_iff

end MulEquivClass

/--
lemma `Irreducible.of_map` / 引理 `Irreducible.of_map`

English:
lemma Irreducible.of_map
  statement: [FunLike F M N] [MonoidHomClass F M N] [IsLocalHom f]
  proof: hfx.not_isUnit hu.map f
  isUnit_or_isUnit := by
    rintro p q rfl; exact (hfx.isUnit_or_isUnit <| map_mul f p q).imp (.of_map f _) (.of_map f _)

@[to_additive]

中文:
引理 不可约.of_map
  结论: [函数状 F M N] [幺半群态射类 F M N] [是Local态射 f]
  证明: hfx.not_isUnit hu.map f
  isUnit_or_isUnit := by
    rintro p q rfl; exact (hfx.isUnit_or_isUnit <| map_mul f p q).imp (.of_map f _) (.of_map f _)

@[to_additive]

Depends on / 依赖: hfx.not_isUnit, hu.map, not_isUnit
-/
lemma Irreducible.of_map [FunLike F M N] [MonoidHomClass F M N] [IsLocalHom f]
    (hfx : Irreducible (f x)) : Irreducible x where
not_isUnit hu := hfx.not_isUnit hu.map f
  isUnit_or_isUnit := by
    rintro p q rfl; exact (hfx.isUnit_or_isUnit <| map_mul f p q).imp (.of_map f _) (.of_map f _)

@[to_additive]
/--
lemma `Irreducible.not_isSquare` / 引理 `Irreducible.not_isSquare`

English:
lemma Irreducible.not_isSquare
  given: (ha : Irreducible x)
  statement: ¬IsSquare x
  proof: by
  rw [isSquare_iff_exists_sq]
  rintro ⟨y, rfl⟩
  exact not_irreducible_pow (by decide) ha

@[to_additive]

中文:
引理 不可约.not_isSquare
  条件: (ha : 不可约 x)
  结论: ¬IsSquare x
  证明: by
  rw [isSquare_iff_exists_sq]
  rintro ⟨y, rfl⟩
  exact not_irreducible_pow (by decide) ha

@[to_additive]

Depends on / 依赖: isSquare_iff_exists_sq, not_irreducible_pow
-/
lemma Irreducible.not_isSquare (ha : Irreducible x) : ¬IsSquare x := by
  rw [isSquare_iff_exists_sq]
  rintro ⟨y, rfl⟩
  exact not_irreducible_pow (by decide) ha

@[to_additive]
/--
lemma `IsSquare.not_irreducible` / 引理 `IsSquare.not_irreducible`

English:
lemma IsSquare.not_irreducible
  given: (ha : IsSquare x)
  statement: ¬Irreducible x
  proof: fun h => h.not_isSquare ha

中文:
引理 IsSquare.not_irreducible
  条件: (ha : IsSquare x)
  结论: ¬不可约 x
  证明: fun h => h.not_isSquare ha

Depends on / 依赖: h.not_isSquare, not_isSquare
-/
lemma IsSquare.not_irreducible (ha : IsSquare x) : ¬Irreducible x := fun h => h.not_isSquare ha

end Monoid
