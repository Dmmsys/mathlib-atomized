/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `Prod`
-/

public section

variable {α R S : Type*}

section
variable [Mul R] [Mul S]

@[to_additive (attr := simp)]
/--
theorem `Prod.isLeftRegular_mk` / 定理 `Prod.isLeftRegular_mk`

English:
theorem Prod.isLeftRegular_mk
  given: {a : R} {b : S}
  proof: have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

@[to_additive (attr := simp)]

中文:
定理 Prod.isLeftRegular_mk
  条件: {a : R} {b : S}
  证明: have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, Prod.map_injective, map_injective
-/
theorem Prod.isLeftRegular_mk {a : R} {b : S} :
    IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

@[to_additive (attr := simp)]
/--
theorem `Prod.isRightRegular_mk` / 定理 `Prod.isRightRegular_mk`

English:
theorem Prod.isRightRegular_mk
  given: {a : R} {b : S}
  proof: have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm .symm Prod.map_injective

@[to_additive (attr := simp)]

中文:
定理 Prod.isRightRegular_mk
  条件: {a : R} {b : S}
  证明: have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm .symm Prod.map_injective

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.symm, Nonempty, Prod.map_injective, map_injective
-/
theorem Prod.isRightRegular_mk {a : R} {b : S} :
    IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b :=
have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm .symm Prod.map_injective

@[to_additive (attr := simp)]
/--
theorem `Prod.isRegular_mk` / 定理 `Prod.isRegular_mk`

English:
theorem Prod.isRegular_mk
  given: {a : R} {b : S}
  statement: IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b
  proof: by
  simp [isRegular_iff, and_and_and_comm]

@[to_additive]

中文:
定理 Prod.isRegular_mk
  条件: {a : R} {b : S}
  结论: IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b
  证明: by
  simp [isRegular_iff, and_and_and_comm]

@[to_additive]

Depends on / 依赖: and_and_and_comm, isRegular_iff
-/
theorem Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b := by
  simp [isRegular_iff, and_and_and_comm]

@[to_additive]
/--
theorem `IsLeftRegular.prodMk` / 定理 `IsLeftRegular.prodMk`

English:
theorem IsLeftRegular.prodMk
  given: {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b)
  proof: Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

@[to_additive]

中文:
定理 IsLeftRegular.prodMk
  条件: {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b)
  证明: Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

@[to_additive]

Depends on / 依赖: Prod.isLeftRegular_mk, isLeftRegular_mk
-/
theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
    IsLeftRegular (a, b) := Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
/--
theorem `IsRightRegular.prodMk` / 定理 `IsRightRegular.prodMk`

English:
theorem IsRightRegular.prodMk
  given: {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b)
  proof: Prod.isRightRegular_mk.2 ⟨ha, hb⟩

@[to_additive]

中文:
定理 IsRightRegular.prodMk
  条件: {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b)
  证明: Prod.isRightRegular_mk.2 ⟨ha, hb⟩

@[to_additive]

Depends on / 依赖: Prod.isRightRegular_mk, isRightRegular_mk
-/
theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
    IsRightRegular (a, b) := Prod.isRightRegular_mk.2 ⟨ha, hb⟩

@[to_additive]
/--
theorem `IsRegular.prodMk` / 定理 `IsRegular.prodMk`

English:
theorem IsRegular.prodMk
  given: {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b)
  proof: Prod.isRegular_mk.2 ⟨ha, hb⟩

中文:
定理 IsRegular.prodMk
  条件: {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b)
  证明: Prod.isRegular_mk.2 ⟨ha, hb⟩

Depends on / 依赖: Prod.isRegular_mk, isRegular_mk
-/
theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
    IsRegular (a, b) := Prod.isRegular_mk.2 ⟨ha, hb⟩

end

@[simp]
/--
theorem `Prod.isSMulRegular_iff` / 定理 `Prod.isSMulRegular_iff`

English:
theorem Prod.isSMulRegular_iff
  given: [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S]
  proof: Prod.map_injective

中文:
定理 Prod.isSMulRegular_iff
  条件: [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S]
  证明: Prod.map_injective

Depends on / 依赖: Prod.map_injective, map_injective
-/
theorem Prod.isSMulRegular_iff [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S] :
    IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r :=
  Prod.map_injective
