/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Algebra.CharP.Defs

/-!

# Some normal forms of elliptic curves

This file defines some normal forms of Weierstrass equations of elliptic curves.

## Main definitions and results

The following normal forms are in [silverman2009], section III.1, page 42.

- `WeierstrassCurve.IsCharNeTwoNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₄X + a₆`. It is the normal form of characteristic ≠ 2.

  If 2 is invertible in the ring (for example, if it is a field of characteristic ≠ 2),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`).
  See also `WeierstrassCurve.toCharNeTwoNF` and `WeierstrassCurve.toCharNeTwoNF_spec`.

The following normal forms are in [silverman2009], Appendix A, Proposition 1.1.

- `WeierstrassCurve.IsShortNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₄X + a₆`. It is the normal form of characteristic ≠ 2 or 3, and
  also the normal form of characteristic = 3 and j = 0.

  If 2 and 3 are invertible in the ring (for example, if it is a field of characteristic ≠ 2 or 3),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isShortNF`).
  See also `WeierstrassCurve.toShortNF` and `WeierstrassCurve.toShortNF_spec`.

  If the ring is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toShortNFOfCharThree`
  and `WeierstrassCurve.toShortNFOfCharThree_spec`).

- `WeierstrassCurve.IsCharThreeJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₆`. It is the normal form of characteristic = 3 and j ≠ 0.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharThreeNF`
  and `WeierstrassCurve.toCharThreeNF_spec_of_b₂_ne_zero`).

- `WeierstrassCurve.IsCharThreeNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² = X³ + a₂X² + a₆` or `Y² = X³ + a₄X + a₆`.
  It is the normal form of characteristic = 3.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharThreeNF`).
  See also `WeierstrassCurve.toCharThreeNF` and `WeierstrassCurve.toCharThreeNF_spec`.

- `WeierstrassCurve.IsCharTwoJEqZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2 and j = 0.

  If the ring is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJEqZeroNF`
  and `WeierstrassCurve.toCharTwoJEqZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + XY = X³ + a₂X² + a₆`. It is the normal form of characteristic = 2 and j ≠ 0.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJNeZeroNF`
  and `WeierstrassCurve.toCharTwoJNeZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² + XY = X³ + a₂X² + a₆` or
  `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharTwoNF`).
  See also `WeierstrassCurve.toCharTwoNF` and `WeierstrassCurve.toCharTwoNF_spec`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

@[expose] public section

variable {R : Type*} [CommRing R] {F : Type*} [Field F] (W : WeierstrassCurve R)

namespace WeierstrassCurve

/-! ## Normal forms of characteristic ≠ 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its `a₁, a₃ = 0`.
In other words it is `Y² = X³ + a₂X² + a₄X + a₆`. -/
@[mk_iff]
/--
Definition of `IsCharNeTwoNF` / `IsCharNeTwoNF` 的定义

English:
class IsCharNeTwoNF
  parameters: : Prop where
  axioms and operations (2):
    - a₁ : W.a₁ = 0
    - a₃ : W.a₃ = 0

中文:
类 IsCharNeTwoNF
  参数: : 命题 where
  公理与运算 (2 个):
    - a₁ : W.a₁ = 0
    - a₃ : W.a₃ = 0
-/
class IsCharNeTwoNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsCharNeTwoNF]

@[simp]
/--
theorem `a₁_of_isCharNeTwoNF` / 定理 `a₁_of_isCharNeTwoNF`

English:
theorem a₁_of_isCharNeTwoNF
  statement: W.a₁ = 0
  proof: IsCharNeTwoNF.a₁

@[simp]

中文:
定理 a₁_of_isCharNeTwoNF
  结论: W.a₁ = 0
  证明: IsCharNeTwoNF.a₁

@[simp]

Depends on / 依赖: IsCharNeTwoNF, IsCharNeTwoNF.a
-/
theorem a₁_of_isCharNeTwoNF : W.a₁ = 0 := IsCharNeTwoNF.a₁

@[simp]
/--
theorem `a₃_of_isCharNeTwoNF` / 定理 `a₃_of_isCharNeTwoNF`

English:
theorem a₃_of_isCharNeTwoNF
  statement: W.a₃ = 0
  proof: IsCharNeTwoNF.a₃

@[simp]

中文:
定理 a₃_of_isCharNeTwoNF
  结论: W.a₃ = 0
  证明: IsCharNeTwoNF.a₃

@[simp]

Depends on / 依赖: IsCharNeTwoNF, IsCharNeTwoNF.a
-/
theorem a₃_of_isCharNeTwoNF : W.a₃ = 0 := IsCharNeTwoNF.a₃

@[simp]
/--
theorem `b₂_of_isCharNeTwoNF` / 定理 `b₂_of_isCharNeTwoNF`

English:
theorem b₂_of_isCharNeTwoNF
  statement: W.b₂ = 4 * W.a₂
  proof: by
  rw [b₂]; rw [a₁_of_isCharNeTwoNF]
  ring1

@[simp]

中文:
定理 b₂_of_isCharNeTwoNF
  结论: W.b₂ = 4 * W.a₂
  证明: by
  rw [b₂]; rw [a₁_of_isCharNeTwoNF]
  ring1

@[simp]
-/
theorem b₂_of_isCharNeTwoNF : W.b₂ = 4 * W.a₂ := by
  rw [b₂]; rw [a₁_of_isCharNeTwoNF]
  ring1

@[simp]
/--
theorem `b₄_of_isCharNeTwoNF` / 定理 `b₄_of_isCharNeTwoNF`

English:
theorem b₄_of_isCharNeTwoNF
  statement: W.b₄ = 2 * W.a₄
  proof: by
  rw [b₄]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]

中文:
定理 b₄_of_isCharNeTwoNF
  结论: W.b₄ = 2 * W.a₄
  证明: by
  rw [b₄]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]
-/
theorem b₄_of_isCharNeTwoNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]
/--
theorem `b₆_of_isCharNeTwoNF` / 定理 `b₆_of_isCharNeTwoNF`

English:
theorem b₆_of_isCharNeTwoNF
  statement: W.b₆ = 4 * W.a₆
  proof: by
  rw [b₆]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]

中文:
定理 b₆_of_isCharNeTwoNF
  结论: W.b₆ = 4 * W.a₆
  证明: by
  rw [b₆]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]
-/
theorem b₆_of_isCharNeTwoNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]
/--
theorem `b₈_of_isCharNeTwoNF` / 定理 `b₈_of_isCharNeTwoNF`

English:
theorem b₈_of_isCharNeTwoNF
  statement: W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2
  proof: by
  rw [b₈]; rw [a₁_of_isCharNeTwoNF]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]

中文:
定理 b₈_of_isCharNeTwoNF
  结论: W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2
  证明: by
  rw [b₈]; rw [a₁_of_isCharNeTwoNF]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]
-/
theorem b₈_of_isCharNeTwoNF : W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2 := by
  rw [b₈]; rw [a₁_of_isCharNeTwoNF]; rw [a₃_of_isCharNeTwoNF]
  ring1

@[simp]
/--
theorem `c₄_of_isCharNeTwoNF` / 定理 `c₄_of_isCharNeTwoNF`

English:
theorem c₄_of_isCharNeTwoNF
  statement: W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄
  proof: by
  rw [c₄]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]
  ring1

@[simp]

中文:
定理 c₄_of_isCharNeTwoNF
  结论: W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄
  证明: by
  rw [c₄]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]
  ring1

@[simp]
-/
theorem c₄_of_isCharNeTwoNF : W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄ := by
  rw [c₄]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]
  ring1

@[simp]
/--
theorem `c₆_of_isCharNeTwoNF` / 定理 `c₆_of_isCharNeTwoNF`

English:
theorem c₆_of_isCharNeTwoNF
  statement: W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆
  proof: by
  rw [c₆]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]; rw [b₆_of_isCharNeTwoNF]
  ring1

@[simp]

中文:
定理 c₆_of_isCharNeTwoNF
  结论: W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆
  证明: by
  rw [c₆]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]; rw [b₆_of_isCharNeTwoNF]
  ring1

@[simp]

Depends on / 依赖: choose_spec, choose_spec.choose_spec, exists_bifibrant
-/
theorem c₆_of_isCharNeTwoNF : W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆ := by
  rw [c₆]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]; rw [b₆_of_isCharNeTwoNF]
  ring1

@[simp]
/--
theorem `Δ_of_isCharNeTwoNF` / 定理 `Δ_of_isCharNeTwoNF`

English:
theorem Δ_of_isCharNeTwoNF
  statement: W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
  proof: by
  rw [Δ]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]; rw [b₆_of_isCharNeTwoNF]; rw [b₈_of_isCharNeTwoNF]
  ring1

中文:
定理 Δ_of_isCharNeTwoNF
  结论: W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
  证明: by
  rw [Δ]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]; rw [b₆_of_isCharNeTwoNF]; rw [b₈_of_isCharNeTwoNF]
  ring1

Depends on / 依赖: choose_spec, choose_spec.choose_spec, exists_bifibrant
-/
theorem Δ_of_isCharNeTwoNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
    - 432 * W.a₆ ^ 2 + 288 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Δ]; rw [b₂_of_isCharNeTwoNF]; rw [b₄_of_isCharNeTwoNF]; rw [b₆_of_isCharNeTwoNF]; rw [b₈_of_isCharNeTwoNF]
  ring1

end Quantity

section VariableChange

variable [Invertible (2 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring. -/
@[simps]
/--
Definition of `toCharNeTwoNF` / `toCharNeTwoNF` 的定义

English:
definition toCharNeTwoNF
  signature: : VariableChange R
  body: ⟨1, 0, ⅟2 * -W.a₁, ⅟2 * -W.a₃⟩

中文:
定义 toCharNeTwoNF
  签名: : VariableChange R
  定义体: ⟨1, 0, ⅟2 * -W.a₁, ⅟2 * -W.a₃⟩

Depends on / 依赖: infer_instance, weakEquivalence_iff_of_objectProperty
-/
def toCharNeTwoNF : VariableChange R := ⟨1, 0, ⅟2 * -W.a₁, ⅟2 * -W.a₃⟩

/--
Instance `toCharNeTwoNF_spec` / 实例 `toCharNeTwoNF_spec`

English:
instance toCharNeTwoNF_spec
  signature: : (W.toCharNeTwoNF • W).IsCharNeTwoNF
  body: by
  constructor <;> simp [variableChange_a₁, variableChange_a₃]

中文:
实例 toCharNeTwoNF_spec
  签名: : (W.toCharNeTwoNF • W).IsCharNeTwoNF
  定义体: by
  constructor <;> simp [variableChange_a₁, variableChange_a₃]
-/
instance toCharNeTwoNF_spec : (W.toCharNeTwoNF • W).IsCharNeTwoNF := by
  constructor <;> simp [variableChange_a₁, variableChange_a₃]

/--
theorem `exists_variableChange_isCharNeTwoNF` / 定理 `exists_variableChange_isCharNeTwoNF`

English:
theorem exists_variableChange_isCharNeTwoNF
  statement: exists C : VariableChange R, (C • W).IsCharNeTwoNF
  proof: ⟨_, W.toCharNeTwoNF_spec⟩

中文:
定理 exists_variableChange_isCharNeTwoNF
  结论: 存在 C : VariableChange R, (C • W).IsCharNeTwoNF
  证明: ⟨_, W.toCharNeTwoNF_spec⟩

Depends on / 依赖: W.toCharNeTwoNF_spec, toCharNeTwoNF_spec
-/
theorem exists_variableChange_isCharNeTwoNF : exists C : VariableChange R, (C • W).IsCharNeTwoNF :=
  ⟨_, W.toCharNeTwoNF_spec⟩

end VariableChange

/-! ## Short normal form -/

/-- A `WeierstrassCurve` is in short normal form, if its `a₁, a₂, a₃ = 0`.
In other words it is `Y² = X³ + a₄X + a₆`.

This is the normal form of characteristic ≠ 2 or 3, and
also the normal form of characteristic = 3 and j = 0. -/
@[mk_iff]
/--
Definition of `IsShortNF` / `IsShortNF` 的定义

English:
class IsShortNF
  parameters: : Prop where
  axioms and operations (3):
    - a₁ : W.a₁ = 0
    - a₂ : W.a₂ = 0
    - a₃ : W.a₃ = 0

中文:
类 IsShortNF
  参数: : 命题 where
  公理与运算 (3 个):
    - a₁ : W.a₁ = 0
    - a₂ : W.a₂ = 0
    - a₃ : W.a₃ = 0
-/
class IsShortNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsShortNF]

/--
Instance `isCharNeTwoNF_of_isShortNF` / 实例 `isCharNeTwoNF_of_isShortNF`

English:
instance isCharNeTwoNF_of_isShortNF
  signature: : W.IsCharNeTwoNF
  body: ⟨IsShortNF.a₁, IsShortNF.a₃⟩

中文:
实例 isCharNeTwoNF_of_isShortNF
  签名: : W.IsCharNeTwoNF
  定义体: ⟨IsShortNF.a₁, IsShortNF.a₃⟩

Depends on / 依赖: IsShortNF, IsShortNF.a
-/
instance isCharNeTwoNF_of_isShortNF : W.IsCharNeTwoNF := ⟨IsShortNF.a₁, IsShortNF.a₃⟩

/--
theorem `a₁_of_isShortNF` / 定理 `a₁_of_isShortNF`

English:
theorem a₁_of_isShortNF
  statement: W.a₁ = 0
  proof: IsShortNF.a₁

@[simp]

中文:
定理 a₁_of_isShortNF
  结论: W.a₁ = 0
  证明: IsShortNF.a₁

@[simp]

Depends on / 依赖: CofibrantObject, CofibrantObject.homMk, IsShortNF, IsShortNF.a, bifibrantResolutionMap, bifibrantResolutionMap_fac, iBifibrantResolutionObj, infer_instance, weakEquivalence_iff, weakEquivalence_precomp_iff, weakEquivalences
-/
theorem a₁_of_isShortNF : W.a₁ = 0 := IsShortNF.a₁

@[simp]
/--
theorem `a₂_of_isShortNF` / 定理 `a₂_of_isShortNF`

English:
theorem a₂_of_isShortNF
  statement: W.a₂ = 0
  proof: IsShortNF.a₂

中文:
定理 a₂_of_isShortNF
  结论: W.a₂ = 0
  证明: IsShortNF.a₂

Depends on / 依赖: IsShortNF, IsShortNF.a
-/
theorem a₂_of_isShortNF : W.a₂ = 0 := IsShortNF.a₂

/--
theorem `a₃_of_isShortNF` / 定理 `a₃_of_isShortNF`

English:
theorem a₃_of_isShortNF
  statement: W.a₃ = 0
  proof: IsShortNF.a₃

中文:
定理 a₃_of_isShortNF
  结论: W.a₃ = 0
  证明: IsShortNF.a₃

Depends on / 依赖: IsShortNF, IsShortNF.a
-/
theorem a₃_of_isShortNF : W.a₃ = 0 := IsShortNF.a₃

/--
theorem `b₂_of_isShortNF` / 定理 `b₂_of_isShortNF`

English:
theorem b₂_of_isShortNF
  statement: W.b₂ = 0
  proof: by
  simp

中文:
定理 b₂_of_isShortNF
  结论: W.b₂ = 0
  证明: by
  simp
-/
theorem b₂_of_isShortNF : W.b₂ = 0 := by
  simp

/--
theorem `b₄_of_isShortNF` / 定理 `b₄_of_isShortNF`

English:
theorem b₄_of_isShortNF
  statement: W.b₄ = 2 * W.a₄
  proof: W.b₄_of_isCharNeTwoNF

中文:
定理 b₄_of_isShortNF
  结论: W.b₄ = 2 * W.a₄
  证明: W.b₄_of_isCharNeTwoNF
-/
theorem b₄_of_isShortNF : W.b₄ = 2 * W.a₄ := W.b₄_of_isCharNeTwoNF

/--
theorem `b₆_of_isShortNF` / 定理 `b₆_of_isShortNF`

English:
theorem b₆_of_isShortNF
  statement: W.b₆ = 4 * W.a₆
  proof: W.b₆_of_isCharNeTwoNF

中文:
定理 b₆_of_isShortNF
  结论: W.b₆ = 4 * W.a₆
  证明: W.b₆_of_isCharNeTwoNF
-/
theorem b₆_of_isShortNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF

/--
theorem `b₈_of_isShortNF` / 定理 `b₈_of_isShortNF`

English:
theorem b₈_of_isShortNF
  statement: W.b₈ = -W.a₄ ^ 2
  proof: by
  simp

中文:
定理 b₈_of_isShortNF
  结论: W.b₈ = -W.a₄ ^ 2
  证明: by
  simp
-/
theorem b₈_of_isShortNF : W.b₈ = -W.a₄ ^ 2 := by
  simp

/--
theorem `c₄_of_isShortNF` / 定理 `c₄_of_isShortNF`

English:
theorem c₄_of_isShortNF
  statement: W.c₄ = -48 * W.a₄
  proof: by
  simp

中文:
定理 c₄_of_isShortNF
  结论: W.c₄ = -48 * W.a₄
  证明: by
  simp
-/
theorem c₄_of_isShortNF : W.c₄ = -48 * W.a₄ := by
  simp

/--
theorem `c₆_of_isShortNF` / 定理 `c₆_of_isShortNF`

English:
theorem c₆_of_isShortNF
  statement: W.c₆ = -864 * W.a₆
  proof: by
  simp

中文:
定理 c₆_of_isShortNF
  结论: W.c₆ = -864 * W.a₆
  证明: by
  simp
-/
theorem c₆_of_isShortNF : W.c₆ = -864 * W.a₆ := by
  simp

/--
theorem `Δ_of_isShortNF` / 定理 `Δ_of_isShortNF`

English:
theorem Δ_of_isShortNF
  statement: W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)
  proof: by
  rw [Δ_of_isCharNeTwoNF]; rw [a₂_of_isShortNF]
  ring1

中文:
定理 Δ_of_isShortNF
  结论: W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)
  证明: by
  rw [Δ_of_isCharNeTwoNF]; rw [a₂_of_isShortNF]
  ring1

Depends on / 依赖: HoCat.adjUnit_app, adjUnit_app, infer_instance, toHoCat_obj_surjective, weakEquivalence_iff_of_objectProperty, weakEquivalence_toHoCat_map_iff
-/
theorem Δ_of_isShortNF : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  rw [Δ_of_isCharNeTwoNF]; rw [a₂_of_isShortNF]
  ring1

variable [CharP R 3]

/--
theorem `b₄_of_isShortNF_of_char_three` / 定理 `b₄_of_isShortNF_of_char_three`

English:
theorem b₄_of_isShortNF_of_char_three
  statement: W.b₄ = -W.a₄
  proof: by
  rw [b₄_of_isShortNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

中文:
定理 b₄_of_isShortNF_of_char_three
  结论: W.b₄ = -W.a₄
  证明: by
  rw [b₄_of_isShortNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₄_of_isShortNF_of_char_three : W.b₄ = -W.a₄ := by
  rw [b₄_of_isShortNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

/--
theorem `b₆_of_isShortNF_of_char_three` / 定理 `b₆_of_isShortNF_of_char_three`

English:
theorem b₆_of_isShortNF_of_char_three
  statement: W.b₆ = W.a₆
  proof: by
  rw [b₆_of_isShortNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

中文:
定理 b₆_of_isShortNF_of_char_three
  结论: W.b₆ = W.a₆
  证明: by
  rw [b₆_of_isShortNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₆_of_isShortNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isShortNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

/--
theorem `c₄_of_isShortNF_of_char_three` / 定理 `c₄_of_isShortNF_of_char_three`

English:
theorem c₄_of_isShortNF_of_char_three
  statement: W.c₄ = 0
  proof: by
  rw [c₄_of_isShortNF]
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3

中文:
定理 c₄_of_isShortNF_of_char_three
  结论: W.c₄ = 0
  证明: by
  rw [c₄_of_isShortNF]
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3

Depends on / 依赖: BifibrantObject, BifibrantObject.homMk, BifibrantObject.toHoCat_obj_surjective, BifibrantObject.weakEquivalence_homMk_iff, CharP.cast_eq_zero, HoCat.adjCounit, WeakEquivalence, X.obj, _app, adjCounit, cast_eq_zero, iBifibrantResolutionObj, infer_instance, linear_combination, toHoCat_obj_surjective, weakEquivalence_homMk_iff
-/
theorem c₄_of_isShortNF_of_char_three : W.c₄ = 0 := by
  rw [c₄_of_isShortNF]
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3

/--
theorem `c₆_of_isShortNF_of_char_three` / 定理 `c₆_of_isShortNF_of_char_three`

English:
theorem c₆_of_isShortNF_of_char_three
  statement: W.c₆ = 0
  proof: by
  rw [c₆_of_isShortNF]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3

中文:
定理 c₆_of_isShortNF_of_char_three
  结论: W.c₆ = 0
  证明: by
  rw [c₆_of_isShortNF]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem c₆_of_isShortNF_of_char_three : W.c₆ = 0 := by
  rw [c₆_of_isShortNF]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3

/--
theorem `Δ_of_isShortNF_of_char_three` / 定理 `Δ_of_isShortNF_of_char_three`

English:
theorem Δ_of_isShortNF_of_char_three
  statement: W.Δ = -W.a₄ ^ 3
  proof: by
  rw [Δ_of_isShortNF]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

中文:
定理 Δ_of_isShortNF_of_char_three
  结论: W.Δ = -W.a₄ ^ 3
  证明: by
  rw [Δ_of_isShortNF]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem Δ_of_isShortNF_of_char_three : W.Δ = -W.a₄ ^ 3 := by
  rw [Δ_of_isShortNF]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]

/--
theorem `j_of_isShortNF` / 定理 `j_of_isShortNF`

English:
theorem j_of_isShortNF
  statement: W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)
  proof: by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isShortNF] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isShortNF]; rw [Δ_of_isShortNF]; rw [div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

@[simp]

中文:
定理 j_of_isShortNF
  结论: W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)
  证明: by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isShortNF] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isShortNF]; rw [Δ_of_isShortNF]; rw [div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

@[simp]

Depends on / 依赖: Units.val_inv_eq_inv_val, div_eq_div_iff, div_eq_inv_mul, ne_zero, right_ne_zero_of_mul, val_inv_eq_inv_val
-/
theorem j_of_isShortNF : W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isShortNF] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isShortNF]; rw [Δ_of_isShortNF]; rw [div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

@[simp]
/--
theorem `j_of_isShortNF_of_char_three` / 定理 `j_of_isShortNF_of_char_three`

English:
theorem j_of_isShortNF_of_char_three
  given: [CharP F 3]
  statement: W.j = 0
  proof: by
  rw [j]; rw [c₄_of_isShortNF_of_char_three]; simp

中文:
定理 j_of_isShortNF_of_char_three
  条件: [CharP F 3]
  结论: W.j = 0
  证明: by
  rw [j]; rw [c₄_of_isShortNF_of_char_three]; simp
-/
theorem j_of_isShortNF_of_char_three [CharP F 3] : W.j = 0 := by
  rw [j]; rw [c₄_of_isShortNF_of_char_three]; simp

end Quantity

section VariableChange

variable [Invertible (2 : R)] [Invertible (3 : R)]

/--
Definition of `toShortNF` / `toShortNF` 的定义

English:
definition toShortNF
  signature: : VariableChange R
  body: ⟨1, ⅟3 * -(W.toCharNeTwoNF • W).a₂, 0, 0⟩ * W.toCharNeTwoNF

中文:
定义 toShortNF
  签名: : VariableChange R
  定义体: ⟨1, ⅟3 * -(W.toCharNeTwoNF • W).a₂, 0, 0⟩ * W.toCharNeTwoNF

Depends on / 依赖: W.toCharNeTwoNF, toCharNeTwoNF
-/
def toShortNF : VariableChange R :=
  ⟨1, ⅟3 * -(W.toCharNeTwoNF • W).a₂, 0, 0⟩ * W.toCharNeTwoNF

/--
Instance `toShortNF_spec` / 实例 `toShortNF_spec`

English:
instance toShortNF_spec
  signature: : (W.toShortNF • W).IsShortNF
  body: by
  rw [toShortNF]; rw [mul_smul]
  constructor <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃]

中文:
实例 toShortNF_spec
  签名: : (W.toShortNF • W).IsShortNF
  定义体: by
  rw [toShortNF]; rw [mul_smul]
  constructor <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃]

Depends on / 依赖: mul_smul, toShortNF
-/
instance toShortNF_spec : (W.toShortNF • W).IsShortNF := by
  rw [toShortNF]; rw [mul_smul]
  constructor <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃]

/--
theorem `exists_variableChange_isShortNF` / 定理 `exists_variableChange_isShortNF`

English:
theorem exists_variableChange_isShortNF
  statement: exists C : VariableChange R, (C • W).IsShortNF
  proof: ⟨_, W.toShortNF_spec⟩

中文:
定理 exists_variableChange_isShortNF
  结论: 存在 C : VariableChange R, (C • W).IsShortNF
  证明: ⟨_, W.toShortNF_spec⟩

Depends on / 依赖: W.toShortNF_spec, toShortNF_spec
-/
theorem exists_variableChange_isShortNF : exists C : VariableChange R, (C • W).IsShortNF :=
  ⟨_, W.toShortNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 3 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its
`a₁, a₃, a₄ = 0`. In other words it is `Y² = X³ + a₂X² + a₆`. -/
@[mk_iff]
/--
Definition of `IsCharThreeJNeZeroNF` / `IsCharThreeJNeZeroNF` 的定义

English:
class IsCharThreeJNeZeroNF
  parameters: : Prop where
  axioms and operations (3):
    - a₁ : W.a₁ = 0
    - a₃ : W.a₃ = 0
    - a₄ : W.a₄ = 0

中文:
类 IsCharThreeJNeZeroNF
  参数: : 命题 where
  公理与运算 (3 个):
    - a₁ : W.a₁ = 0
    - a₃ : W.a₃ = 0
    - a₄ : W.a₄ = 0

Depends on / 依赖: HoCat.adj, infer_instance, toHoCat_obj_surjective
-/
class IsCharThreeJNeZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharThreeJNeZeroNF]

/--
Instance `isCharNeTwoNF_of_isCharThreeJNeZeroNF` / 实例 `isCharNeTwoNF_of_isCharThreeJNeZeroNF`

English:
instance isCharNeTwoNF_of_isCharThreeJNeZeroNF
  signature: : W.IsCharNeTwoNF
  body: ⟨IsCharThreeJNeZeroNF.a₁, IsCharThreeJNeZeroNF.a₃⟩

中文:
实例 isCharNeTwoNF_of_isCharThreeJNeZeroNF
  签名: : W.IsCharNeTwoNF
  定义体: ⟨IsCharThreeJNeZeroNF.a₁, IsCharThreeJNeZeroNF.a₃⟩

Depends on / 依赖: IsCharThreeJNeZeroNF, IsCharThreeJNeZeroNF.a
-/
instance isCharNeTwoNF_of_isCharThreeJNeZeroNF : W.IsCharNeTwoNF :=
  ⟨IsCharThreeJNeZeroNF.a₁, IsCharThreeJNeZeroNF.a₃⟩

/--
theorem `a₁_of_isCharThreeJNeZeroNF` / 定理 `a₁_of_isCharThreeJNeZeroNF`

English:
theorem a₁_of_isCharThreeJNeZeroNF
  statement: W.a₁ = 0
  proof: IsCharThreeJNeZeroNF.a₁

中文:
定理 a₁_of_isCharThreeJNeZeroNF
  结论: W.a₁ = 0
  证明: IsCharThreeJNeZeroNF.a₁

Depends on / 依赖: IsCharThreeJNeZeroNF, IsCharThreeJNeZeroNF.a
-/
theorem a₁_of_isCharThreeJNeZeroNF : W.a₁ = 0 := IsCharThreeJNeZeroNF.a₁

/--
theorem `a₃_of_isCharThreeJNeZeroNF` / 定理 `a₃_of_isCharThreeJNeZeroNF`

English:
theorem a₃_of_isCharThreeJNeZeroNF
  statement: W.a₃ = 0
  proof: IsCharThreeJNeZeroNF.a₃

@[simp]

中文:
定理 a₃_of_isCharThreeJNeZeroNF
  结论: W.a₃ = 0
  证明: IsCharThreeJNeZeroNF.a₃

@[simp]

Depends on / 依赖: IsCharThreeJNeZeroNF, IsCharThreeJNeZeroNF.a
-/
theorem a₃_of_isCharThreeJNeZeroNF : W.a₃ = 0 := IsCharThreeJNeZeroNF.a₃

@[simp]
/--
theorem `a₄_of_isCharThreeJNeZeroNF` / 定理 `a₄_of_isCharThreeJNeZeroNF`

English:
theorem a₄_of_isCharThreeJNeZeroNF
  statement: W.a₄ = 0
  proof: IsCharThreeJNeZeroNF.a₄

中文:
定理 a₄_of_isCharThreeJNeZeroNF
  结论: W.a₄ = 0
  证明: IsCharThreeJNeZeroNF.a₄

Depends on / 依赖: IsCharThreeJNeZeroNF, IsCharThreeJNeZeroNF.a
-/
theorem a₄_of_isCharThreeJNeZeroNF : W.a₄ = 0 := IsCharThreeJNeZeroNF.a₄

/--
theorem `b₂_of_isCharThreeJNeZeroNF` / 定理 `b₂_of_isCharThreeJNeZeroNF`

English:
theorem b₂_of_isCharThreeJNeZeroNF
  statement: W.b₂ = 4 * W.a₂
  proof: W.b₂_of_isCharNeTwoNF

中文:
定理 b₂_of_isCharThreeJNeZeroNF
  结论: W.b₂ = 4 * W.a₂
  证明: W.b₂_of_isCharNeTwoNF
-/
theorem b₂_of_isCharThreeJNeZeroNF : W.b₂ = 4 * W.a₂ := W.b₂_of_isCharNeTwoNF

/--
theorem `b₄_of_isCharThreeJNeZeroNF` / 定理 `b₄_of_isCharThreeJNeZeroNF`

English:
theorem b₄_of_isCharThreeJNeZeroNF
  statement: W.b₄ = 0
  proof: by
  simp

中文:
定理 b₄_of_isCharThreeJNeZeroNF
  结论: W.b₄ = 0
  证明: by
  simp

Depends on / 依赖: IsLocalization, functor
-/
theorem b₄_of_isCharThreeJNeZeroNF : W.b₄ = 0 := by
  simp

/--
theorem `b₆_of_isCharThreeJNeZeroNF` / 定理 `b₆_of_isCharThreeJNeZeroNF`

English:
theorem b₆_of_isCharThreeJNeZeroNF
  statement: W.b₆ = 4 * W.a₆
  proof: W.b₆_of_isCharNeTwoNF

中文:
定理 b₆_of_isCharThreeJNeZeroNF
  结论: W.b₆ = 4 * W.a₆
  证明: W.b₆_of_isCharNeTwoNF
-/
theorem b₆_of_isCharThreeJNeZeroNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF

/--
theorem `b₈_of_isCharThreeJNeZeroNF` / 定理 `b₈_of_isCharThreeJNeZeroNF`

English:
theorem b₈_of_isCharThreeJNeZeroNF
  statement: W.b₈ = 4 * W.a₂ * W.a₆
  proof: by
  simp

中文:
定理 b₈_of_isCharThreeJNeZeroNF
  结论: W.b₈ = 4 * W.a₂ * W.a₆
  证明: by
  simp

Depends on / 依赖: IsLocalization, functor, localizerMorphism
-/
theorem b₈_of_isCharThreeJNeZeroNF : W.b₈ = 4 * W.a₂ * W.a₆ := by
  simp

/--
theorem `c₄_of_isCharThreeJNeZeroNF` / 定理 `c₄_of_isCharThreeJNeZeroNF`

English:
theorem c₄_of_isCharThreeJNeZeroNF
  statement: W.c₄ = 16 * W.a₂ ^ 2
  proof: by
  simp

中文:
定理 c₄_of_isCharThreeJNeZeroNF
  结论: W.c₄ = 16 * W.a₂ ^ 2
  证明: by
  simp
-/
theorem c₄_of_isCharThreeJNeZeroNF : W.c₄ = 16 * W.a₂ ^ 2 := by
  simp

/--
theorem `c₆_of_isCharThreeJNeZeroNF` / 定理 `c₆_of_isCharThreeJNeZeroNF`

English:
theorem c₆_of_isCharThreeJNeZeroNF
  statement: W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆
  proof: by
  simp

中文:
定理 c₆_of_isCharThreeJNeZeroNF
  结论: W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆
  证明: by
  simp

Depends on / 依赖: IsLocalization, functor
-/
theorem c₆_of_isCharThreeJNeZeroNF : W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆ := by
  simp

/--
theorem `Δ_of_isCharThreeJNeZeroNF` / 定理 `Δ_of_isCharThreeJNeZeroNF`

English:
theorem Δ_of_isCharThreeJNeZeroNF
  statement: W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2
  proof: by
  simp

中文:
定理 Δ_of_isCharThreeJNeZeroNF
  结论: W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2
  证明: by
  simp
-/
theorem Δ_of_isCharThreeJNeZeroNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2 := by
  simp

variable [CharP R 3]

/--
theorem `b₂_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `b₂_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem b₂_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.b₂ = W.a₂
  proof: by
  rw [b₂_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

中文:
定理 b₂_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.b₂ = W.a₂
  证明: by
  rw [b₂_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₂_of_isCharThreeJNeZeroNF_of_char_three : W.b₂ = W.a₂ := by
  rw [b₂_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

/--
theorem `b₆_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `b₆_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem b₆_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.b₆ = W.a₆
  proof: by
  rw [b₆_of_isCharThreeJNeZeroNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

中文:
定理 b₆_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.b₆ = W.a₆
  证明: by
  rw [b₆_of_isCharThreeJNeZeroNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₆_of_isCharThreeJNeZeroNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isCharThreeJNeZeroNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

/--
theorem `b₈_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `b₈_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem b₈_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.b₈ = W.a₂ * W.a₆
  proof: by
  rw [b₈_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

中文:
定理 b₈_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.b₈ = W.a₂ * W.a₆
  证明: by
  rw [b₈_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₈_of_isCharThreeJNeZeroNF_of_char_three : W.b₈ = W.a₂ * W.a₆ := by
  rw [b₈_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

/--
theorem `c₄_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `c₄_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem c₄_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.c₄ = W.a₂ ^ 2
  proof: by
  rw [c₄_of_isCharThreeJNeZeroNF]
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3

中文:
定理 c₄_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.c₄ = W.a₂ ^ 2
  证明: by
  rw [c₄_of_isCharThreeJNeZeroNF]
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem c₄_of_isCharThreeJNeZeroNF_of_char_three : W.c₄ = W.a₂ ^ 2 := by
  rw [c₄_of_isCharThreeJNeZeroNF]
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3

/--
theorem `c₆_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `c₆_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem c₆_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.c₆ = -W.a₂ ^ 3
  proof: by
  rw [c₆_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3

中文:
定理 c₆_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.c₆ = -W.a₂ ^ 3
  证明: by
  rw [c₆_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem c₆_of_isCharThreeJNeZeroNF_of_char_three : W.c₆ = -W.a₂ ^ 3 := by
  rw [c₆_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3

/--
theorem `Δ_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `Δ_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem Δ_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.Δ = -W.a₂ ^ 3 * W.a₆
  proof: by
  rw [Δ_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

中文:
定理 Δ_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.Δ = -W.a₂ ^ 3 * W.a₆
  证明: by
  rw [Δ_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem Δ_of_isCharThreeJNeZeroNF_of_char_three : W.Δ = -W.a₂ ^ 3 * W.a₆ := by
  rw [Δ_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharThreeJNeZeroNF] [CharP F 3]

@[simp]
/--
theorem `j_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `j_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem j_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.j = -W.a₂ ^ 3 / W.a₆
  proof: by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharThreeJNeZeroNF_of_char_three] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharThreeJNeZeroNF_of_char_three]; rw [Δ_of_isCharThreeJNeZeroNF_of_char_three]; rw [div_eq_div_iff h (right_ne_zero_o

中文:
定理 j_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.j = -W.a₂ ^ 3 / W.a₆
  证明: by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharThreeJNeZeroNF_of_char_three] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharThreeJNeZeroNF_of_char_three]; rw [Δ_of_isCharThreeJNeZeroNF_of_char_three]; rw [div_eq_div_iff h (right_ne_zero_o

Depends on / 依赖: Units.val_inv_eq_inv_val, div_eq_div_iff, div_eq_inv_mul, ne_zero, right_ne_zero_of_mul, val_inv_eq_inv_val
-/
theorem j_of_isCharThreeJNeZeroNF_of_char_three : W.j = -W.a₂ ^ 3 / W.a₆ := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharThreeJNeZeroNF_of_char_three] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharThreeJNeZeroNF_of_char_three]; rw [Δ_of_isCharThreeJNeZeroNF_of_char_three]; rw [div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

/--
theorem `j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three` / 定理 `j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three`

English:
theorem j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three
  statement: W.j != 0
  proof: by
  rw [j_of_isCharThreeJNeZeroNF_of_char_three]; rw [div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rwa [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff] at h

中文:
定理 j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three
  结论: W.j != 0
  证明: by
  rw [j_of_isCharThreeJNeZeroNF_of_char_three]; rw [div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rwa [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff] at h

Depends on / 依赖: div_ne_zero_iff, j_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff, ne_zero
-/
theorem j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three : W.j != 0 := by
  rw [j_of_isCharThreeJNeZeroNF_of_char_three]; rw [div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rwa [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff] at h

end Quantity

/-! ## Normal forms of characteristic = 3 -/

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: IsCharThreeNF
  (no additional axioms)

中文:
类 inductive
  参数: IsCharThreeNF
  (无附加公理)
-/
class inductive IsCharThreeNF : Prop
| of_j_ne_zero [W.IsCharThreeJNeZeroNF] : IsCharThreeNF
| of_j_eq_zero [W.IsShortNF] : IsCharThreeNF

/--
Instance `isCharThreeNF_of_isCharThreeJNeZeroNF` / 实例 `isCharThreeNF_of_isCharThreeJNeZeroNF`

English:
instance isCharThreeNF_of_isCharThreeJNeZeroNF
  signature: [W.IsCharThreeJNeZeroNF]
  body: IsCharThreeNF.of_j_ne_zero

中文:
实例 isCharThreeNF_of_isCharThreeJNeZeroNF
  签名: [W.IsCharThreeJNeZeroNF]
  定义体: IsCharThreeNF.of_j_ne_zero

Depends on / 依赖: IsCharThreeNF, IsCharThreeNF.of_j_ne_zero, of_j_ne_zero
-/
instance isCharThreeNF_of_isCharThreeJNeZeroNF [W.IsCharThreeJNeZeroNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_ne_zero

/--
Instance `isCharThreeNF_of_isShortNF` / 实例 `isCharThreeNF_of_isShortNF`

English:
instance isCharThreeNF_of_isShortNF
  signature: [W.IsShortNF]
  body: IsCharThreeNF.of_j_eq_zero

中文:
实例 isCharThreeNF_of_isShortNF
  签名: [W.IsShortNF]
  定义体: IsCharThreeNF.of_j_eq_zero

Depends on / 依赖: IsCharThreeNF, IsCharThreeNF.of_j_eq_zero, of_j_eq_zero
-/
instance isCharThreeNF_of_isShortNF [W.IsShortNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_eq_zero

/--
Instance `isCharNeTwoNF_of_isCharThreeNF` / 实例 `isCharNeTwoNF_of_isCharThreeNF`

English:
instance isCharNeTwoNF_of_isCharThreeNF
  signature: [W.IsCharThreeNF]
  body: by
  cases ‹W.IsCharThreeNF› <;> infer_instance

中文:
实例 isCharNeTwoNF_of_isCharThreeNF
  签名: [W.IsCharThreeNF]
  定义体: by
  cases ‹W.IsCharThreeNF› <;> infer_instance

Depends on / 依赖: IsCharThreeNF, W.IsCharThreeNF, infer_instance
-/
instance isCharNeTwoNF_of_isCharThreeNF [W.IsCharThreeNF] : W.IsCharNeTwoNF := by
  cases ‹W.IsCharThreeNF› <;> infer_instance

section VariableChange

variable [CharP R 3] [CharP F 3]

/--
Definition of `toShortNFOfCharThree` / `toShortNFOfCharThree` 的定义

English:
definition toShortNFOfCharThree
  signature: : VariableChange R
  body: have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF

中文:
定义 toShortNFOfCharThree
  签名: : VariableChange R
  定义体: have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF

Depends on / 依赖: CharP.cast_eq_zero, Invertible, W.toCharNeTwoNF, cast_eq_zero, linear_combination, toCharNeTwoNF
-/
def toShortNFOfCharThree : VariableChange R :=
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF

/--
lemma `toShortNFOfCharThree_a₂` / 引理 `toShortNFOfCharThree_a₂`

English:
lemma toShortNFOfCharThree_a₂
  statement: (W.toShortNFOfCharThree • W).a₂ = W.b₂
  proof: by
  simp_rw [toShortNFOfCharThree, toCharNeTwoNF, variableChange_a₂, inv_one, Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

中文:
引理 toShortNFOfCharThree_a₂
  结论: (W.toShortNFOfCharThree • W).a₂ = W.b₂
  证明: by
  simp_rw [toShortNFOfCharThree, toCharNeTwoNF, variableChange_a₂, inv_one, Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

Depends on / 依赖: CharP.cast_eq_zero, Units.val_one, cast_eq_zero, inv_one, linear_combination, simp_rw, toCharNeTwoNF, toShortNFOfCharThree, val_one
-/
lemma toShortNFOfCharThree_a₂ : (W.toShortNFOfCharThree • W).a₂ = W.b₂ := by
  simp_rw [toShortNFOfCharThree, toCharNeTwoNF, variableChange_a₂, inv_one, Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

/--
theorem `toShortNFOfCharThree_spec` / 定理 `toShortNFOfCharThree_spec`

English:
theorem toShortNFOfCharThree_spec
  given: (hb₂ : W.b₂ = 0)
  statement: (W.toShortNFOfCharThree • W).IsShortNF
  proof: by
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  let : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toShortNFOfCharThree_a₂, H.a₃⟩

中文:
定理 toShortNFOfCharThree_spec
  条件: (hb₂ : W.b₂ = 0)
  结论: (W.toShortNFOfCharThree • W).IsShortNF
  证明: by
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  let : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toShortNFOfCharThree_a₂, H.a₃⟩

Depends on / 依赖: CharP.cast_eq_zero, Invertible, W.toCharNeTwoNF_spec, W.toShortNFOfCharThree_a, cast_eq_zero, linear_combination, toCharNeTwoNF_spec
-/
theorem toShortNFOfCharThree_spec (hb₂ : W.b₂ = 0) : (W.toShortNFOfCharThree • W).IsShortNF := by
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  let : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toShortNFOfCharThree_a₂, H.a₃⟩

variable (W : WeierstrassCurve F)

/--
Definition of `toCharThreeNF` / `toCharThreeNF` 的定义

English:
definition toCharThreeNF
  signature: : VariableChange F
  body: ⟨1, (W.toShortNFOfCharThree • W).a₄ /
    (W.toShortNFOfCharThree • W).a₂, 0, 0⟩ * W.toShortNFOfCharThree

中文:
定义 toCharThreeNF
  签名: : VariableChange F
  定义体: ⟨1, (W.toShortNFOfCharThree • W).a₄ /
    (W.toShortNFOfCharThree • W).a₂, 0, 0⟩ * W.toShortNFOfCharThree

Depends on / 依赖: W.toShortNFOfCharThree, toShortNFOfCharThree
-/
def toCharThreeNF : VariableChange F :=
  ⟨1, (W.toShortNFOfCharThree • W).a₄ /
    (W.toShortNFOfCharThree • W).a₂, 0, 0⟩ * W.toShortNFOfCharThree

/--
theorem `toCharThreeNF_spec_of_b₂_ne_zero` / 定理 `toCharThreeNF_spec_of_b₂_ne_zero`

English:
theorem toCharThreeNF_spec_of_b₂_ne_zero
  given: (hb₂ : W.b₂ != 0)
  proof: by
  have h : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  let : Invertible (2 : F) := ⟨2, h, h⟩
  rw [toCharThreeNF]; rw [mul_smul]
  set W' := W.toShortNFOfCharThree • W
  have : W'.IsCharNeTwoNF := W.toCharNeTwoNF_spec
  constructor
  · simp [variableChange_a₁]
  · simp [vari

中文:
定理 toCharThreeNF_spec_of_b₂_ne_zero
  条件: (hb₂ : W.b₂ != 0)
  证明: by
  have h : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  let : Invertible (2 : F) := ⟨2, h, h⟩
  rw [toCharThreeNF]; rw [mul_smul]
  set W' := W.toShortNFOfCharThree • W
  have : W'.IsCharNeTwoNF := W.toCharNeTwoNF_spec
  constructor
  · simp [variableChange_a₁]
  · simp [vari

Depends on / 依赖: CharP.cast_eq_zero, Invertible, IsCharNeTwoNF, W.toCharNeTwoNF_spec, W.toShortNFOfCharThree, W.toShortNFOfCharThree_a, cast_eq_zero, linear_combination, mul_eq_zero, mul_smul, toCharNeTwoNF_spec, toCharThreeNF, toShortNFOfCharThree
-/
theorem toCharThreeNF_spec_of_b₂_ne_zero (hb₂ : W.b₂ != 0) :
    (W.toCharThreeNF • W).IsCharThreeJNeZeroNF := by
  have h : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  let : Invertible (2 : F) := ⟨2, h, h⟩
  rw [toCharThreeNF]; rw [mul_smul]
  set W' := W.toShortNFOfCharThree • W
  have : W'.IsCharNeTwoNF := W.toCharNeTwoNF_spec
  constructor
  · simp [variableChange_a₁]
  · simp [variableChange_a₃]
  · have ha₂ : W'.a₂ != 0 := W.toShortNFOfCharThree_a₂ ▸ hb₂
    simp [field, variableChange_a₄, -mul_eq_zero]
    linear_combination (W'.a₄ * W'.a₂ ^ 2 + W'.a₄ ^ 2) * CharP.cast_eq_zero F 3

/--
theorem `toCharThreeNF_spec_of_b₂_eq_zero` / 定理 `toCharThreeNF_spec_of_b₂_eq_zero`

English:
theorem toCharThreeNF_spec_of_b₂_eq_zero
  given: (hb₂ : W.b₂ = 0)
  statement: (W.toCharThreeNF • W).IsShortNF
  proof: by
  rw [toCharThreeNF]; rw [toShortNFOfCharThree_a₂]; rw [hb₂]; rw [div_zero]; rw [← VariableChange.one_def]; rw [one_mul]
  exact W.toShortNFOfCharThree_spec hb₂

中文:
定理 toCharThreeNF_spec_of_b₂_eq_zero
  条件: (hb₂ : W.b₂ = 0)
  结论: (W.toCharThreeNF • W).IsShortNF
  证明: by
  rw [toCharThreeNF]; rw [toShortNFOfCharThree_a₂]; rw [hb₂]; rw [div_zero]; rw [← VariableChange.one_def]; rw [one_mul]
  exact W.toShortNFOfCharThree_spec hb₂

Depends on / 依赖: VariableChange, VariableChange.one_def, W.toShortNFOfCharThree_spec, div_zero, one_def, one_mul, toCharThreeNF, toShortNFOfCharThree_spec
-/
theorem toCharThreeNF_spec_of_b₂_eq_zero (hb₂ : W.b₂ = 0) : (W.toCharThreeNF • W).IsShortNF := by
  rw [toCharThreeNF]; rw [toShortNFOfCharThree_a₂]; rw [hb₂]; rw [div_zero]; rw [← VariableChange.one_def]; rw [one_mul]
  exact W.toShortNFOfCharThree_spec hb₂

/--
Instance `toCharThreeNF_spec` / 实例 `toCharThreeNF_spec`

English:
instance toCharThreeNF_spec
  signature: : (W.toCharThreeNF • W).IsCharThreeNF
  body: by
  by_cases hb₂ : W.b₂ = 0
  · have := W.toCharThreeNF_spec_of_b₂_eq_zero hb₂
    infer_instance
  · have := W.toCharThreeNF_spec_of_b₂_ne_zero hb₂
    infer_instance

中文:
实例 toCharThreeNF_spec
  签名: : (W.toCharThreeNF • W).IsCharThreeNF
  定义体: by
  by_cases hb₂ : W.b₂ = 0
  · have := W.toCharThreeNF_spec_of_b₂_eq_zero hb₂
    infer_instance
  · have := W.toCharThreeNF_spec_of_b₂_ne_zero hb₂
    infer_instance

Depends on / 依赖: W.toCharThreeNF_spec_of_b, infer_instance
-/
instance toCharThreeNF_spec : (W.toCharThreeNF • W).IsCharThreeNF := by
  by_cases hb₂ : W.b₂ = 0
  · have := W.toCharThreeNF_spec_of_b₂_eq_zero hb₂
    infer_instance
  · have := W.toCharThreeNF_spec_of_b₂_ne_zero hb₂
    infer_instance

/--
theorem `exists_variableChange_isCharThreeNF` / 定理 `exists_variableChange_isCharThreeNF`

English:
theorem exists_variableChange_isCharThreeNF
  statement: exists C : VariableChange F, (C • W).IsCharThreeNF
  proof: ⟨_, W.toCharThreeNF_spec⟩

中文:
定理 exists_variableChange_isCharThreeNF
  结论: 存在 C : VariableChange F, (C • W).IsCharThreeNF
  证明: ⟨_, W.toCharThreeNF_spec⟩

Depends on / 依赖: W.toCharThreeNF_spec, toCharThreeNF_spec
-/
theorem exists_variableChange_isCharThreeNF : exists C : VariableChange F, (C • W).IsCharThreeNF :=
  ⟨_, W.toCharThreeNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 2 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j ≠ 0, if its `a₁ = 1` and
`a₃, a₄ = 0`. In other words it is `Y² + XY = X³ + a₂X² + a₆`. -/
@[mk_iff]
/--
Definition of `IsCharTwoJNeZeroNF` / `IsCharTwoJNeZeroNF` 的定义

English:
class IsCharTwoJNeZeroNF
  parameters: : Prop where
  axioms and operations (3):
    - a₁ : W.a₁ = 1
    - a₃ : W.a₃ = 0
    - a₄ : W.a₄ = 0

中文:
类 IsCharTwoJNeZeroNF
  参数: : 命题 where
  公理与运算 (3 个):
    - a₁ : W.a₁ = 1
    - a₃ : W.a₃ = 0
    - a₄ : W.a₄ = 0
-/
class IsCharTwoJNeZeroNF : Prop where
  a₁ : W.a₁ = 1
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharTwoJNeZeroNF]

@[simp]
/--
theorem `a₁_of_isCharTwoJNeZeroNF` / 定理 `a₁_of_isCharTwoJNeZeroNF`

English:
theorem a₁_of_isCharTwoJNeZeroNF
  statement: W.a₁ = 1
  proof: IsCharTwoJNeZeroNF.a₁

@[simp]

中文:
定理 a₁_of_isCharTwoJNeZeroNF
  结论: W.a₁ = 1
  证明: IsCharTwoJNeZeroNF.a₁

@[simp]

Depends on / 依赖: IsCharTwoJNeZeroNF, IsCharTwoJNeZeroNF.a
-/
theorem a₁_of_isCharTwoJNeZeroNF : W.a₁ = 1 := IsCharTwoJNeZeroNF.a₁

@[simp]
/--
theorem `a₃_of_isCharTwoJNeZeroNF` / 定理 `a₃_of_isCharTwoJNeZeroNF`

English:
theorem a₃_of_isCharTwoJNeZeroNF
  statement: W.a₃ = 0
  proof: IsCharTwoJNeZeroNF.a₃

@[simp]

中文:
定理 a₃_of_isCharTwoJNeZeroNF
  结论: W.a₃ = 0
  证明: IsCharTwoJNeZeroNF.a₃

@[simp]

Depends on / 依赖: IsCharTwoJNeZeroNF, IsCharTwoJNeZeroNF.a
-/
theorem a₃_of_isCharTwoJNeZeroNF : W.a₃ = 0 := IsCharTwoJNeZeroNF.a₃

@[simp]
/--
theorem `a₄_of_isCharTwoJNeZeroNF` / 定理 `a₄_of_isCharTwoJNeZeroNF`

English:
theorem a₄_of_isCharTwoJNeZeroNF
  statement: W.a₄ = 0
  proof: IsCharTwoJNeZeroNF.a₄

@[simp]

中文:
定理 a₄_of_isCharTwoJNeZeroNF
  结论: W.a₄ = 0
  证明: IsCharTwoJNeZeroNF.a₄

@[simp]

Depends on / 依赖: IsCharTwoJNeZeroNF, IsCharTwoJNeZeroNF.a
-/
theorem a₄_of_isCharTwoJNeZeroNF : W.a₄ = 0 := IsCharTwoJNeZeroNF.a₄

@[simp]
/--
theorem `b₂_of_isCharTwoJNeZeroNF` / 定理 `b₂_of_isCharTwoJNeZeroNF`

English:
theorem b₂_of_isCharTwoJNeZeroNF
  statement: W.b₂ = 1 + 4 * W.a₂
  proof: by
  rw [b₂]; rw [a₁_of_isCharTwoJNeZeroNF]
  ring1

@[simp]

中文:
定理 b₂_of_isCharTwoJNeZeroNF
  结论: W.b₂ = 1 + 4 * W.a₂
  证明: by
  rw [b₂]; rw [a₁_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
-/
theorem b₂_of_isCharTwoJNeZeroNF : W.b₂ = 1 + 4 * W.a₂ := by
  rw [b₂]; rw [a₁_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/--
theorem `b₄_of_isCharTwoJNeZeroNF` / 定理 `b₄_of_isCharTwoJNeZeroNF`

English:
theorem b₄_of_isCharTwoJNeZeroNF
  statement: W.b₄ = 0
  proof: by
  rw [b₄]; rw [a₃_of_isCharTwoJNeZeroNF]; rw [a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]

中文:
定理 b₄_of_isCharTwoJNeZeroNF
  结论: W.b₄ = 0
  证明: by
  rw [b₄]; rw [a₃_of_isCharTwoJNeZeroNF]; rw [a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
-/
theorem b₄_of_isCharTwoJNeZeroNF : W.b₄ = 0 := by
  rw [b₄]; rw [a₃_of_isCharTwoJNeZeroNF]; rw [a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/--
theorem `b₆_of_isCharTwoJNeZeroNF` / 定理 `b₆_of_isCharTwoJNeZeroNF`

English:
theorem b₆_of_isCharTwoJNeZeroNF
  statement: W.b₆ = 4 * W.a₆
  proof: by
  rw [b₆]; rw [a₃_of_isCharTwoJNeZeroNF]
  ring1

@[simp]

中文:
定理 b₆_of_isCharTwoJNeZeroNF
  结论: W.b₆ = 4 * W.a₆
  证明: by
  rw [b₆]; rw [a₃_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
-/
theorem b₆_of_isCharTwoJNeZeroNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆]; rw [a₃_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/--
theorem `b₈_of_isCharTwoJNeZeroNF` / 定理 `b₈_of_isCharTwoJNeZeroNF`

English:
theorem b₈_of_isCharTwoJNeZeroNF
  statement: W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆
  proof: by
  rw [b₈]; rw [a₁_of_isCharTwoJNeZeroNF]; rw [a₃_of_isCharTwoJNeZeroNF]; rw [a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]

中文:
定理 b₈_of_isCharTwoJNeZeroNF
  结论: W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆
  证明: by
  rw [b₈]; rw [a₁_of_isCharTwoJNeZeroNF]; rw [a₃_of_isCharTwoJNeZeroNF]; rw [a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
-/
theorem b₈_of_isCharTwoJNeZeroNF : W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆ := by
  rw [b₈]; rw [a₁_of_isCharTwoJNeZeroNF]; rw [a₃_of_isCharTwoJNeZeroNF]; rw [a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/--
theorem `c₄_of_isCharTwoJNeZeroNF` / 定理 `c₄_of_isCharTwoJNeZeroNF`

English:
theorem c₄_of_isCharTwoJNeZeroNF
  statement: W.c₄ = W.b₂ ^ 2
  proof: by
  rw [c₄]; rw [b₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]

中文:
定理 c₄_of_isCharTwoJNeZeroNF
  结论: W.c₄ = W.b₂ ^ 2
  证明: by
  rw [c₄]; rw [b₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
-/
theorem c₄_of_isCharTwoJNeZeroNF : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄]; rw [b₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/--
theorem `c₆_of_isCharTwoJNeZeroNF` / 定理 `c₆_of_isCharTwoJNeZeroNF`

English:
theorem c₆_of_isCharTwoJNeZeroNF
  statement: W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆
  proof: by
  rw [c₆]; rw [b₄_of_isCharTwoJNeZeroNF]; rw [b₆_of_isCharTwoJNeZeroNF]
  ring1

中文:
定理 c₆_of_isCharTwoJNeZeroNF
  结论: W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆
  证明: by
  rw [c₆]; rw [b₄_of_isCharTwoJNeZeroNF]; rw [b₆_of_isCharTwoJNeZeroNF]
  ring1
-/
theorem c₆_of_isCharTwoJNeZeroNF : W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆ := by
  rw [c₆]; rw [b₄_of_isCharTwoJNeZeroNF]; rw [b₆_of_isCharTwoJNeZeroNF]
  ring1

variable [CharP R 2]

/--
theorem `b₂_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `b₂_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem b₂_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.b₂ = 1
  proof: by
  rw [b₂_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

中文:
定理 b₂_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.b₂ = 1
  证明: by
  rw [b₂_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₂_of_isCharTwoJNeZeroNF_of_char_two : W.b₂ = 1 := by
  rw [b₂_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

/--
theorem `b₆_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `b₆_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem b₆_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.b₆ = 0
  proof: by
  rw [b₆_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

中文:
定理 b₆_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.b₆ = 0
  证明: by
  rw [b₆_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₆_of_isCharTwoJNeZeroNF_of_char_two : W.b₆ = 0 := by
  rw [b₆_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

/--
theorem `b₈_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `b₈_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem b₈_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.b₈ = W.a₆
  proof: by
  rw [b₈_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2

中文:
定理 b₈_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.b₈ = W.a₆
  证明: by
  rw [b₈_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, cofibration_unop_iff, linear_combination
-/
theorem b₈_of_isCharTwoJNeZeroNF_of_char_two : W.b₈ = W.a₆ := by
  rw [b₈_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2

/--
theorem `c₄_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `c₄_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem c₄_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.c₄ = 1
  proof: by
  rw [c₄_of_isCharTwoJNeZeroNF]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]
  ring1

中文:
定理 c₄_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.c₄ = 1
  证明: by
  rw [c₄_of_isCharTwoJNeZeroNF]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]
  ring1
-/
theorem c₄_of_isCharTwoJNeZeroNF_of_char_two : W.c₄ = 1 := by
  rw [c₄_of_isCharTwoJNeZeroNF]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]
  ring1

/--
theorem `c₆_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `c₆_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem c₆_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.c₆ = 1
  proof: by
  rw [c₆_of_isCharTwoJNeZeroNF]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

@[simp]

中文:
定理 c₆_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.c₆ = 1
  证明: by
  rw [c₆_of_isCharTwoJNeZeroNF]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

@[simp]

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem c₆_of_isCharTwoJNeZeroNF_of_char_two : W.c₆ = 1 := by
  rw [c₆_of_isCharTwoJNeZeroNF]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

@[simp]
/--
theorem `Δ_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `Δ_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem Δ_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.Δ = W.a₆
  proof: by
  rw [Δ]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]; rw [b₄_of_isCharTwoJNeZeroNF]; rw [b₆_of_isCharTwoJNeZeroNF_of_char_two]; rw [b₈_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

中文:
定理 Δ_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.Δ = W.a₆
  证明: by
  rw [Δ]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]; rw [b₄_of_isCharTwoJNeZeroNF]; rw [b₆_of_isCharTwoJNeZeroNF_of_char_two]; rw [b₈_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem Δ_of_isCharTwoJNeZeroNF_of_char_two : W.Δ = W.a₆ := by
  rw [Δ]; rw [b₂_of_isCharTwoJNeZeroNF_of_char_two]; rw [b₄_of_isCharTwoJNeZeroNF]; rw [b₆_of_isCharTwoJNeZeroNF_of_char_two]; rw [b₈_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] [CharP F 2]

@[simp]
/--
theorem `j_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `j_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem j_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.j = 1 / W.a₆
  proof: by
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharTwoJNeZeroNF_of_char_two]; rw [Δ_of_isCharTwoJNeZeroNF_of_char_two]; rw [one_pow]

中文:
定理 j_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.j = 1 / W.a₆
  证明: by
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharTwoJNeZeroNF_of_char_two]; rw [Δ_of_isCharTwoJNeZeroNF_of_char_two]; rw [one_pow]

Depends on / 依赖: Units.val_inv_eq_inv_val, div_eq_inv_mul, one_pow, val_inv_eq_inv_val
-/
theorem j_of_isCharTwoJNeZeroNF_of_char_two : W.j = 1 / W.a₆ := by
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharTwoJNeZeroNF_of_char_two]; rw [Δ_of_isCharTwoJNeZeroNF_of_char_two]; rw [one_pow]

/--
theorem `j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two` / 定理 `j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two`

English:
theorem j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two
  statement: W.j != 0
  proof: by
  rw [j_of_isCharTwoJNeZeroNF_of_char_two]; rw [div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

中文:
定理 j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two
  结论: W.j != 0
  证明: by
  rw [j_of_isCharTwoJNeZeroNF_of_char_two]; rw [div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

Depends on / 依赖: div_ne_zero_iff, j_of_isCharTwoJNeZeroNF_of_char_two, ne_zero, one_ne_zero
-/
theorem j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two : W.j != 0 := by
  rw [j_of_isCharTwoJNeZeroNF_of_char_two]; rw [div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

end Quantity

/-! ## Normal forms of characteristic = 2 and j = 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j = 0, if its `a₁, a₂ = 0`.
In other words it is `Y² + a₃Y = X³ + a₄X + a₆`. -/
@[mk_iff]
/--
Definition of `IsCharTwoJEqZeroNF` / `IsCharTwoJEqZeroNF` 的定义

English:
class IsCharTwoJEqZeroNF
  parameters: : Prop where
  axioms and operations (2):
    - a₁ : W.a₁ = 0
    - a₂ : W.a₂ = 0

中文:
类 IsCharTwoJEqZeroNF
  参数: : 命题 where
  公理与运算 (2 个):
    - a₁ : W.a₁ = 0
    - a₂ : W.a₂ = 0
-/
class IsCharTwoJEqZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0

section Quantity

variable [W.IsCharTwoJEqZeroNF]

@[simp]
/--
theorem `a₁_of_isCharTwoJEqZeroNF` / 定理 `a₁_of_isCharTwoJEqZeroNF`

English:
theorem a₁_of_isCharTwoJEqZeroNF
  statement: W.a₁ = 0
  proof: IsCharTwoJEqZeroNF.a₁

@[simp]

中文:
定理 a₁_of_isCharTwoJEqZeroNF
  结论: W.a₁ = 0
  证明: IsCharTwoJEqZeroNF.a₁

@[simp]

Depends on / 依赖: IsCharTwoJEqZeroNF, IsCharTwoJEqZeroNF.a, fibration_unop_iff
-/
theorem a₁_of_isCharTwoJEqZeroNF : W.a₁ = 0 := IsCharTwoJEqZeroNF.a₁

@[simp]
/--
theorem `a₂_of_isCharTwoJEqZeroNF` / 定理 `a₂_of_isCharTwoJEqZeroNF`

English:
theorem a₂_of_isCharTwoJEqZeroNF
  statement: W.a₂ = 0
  proof: IsCharTwoJEqZeroNF.a₂

@[simp]

中文:
定理 a₂_of_isCharTwoJEqZeroNF
  结论: W.a₂ = 0
  证明: IsCharTwoJEqZeroNF.a₂

@[simp]

Depends on / 依赖: IsCharTwoJEqZeroNF, IsCharTwoJEqZeroNF.a
-/
theorem a₂_of_isCharTwoJEqZeroNF : W.a₂ = 0 := IsCharTwoJEqZeroNF.a₂

@[simp]
/--
theorem `b₂_of_isCharTwoJEqZeroNF` / 定理 `b₂_of_isCharTwoJEqZeroNF`

English:
theorem b₂_of_isCharTwoJEqZeroNF
  statement: W.b₂ = 0
  proof: by
  rw [b₂]; rw [a₁_of_isCharTwoJEqZeroNF]; rw [a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]

中文:
定理 b₂_of_isCharTwoJEqZeroNF
  结论: W.b₂ = 0
  证明: by
  rw [b₂]; rw [a₁_of_isCharTwoJEqZeroNF]; rw [a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
-/
theorem b₂_of_isCharTwoJEqZeroNF : W.b₂ = 0 := by
  rw [b₂]; rw [a₁_of_isCharTwoJEqZeroNF]; rw [a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/--
theorem `b₄_of_isCharTwoJEqZeroNF` / 定理 `b₄_of_isCharTwoJEqZeroNF`

English:
theorem b₄_of_isCharTwoJEqZeroNF
  statement: W.b₄ = 2 * W.a₄
  proof: by
  rw [b₄]; rw [a₁_of_isCharTwoJEqZeroNF]
  ring1

@[simp]

中文:
定理 b₄_of_isCharTwoJEqZeroNF
  结论: W.b₄ = 2 * W.a₄
  证明: by
  rw [b₄]; rw [a₁_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
-/
theorem b₄_of_isCharTwoJEqZeroNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄]; rw [a₁_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/--
theorem `b₈_of_isCharTwoJEqZeroNF` / 定理 `b₈_of_isCharTwoJEqZeroNF`

English:
theorem b₈_of_isCharTwoJEqZeroNF
  statement: W.b₈ = -W.a₄ ^ 2
  proof: by
  rw [b₈]; rw [a₁_of_isCharTwoJEqZeroNF]; rw [a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]

中文:
定理 b₈_of_isCharTwoJEqZeroNF
  结论: W.b₈ = -W.a₄ ^ 2
  证明: by
  rw [b₈]; rw [a₁_of_isCharTwoJEqZeroNF]; rw [a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
-/
theorem b₈_of_isCharTwoJEqZeroNF : W.b₈ = -W.a₄ ^ 2 := by
  rw [b₈]; rw [a₁_of_isCharTwoJEqZeroNF]; rw [a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/--
theorem `c₄_of_isCharTwoJEqZeroNF` / 定理 `c₄_of_isCharTwoJEqZeroNF`

English:
theorem c₄_of_isCharTwoJEqZeroNF
  statement: W.c₄ = -48 * W.a₄
  proof: by
  rw [c₄]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]

中文:
定理 c₄_of_isCharTwoJEqZeroNF
  结论: W.c₄ = -48 * W.a₄
  证明: by
  rw [c₄]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
-/
theorem c₄_of_isCharTwoJEqZeroNF : W.c₄ = -48 * W.a₄ := by
  rw [c₄]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/--
theorem `c₆_of_isCharTwoJEqZeroNF` / 定理 `c₆_of_isCharTwoJEqZeroNF`

English:
theorem c₆_of_isCharTwoJEqZeroNF
  statement: W.c₆ = -216 * W.b₆
  proof: by
  rw [c₆]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]

中文:
定理 c₆_of_isCharTwoJEqZeroNF
  结论: W.c₆ = -216 * W.b₆
  证明: by
  rw [c₆]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
-/
theorem c₆_of_isCharTwoJEqZeroNF : W.c₆ = -216 * W.b₆ := by
  rw [c₆]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/--
theorem `Δ_of_isCharTwoJEqZeroNF` / 定理 `Δ_of_isCharTwoJEqZeroNF`

English:
theorem Δ_of_isCharTwoJEqZeroNF
  statement: W.Δ = -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2)
  proof: by
  rw [Δ]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

中文:
定理 Δ_of_isCharTwoJEqZeroNF
  结论: W.Δ = -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2)
  证明: by
  rw [Δ]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

Depends on / 依赖: weakEquivalences_unop_iff
-/
theorem Δ_of_isCharTwoJEqZeroNF : W.Δ = -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  rw [Δ]; rw [b₂_of_isCharTwoJEqZeroNF]; rw [b₄_of_isCharTwoJEqZeroNF]
  ring1

variable [CharP R 2]

/--
theorem `b₄_of_isCharTwoJEqZeroNF_of_char_two` / 定理 `b₄_of_isCharTwoJEqZeroNF_of_char_two`

English:
theorem b₄_of_isCharTwoJEqZeroNF_of_char_two
  statement: W.b₄ = 0
  proof: by
  rw [b₄_of_isCharTwoJEqZeroNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

中文:
定理 b₄_of_isCharTwoJEqZeroNF_of_char_two
  结论: W.b₄ = 0
  证明: by
  rw [b₄_of_isCharTwoJEqZeroNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₄_of_isCharTwoJEqZeroNF_of_char_two : W.b₄ = 0 := by
  rw [b₄_of_isCharTwoJEqZeroNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

/--
theorem `b₈_of_isCharTwoJEqZeroNF_of_char_two` / 定理 `b₈_of_isCharTwoJEqZeroNF_of_char_two`

English:
theorem b₈_of_isCharTwoJEqZeroNF_of_char_two
  statement: W.b₈ = W.a₄ ^ 2
  proof: by
  rw [b₈_of_isCharTwoJEqZeroNF]
  linear_combination -W.a₄ ^ 2 * CharP.cast_eq_zero R 2

中文:
定理 b₈_of_isCharTwoJEqZeroNF_of_char_two
  结论: W.b₈ = W.a₄ ^ 2
  证明: by
  rw [b₈_of_isCharTwoJEqZeroNF]
  linear_combination -W.a₄ ^ 2 * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem b₈_of_isCharTwoJEqZeroNF_of_char_two : W.b₈ = W.a₄ ^ 2 := by
  rw [b₈_of_isCharTwoJEqZeroNF]
  linear_combination -W.a₄ ^ 2 * CharP.cast_eq_zero R 2

/--
theorem `c₄_of_isCharTwoJEqZeroNF_of_char_two` / 定理 `c₄_of_isCharTwoJEqZeroNF_of_char_two`

English:
theorem c₄_of_isCharTwoJEqZeroNF_of_char_two
  statement: W.c₄ = 0
  proof: by
  rw [c₄_of_isCharTwoJEqZeroNF]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2

中文:
定理 c₄_of_isCharTwoJEqZeroNF_of_char_two
  结论: W.c₄ = 0
  证明: by
  rw [c₄_of_isCharTwoJEqZeroNF]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem c₄_of_isCharTwoJEqZeroNF_of_char_two : W.c₄ = 0 := by
  rw [c₄_of_isCharTwoJEqZeroNF]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2

/--
theorem `c₆_of_isCharTwoJEqZeroNF_of_char_two` / 定理 `c₆_of_isCharTwoJEqZeroNF_of_char_two`

English:
theorem c₆_of_isCharTwoJEqZeroNF_of_char_two
  statement: W.c₆ = 0
  proof: by
  rw [c₆_of_isCharTwoJEqZeroNF]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2

中文:
定理 c₆_of_isCharTwoJEqZeroNF_of_char_two
  结论: W.c₆ = 0
  证明: by
  rw [c₆_of_isCharTwoJEqZeroNF]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem c₆_of_isCharTwoJEqZeroNF_of_char_two : W.c₆ = 0 := by
  rw [c₆_of_isCharTwoJEqZeroNF]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2

/--
theorem `Δ_of_isCharTwoJEqZeroNF_of_char_two` / 定理 `Δ_of_isCharTwoJEqZeroNF_of_char_two`

English:
theorem Δ_of_isCharTwoJEqZeroNF_of_char_two
  statement: W.Δ = W.a₃ ^ 4
  proof: by
  rw [Δ_of_isCharTwoJEqZeroNF]; rw [b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

中文:
定理 Δ_of_isCharTwoJEqZeroNF_of_char_two
  结论: W.Δ = W.a₃ ^ 4
  证明: by
  rw [Δ_of_isCharTwoJEqZeroNF]; rw [b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination
-/
theorem Δ_of_isCharTwoJEqZeroNF_of_char_two : W.Δ = W.a₃ ^ 4 := by
  rw [Δ_of_isCharTwoJEqZeroNF]; rw [b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]

/--
theorem `j_of_isCharTwoJEqZeroNF` / 定理 `j_of_isCharTwoJEqZeroNF`

English:
theorem j_of_isCharTwoJEqZeroNF
  statement: W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2)
  proof: by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharTwoJEqZeroNF] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharTwoJEqZeroNF]; rw [Δ_of_isCharTwoJEqZeroNF]; rw [div_eq_div_iff h (neg_ne_zero.1 h)]
  ring1

@[simp]

中文:
定理 j_of_isCharTwoJEqZeroNF
  结论: W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2)
  证明: by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharTwoJEqZeroNF] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharTwoJEqZeroNF]; rw [Δ_of_isCharTwoJEqZeroNF]; rw [div_eq_div_iff h (neg_ne_zero.1 h)]
  ring1

@[simp]

Depends on / 依赖: Units.val_inv_eq_inv_val, div_eq_div_iff, div_eq_inv_mul, ne_zero, neg_ne_zero, val_inv_eq_inv_val
-/
theorem j_of_isCharTwoJEqZeroNF : W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ']; rw [Δ_of_isCharTwoJEqZeroNF] at h
  rw [j]; rw [Units.val_inv_eq_inv_val]; rw [← div_eq_inv_mul]; rw [coe_Δ']; rw [c₄_of_isCharTwoJEqZeroNF]; rw [Δ_of_isCharTwoJEqZeroNF]; rw [div_eq_div_iff h (neg_ne_zero.1 h)]
  ring1

@[simp]
/--
theorem `j_of_isCharTwoJEqZeroNF_of_char_two` / 定理 `j_of_isCharTwoJEqZeroNF_of_char_two`

English:
theorem j_of_isCharTwoJEqZeroNF_of_char_two
  given: [CharP F 2]
  statement: W.j = 0
  proof: by
  rw [j]; rw [c₄_of_isCharTwoJEqZeroNF_of_char_two]; simp

中文:
定理 j_of_isCharTwoJEqZeroNF_of_char_two
  条件: [CharP F 2]
  结论: W.j = 0
  证明: by
  rw [j]; rw [c₄_of_isCharTwoJEqZeroNF_of_char_two]; simp
-/
theorem j_of_isCharTwoJEqZeroNF_of_char_two [CharP F 2] : W.j = 0 := by
  rw [j]; rw [c₄_of_isCharTwoJEqZeroNF_of_char_two]; simp

end Quantity

/-! ## Normal forms of characteristic = 2 -/

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: IsCharTwoNF
  (no additional axioms)

中文:
类 inductive
  参数: IsCharTwoNF
  (无附加公理)
-/
class inductive IsCharTwoNF : Prop
| of_j_ne_zero [W.IsCharTwoJNeZeroNF] : IsCharTwoNF
| of_j_eq_zero [W.IsCharTwoJEqZeroNF] : IsCharTwoNF

/--
Instance `isCharTwoNF_of_isCharTwoJNeZeroNF` / 实例 `isCharTwoNF_of_isCharTwoJNeZeroNF`

English:
instance isCharTwoNF_of_isCharTwoJNeZeroNF
  signature: [W.IsCharTwoJNeZeroNF]
  body: IsCharTwoNF.of_j_ne_zero

中文:
实例 isCharTwoNF_of_isCharTwoJNeZeroNF
  签名: [W.IsCharTwoJNeZeroNF]
  定义体: IsCharTwoNF.of_j_ne_zero

Depends on / 依赖: IsCharTwoNF, IsCharTwoNF.of_j_ne_zero, of_j_ne_zero
-/
instance isCharTwoNF_of_isCharTwoJNeZeroNF [W.IsCharTwoJNeZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_ne_zero

/--
Instance `isCharTwoNF_of_isCharTwoJEqZeroNF` / 实例 `isCharTwoNF_of_isCharTwoJEqZeroNF`

English:
instance isCharTwoNF_of_isCharTwoJEqZeroNF
  signature: [W.IsCharTwoJEqZeroNF]
  body: IsCharTwoNF.of_j_eq_zero

中文:
实例 isCharTwoNF_of_isCharTwoJEqZeroNF
  签名: [W.IsCharTwoJEqZeroNF]
  定义体: IsCharTwoNF.of_j_eq_zero

Depends on / 依赖: IsCharTwoNF, IsCharTwoNF.of_j_eq_zero, of_j_eq_zero, weakEquivalence_iff_of_objectProperty
-/
instance isCharTwoNF_of_isCharTwoJEqZeroNF [W.IsCharTwoJEqZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_eq_zero

section VariableChange

variable [CharP R 2] [CharP F 2]

/--
Definition of `toCharTwoJEqZeroNF` / `toCharTwoJEqZeroNF` 的定义

English:
definition toCharTwoJEqZeroNF
  signature: : VariableChange R
  body: ⟨1, W.a₂, 0, 0⟩

中文:
定义 toCharTwoJEqZeroNF
  签名: : VariableChange R
  定义体: ⟨1, W.a₂, 0, 0⟩

Depends on / 依赖: infer_instance
-/
def toCharTwoJEqZeroNF : VariableChange R := ⟨1, W.a₂, 0, 0⟩

/--
theorem `toCharTwoJEqZeroNF_spec` / 定理 `toCharTwoJEqZeroNF_spec`

English:
theorem toCharTwoJEqZeroNF_spec
  given: (ha₁ : W.a₁ = 0)
  proof: by
  constructor
  · simp [toCharTwoJEqZeroNF, ha₁, variableChange_a₁]
  · simp_rw [toCharTwoJEqZeroNF, variableChange_a₂, inv_one, Units.val_one]
    linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

中文:
定理 toCharTwoJEqZeroNF_spec
  条件: (ha₁ : W.a₁ = 0)
  证明: by
  constructor
  · simp [toCharTwoJEqZeroNF, ha₁, variableChange_a₁]
  · simp_rw [toCharTwoJEqZeroNF, variableChange_a₂, inv_one, Units.val_one]
    linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

Depends on / 依赖: CharP.cast_eq_zero, Units.val_one, cast_eq_zero, inv_one, linear_combination, simp_rw, toCharTwoJEqZeroNF, val_one
-/
theorem toCharTwoJEqZeroNF_spec (ha₁ : W.a₁ = 0) :
    (W.toCharTwoJEqZeroNF • W).IsCharTwoJEqZeroNF := by
  constructor
  · simp [toCharTwoJEqZeroNF, ha₁, variableChange_a₁]
  · simp_rw [toCharTwoJEqZeroNF, variableChange_a₂, inv_one, Units.val_one]
    linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F)

/--
Definition of `toCharTwoJNeZeroNF` / `toCharTwoJNeZeroNF` 的定义

English:
definition toCharTwoJNeZeroNF
  signature: (W : WeierstrassCurve F) (ha₁ : W.a₁ != 0)
  body: ⟨Units.mk0 _ ha₁, W.a₃ / W.a₁, 0, (W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) / W.a₁ ^ 3⟩

中文:
定义 toCharTwoJNeZeroNF
  签名: (W : WeierstrassCurve F) (ha₁ : W.a₁ != 0)
  定义体: ⟨Units.mk0 _ ha₁, W.a₃ / W.a₁, 0, (W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) / W.a₁ ^ 3⟩

Depends on / 依赖: Units.mk0
-/
def toCharTwoJNeZeroNF (W : WeierstrassCurve F) (ha₁ : W.a₁ != 0) : VariableChange F :=
  ⟨Units.mk0 _ ha₁, W.a₃ / W.a₁, 0, (W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) / W.a₁ ^ 3⟩

/--
theorem `toCharTwoJNeZeroNF_spec` / 定理 `toCharTwoJNeZeroNF_spec`

English:
theorem toCharTwoJNeZeroNF_spec
  given: (ha₁ : W.a₁ != 0)
  proof: by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁, variableChange_a₁]
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₃, -mul_eq_zero]
    linear_combination (W.a₃ * W.a₁ ^ 3 + W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) * CharP.cast_eq_zero F 2
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₄, -mul_eq_

中文:
定理 toCharTwoJNeZeroNF_spec
  条件: (ha₁ : W.a₁ != 0)
  证明: by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁, variableChange_a₁]
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₃, -mul_eq_zero]
    linear_combination (W.a₃ * W.a₁ ^ 3 + W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) * CharP.cast_eq_zero F 2
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₄, -mul_eq_

Depends on / 依赖: CharP.cast_eq_zero, cast_eq_zero, linear_combination, mul_eq_zero, toCharTwoJNeZeroNF
-/
theorem toCharTwoJNeZeroNF_spec (ha₁ : W.a₁ != 0) :
    (W.toCharTwoJNeZeroNF ha₁ • W).IsCharTwoJNeZeroNF := by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁, variableChange_a₁]
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₃, -mul_eq_zero]
    linear_combination (W.a₃ * W.a₁ ^ 3 + W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) * CharP.cast_eq_zero F 2
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₄, -mul_eq_zero]
    linear_combination (W.a₃ ^ 2 + W.a₁ * W.a₃ * W.a₂) * CharP.cast_eq_zero F 2

/--
Definition of `toCharTwoNF` / `toCharTwoNF` 的定义

English:
definition toCharTwoNF
  signature: [DecidableEq F]
  body: if ha₁ : W.a₁ = 0 then W.toCharTwoJEqZeroNF else W.toCharTwoJNeZeroNF ha₁

中文:
定义 toCharTwoNF
  签名: [DecidableEq F]
  定义体: if ha₁ : W.a₁ = 0 then W.toCharTwoJEqZeroNF else W.toCharTwoJNeZeroNF ha₁

Depends on / 依赖: W.toCharTwoJEqZeroNF, W.toCharTwoJNeZeroNF, toCharTwoJEqZeroNF, toCharTwoJNeZeroNF
-/
def toCharTwoNF [DecidableEq F] : VariableChange F :=
  if ha₁ : W.a₁ = 0 then W.toCharTwoJEqZeroNF else W.toCharTwoJNeZeroNF ha₁

/--
Instance `toCharTwoNF_spec` / 实例 `toCharTwoNF_spec`

English:
instance toCharTwoNF_spec
  signature: [DecidableEq F]
  body: by
  by_cases ha₁ : W.a₁ = 0
  · rw [toCharTwoNF, dif_pos ha₁]
    have := W.toCharTwoJEqZeroNF_spec ha₁
    infer_instance
  · rw [toCharTwoNF, dif_neg ha₁]
    have := W.toCharTwoJNeZeroNF_spec ha₁
    infer_instance

中文:
实例 toCharTwoNF_spec
  签名: [DecidableEq F]
  定义体: by
  by_cases ha₁ : W.a₁ = 0
  · rw [toCharTwoNF, dif_pos ha₁]
    have := W.toCharTwoJEqZeroNF_spec ha₁
    infer_instance
  · rw [toCharTwoNF, dif_neg ha₁]
    have := W.toCharTwoJNeZeroNF_spec ha₁
    infer_instance

Depends on / 依赖: W.toCharTwoJEqZeroNF_spec, W.toCharTwoJNeZeroNF_spec, dif_neg, dif_pos, infer_instance, toCharTwoJEqZeroNF_spec, toCharTwoJNeZeroNF_spec, toCharTwoNF
-/
instance toCharTwoNF_spec [DecidableEq F] : (W.toCharTwoNF • W).IsCharTwoNF := by
  by_cases ha₁ : W.a₁ = 0
  · rw [toCharTwoNF, dif_pos ha₁]
    have := W.toCharTwoJEqZeroNF_spec ha₁
    infer_instance
  · rw [toCharTwoNF, dif_neg ha₁]
    have := W.toCharTwoJNeZeroNF_spec ha₁
    infer_instance

/--
theorem `exists_variableChange_isCharTwoNF` / 定理 `exists_variableChange_isCharTwoNF`

English:
theorem exists_variableChange_isCharTwoNF
  statement: exists C : VariableChange F, (C • W).IsCharTwoNF
  proof: by
  classical
  exact ⟨_, W.toCharTwoNF_spec⟩

中文:
定理 exists_variableChange_isCharTwoNF
  结论: 存在 C : VariableChange F, (C • W).IsCharTwoNF
  证明: by
  classical
  exact ⟨_, W.toCharTwoNF_spec⟩

Depends on / 依赖: W.toCharTwoNF_spec, classical, toCharTwoNF_spec
-/
theorem exists_variableChange_isCharTwoNF : exists C : VariableChange F, (C • W).IsCharTwoNF := by
  classical
  exact ⟨_, W.toCharTwoNF_spec⟩

end VariableChange

end WeierstrassCurve
