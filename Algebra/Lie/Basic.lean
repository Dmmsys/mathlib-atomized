/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Bracket
public import Mathlib.Tactic.Abel

/-!
# Lie algebras

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `LieRing`
  * `LieAlgebra`
  * `LieRingModule`
  * `LieModule`
  * `LieHom`
  * `LieEquiv`
  * `LieModuleHom`
  * `LieModuleEquiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
* `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
* `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
* `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
* `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tags

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/

@[expose] public section


universe u v w w₁ w₂

open Function

/--
Definition of `LieRing` / `LieRing` 的定义

English:
class LieRing
  parameters: (L : Type v)
  extends: AddCommGroup L, Bracket L L
  axioms and operations (4):
    - add_lie : forall x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
    - lie_add : forall x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
    - lie_self : forall x : L, ⁅x, x⁆ = 0
    - leibniz_lie : forall x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆

中文:
类 LieRing
  参数: (L : 类型v)
  继承: AddCommGroup L, Bracket L L
  公理与运算 (4 个):
    - add_lie : 对任意 x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
    - lie_add : 对任意 x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
    - lie_self : 对任意 x : L, ⁅x, x⁆ = 0
    - leibniz_lie : 对任意 x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
-/
class LieRing (L : Type v) extends AddCommGroup L, Bracket L L where
  /-- A Lie ring bracket is additive in its first component. -/
  protected add_lie : forall x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  /-- A Lie ring bracket is additive in its second component. -/
  protected lie_add : forall x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  /-- A Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : forall x : L, ⁅x, x⁆ = 0
  /-- A Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : forall x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆

/--
Definition of `LieAlgebra` / `LieAlgebra` 的定义

English:
class LieAlgebra
  parameters: (R : Type u) (L : Type v) [CommRing R] [LieRing L]
  extends: Module R L
  axioms and operations (1):
    - lie_smul : forall (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆

中文:
类 LieAlgebra
  参数: (R : 类型u) (L : 类型v) [CommRing R] [LieRing L]
  继承: Module R L
  公理与运算 (1 个):
    - lie_smul : 对任意 (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆
-/
@[ext] class LieAlgebra (R : Type u) (L : Type v) [CommRing R] [LieRing L] extends Module R L where
  /-- A Lie algebra bracket is compatible with scalar multiplication in its second argument.

  The compatibility in the first argument is not a class property, but follows since every
  Lie algebra has a natural Lie module action on itself, see `LieModule`. -/
  protected lie_smul : forall (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆

/--
Definition of `LieRingModule` / `LieRingModule` 的定义

English:
class LieRingModule
  parameters: (L : Type v) (M : Type w) [LieRing L] [AddCommGroup M]
  extends: Bracket L M
  axioms and operations (3):
    - add_lie : forall (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
    - lie_add : forall (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
    - leibniz_lie : forall (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

中文:
类 LieRingModule
  参数: (L : 类型v) (M : Type w) [LieRing L] [AddCommGroup M]
  继承: Bracket L M
  公理与运算 (3 个):
    - add_lie : 对任意 (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
    - lie_add : 对任意 (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
    - leibniz_lie : 对任意 (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
-/
class LieRingModule (L : Type v) (M : Type w) [LieRing L] [AddCommGroup M] extends Bracket L M where
  /-- A Lie ring module bracket is additive in its first component. -/
  protected add_lie : forall (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  /-- A Lie ring module bracket is additive in its second component. -/
  protected lie_add : forall (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  /-- A Lie ring module bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : forall (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

/--
Definition of `LieModule` / `LieModule` 的定义

English:
class LieModule
  parameters: (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  axioms and operations (2):
    - smul_lie : forall (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
    - lie_smul : forall (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆

中文:
类 LieModule
  参数: (R : 类型u) (L : 类型v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  公理与运算 (2 个):
    - smul_lie : 对任意 (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
    - lie_smul : 对任意 (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆
-/
class LieModule (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] : Prop where
  /-- A Lie module bracket is compatible with scalar multiplication in its first argument. -/
  protected smul_lie : forall (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
  /-- A Lie module bracket is compatible with scalar multiplication in its second argument. -/
  protected lie_smul : forall (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆

/--
Definition of `IsLieTower` / `IsLieTower` 的定义

English:
class IsLieTower
  parameters: (L₁ L₂ M : Type*) [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [Add M]
  axioms and operations (1):
    - leibniz_lie((x : L₁) (y : L₂) (m : M)) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

中文:
类 IsLieTower
  参数: (L₁ L₂ M : 类型) [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [Add M]
  公理与运算 (1 个):
    - leibniz_lie((x : L₁) (y : L₂) (m : M)) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
-/
class IsLieTower (L₁ L₂ M : Type*) [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [Add M] where
  protected leibniz_lie (x : L₁) (y : L₂) (m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

section IsLieTower

variable {L₁ L₂ M : Type*} [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M]

/--
lemma `leibniz_lie` / 引理 `leibniz_lie`

English:
lemma leibniz_lie
  given: [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M)
  proof: IsLieTower.leibniz_lie x y m

中文:
引理 leibniz_lie
  条件: [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M)
  证明: IsLieTower.leibniz_lie x y m

Depends on / 依赖: IsLieTower, IsLieTower.leibniz_lie, leibniz_lie
-/
lemma leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M) :
    ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := IsLieTower.leibniz_lie x y m

/--
lemma `lie_swap_lie` / 引理 `lie_swap_lie`

English:
lemma lie_swap_lie
  statement: [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieTower L₂ L₁ M]
  proof: by
  have h1 := leibniz_lie x y m
  have h2 := leibniz_lie y x m
  convert congr($h1.symm - $h2) <;> simp only [add_sub_cancel_right, sub_add_cancel_right]

中文:
引理 lie_swap_lie
  结论: [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieTower L₂ L₁ M]
  证明: by
  have h1 := leibniz_lie x y m
  have h2 := leibniz_lie y x m
  convert congr($h1.symm - $h2) <;> simp only [add_sub_cancel_right, sub_add_cancel_right]

Depends on / 依赖: add_sub_cancel_right, convert, h1.symm, leibniz_lie, sub_add_cancel_right
-/
lemma lie_swap_lie [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieTower L₂ L₁ M]
    (x : L₁) (y : L₂) (m : M) : ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆ := by
  have h1 := leibniz_lie x y m
  have h2 := leibniz_lie y x m
  convert congr($h1.symm - $h2) <;> simp only [add_sub_cancel_right, sub_add_cancel_right]

end IsLieTower

section BasicProperties

/--
theorem `LieAlgebra.toModule_injective` / 定理 `LieAlgebra.toModule_injective`

English:
theorem LieAlgebra.toModule_injective
  given: (L : Type*) [LieRing L]
  proof: by
  rintro ⟨h₁⟩ ⟨h₂⟩ heq
  congr

中文:
定理 LieAlgebra.toModule_injective
  条件: (L : 类型) [LieRing L]
  证明: by
  rintro ⟨h₁⟩ ⟨h₂⟩ heq
  congr
-/
theorem LieAlgebra.toModule_injective (L : Type*) [LieRing L] :
    Function.Injective (@LieAlgebra.toModule _ _ _ _ : LieAlgebra Rat L -> Module Rat L) := by
  rintro ⟨h₁⟩ ⟨h₂⟩ heq
  congr

instance (L : Type*) [LieRing L] : Subsingleton (LieAlgebra Rat L) :=
.subsingleton LieAlgebra.toModule_injective L

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

@[simp]
/--
theorem `add_lie` / 定理 `add_lie`

English:
theorem add_lie
  statement: ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  proof: LieRingModule.add_lie x y m

@[simp]

中文:
定理 add_lie
  结论: ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  证明: LieRingModule.add_lie x y m

@[simp]

Depends on / 依赖: LieRingModule, LieRingModule.add_lie, add_lie
-/
theorem add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ :=
  LieRingModule.add_lie x y m

@[simp]
/--
theorem `lie_add` / 定理 `lie_add`

English:
theorem lie_add
  statement: ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  proof: LieRingModule.lie_add x m n

@[simp]

中文:
定理 lie_add
  结论: ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  证明: LieRingModule.lie_add x m n

@[simp]

Depends on / 依赖: LieRingModule, LieRingModule.lie_add, lie_add
-/
theorem lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ :=
  LieRingModule.lie_add x m n

@[simp]
/--
theorem `smul_lie` / 定理 `smul_lie`

English:
theorem smul_lie
  statement: ⁅t • x, m⁆ = t • ⁅x, m⁆
  proof: LieModule.smul_lie t x m

@[simp]

中文:
定理 smul_lie
  结论: ⁅t • x, m⁆ = t • ⁅x, m⁆
  证明: LieModule.smul_lie t x m

@[simp]

Depends on / 依赖: LieModule, LieModule.smul_lie, smul_lie
-/
theorem smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ :=
  LieModule.smul_lie t x m

@[simp]
/--
theorem `lie_smul` / 定理 `lie_smul`

English:
theorem lie_smul
  statement: ⁅x, t • m⁆ = t • ⁅x, m⁆
  proof: LieModule.lie_smul t x m

中文:
定理 lie_smul
  结论: ⁅x, t • m⁆ = t • ⁅x, m⁆
  证明: LieModule.lie_smul t x m

Depends on / 依赖: LieModule, LieModule.lie_smul, lie_smul
-/
theorem lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ :=
  LieModule.lie_smul t x m

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLieTower L L M
  body: LieRingModule.leibniz_lie x y m

@[simp]

中文:
实例 :
  签名: IsLieTower L L M
  定义体: LieRingModule.leibniz_lie x y m

@[simp]

Depends on / 依赖: LieRingModule, LieRingModule.leibniz_lie, leibniz_lie
-/
instance : IsLieTower L L M where
  leibniz_lie x y m := LieRingModule.leibniz_lie x y m

@[simp]
/--
theorem `lie_zero` / 定理 `lie_zero`

English:
theorem lie_zero
  statement: ⁅x, 0⁆ = (0 : M)
  proof: (AddMonoidHom.mk' _ (lie_add x)).map_zero

@[simp]

中文:
定理 lie_zero
  结论: ⁅x, 0⁆ = (0 : M)
  证明: (AddMonoidHom.mk' _ (lie_add x)).map_zero

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, lie_add, map_zero
-/
theorem lie_zero : ⁅x, 0⁆ = (0 : M) :=
  (AddMonoidHom.mk' _ (lie_add x)).map_zero

@[simp]
/--
theorem `zero_lie` / 定理 `zero_lie`

English:
theorem zero_lie
  statement: ⁅(0 : L), m⁆ = 0
  proof: (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

@[simp]

中文:
定理 zero_lie
  结论: ⁅(0 : L), m⁆ = 0
  证明: (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, add_lie, map_zero
-/
theorem zero_lie : ⁅(0 : L), m⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

@[simp]
/--
theorem `lie_self` / 定理 `lie_self`

English:
theorem lie_self
  statement: ⁅x, x⁆ = 0
  proof: LieRing.lie_self x

中文:
定理 lie_self
  结论: ⁅x, x⁆ = 0
  证明: LieRing.lie_self x

Depends on / 依赖: LieRing, LieRing.lie_self, lie_self
-/
theorem lie_self : ⁅x, x⁆ = 0 :=
  LieRing.lie_self x

/--
Instance `lieRingSelfModule` / 实例 `lieRingSelfModule`

English:
instance lieRingSelfModule
  signature: : LieRingModule L L
  body: { (inferInstance : LieRing L) with }

@[simp]

中文:
实例 lieRingSelfModule
  签名: : LieRingModule L L
  定义体: { (inferInstance : LieRing L) with }

@[simp]

Depends on / 依赖: LieRing
-/
instance lieRingSelfModule : LieRingModule L L :=
  { (inferInstance : LieRing L) with }

@[simp]
/--
theorem `lie_skew` / 定理 `lie_skew`

English:
theorem lie_skew
  statement: -⁅y, x⁆ = ⁅x, y⁆
  proof: by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h

中文:
定理 lie_skew
  结论: -⁅y, x⁆ = ⁅x, y⁆
  证明: by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h

Depends on / 依赖: lie_add, lie_self, neg_eq_iff_add_eq_zero
-/
theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h

/--
Instance `lieAlgebraSelfModule` / 实例 `lieAlgebraSelfModule`

English:
instance lieAlgebraSelfModule
  signature: : LieModule R L L where
  body: by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
  lie_smul := by apply LieAlgebra.lie_smul

@[simp]

中文:
实例 lieAlgebraSelfModule
  签名: : LieModule R L L where
  定义体: by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
  lie_smul := by apply LieAlgebra.lie_smul

@[simp]

Depends on / 依赖: LieAlgebra, LieAlgebra.lie_smul, lie_skew, lie_smul, smul_neg
-/
instance lieAlgebraSelfModule : LieModule R L L where
  smul_lie t x m := by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
  lie_smul := by apply LieAlgebra.lie_smul

@[simp]
/--
theorem `neg_lie` / 定理 `neg_lie`

English:
theorem neg_lie
  statement: ⁅-x, m⁆ = -⁅x, m⁆
  proof: by
  rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← add_lie]
  simp

@[simp]

中文:
定理 neg_lie
  结论: ⁅-x, m⁆ = -⁅x, m⁆
  证明: by
  rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← add_lie]
  simp

@[simp]

Depends on / 依赖: add_lie, sub_eq_zero, sub_neg_eq_add
-/
theorem neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← add_lie]
  simp

@[simp]
/--
theorem `lie_neg` / 定理 `lie_neg`

English:
theorem lie_neg
  statement: ⁅x, -m⁆ = -⁅x, m⁆
  proof: by
  rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← lie_add]
  simp

@[simp]

中文:
定理 lie_neg
  结论: ⁅x, -m⁆ = -⁅x, m⁆
  证明: by
  rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← lie_add]
  simp

@[simp]

Depends on / 依赖: lie_add, sub_eq_zero, sub_neg_eq_add
-/
theorem lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← lie_add]
  simp

@[simp]
/--
theorem `sub_lie` / 定理 `sub_lie`

English:
theorem sub_lie
  statement: ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
  proof: by simp [sub_eq_add_neg]

@[simp]

中文:
定理 sub_lie
  结论: ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
  证明: by simp [sub_eq_add_neg]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by simp [sub_eq_add_neg]

@[simp]
/--
theorem `lie_sub` / 定理 `lie_sub`

English:
theorem lie_sub
  statement: ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆
  proof: by simp [sub_eq_add_neg]

@[simp]

中文:
定理 lie_sub
  结论: ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆
  证明: by simp [sub_eq_add_neg]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by simp [sub_eq_add_neg]

@[simp]
/--
theorem `nsmul_lie` / 定理 `nsmul_lie`

English:
theorem nsmul_lie
  given: (n : Nat)
  statement: ⁅n • x, m⁆ = n • ⁅x, m⁆
  proof: AddMonoidHom.map_nsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

@[simp]

中文:
定理 nsmul_lie
  条件: (n : 自然数)
  结论: ⁅n • x, m⁆ = n • ⁅x, m⁆
  证明: AddMonoidHom.map_nsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_nsmul, add_lie, map_add, map_nsmul, map_zero, zero_lie
-/
theorem nsmul_lie (n : Nat) : ⁅n • x, m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

@[simp]
/--
theorem `lie_nsmul` / 定理 `lie_nsmul`

English:
theorem lie_nsmul
  given: (n : Nat)
  statement: ⁅x, n • m⁆ = n • ⁅x, m⁆
  proof: AddMonoidHom.map_nsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

中文:
定理 lie_nsmul
  条件: (n : 自然数)
  结论: ⁅x, n • m⁆ = n • ⁅x, m⁆
  证明: AddMonoidHom.map_nsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_nsmul, lie_add, lie_zero, map_add, map_nsmul, map_zero
-/
theorem lie_nsmul (n : Nat) : ⁅x, n • m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

/--
theorem `zsmul_lie` / 定理 `zsmul_lie`

English:
theorem zsmul_lie
  given: (a : Int)
  statement: ⁅a • x, m⁆ = a • ⁅x, m⁆
  proof: AddMonoidHom.map_zsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

中文:
定理 zsmul_lie
  条件: (a : 整数)
  结论: ⁅a • x, m⁆ = a • ⁅x, m⁆
  证明: AddMonoidHom.map_zsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_zsmul, add_lie, map_add, map_zero, map_zsmul, zero_lie
-/
theorem zsmul_lie (a : Int) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

/--
theorem `lie_zsmul` / 定理 `lie_zsmul`

English:
theorem lie_zsmul
  given: (a : Int)
  statement: ⁅x, a • m⁆ = a • ⁅x, m⁆
  proof: AddMonoidHom.map_zsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

@[simp]

中文:
定理 lie_zsmul
  条件: (a : 整数)
  结论: ⁅x, a • m⁆ = a • ⁅x, m⁆
  证明: AddMonoidHom.map_zsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_zsmul, lie_add, lie_zero, map_add, map_zero, map_zsmul
-/
theorem lie_zsmul (a : Int) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

@[simp]
/--
lemma `lie_lie` / 引理 `lie_lie`

English:
lemma lie_lie
  statement: ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
  proof: by rw [leibniz_lie, add_sub_cancel_right]

中文:
引理 lie_lie
  结论: ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
  证明: by rw [leibniz_lie, add_sub_cancel_right]

Depends on / 依赖: add_sub_cancel_right, leibniz_lie
-/
lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by rw [leibniz_lie, add_sub_cancel_right]

/--
theorem `lie_jacobi` / 定理 `lie_jacobi`

English:
theorem lie_jacobi
  statement: ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0
  proof: by
  rw [← neg_neg ⁅x]; rw [y⁆]; rw [lie_neg z]; rw [lie_skew y x]; rw [← lie_skew]; rw [lie_lie]
  abel

中文:
定理 lie_jacobi
  结论: ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0
  证明: by
  rw [← neg_neg ⁅x]; rw [y⁆]; rw [lie_neg z]; rw [lie_skew y x]; rw [← lie_skew]; rw [lie_lie]
  abel

Depends on / 依赖: lie_lie, lie_neg, lie_skew, neg_neg
-/
theorem lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  rw [← neg_neg ⁅x]; rw [y⁆]; rw [lie_neg z]; rw [lie_skew y x]; rw [← lie_skew]; rw [lie_lie]
  abel

variable (L M) in
/--
Definition of `LieRingModule.toEnd` / `LieRingModule.toEnd` 的定义

English:
definition LieRingModule.toEnd
  signature: : L ->+ M ->+ M where
  body: ⟨⟨fun m => ⁅x, m⁆, lie_zero x⟩, LieRingModule.lie_add x⟩
  map_zero' := by ext n; exact zero_lie n
  map_add' y z := by ext n; exact add_lie y z n

中文:
定义 LieRingModule.toEnd
  签名: : L ->+ M ->+ M where
  定义体: ⟨⟨fun m => ⁅x, m⁆, lie_zero x⟩, LieRingModule.lie_add x⟩
  map_zero' := by ext n; exact zero_lie n
  map_add' y z := by ext n; exact add_lie y z n
-/
@[simps] def LieRingModule.toEnd : L ->+ M ->+ M where
  toFun x := ⟨⟨fun m => ⁅x, m⁆, lie_zero x⟩, LieRingModule.lie_add x⟩
  map_zero' := by ext n; exact zero_lie n
  map_add' y z := by ext n; exact add_lie y z n

/--
Instance `LieRing.instLieAlgebra` / 实例 `LieRing.instLieAlgebra`

English:
instance LieRing.instLieAlgebra
  signature: : LieAlgebra Int L where lie_smul n x y
  body: lie_zsmul x y n

中文:
实例 LieRing.instLieAlgebra
  签名: : LieAlgebra 整数 L where lie_smul n x y
  定义体: lie_zsmul x y n

Depends on / 依赖: lie_zsmul
-/
instance LieRing.instLieAlgebra : LieAlgebra Int L where lie_smul n x y := lie_zsmul x y n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule Int L M
  body: zsmul_lie x m n
  lie_smul n x m := lie_zsmul x m n

中文:
实例 :
  签名: LieModule 整数 L M
  定义体: zsmul_lie x m n
  lie_smul n x m := lie_zsmul x m n
-/
instance : LieModule Int L M where
  smul_lie n x m := zsmul_lie x m n
  lie_smul n x m := lie_zsmul x m n

set_option backward.isDefEq.respectTransparency false in
/--
Instance `LinearMap.instLieRingModule` / 实例 `LinearMap.instLieRingModule`

English:
instance LinearMap.instLieRingModule
  signature: : LieRingModule L (M ->ₗ[R] N) where
  body: { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, coe_mk, AddHom.coe_m

中文:
实例 LinearMap.instLieRingModule
  签名: : LieRingModule L (M ->ₗ[R] N) where
  定义体: { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, coe_mk, AddHom.coe_m

Depends on / 依赖: AddHom, AddHom.coe_mk, RingHom, RingHom.id_apply, add_apply, add_lie, coe_mk, id_apply, leibniz_lie, lie_add, lie_lie, lie_smul, lie_sub, map_add, map_smul, map_sub, smul_sub
-/
instance LinearMap.instLieRingModule : LieRingModule L (M ->ₗ[R] N) where
  bracket x f :=
    { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, coe_mk, AddHom.coe_mk, add_apply, map_add]
    abel
  lie_add x f g := by
    ext n
    simp only [coe_mk, AddHom.coe_mk, lie_add, add_apply]
    abel
  leibniz_lie x y f := by
    ext n
    simp only [lie_lie, coe_mk, AddHom.coe_mk, map_sub, add_apply, lie_sub]
    abel

@[simp]
/--
theorem `LieHom.lie_apply` / 定理 `LieHom.lie_apply`

English:
theorem LieHom.lie_apply
  given: (f : M ->ₗ[R] N) (x : L) (m : M)
  statement: ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆
  proof: rfl

中文:
定理 LieHom.lie_apply
  条件: (f : M ->ₗ[R] N) (x : L) (m : M)
  结论: ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆
  证明: rfl
-/
theorem LieHom.lie_apply (f : M ->ₗ[R] N) (x : L) (m : M) : ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `LinearMap.instLieModule` / 实例 `LinearMap.instLieModule`

English:
instance LinearMap.instLieModule
  signature: : LieModule R L (M ->ₗ[R] N) where
  body: by
    ext n
    simp only [smul_sub, smul_lie, smul_apply, LieHom.lie_apply, map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, smul_apply, LieHom.lie_apply, lie_smul]

中文:
实例 LinearMap.instLieModule
  签名: : LieModule R L (M ->ₗ[R] N) where
  定义体: by
    ext n
    simp only [smul_sub, smul_lie, smul_apply, LieHom.lie_apply, map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, smul_apply, LieHom.lie_apply, lie_smul]

Depends on / 依赖: LieHom, LieHom.lie_apply, lie_apply, lie_smul, map_smul, smul_apply, smul_lie, smul_sub
-/
instance LinearMap.instLieModule : LieModule R L (M ->ₗ[R] N) where
  smul_lie t x f := by
    ext n
    simp only [smul_sub, smul_lie, smul_apply, LieHom.lie_apply, map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, smul_apply, LieHom.lie_apply, lie_smul]

/--
Instance `Module.Dual.instLieRingModule` / 实例 `Module.Dual.instLieRingModule`

English:
instance Module.Dual.instLieRingModule
  signature: : LieRingModule L (M ->ₗ[R] R) where
  body: fun x f =>
    { toFun := fun m => - f ⁅x, m⁆
      map_add' := by simp [-neg_add_rev, neg_add]
      map_smul' := by simp }
  add_lie := fun x y m => by ext n; simp [-neg_add_rev, neg_add]
  lie_add := fun x m n => by ext p; simp [-neg_add_rev, neg_add]
  leibniz_lie := fun x m n => by ext p; simp

中文:
实例 Module.Dual.instLieRingModule
  签名: : LieRingModule L (M ->ₗ[R] R) where
  定义体: fun x f =>
    { toFun := fun m => - f ⁅x, m⁆
      map_add' := by simp [-neg_add_rev, neg_add]
      map_smul' := by simp }
  add_lie := fun x y m => by ext n; simp [-neg_add_rev, neg_add]
  lie_add := fun x m n => by ext p; simp [-neg_add_rev, neg_add]
  leibniz_lie := fun x m n => by ext p; simp
-/
instance Module.Dual.instLieRingModule : LieRingModule L (M ->ₗ[R] R) where
  bracket := fun x f =>
    { toFun := fun m => - f ⁅x, m⁆
      map_add' := by simp [-neg_add_rev, neg_add]
      map_smul' := by simp }
  add_lie := fun x y m => by ext n; simp [-neg_add_rev, neg_add]
  lie_add := fun x m n => by ext p; simp [-neg_add_rev, neg_add]
  leibniz_lie := fun x m n => by ext p; simp

/--
lemma `Module.Dual.lie_apply` / 引理 `Module.Dual.lie_apply`

English:
lemma Module.Dual.lie_apply
  given: (f : M ->ₗ[R] R)
  statement: ⁅x, f⁆ m = - f ⁅x, m⁆
  proof: rfl

中文:
引理 Module.Dual.lie_apply
  条件: (f : M ->ₗ[R] R)
  结论: ⁅x, f⁆ m = - f ⁅x, m⁆
  证明: rfl
-/
@[simp] lemma Module.Dual.lie_apply (f : M ->ₗ[R] R) : ⁅x, f⁆ m = - f ⁅x, m⁆ := rfl

/--
Instance `Module.Dual.instLieModule` / 实例 `Module.Dual.instLieModule`

English:
instance Module.Dual.instLieModule
  signature: : LieModule R L (M ->ₗ[R] R) where
  body: fun t x m => by ext n; simp
  lie_smul := fun t x m => by ext n; simp

中文:
实例 Module.Dual.instLieModule
  签名: : LieModule R L (M ->ₗ[R] R) where
  定义体: fun t x m => by ext n; simp
  lie_smul := fun t x m => by ext n; simp
-/
instance Module.Dual.instLieModule : LieModule R L (M ->ₗ[R] R) where
  smul_lie := fun t x m => by ext n; simp
  lie_smul := fun t x m => by ext n; simp

variable (L) in
/-- It is sometimes useful to regard a `LieRing` as a `NonUnitalNonAssocRing`. -/
@[instance_reducible]
/--
Definition of `LieRing.toNonUnitalNonAssocRing` / `LieRing.toNonUnitalNonAssocRing` 的定义

English:
definition LieRing.toNonUnitalNonAssocRing
  signature: : NonUnitalNonAssocRing L
  body: { mul := Bracket.bracket
    left_distrib := lie_add
    right_distrib := add_lie
    zero_mul := zero_lie
    mul_zero := lie_zero }

中文:
定义 LieRing.toNonUnitalNonAssocRing
  签名: : NonUnitalNonAssocRing L
  定义体: { mul := Bracket.bracket
    left_distrib := lie_add
    right_distrib := add_lie
    zero_mul := zero_lie
    mul_zero := lie_zero }

Depends on / 依赖: Bracket, Bracket.bracket, add_lie, bracket, left_distrib, lie_add, lie_zero, mul_zero, right_distrib, zero_lie, zero_mul
-/
def LieRing.toNonUnitalNonAssocRing : NonUnitalNonAssocRing L :=
  { mul := Bracket.bracket
    left_distrib := lie_add
    right_distrib := add_lie
    zero_mul := zero_lie
    mul_zero := lie_zero }

variable {ι κ : Type*}

/--
theorem `sum_lie` / 定理 `sum_lie`

English:
theorem sum_lie
  given: (s : Finset ι) (f : ι -> L) (m : M)
  statement: ⁅∑ i in s, f i, m⁆ = ∑ i in s, ⁅f i, m⁆
  proof: map_sum ((LieRingModule.toEnd L M).flip m) f s

中文:
定理 sum_lie
  条件: (s : Finset ι) (f : ι -> L) (m : M)
  结论: ⁅∑ i in s, f i, m⁆ = ∑ i in s, ⁅f i, m⁆
  证明: map_sum ((LieRingModule.toEnd L M).flip m) f s

Depends on / 依赖: LieRingModule, LieRingModule.toEnd, map_sum
-/
theorem sum_lie (s : Finset ι) (f : ι -> L) (m : M) : ⁅∑ i in s, f i, m⁆ = ∑ i in s, ⁅f i, m⁆ :=
  map_sum ((LieRingModule.toEnd L M).flip m) f s

/--
theorem `lie_sum` / 定理 `lie_sum`

English:
theorem lie_sum
  given: (s : Finset ι) (f : ι -> M) (a : L)
  statement: ⁅a, ∑ i in s, f i⁆ = ∑ i in s, ⁅a, f i⁆
  proof: map_sum (LieRingModule.toEnd L M a) f s

中文:
定理 lie_sum
  条件: (s : Finset ι) (f : ι -> M) (a : L)
  结论: ⁅a, ∑ i in s, f i⁆ = ∑ i in s, ⁅a, f i⁆
  证明: map_sum (LieRingModule.toEnd L M a) f s

Depends on / 依赖: LieRingModule, LieRingModule.toEnd, map_sum
-/
theorem lie_sum (s : Finset ι) (f : ι -> M) (a : L) : ⁅a, ∑ i in s, f i⁆ = ∑ i in s, ⁅a, f i⁆ :=
  map_sum (LieRingModule.toEnd L M a) f s

/--
theorem `sum_lie_sum` / 定理 `sum_lie_sum`

English:
theorem sum_lie_sum
  given: {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι -> L) (g : κ -> M)
  proof: by
  simp_rw [sum_lie, lie_sum]

中文:
定理 sum_lie_sum
  条件: {κ : 类型} (s : Finset ι) (t : Finset κ) (f : ι -> L) (g : κ -> M)
  证明: by
  simp_rw [sum_lie, lie_sum]

Depends on / 依赖: lie_sum, simp_rw, sum_lie
-/
theorem sum_lie_sum {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι -> L) (g : κ -> M) :
    ⁅(∑ i in s, f i), ∑ j in t, g j⁆ = ∑ i in s, ∑ j in t, ⁅f i, g j⁆ := by
  simp_rw [sum_lie, lie_sum]

end BasicProperties

/--
Definition of `LieHom` / `LieHom` 的定义

English:
structure LieHom
  parameters: (R L L' : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  extends: L ->ₗ[R] L'
  axioms and operations (1):
    - map_lie' : forall {x y : L}, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆

中文:
结构 LieHom
  参数: (R L L' : 类型) [CommRing R] [LieRing L] [LieAlgebra R L]
  继承: L ->ₗ[R] L'
  公理与运算 (1 个):
    - map_lie' : 对任意 {x y : L}, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆
-/
structure LieHom (R L L' : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L ->ₗ[R] L' where
  /-- A morphism of Lie algebras is compatible with brackets. -/
  map_lie' : forall {x y : L}, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆

@[inherit_doc]
notation:25 L " ->ₗ⁅" R:25 "⁆ " L':0 => LieHom R L L'

namespace LieHom

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variable [CommRing R]
variable [LieRing L₁] [LieAlgebra R L₁]
variable [LieRing L₂] [LieAlgebra R L₂]
variable [LieRing L₃] [LieAlgebra R L₃]

attribute [coe] LieHom.toLinearMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (L₁ ->ₗ⁅R⁆ L₂) (L₁ ->ₗ[R] L₂)
  body: ⟨LieHom.toLinearMap⟩

中文:
实例 :
  签名: Coe (L₁ ->ₗ⁅R⁆ L₂) (L₁ ->ₗ[R] L₂)
  定义体: ⟨LieHom.toLinearMap⟩

Depends on / 依赖: LieHom, LieHom.toLinearMap, toLinearMap
-/
instance : Coe (L₁ ->ₗ⁅R⁆ L₂) (L₁ ->ₗ[R] L₂) :=
  ⟨LieHom.toLinearMap⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (L₁ ->ₗ⁅R⁆ L₂) L₁ L₂
  body: f.toFun
  coe_injective x y h := by
    cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieHom (toFun -> apply)

@[simp, norm_cast]

中文:
实例 :
  签名: FunLike (L₁ ->ₗ⁅R⁆ L₂) L₁ L₂
  定义体: f.toFun
  coe_injective x y h := by
    cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieHom (toFun -> apply)

@[simp, norm_cast]

Depends on / 依赖: f.toFun
-/
instance : FunLike (L₁ ->ₗ⁅R⁆ L₂) L₁ L₂ where
  coe f := f.toFun
  coe_injective x y h := by
    cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieHom (toFun -> apply)

@[simp, norm_cast]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : L₁ ->ₗ⁅R⁆ L₂)
  statement: ⇑(f : L₁ ->ₗ[R] L₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_toLinearMap
  条件: (f : L₁ ->ₗ⁅R⁆ L₂)
  结论: ⇑(f : L₁ ->ₗ[R] L₂) = f
  证明: rfl

@[simp]
-/
theorem coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->ₗ[R] L₂) = f :=
  rfl

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : L₁ ->ₗ⁅R⁆ L₂)
  statement: f.toFun = ⇑f
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: (f : L₁ ->ₗ⁅R⁆ L₂)
  结论: f.toFun = ⇑f
  证明: rfl
-/
theorem toFun_eq_coe (f : L₁ ->ₗ⁅R⁆ L₂) : f.toFun = ⇑f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (L₁ ->ₗ⁅R⁆ L₂) R L₁ L₂
  body: by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]

中文:
实例 :
  签名: LinearMapClass (L₁ ->ₗ⁅R⁆ L₂) R L₁ L₂
  定义体: by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]

Depends on / 依赖: coe_toLinearMap, map_add
-/
instance : LinearMapClass (L₁ ->ₗ⁅R⁆ L₂) R L₁ L₂ where
  map_add _ _ _ := by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]
/--
theorem `map_lie` / 定理 `map_lie`

English:
theorem map_lie
  given: (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁)
  statement: f ⁅x, y⁆ = ⁅f x, f y⁆
  proof: LieHom.map_lie' f

中文:
定理 map_lie
  条件: (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁)
  结论: f ⁅x, y⁆ = ⁅f x, f y⁆
  证明: LieHom.map_lie' f

Depends on / 依赖: LieHom, LieHom.map_lie, map_lie
-/
theorem map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  LieHom.map_lie' f

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : L₁ ->ₗ⁅R⁆ L₁
  body: { (LinearMap.id : L₁ ->ₗ[R] L₁) with map_lie' := rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : L₁ ->ₗ⁅R⁆ L₁
  定义体: { (LinearMap.id : L₁ ->ₗ[R] L₁) with map_lie' := rfl }

@[simp, norm_cast]

Depends on / 依赖: LinearMap, LinearMap.id, map_lie
-/
def id : L₁ ->ₗ⁅R⁆ L₁ :=
  { (LinearMap.id : L₁ ->ₗ[R] L₁) with map_lie' := rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(id : L₁ ->ₗ⁅R⁆ L₁) = _root_.id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(id : L₁ ->ₗ⁅R⁆ L₁) = _root_.id
  证明: rfl
-/
theorem coe_id : ⇑(id : L₁ ->ₗ⁅R⁆ L₁) = _root_.id :=
  rfl

/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : L₁)
  statement: (id : L₁ ->ₗ⁅R⁆ L₁) x = x
  proof: rfl

中文:
定理 id_apply
  条件: (x : L₁)
  结论: (id : L₁ ->ₗ⁅R⁆ L₁) x = x
  证明: rfl
-/
theorem id_apply (x : L₁) : (id : L₁ ->ₗ⁅R⁆ L₁) x = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (L₁ ->ₗ⁅R⁆ L₂)
  body: ⟨{ (0 : L₁ ->ₗ[R] L₂) with map_lie' := by simp }⟩

@[norm_cast, simp]

中文:
实例 :
  签名: Zero (L₁ ->ₗ⁅R⁆ L₂)
  定义体: ⟨{ (0 : L₁ ->ₗ[R] L₂) with map_lie' := by simp }⟩

@[norm_cast, simp]

Depends on / 依赖: map_lie
-/
instance : Zero (L₁ ->ₗ⁅R⁆ L₂) :=
  ⟨{ (0 : L₁ ->ₗ[R] L₂) with map_lie' := by simp }⟩

@[norm_cast, simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x : L₁)
  statement: (0 : L₁ ->ₗ⁅R⁆ L₂) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (x : L₁)
  结论: (0 : L₁ ->ₗ⁅R⁆ L₂) x = 0
  证明: rfl
-/
theorem zero_apply (x : L₁) : (0 : L₁ ->ₗ⁅R⁆ L₂) x = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (L₁ ->ₗ⁅R⁆ L₁)
  body: ⟨id⟩

@[simp]

中文:
实例 :
  签名: One (L₁ ->ₗ⁅R⁆ L₁)
  定义体: ⟨id⟩

@[simp]
-/
instance : One (L₁ ->ₗ⁅R⁆ L₁) :=
  ⟨id⟩

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : L₁ ->ₗ⁅R⁆ L₁) : L₁ -> L₁) = _root_.id
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : L₁ ->ₗ⁅R⁆ L₁) : L₁ -> L₁) = _root_.id
  证明: rfl
-/
theorem coe_one : ((1 : L₁ ->ₗ⁅R⁆ L₁) : L₁ -> L₁) = _root_.id :=
  rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : L₁)
  statement: (1 : L₁ ->ₗ⁅R⁆ L₁) x = x
  proof: rfl

中文:
定理 one_apply
  条件: (x : L₁)
  结论: (1 : L₁ ->ₗ⁅R⁆ L₁) x = x
  证明: rfl
-/
theorem one_apply (x : L₁) : (1 : L₁ ->ₗ⁅R⁆ L₁) x = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (L₁ ->ₗ⁅R⁆ L₂)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (L₁ ->ₗ⁅R⁆ L₂)
  定义体: ⟨0⟩
-/
instance : Inhabited (L₁ ->ₗ⁅R⁆ L₂) :=
  ⟨0⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (L₁ ->ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑)
  proof: by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  congr

@[ext]

中文:
定理 coe_injective
  结论: @Function.Injective (L₁ ->ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑)
  证明: by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  congr

@[ext]
-/
theorem coe_injective : @Function.Injective (L₁ ->ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  congr

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : L₁ ->ₗ⁅R⁆ L₂} (h : forall x, f x = g x)
  statement: f = g
  proof: coe_injective funext h

中文:
定理 ext
  条件: {f g : L₁ ->ₗ⁅R⁆ L₂} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: coe_injective funext h

Depends on / 依赖: coe_injective
-/
theorem ext {f g : L₁ ->ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g :=
coe_injective funext h

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : L₁ ->ₗ⁅R⁆ L₂} (h : f = g) (x : L₁)
  statement: f x = g x
  proof: h ▸ rfl

@[simp]

中文:
定理 congr_fun
  条件: {f g : L₁ ->ₗ⁅R⁆ L₂} (h : f = g) (x : L₁)
  结论: f x = g x
  证明: h ▸ rfl

@[simp]

Depends on / 依赖: DistribLattice, LieIdeal, instDistribLattice
-/
theorem congr_fun {f g : L₁ ->ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x :=
  h ▸ rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : L₁ ->ₗ⁅R⁆ L₂) (h₁ h₂ h₃)
  statement: (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) = f
  proof: by
  ext
  rfl

@[simp]

中文:
定理 mk_coe
  条件: (f : L₁ ->ₗ⁅R⁆ L₂) (h₁ h₂ h₃)
  结论: (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) = f
  证明: by
  ext
  rfl

@[simp]

Depends on / 依赖: BooleanAlgebra, LieIdeal, instBooleanAlgebra
-/
theorem mk_coe (f : L₁ ->ₗ⁅R⁆ L₂) (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) = f := by
  ext
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : L₁ -> L₂) (h₁ h₂ h₃)
  statement: ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : L₁ -> L₂) (h₁ h₂ h₃)
  结论: ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = f
  证明: rfl

Depends on / 依赖: HasTrivialRadical, IsSemisimple, IsSemisimple.non_abelian_of_isAtom, LieIdeal, LieIdeal.coe_bracket_of_module, LieSubmodule, LieSubmodule.coe_bracket, Subtype, Subtype.val, ZeroMemClass, ZeroMemClass.coe_zero, apply_fun, coe_bracket, coe_bracket_of_module, coe_zero, eq_bot_or_exists_atom_le, hasTrivialRadical_iff_no_abelian_ideals, instHasTrivialRadical, non_abelian_of_isAtom, resolve_right
-/
theorem coe_mk (f : L₁ -> L₂) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = f :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂)
  body: { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }

中文:
定义 comp
  签名: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂)
  定义体: { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }

Depends on / 依赖: IsSimple, IsSimple.instIsSemisimple, LinearMap, LinearMap.comp, f.toLinearMap, g.toLinearMap, instIsSemisimple, map_lie, toLinearMap
-/
def comp (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) : L₁ ->ₗ⁅R⁆ L₃ :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) (x : L₁)
  statement: f.comp g x = f (g x)
  proof: rfl

@[norm_cast, simp]

中文:
定理 comp_apply
  条件: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) (x : L₁)
  结论: f.comp g x = f (g x)
  证明: rfl

@[norm_cast, simp]
-/
theorem comp_apply (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f (g x) :=
  rfl

@[norm_cast, simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂)
  statement: (f.comp g : L₁ -> L₃) = f ∘ g
  proof: rfl

@[norm_cast, simp]

中文:
定理 coe_comp
  条件: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂)
  结论: (f.comp g : L₁ -> L₃) = f ∘ g
  证明: rfl

@[norm_cast, simp]
-/
theorem coe_comp (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) : (f.comp g : L₁ -> L₃) = f ∘ g :=
  rfl

@[norm_cast, simp]
/--
theorem `toLinearMap_comp` / 定理 `toLinearMap_comp`

English:
theorem toLinearMap_comp
  given: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_comp
  条件: (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂)
  证明: rfl

@[simp]
-/
theorem toLinearMap_comp (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) :
    (f.comp g : L₁ ->ₗ[R] L₃) = (f : L₂ ->ₗ[R] L₃).comp (g : L₁ ->ₗ[R] L₂) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : L₁ ->ₗ⁅R⁆ L₂)
  statement: f.comp (id : L₁ ->ₗ⁅R⁆ L₁) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : L₁ ->ₗ⁅R⁆ L₂)
  结论: f.comp (id : L₁ ->ₗ⁅R⁆ L₁) = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : L₁ ->ₗ⁅R⁆ L₂) : f.comp (id : L₁ ->ₗ⁅R⁆ L₁) = f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : L₁ ->ₗ⁅R⁆ L₂)
  statement: (id : L₂ ->ₗ⁅R⁆ L₂).comp f = f
  proof: rfl

中文:
定理 id_comp
  条件: (f : L₁ ->ₗ⁅R⁆ L₂)
  结论: (id : L₂ ->ₗ⁅R⁆ L₂).comp f = f
  证明: rfl
-/
theorem id_comp (f : L₁ ->ₗ⁅R⁆ L₂) : (id : L₂ ->ₗ⁅R⁆ L₂).comp f = f :=
  rfl

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₂ -> L₁) (h₁ : Function.LeftInverse g f)
  body: { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x y
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }

中文:
定义 inverse
  签名: (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₂ -> L₁) (h₁ : Function.LeftInverse g f)
  定义体: { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x y
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }

Depends on / 依赖: LinearMap, LinearMap.inverse, conv_lhs, f.toLinearMap, inverse, map_lie, toLinearMap
-/
def inverse (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₂ -> L₁) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : L₂ ->ₗ⁅R⁆ L₁ :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x y
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }

end LieHom

section ModulePullBack

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)
variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M] [LieRingModule L₂ M]
variable (f : L₁ ->ₗ⁅R⁆ L₂)

/-- A Lie ring module may be pulled back along a morphism of Lie algebras.

See note [reducible non-instances]. -/
@[instance_reducible]
/--
Definition of `LieRingModule.compLieHom` / `LieRingModule.compLieHom` 的定义

English:
definition LieRingModule.compLieHom
  signature: : LieRingModule L₁ M where
  body: ⁅f x, m⁆
  lie_add x := lie_add (f x)
  add_lie x y m := by simp only [map_add, add_lie]
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]

中文:
定义 LieRingModule.compLieHom
  签名: : LieRingModule L₁ M where
  定义体: ⁅f x, m⁆
  lie_add x := lie_add (f x)
  add_lie x y m := by simp only [map_add, add_lie]
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]
-/
def LieRingModule.compLieHom : LieRingModule L₁ M where
  bracket x m := ⁅f x, m⁆
  lie_add x := lie_add (f x)
  add_lie x y m := by simp only [map_add, add_lie]
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]

/--
theorem `LieRingModule.compLieHom_apply` / 定理 `LieRingModule.compLieHom_apply`

English:
theorem LieRingModule.compLieHom_apply
  given: (x : L₁) (m : M)
  proof: LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl

中文:
定理 LieRingModule.compLieHom_apply
  条件: (x : L₁) (m : M)
  证明: LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl

Depends on / 依赖: LieRingModule, LieRingModule.compLieHom, compLieHom
-/
theorem LieRingModule.compLieHom_apply (x : L₁) (m : M) :
    haveI := LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LieModule.compLieHom` / 定理 `LieModule.compLieHom`

English:
theorem LieModule.compLieHom
  given: [Module R M] [LieModule R L₂ M]
  proof: { __ := LieRingModule.compLieHom M f
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, map_smul]
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }

中文:
定理 LieModule.compLieHom
  条件: [Module R M] [LieModule R L₂ M]
  证明: { __ := LieRingModule.compLieHom M f
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, map_smul]
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }

Depends on / 依赖: LieRingModule, LieRingModule.compLieHom, LieRingModule.compLieHom_apply, compLieHom, compLieHom_apply, lie_smul, map_smul, smul_lie
-/
theorem LieModule.compLieHom [Module R M] [LieModule R L₂ M] :
    @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f) :=
  { __ := LieRingModule.compLieHom M f
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, map_smul]
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }

end ModulePullBack

/--
Definition of `LieEquiv` / `LieEquiv` 的定义

English:
structure LieEquiv
  parameters: (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  extends: L ->ₗ⁅R⁆ L'
  axioms and operations (3):
    - invFun : L' -> L
    - left_inv : Function.LeftInverse invFun toLieHom.toFun  [default: by intro; first | rfl | ext <;> rfl]
    - right_inv : Function.RightInverse invFun toLieHom.toFun  [default: by intro; first | rfl | ext <;> rfl]

中文:
结构 LieEquiv
  参数: (R : 类型u) (L : 类型v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  继承: L ->ₗ⁅R⁆ L'
  公理与运算 (3 个):
    - invFun : L' -> L
    - left_inv : Function.LeftInverse invFun toLieHom.toFun  [默认: by intro; first | rfl | ext <;> rfl]
    - right_inv : Function.RightInverse invFun toLieHom.toFun  [默认: by intro; first | rfl | ext <;> rfl]
-/
structure LieEquiv (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L ->ₗ⁅R⁆ L' where
  /-- The inverse function of an equivalence of Lie algebras -/
  invFun : L' -> L
  /-- The inverse function of an equivalence of Lie algebras is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toLieHom.toFun := by intro; first | rfl | ext <;> rfl
  /-- The inverse function of an equivalence of Lie algebras is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toLieHom.toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
notation:50 L " ≃ₗ⁅" R "⁆ " L' => LieEquiv R L L'

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]
variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (f : L₁ ≃ₗ⁅R⁆ L₂)
  body: { f.toLieHom, f with }

中文:
定义 toLinearEquiv
  签名: (f : L₁ ≃ₗ⁅R⁆ L₂)
  定义体: { f.toLieHom, f with }

Depends on / 依赖: f.toLieHom, toLieHom
-/
def toLinearEquiv (f : L₁ ≃ₗ⁅R⁆ L₂) : L₁ ≃ₗ[R] L₂ :=
  { f.toLieHom, f with }

/--
Instance `hasCoeToLieHom` / 实例 `hasCoeToLieHom`

English:
instance hasCoeToLieHom
  signature: : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ->ₗ⁅R⁆ L₂)
  body: ⟨toLieHom⟩

中文:
实例 hasCoeToLieHom
  签名: : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ->ₗ⁅R⁆ L₂)
  定义体: ⟨toLieHom⟩

Depends on / 依赖: toLieHom
-/
instance hasCoeToLieHom : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ->ₗ⁅R⁆ L₂) :=
  ⟨toLieHom⟩

/--
Instance `hasCoeToLinearEquiv` / 实例 `hasCoeToLinearEquiv`

English:
instance hasCoeToLinearEquiv
  signature: : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂)
  body: ⟨toLinearEquiv⟩

中文:
实例 hasCoeToLinearEquiv
  签名: : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂)
  定义体: ⟨toLinearEquiv⟩

Depends on / 依赖: toLinearEquiv
-/
instance hasCoeToLinearEquiv : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) :=
  ⟨toLinearEquiv⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (L₁ ≃ₗ⁅R⁆ L₂) L₁ L₂
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

中文:
实例 :
  签名: EquivLike (L₁ ≃ₗ⁅R⁆ L₂) L₁ L₂
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

Depends on / 依赖: f.toFun
-/
instance : EquivLike (L₁ ≃ₗ⁅R⁆ L₂) L₁ L₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

/--
theorem `coe_toLieHom` / 定理 `coe_toLieHom`

English:
theorem coe_toLieHom
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: ⇑(e : L₁ ->ₗ⁅R⁆ L₂) = e
  proof: rfl

@[simp]

中文:
定理 coe_toLieHom
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: ⇑(e : L₁ ->ₗ⁅R⁆ L₂) = e
  证明: rfl

@[simp]
-/
theorem coe_toLieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ->ₗ⁅R⁆ L₂) = e :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: ⇑(e : L₁ ≃ₗ[R] L₂) = e
  proof: rfl

中文:
定理 coe_toLinearEquiv
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: ⇑(e : L₁ ≃ₗ[R] L₂) = e
  证明: rfl
-/
theorem coe_toLinearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ≃ₗ[R] L₂) = e :=
  rfl

/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: ⇑e.toLieHom = e
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: ⇑e.toLieHom = e
  证明: rfl

@[simp]
-/
@[simp] theorem coe_coe (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑e.toLieHom = e := rfl

@[simp]
/--
theorem `toLinearEquiv_mk` / 定理 `toLinearEquiv_mk`

English:
theorem toLinearEquiv_mk
  given: (f : L₁ ->ₗ⁅R⁆ L₂) (g h₁ h₂)
  proof: rfl

中文:
定理 toLinearEquiv_mk
  条件: (f : L₁ ->ₗ⁅R⁆ L₂) (g h₁ h₂)
  证明: rfl
-/
theorem toLinearEquiv_mk (f : L₁ ->ₗ⁅R⁆ L₂) (g h₁ h₂) :
    (mk f g h₁ h₂ : L₁ ≃ₗ[R] L₂) =
      { f with
        invFun := g
        left_inv := h₁
        right_inv := h₂ } :=
  rfl

/--
theorem `toLinearEquiv_injective` / 定理 `toLinearEquiv_injective`

English:
theorem toLinearEquiv_injective
  statement: Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) -> L₁ ≃ₗ[R] L₂)
  proof: by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

中文:
定理 toLinearEquiv_injective
  结论: Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) -> L₁ ≃ₗ[R] L₂)
  证明: by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

Depends on / 依赖: f_inv, g_inv
-/
theorem toLinearEquiv_injective : Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) -> L₁ ≃ₗ[R] L₂) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑)
  proof: LinearEquiv.coe_injective.comp toLinearEquiv_injective

中文:
定理 coe_injective
  结论: @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑)
  证明: LinearEquiv.coe_injective.comp toLinearEquiv_injective

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_injective.comp, coe_injective, toLinearEquiv_injective
-/
theorem coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑) :=
  LinearEquiv.coe_injective.comp toLinearEquiv_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearEquivClass (L₁ ≃ₗ⁅R⁆ L₂) R L₁ L₂
  body: by
    rw [← coe_toLinearEquiv]; rw [map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_smul]; rw [RingHom.id_apply]

@[ext]

中文:
实例 :
  签名: LinearEquivClass (L₁ ≃ₗ⁅R⁆ L₂) R L₁ L₂
  定义体: by
    rw [← coe_toLinearEquiv]; rw [map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_smul]; rw [RingHom.id_apply]

@[ext]

Depends on / 依赖: RingHom, RingHom.id_apply, coe_toLinearEquiv, id_apply, map_add, map_smul
-/
instance : LinearEquivClass (L₁ ≃ₗ⁅R⁆ L₂) R L₁ L₂ where
  map_add _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_smul]; rw [RingHom.id_apply]

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : forall x, f x = g x)
  statement: f = g
  proof: coe_injective funext h

中文:
定理 ext
  条件: {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: coe_injective funext h

Depends on / 依赖: coe_injective
-/
theorem ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g :=
coe_injective funext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (L₁ ≃ₗ⁅R⁆ L₁)
  body: ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := rfl }⟩

@[simp]

中文:
实例 :
  签名: One (L₁ ≃ₗ⁅R⁆ L₁)
  定义体: ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := rfl }⟩

@[simp]

Depends on / 依赖: map_lie
-/
instance : One (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := rfl }⟩

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : L₁)
  statement: (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x
  proof: rfl

中文:
定理 one_apply
  条件: (x : L₁)
  结论: (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x
  证明: rfl
-/
theorem one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (L₁ ≃ₗ⁅R⁆ L₁)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (L₁ ≃ₗ⁅R⁆ L₁)
  定义体: ⟨1⟩
-/
instance : Inhabited (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨1⟩

/--
lemma `map_lie` / 引理 `map_lie`

English:
lemma map_lie
  given: (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁)
  statement: e ⁅x, y⁆ = ⁅e x, e y⁆
  proof: LieHom.map_lie e.toLieHom x y

中文:
引理 map_lie
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁)
  结论: e ⁅x, y⁆ = ⁅e x, e y⁆
  证明: LieHom.map_lie e.toLieHom x y

Depends on / 依赖: LieHom, LieHom.map_lie, e.toLieHom, map_lie, toLieHom
-/
lemma map_lie (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁) : e ⁅x, y⁆ = ⁅e x, e y⁆ :=
  LieHom.map_lie e.toLieHom x y

/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : L₁ ≃ₗ⁅R⁆ L₁
  body: 1

@[simp]

中文:
定义 refl
  签名: : L₁ ≃ₗ⁅R⁆ L₁
  定义体: 1

@[simp]
-/
def refl : L₁ ≃ₗ⁅R⁆ L₁ :=
  1

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : L₁)
  statement: (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x
  proof: rfl

中文:
定理 refl_apply
  条件: (x : L₁)
  结论: (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x
  证明: rfl
-/
theorem refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl

/-- Lie algebra equivalences are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : L₁ ≃ₗ⁅R⁆ L₂)
  body: { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }

@[simp]

中文:
定义 symm
  签名: (e : L₁ ≃ₗ⁅R⁆ L₂)
  定义体: { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }

@[simp]

Depends on / 依赖: LieHom, LieHom.inverse, e.invFun, e.left_inv, e.right_inv, e.toLieHom, e.toLinearEquiv.symm, invFun, inverse, left_inv, right_inv, toLieHom, toLinearEquiv
-/
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
  { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) -> L₂ ≃ₗ⁅R⁆ L₁)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) -> L₂ ≃ₗ⁅R⁆ L₁)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) -> L₂ ≃ₗ⁅R⁆ L₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: forall x, e (e.symm x) = x
  proof: e.toLinearEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toLinearEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toLinearEquiv.apply_symm_apply, toLinearEquiv
-/
theorem apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: forall x, e.symm (e x) = x
  proof: e.toLinearEquiv.symm_apply_apply

中文:
定理 symm_apply_apply
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toLinearEquiv.symm_apply_apply

Depends on / 依赖: e.toLinearEquiv.symm_apply_apply, symm_apply_apply, toLinearEquiv
-/
theorem symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : L₁ ≃ₗ⁅R⁆ L₂) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toLinearEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toLinearEquiv.symm_apply_eq

Depends on / 依赖: e.toLinearEquiv.symm_apply_eq, symm_apply_eq, toLinearEquiv
-/
theorem symm_apply_eq (e : L₁ ≃ₗ⁅R⁆ L₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : L₁ ≃ₗ⁅R⁆ L₂) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toLinearEquiv.eq_symm_apply

@[simp]

中文:
定理 eq_symm_apply
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toLinearEquiv.eq_symm_apply

@[simp]

Depends on / 依赖: e.toLinearEquiv.eq_symm_apply, eq_symm_apply, toLinearEquiv
-/
theorem eq_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl
  proof: rfl

中文:
定理 refl_symm
  结论: (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl
  证明: rfl
-/
theorem refl_symm : (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl :=
  rfl

/-- Lie algebra equivalences are transitive. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃)
  body: { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]

中文:
定义 trans
  签名: (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃)
  定义体: { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]

Depends on / 依赖: LieHom, LieHom.comp, LinearEquiv, LinearEquiv.trans, toLieHom, toLinearEquiv
-/
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
  { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: e.trans e.symm = refl
  proof: ext e.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: e.trans e.symm = refl
  证明: ext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = refl :=
  ext e.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: e.symm.trans e = refl
  proof: e.symm.self_trans_symm

@[simp]

中文:
定理 symm_trans_self
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: e.symm.trans e = refl
  证明: e.symm.self_trans_symm

@[simp]

Depends on / 依赖: e.symm.self_trans_symm, self_trans_symm
-/
theorem symm_trans_self (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.trans e = refl :=
  e.symm.self_trans_symm

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁)
  statement: (e₁.trans e₂) x = e₂ (e₁ x)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁)
  结论: (e₁.trans e₂) x = e₂ (e₁ x)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃)
  proof: rfl

中文:
定理 symm_trans
  条件: (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃)
  证明: rfl
-/
theorem symm_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: Function.Bijective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂)
  proof: e.toLinearEquiv.bijective

中文:
定理 bijective
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: Function.Bijective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂)
  证明: e.toLinearEquiv.bijective
-/
protected theorem bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Bijective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) :=
  e.toLinearEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  statement: Function.Injective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂)
  proof: e.toLinearEquiv.injective

中文:
定理 injective
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  结论: Function.Injective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂)
  证明: e.toLinearEquiv.injective
-/
protected theorem injective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Injective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) :=
  e.toLinearEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : L₁ ≃ₗ⁅R⁆ L₂)
  proof: e.toLinearEquiv.surjective

中文:
定理 surjective
  条件: (e : L₁ ≃ₗ⁅R⁆ L₂)
  证明: e.toLinearEquiv.surjective
-/
protected theorem surjective (e : L₁ ≃ₗ⁅R⁆ L₂) :
    Function.Surjective ((e : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) :=
  e.toLinearEquiv.surjective

/-- A bijective morphism of Lie algebras yields an equivalence of Lie algebras. -/
@[simps!]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Bijective f)
  body: { LinearEquiv.ofBijective (f : L₁ ->ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := by intro x y; exact f.map_lie x y }

中文:
定义 ofBijective
  签名: (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Bijective f)
  定义体: { LinearEquiv.ofBijective (f : L₁ ->ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := by intro x y; exact f.map_lie x y }

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, f.map_lie, map_lie, ofBijective
-/
noncomputable def ofBijective (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Bijective f) : L₁ ≃ₗ⁅R⁆ L₂ :=
  { LinearEquiv.ofBijective (f : L₁ ->ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := by intro x y; exact f.map_lie x y }

end LieEquiv

section LieModuleMorphisms

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]
variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

/--
Definition of `LieModuleHom` / `LieModuleHom` 的定义

English:
structure LieModuleHom
  parameters: extends M ->ₗ[R] N
  extends: M ->ₗ[R] N
  axioms and operations (1):
    - map_lie' : forall {x : L} {m : M}, toFun ⁅x, m⁆ = ⁅x, toFun m⁆

中文:
结构 LieModuleHom
  参数: extends M ->ₗ[R] N
  继承: M ->ₗ[R] N
  公理与运算 (1 个):
    - map_lie' : 对任意 {x : L} {m : M}, toFun ⁅x, m⁆ = ⁅x, toFun m⁆
-/
structure LieModuleHom extends M ->ₗ[R] N where
  /-- A module of Lie algebra modules is compatible with the action of the Lie algebra on the
  modules. -/
  map_lie' : forall {x : L} {m : M}, toFun ⁅x, m⁆ = ⁅x, toFun m⁆

@[inherit_doc]
notation:25 M " ->ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleHom R L M N

namespace LieModuleHom

variable {R L M N P}

attribute [coe] LieModuleHom.toLinearMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (M ->ₗ⁅R,L⁆ N) (M ->ₗ[R] N)
  body: ⟨LieModuleHom.toLinearMap⟩

中文:
实例 :
  签名: CoeOut (M ->ₗ⁅R,L⁆ N) (M ->ₗ[R] N)
  定义体: ⟨LieModuleHom.toLinearMap⟩

Depends on / 依赖: LieModuleHom, LieModuleHom.toLinearMap, toLinearMap
-/
instance : CoeOut (M ->ₗ⁅R,L⁆ N) (M ->ₗ[R] N) :=
  ⟨LieModuleHom.toLinearMap⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (M ->ₗ⁅R,L⁆ N) M N
  body: f.toFun
  coe_injective x y h := by cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieModuleHom (toFun -> apply)

@[simp, norm_cast]

中文:
实例 :
  签名: FunLike (M ->ₗ⁅R,L⁆ N) M N
  定义体: f.toFun
  coe_injective x y h := by cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieModuleHom (toFun -> apply)

@[simp, norm_cast]

Depends on / 依赖: f.toFun
-/
instance : FunLike (M ->ₗ⁅R,L⁆ N) M N where
  coe f := f.toFun
  coe_injective x y h := by cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieModuleHom (toFun -> apply)

@[simp, norm_cast]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : M ->ₗ⁅R,L⁆ N)
  statement: ((f : M ->ₗ[R] N) : M -> N) = f
  proof: rfl

中文:
定理 coe_toLinearMap
  条件: (f : M ->ₗ⁅R,L⁆ N)
  结论: ((f : M ->ₗ[R] N) : M -> N) = f
  证明: rfl
-/
theorem coe_toLinearMap (f : M ->ₗ⁅R,L⁆ N) : ((f : M ->ₗ[R] N) : M -> N) = f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (M ->ₗ⁅R,L⁆ N) R M N
  body: by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]

中文:
实例 :
  签名: LinearMapClass (M ->ₗ⁅R,L⁆ N) R M N
  定义体: by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]

Depends on / 依赖: coe_toLinearMap, map_add
-/
instance : LinearMapClass (M ->ₗ⁅R,L⁆ N) R M N where
  map_add _ _ _ := by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]
/--
theorem `map_lie` / 定理 `map_lie`

English:
theorem map_lie
  given: (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M)
  statement: f ⁅x, m⁆ = ⁅x, f m⁆
  proof: LieModuleHom.map_lie' f

中文:
定理 map_lie
  条件: (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M)
  结论: f ⁅x, m⁆ = ⁅x, f m⁆
  证明: LieModuleHom.map_lie' f

Depends on / 依赖: LieModuleHom, LieModuleHom.map_lie, map_lie
-/
theorem map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
  LieModuleHom.map_lie' f

variable [LieAlgebra R L] [LieModule R L N] [LieModule R L P] in
/--
theorem `map_lie₂` / 定理 `map_lie₂`

English:
theorem map_lie₂
  given: (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (x : L) (m : M) (n : N)
  proof: by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]

中文:
定理 map_lie₂
  条件: (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (x : L) (m : M) (n : N)
  证明: by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]

Depends on / 依赖: LieHom, LieHom.lie_apply, lie_apply, map_lie, sub_add_cancel
-/
theorem map_lie₂ (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (x : L) (m : M) (n : N) :
    ⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆ := by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : M ->ₗ⁅R,L⁆ M
  body: { (LinearMap.id : M ->ₗ[R] M) with map_lie' := rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : M ->ₗ⁅R,L⁆ M
  定义体: { (LinearMap.id : M ->ₗ[R] M) with map_lie' := rfl }

@[simp, norm_cast]

Depends on / 依赖: LinearMap, LinearMap.id, map_lie
-/
def id : M ->ₗ⁅R,L⁆ M :=
  { (LinearMap.id : M ->ₗ[R] M) with map_lie' := rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ((id : M ->ₗ⁅R,L⁆ M) : M -> M) = _root_.id
  proof: rfl

中文:
定理 coe_id
  结论: ((id : M ->ₗ⁅R,L⁆ M) : M -> M) = _root_.id
  证明: rfl
-/
theorem coe_id : ((id : M ->ₗ⁅R,L⁆ M) : M -> M) = _root_.id :=
  rfl

/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : M)
  statement: (id : M ->ₗ⁅R,L⁆ M) x = x
  proof: rfl

中文:
定理 id_apply
  条件: (x : M)
  结论: (id : M ->ₗ⁅R,L⁆ M) x = x
  证明: rfl
-/
theorem id_apply (x : M) : (id : M ->ₗ⁅R,L⁆ M) x = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ->ₗ⁅R,L⁆ N)
  body: ⟨{ (0 : M ->ₗ[R] N) with map_lie' := by simp }⟩

@[norm_cast, simp]

中文:
实例 :
  签名: Zero (M ->ₗ⁅R,L⁆ N)
  定义体: ⟨{ (0 : M ->ₗ[R] N) with map_lie' := by simp }⟩

@[norm_cast, simp]

Depends on / 依赖: map_lie
-/
instance : Zero (M ->ₗ⁅R,L⁆ N) :=
  ⟨{ (0 : M ->ₗ[R] N) with map_lie' := by simp }⟩

@[norm_cast, simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : M ->ₗ⁅R,L⁆ N) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ⇑(0 : M ->ₗ⁅R,L⁆ N) = 0
  证明: rfl
-/
theorem coe_zero : ⇑(0 : M ->ₗ⁅R,L⁆ N) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (m : M)
  statement: (0 : M ->ₗ⁅R,L⁆ N) m = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (m : M)
  结论: (0 : M ->ₗ⁅R,L⁆ N) m = 0
  证明: rfl
-/
theorem zero_apply (m : M) : (0 : M ->ₗ⁅R,L⁆ N) m = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (M ->ₗ⁅R,L⁆ M)
  body: ⟨id⟩

中文:
实例 :
  签名: One (M ->ₗ⁅R,L⁆ M)
  定义体: ⟨id⟩
-/
instance : One (M ->ₗ⁅R,L⁆ M) :=
  ⟨id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ->ₗ⁅R,L⁆ N)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (M ->ₗ⁅R,L⁆ N)
  定义体: ⟨0⟩
-/
instance : Inhabited (M ->ₗ⁅R,L⁆ N) :=
  ⟨0⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (M ->ₗ⁅R,L⁆ N) (M -> N) (↑)
  proof: by
  rintro ⟨⟨⟨f, _⟩⟩⟩ ⟨⟨⟨g, _⟩⟩⟩ h
  congr

@[ext]

中文:
定理 coe_injective
  结论: @Function.Injective (M ->ₗ⁅R,L⁆ N) (M -> N) (↑)
  证明: by
  rintro ⟨⟨⟨f, _⟩⟩⟩ ⟨⟨⟨g, _⟩⟩⟩ h
  congr

@[ext]
-/
theorem coe_injective : @Function.Injective (M ->ₗ⁅R,L⁆ N) (M -> N) (↑) := by
  rintro ⟨⟨⟨f, _⟩⟩⟩ ⟨⟨⟨g, _⟩⟩⟩ h
  congr

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M ->ₗ⁅R,L⁆ N} (h : forall m, f m = g m)
  statement: f = g
  proof: coe_injective funext h

中文:
定理 ext
  条件: {f g : M ->ₗ⁅R,L⁆ N} (h : 对任意 m, f m = g m)
  结论: f = g
  证明: coe_injective funext h

Depends on / 依赖: coe_injective
-/
theorem ext {f g : M ->ₗ⁅R,L⁆ N} (h : forall m, f m = g m) : f = g :=
coe_injective funext h

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : M ->ₗ⁅R,L⁆ N} (h : f = g) (x : M)
  statement: f x = g x
  proof: h ▸ rfl

@[simp]

中文:
定理 congr_fun
  条件: {f g : M ->ₗ⁅R,L⁆ N} (h : f = g) (x : M)
  结论: f x = g x
  证明: h ▸ rfl

@[simp]
-/
theorem congr_fun {f g : M ->ₗ⁅R,L⁆ N} (h : f = g) (x : M) : f x = g x :=
  h ▸ rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : M ->ₗ⁅R,L⁆ N) (h)
  statement: (⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) = f
  proof: by
  rfl

@[simp]

中文:
定理 mk_coe
  条件: (f : M ->ₗ⁅R,L⁆ N) (h)
  结论: (⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) = f
  证明: by
  rfl

@[simp]
-/
theorem mk_coe (f : M ->ₗ⁅R,L⁆ N) (h) : (⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) = f := by
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : M ->ₗ[R] N) (h)
  statement: ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M -> N) = f
  proof: by
  rfl

@[norm_cast]

中文:
定理 coe_mk
  条件: (f : M ->ₗ[R] N) (h)
  结论: ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M -> N) = f
  证明: by
  rfl

@[norm_cast]
-/
theorem coe_mk (f : M ->ₗ[R] N) (h) : ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M -> N) = f := by
  rfl

@[norm_cast]
/--
theorem `coe_linear_mk` / 定理 `coe_linear_mk`

English:
theorem coe_linear_mk
  given: (f : M ->ₗ[R] N) (h)
  statement: ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M ->ₗ[R] N) = f
  proof: by
  rfl

中文:
定理 coe_linear_mk
  条件: (f : M ->ₗ[R] N) (h)
  结论: ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M ->ₗ[R] N) = f
  证明: by
  rfl
-/
theorem coe_linear_mk (f : M ->ₗ[R] N) (h) : ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M ->ₗ[R] N) = f := by
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N)
  body: { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }

中文:
定义 comp
  签名: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N)
  定义体: { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }

Depends on / 依赖: LinearMap, LinearMap.comp, f.toLinearMap, g.toLinearMap, map_lie, toLinearMap
-/
def comp (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) : M ->ₗ⁅R,L⁆ P :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: f.comp g m = f (g m)
  proof: rfl

@[norm_cast, simp]

中文:
定理 comp_apply
  条件: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: f.comp g m = f (g m)
  证明: rfl

@[norm_cast, simp]
-/
theorem comp_apply (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f (g m) :=
  rfl

@[norm_cast, simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[norm_cast, simp]

中文:
定理 coe_comp
  条件: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[norm_cast, simp]
-/
theorem coe_comp (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[norm_cast, simp]
/--
theorem `toLinearMap_comp` / 定理 `toLinearMap_comp`

English:
theorem toLinearMap_comp
  given: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N)
  proof: rfl

中文:
定理 toLinearMap_comp
  条件: (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N)
  证明: rfl
-/
theorem toLinearMap_comp (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) :
    (f.comp g : M ->ₗ[R] P) = (f : N ->ₗ[R] P).comp (g : M ->ₗ[R] N) :=
  rfl

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ : Function.LeftInverse g f)
  body: { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x n
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }

中文:
定义 inverse
  签名: (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ : Function.LeftInverse g f)
  定义体: { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x n
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }

Depends on / 依赖: LinearMap, LinearMap.inverse, f.toLinearMap, inverse, map_lie, toLinearMap
-/
def inverse (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N ->ₗ⁅R,L⁆ M :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x n
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (M ->ₗ⁅R,L⁆ N)
  body: { (f : M ->ₗ[R] N) + (g : M ->ₗ[R] N) with map_lie' := by simp }

中文:
实例 :
  签名: Add (M ->ₗ⁅R,L⁆ N)
  定义体: { (f : M ->ₗ[R] N) + (g : M ->ₗ[R] N) with map_lie' := by simp }

Depends on / 依赖: map_lie
-/
instance : Add (M ->ₗ⁅R,L⁆ N) where
  add f g := { (f : M ->ₗ[R] N) + (g : M ->ₗ[R] N) with map_lie' := by simp }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (M ->ₗ⁅R,L⁆ N)
  body: { (f : M ->ₗ[R] N) - (g : M ->ₗ[R] N) with map_lie' := by simp }

中文:
实例 :
  签名: Sub (M ->ₗ⁅R,L⁆ N)
  定义体: { (f : M ->ₗ[R] N) - (g : M ->ₗ[R] N) with map_lie' := by simp }

Depends on / 依赖: map_lie
-/
instance : Sub (M ->ₗ⁅R,L⁆ N) where
  sub f g := { (f : M ->ₗ[R] N) - (g : M ->ₗ[R] N) with map_lie' := by simp }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (M ->ₗ⁅R,L⁆ N)
  body: { -(f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

中文:
实例 :
  签名: Neg (M ->ₗ⁅R,L⁆ N)
  定义体: { -(f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

Depends on / 依赖: map_lie
-/
instance : Neg (M ->ₗ⁅R,L⁆ N) where neg f := { -(f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
定理 coe_add
  条件: (f g : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
theorem coe_add (f g : M ->ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g :=
  rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: (f + g) m = f m + g m
  proof: rfl

@[norm_cast, simp]

中文:
定理 add_apply
  条件: (f g : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: (f + g) m = f m + g m
  证明: rfl

@[norm_cast, simp]
-/
theorem add_apply (f g : M ->ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
  rfl

@[norm_cast, simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(f - g) = f - g
  proof: rfl

中文:
定理 coe_sub
  条件: (f g : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(f - g) = f - g
  证明: rfl

Depends on / 依赖: IsTriangularizable, IsTriangularizable.maxGenEigenspace_eq_top, maxGenEigenspace_eq_top
-/
theorem coe_sub (f g : M ->ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g :=
  rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: (f - g) m = f m - g m
  proof: rfl

@[norm_cast, simp]

中文:
定理 sub_apply
  条件: (f g : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: (f - g) m = f m - g m
  证明: rfl

@[norm_cast, simp]

Depends on / 依赖: IsTriangularizable, IsTriangularizable.maxGenEigenspace_eq_top, maxGenEigenspace_eq_top
-/
theorem sub_apply (f g : M ->ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
  rfl

@[norm_cast, simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(-f) = -f
  proof: rfl

中文:
定理 coe_neg
  条件: (f : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(-f) = -f
  证明: rfl
-/
theorem coe_neg (f : M ->ₗ⁅R,L⁆ N) : ⇑(-f) = -f :=
  rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: (-f) m = -f m
  proof: rfl

中文:
定理 neg_apply
  条件: (f : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: (-f) m = -f m
  证明: rfl
-/
theorem neg_apply (f : M ->ₗ⁅R,L⁆ N) (m : M) : (-f) m = -f m :=
  rfl

/--
Instance `hasNSMul` / 实例 `hasNSMul`

English:
instance hasNSMul
  signature: : SMul Nat (M ->ₗ⁅R,L⁆ N) where
  body: { n • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

中文:
实例 hasNSMul
  签名: : SMul 自然数 (M ->ₗ⁅R,L⁆ N) where
  定义体: { n • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

Depends on / 依赖: map_lie
-/
instance hasNSMul : SMul Nat (M ->ₗ⁅R,L⁆ N) where
  smul n f := { n • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (n : Nat) (f : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(n • f) = n • (⇑f)
  proof: rfl

中文:
定理 coe_nsmul
  条件: (n : 自然数) (f : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(n • f) = n • (⇑f)
  证明: rfl
-/
theorem coe_nsmul (n : Nat) (f : M ->ₗ⁅R,L⁆ N) : ⇑(n • f) = n • (⇑f) :=
  rfl

/--
theorem `nsmul_apply` / 定理 `nsmul_apply`

English:
theorem nsmul_apply
  given: (n : Nat) (f : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: (n • f) m = n • f m
  proof: rfl

中文:
定理 nsmul_apply
  条件: (n : 自然数) (f : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: (n • f) m = n • f m
  证明: rfl
-/
theorem nsmul_apply (n : Nat) (f : M ->ₗ⁅R,L⁆ N) (m : M) : (n • f) m = n • f m :=
  rfl

/--
Instance `hasZSMul` / 实例 `hasZSMul`

English:
instance hasZSMul
  signature: : SMul Int (M ->ₗ⁅R,L⁆ N) where
  body: { z • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

中文:
实例 hasZSMul
  签名: : SMul 整数 (M ->ₗ⁅R,L⁆ N) where
  定义体: { z • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

Depends on / 依赖: IsTriangularizable, IsTriangularizable.maxGenEigenspace_eq_top, Module, Module.End.genEigenspace_restrict_eq_top, N.toEnd_restrict_eq_toEnd, genEigenspace_restrict_eq_top, map_lie, maxGenEigenspace_eq_top, toEnd_restrict_eq_toEnd
-/
instance hasZSMul : SMul Int (M ->ₗ⁅R,L⁆ N) where
  smul z f := { z • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (z : Int) (f : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(z • f) = z • (⇑f)
  proof: rfl

中文:
定理 coe_zsmul
  条件: (z : 整数) (f : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(z • f) = z • (⇑f)
  证明: rfl
-/
theorem coe_zsmul (z : Int) (f : M ->ₗ⁅R,L⁆ N) : ⇑(z • f) = z • (⇑f) :=
  rfl

/--
theorem `zsmul_apply` / 定理 `zsmul_apply`

English:
theorem zsmul_apply
  given: (z : Int) (f : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: (z • f) m = z • f m
  proof: rfl

中文:
定理 zsmul_apply
  条件: (z : 整数) (f : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: (z • f) m = z • f m
  证明: rfl
-/
theorem zsmul_apply (z : Int) (f : M ->ₗ⁅R,L⁆ N) (m : M) : (z • f) m = z • f m :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (M ->ₗ⁅R,L⁆ N)
  body: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

中文:
实例 :
  签名: AddCommGroup (M ->ₗ⁅R,L⁆ N)
  定义体: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

Depends on / 依赖: addCommGroup, coe_add, coe_injective, coe_injective.addCommGroup, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul
-/
instance : AddCommGroup (M ->ₗ⁅R,L⁆ N) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

variable [LieAlgebra R L] [LieModule R L N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (M ->ₗ⁅R,L⁆ N)
  body: { t • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

中文:
实例 :
  签名: SMul R (M ->ₗ⁅R,L⁆ N)
  定义体: { t • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]

Depends on / 依赖: map_lie
-/
instance : SMul R (M ->ₗ⁅R,L⁆ N) where
  smul t f := { t • (f : M ->ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (t : R) (f : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(t • f) = t • (⇑f)
  proof: rfl

中文:
定理 coe_smul
  条件: (t : R) (f : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(t • f) = t • (⇑f)
  证明: rfl
-/
theorem coe_smul (t : R) (f : M ->ₗ⁅R,L⁆ N) : ⇑(t • f) = t • (⇑f) :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (t : R) (f : M ->ₗ⁅R,L⁆ N) (m : M)
  statement: (t • f) m = t • f m
  proof: rfl

中文:
定理 smul_apply
  条件: (t : R) (f : M ->ₗ⁅R,L⁆ N) (m : M)
  结论: (t • f) m = t • f m
  证明: rfl
-/
theorem smul_apply (t : R) (f : M ->ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (M ->ₗ⁅R,L⁆ N)
  body: Function.Injective.module R
    { toFun := fun f => f.toLinearMap.toFun, map_zero' := rfl, map_add' := coe_add }
    coe_injective coe_smul

中文:
实例 :
  签名: Module R (M ->ₗ⁅R,L⁆ N)
  定义体: Function.Injective.module R
    { toFun := fun f => f.toLinearMap.toFun, map_zero' := rfl, map_add' := coe_add }
    coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, coe_add, coe_injective, coe_smul, f.toLinearMap.toFun, map_add, map_zero, module, toLinearMap
-/
instance : Module R (M ->ₗ⁅R,L⁆ N) :=
  Function.Injective.module R
    { toFun := fun f => f.toLinearMap.toFun, map_zero' := rfl, map_add' := coe_add }
    coe_injective coe_smul

end LieModuleHom

/--
Definition of `LieModuleEquiv` / `LieModuleEquiv` 的定义

English:
structure LieModuleEquiv
  parameters: extends M ->ₗ⁅R,L⁆ N
  extends: M ->ₗ⁅R, L⁆ N
  axioms and operations (3):
    - invFun : N -> M
    - left_inv : Function.LeftInverse invFun toFun
    - right_inv : Function.RightInverse invFun toFun

中文:
结构 LieModuleEquiv
  参数: extends M ->ₗ⁅R,L⁆ N
  继承: M ->ₗ⁅R, L⁆ N
  公理与运算 (3 个):
    - invFun : N -> M
    - left_inv : Function.LeftInverse invFun toFun
    - right_inv : Function.RightInverse invFun toFun
-/
structure LieModuleEquiv extends M ->ₗ⁅R,L⁆ N where
  /-- The inverse function of an equivalence of Lie modules -/
  invFun : N -> M
  /-- The inverse function of an equivalence of Lie modules is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toFun
  /-- The inverse function of an equivalence of Lie modules is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toFun

attribute [nolint docBlame] LieModuleEquiv.toLieModuleHom

@[inherit_doc]
notation:25 M " ≃ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleEquiv R L M N

namespace LieModuleEquiv

variable {R L M N P}

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (e : M ≃ₗ⁅R,L⁆ N)
  body: { e with }

中文:
定义 toLinearEquiv
  签名: (e : M ≃ₗ⁅R,L⁆ N)
  定义体: { e with }
-/
def toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ₗ[R] N :=
  { e with }

/--
Definition of `toEquiv` / `toEquiv` 的定义

English:
definition toEquiv
  signature: (e : M ≃ₗ⁅R,L⁆ N)
  body: { e with }

中文:
定义 toEquiv
  签名: (e : M ≃ₗ⁅R,L⁆ N)
  定义体: { e with }
-/
def toEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ N :=
  { e with }

/--
Instance `hasCoeToEquiv` / 实例 `hasCoeToEquiv`

English:
instance hasCoeToEquiv
  signature: : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N)
  body: ⟨toEquiv⟩

中文:
实例 hasCoeToEquiv
  签名: : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N)
  定义体: ⟨toEquiv⟩

Depends on / 依赖: toEquiv
-/
instance hasCoeToEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N) :=
  ⟨toEquiv⟩

/--
Instance `hasCoeToLieModuleHom` / 实例 `hasCoeToLieModuleHom`

English:
instance hasCoeToLieModuleHom
  signature: : Coe (M ≃ₗ⁅R,L⁆ N) (M ->ₗ⁅R,L⁆ N)
  body: ⟨toLieModuleHom⟩

中文:
实例 hasCoeToLieModuleHom
  签名: : Coe (M ≃ₗ⁅R,L⁆ N) (M ->ₗ⁅R,L⁆ N)
  定义体: ⟨toLieModuleHom⟩

Depends on / 依赖: toLieModuleHom
-/
instance hasCoeToLieModuleHom : Coe (M ≃ₗ⁅R,L⁆ N) (M ->ₗ⁅R,L⁆ N) :=
  ⟨toLieModuleHom⟩

/--
Instance `hasCoeToLinearEquiv` / 实例 `hasCoeToLinearEquiv`

English:
instance hasCoeToLinearEquiv
  signature: : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N)
  body: ⟨toLinearEquiv⟩

中文:
实例 hasCoeToLinearEquiv
  签名: : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N)
  定义体: ⟨toLinearEquiv⟩

Depends on / 依赖: toLinearEquiv
-/
instance hasCoeToLinearEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) :=
  ⟨toLinearEquiv⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (M ≃ₗ⁅R,L⁆ N) M N
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

中文:
实例 :
  签名: EquivLike (M ≃ₗ⁅R,L⁆ N) M N
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

Depends on / 依赖: f.toFun
-/
instance : EquivLike (M ≃ₗ⁅R,L⁆ N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

/--
lemma `coe_coe` / 引理 `coe_coe`

English:
lemma coe_coe
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: ⇑(e : M ->ₗ⁅R,L⁆ N) = e
  proof: rfl

中文:
引理 coe_coe
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: ⇑(e : M ->ₗ⁅R,L⁆ N) = e
  证明: rfl
-/
@[simp] lemma coe_coe (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M ->ₗ⁅R,L⁆ N) = e := rfl

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: Function.Injective e
  proof: e.toEquiv.injective

中文:
定理 injective
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: Function.Injective e
  证明: e.toEquiv.injective

Depends on / 依赖: e.toEquiv.injective, injective, toEquiv
-/
theorem injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injective e :=
  e.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: Function.Surjective e
  proof: e.toEquiv.surjective

@[simp]

中文:
定理 surjective
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: Function.Surjective e
  证明: e.toEquiv.surjective

@[simp]

Depends on / 依赖: e.toEquiv.surjective, surjective, toEquiv
-/
theorem surjective (e : M ≃ₗ⁅R,L⁆ N) : Function.Surjective e :=
  e.toEquiv.surjective

@[simp]
/--
theorem `toEquiv_mk` / 定理 `toEquiv_mk`

English:
theorem toEquiv_mk
  given: (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ h₂)
  proof: rfl

@[simp]

中文:
定理 toEquiv_mk
  条件: (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ h₂)
  证明: rfl

@[simp]
-/
theorem toEquiv_mk (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ h₂) :
    toEquiv (mk f g h₁ h₂ : M ≃ₗ⁅R,L⁆ N) = Equiv.mk f g h₁ h₂ :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : M ->ₗ⁅R,L⁆ N) (invFun h₁ h₂)
  proof: rfl

中文:
定理 coe_mk
  条件: (f : M ->ₗ⁅R,L⁆ N) (invFun h₁ h₂)
  证明: rfl
-/
theorem coe_mk (f : M ->ₗ⁅R,L⁆ N) (invFun h₁ h₂) :
    ((⟨f, invFun, h₁, h₂⟩ : M ≃ₗ⁅R,L⁆ N) : M -> N) = f :=
  rfl

/--
theorem `coe_toLieModuleHom` / 定理 `coe_toLieModuleHom`

English:
theorem coe_toLieModuleHom
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: ⇑(e : M ->ₗ⁅R,L⁆ N) = e
  proof: rfl

@[simp]

中文:
定理 coe_toLieModuleHom
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: ⇑(e : M ->ₗ⁅R,L⁆ N) = e
  证明: rfl

@[simp]
-/
theorem coe_toLieModuleHom (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M ->ₗ⁅R,L⁆ N) = e :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: ((e : M ≃ₗ[R] N) : M -> N) = e
  proof: rfl

中文:
定理 coe_toLinearEquiv
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: ((e : M ≃ₗ[R] N) : M -> N) = e
  证明: rfl
-/
theorem coe_toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M -> N) = e :=
  rfl

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) -> M ≃ N)
  proof: by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

@[ext]

中文:
定理 toEquiv_injective
  结论: Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) -> M ≃ N)
  证明: by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

@[ext]

Depends on / 依赖: f_inv, g_inv
-/
theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) -> M ≃ N) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : forall m, e₁ m = e₂ m)
  statement: e₁ = e₂
  proof: toEquiv_injective (Equiv.ext h)

中文:
定理 ext
  条件: (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : 对任意 m, e₁ m = e₂ m)
  结论: e₁ = e₂
  证明: toEquiv_injective (Equiv.ext h)

Depends on / 依赖: Equiv.ext, toEquiv_injective
-/
theorem ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : forall m, e₁ m = e₂ m) : e₁ = e₂ :=
  toEquiv_injective (Equiv.ext h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearEquivClass (M ≃ₗ⁅R,L⁆ N) R M N
  body: by
    rw [← coe_toLinearEquiv]; rw [map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_smul]; rw [RingHom.id_apply]

中文:
实例 :
  签名: LinearEquivClass (M ≃ₗ⁅R,L⁆ N) R M N
  定义体: by
    rw [← coe_toLinearEquiv]; rw [map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_smul]; rw [RingHom.id_apply]

Depends on / 依赖: RingHom, RingHom.id_apply, coe_toLinearEquiv, id_apply, map_add, map_smul
-/
instance : LinearEquivClass (M ≃ₗ⁅R,L⁆ N) R M N where
  map_add _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv]; rw [map_smul]; rw [RingHom.id_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (M ≃ₗ⁅R,L⁆ M)
  body: ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := rfl }⟩

@[simp]

中文:
实例 :
  签名: One (M ≃ₗ⁅R,L⁆ M)
  定义体: ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := rfl }⟩

@[simp]

Depends on / 依赖: map_lie
-/
instance : One (M ≃ₗ⁅R,L⁆ M) :=
  ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := rfl }⟩

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (m : M)
  statement: (1 : M ≃ₗ⁅R,L⁆ M) m = m
  proof: rfl

中文:
定理 one_apply
  条件: (m : M)
  结论: (1 : M ≃ₗ⁅R,L⁆ M) m = m
  证明: rfl
-/
theorem one_apply (m : M) : (1 : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ≃ₗ⁅R,L⁆ M)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (M ≃ₗ⁅R,L⁆ M)
  定义体: ⟨1⟩
-/
instance : Inhabited (M ≃ₗ⁅R,L⁆ M) :=
  ⟨1⟩

/-- Lie module equivalences are reflexive. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M ≃ₗ⁅R,L⁆ M
  body: 1

@[simp]

中文:
定义 refl
  签名: : M ≃ₗ⁅R,L⁆ M
  定义体: 1

@[simp]
-/
def refl : M ≃ₗ⁅R,L⁆ M :=
  1

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (m : M)
  statement: (refl : M ≃ₗ⁅R,L⁆ M) m = m
  proof: rfl

中文:
定理 refl_apply
  条件: (m : M)
  结论: (refl : M ≃ₗ⁅R,L⁆ M) m = m
  证明: rfl
-/
theorem refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl

/-- Lie module equivalences are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : M ≃ₗ⁅R,L⁆ N)
  body: { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }

@[simp]

中文:
定义 symm
  签名: (e : M ≃ₗ⁅R,L⁆ N)
  定义体: { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }

@[simp]

Depends on / 依赖: LieModuleHom, LieModuleHom.inverse, e.invFun, e.left_inv, e.right_inv, e.toLieModuleHom, invFun, inverse, left_inv, right_inv, toLieModuleHom
-/
def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
  { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: forall x, e (e.symm x) = x
  proof: e.toLinearEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toLinearEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toLinearEquiv.apply_symm_apply, toLinearEquiv
-/
theorem apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : forall x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: forall x, e.symm (e x) = x
  proof: e.toLinearEquiv.symm_apply_apply

中文:
定理 symm_apply_apply
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toLinearEquiv.symm_apply_apply

Depends on / 依赖: e.toLinearEquiv.symm_apply_apply, symm_apply_apply, toLinearEquiv
-/
theorem symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : forall x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N)
  statement: e.symm n = m ↔ n = e m
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N)
  结论: e.symm n = m ↔ n = e m
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : e.symm n = m ↔ n = e m :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N)
  statement: m = e.symm n ↔ e m = n
  proof: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

中文:
定理 eq_symm_apply
  条件: {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N)
  结论: m = e.symm n ↔ e m = n
  证明: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : m = e.symm n ↔ e m = n :=
  e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/--
theorem `apply_eq_iff_eq_symm_apply` / 定理 `apply_eq_iff_eq_symm_apply`

English:
theorem apply_eq_iff_eq_symm_apply
  given: {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N)
  proof: e.eq_symm_apply.symm

@[simp]

中文:
定理 apply_eq_iff_eq_symm_apply
  条件: {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N)
  证明: e.eq_symm_apply.symm

@[simp]

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) :
    e m = n ↔ m = e.symm n :=
  e.eq_symm_apply.symm

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective :
    Function.Bijective (LieModuleEquiv.symm : (M ≃ₗ⁅R,L⁆ N) -> N ≃ₗ⁅R,L⁆ M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- Lie module equivalences are transitive. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P)
  body: { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]

中文:
定义 trans
  签名: (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P)
  定义体: { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]

Depends on / 依赖: LieModuleHom, LieModuleHom.comp, LinearEquiv, LinearEquiv.trans, toLieModuleHom, toLinearEquiv
-/
def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
  { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M)
  statement: (e₁.trans e₂) m = e₂ (e₁ m)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M)
  结论: (e₁.trans e₂) m = e₂ (e₁ m)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) : (e₁.trans e₂) m = e₂ (e₁ m) :=
  rfl

@[simp]
/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P)
  proof: rfl

@[simp]

中文:
定理 symm_trans
  条件: (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P)
  证明: rfl

@[simp]
-/
theorem symm_trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: e.trans e.symm = refl
  proof: ext _ _ e.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: e.trans e.symm = refl
  证明: ext _ _ e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (e : M ≃ₗ⁅R,L⁆ N) : e.trans e.symm = refl :=
  ext _ _ e.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : M ≃ₗ⁅R,L⁆ N)
  statement: e.symm.trans e = refl
  proof: ext _ _ e.apply_symm_apply

中文:
定理 symm_trans_self
  条件: (e : M ≃ₗ⁅R,L⁆ N)
  结论: e.symm.trans e = refl
  证明: ext _ _ e.apply_symm_apply

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self (e : M ≃ₗ⁅R,L⁆ N) : e.symm.trans e = refl :=
  ext _ _ e.apply_symm_apply

end LieModuleEquiv

end LieModuleMorphisms
