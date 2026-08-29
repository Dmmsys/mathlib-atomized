/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Quotients of Lie algebras and Lie modules

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `LieSubmodule.Quotient.lieQuotientLieModule`
  * `LieSubmodule.Quotient.lieQuotientLieAlgebra`

## Tags

lie algebra, quotient
-/

@[expose] public section


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
variable (N N' : LieSubmodule R L M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasQuotient M (LieSubmodule R L M)
  body: ⟨fun N => M ⧸ N.toSubmodule⟩

中文:
实例 :
  签名: HasQuotient M (LieSubmodule R L M)
  定义体: ⟨fun N => M ⧸ N.toSubmodule⟩

Depends on / 依赖: N.toSubmodule, toSubmodule
-/
instance : HasQuotient M (LieSubmodule R L M) :=
  ⟨fun N => M ⧸ N.toSubmodule⟩

namespace Quotient

variable {N}

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup (M ⧸ N)
  body: Submodule.Quotient.addCommGroup _

中文:
实例 addCommGroup
  签名: : AddCommGroup (M ⧸ N)
  定义体: Submodule.Quotient.addCommGroup _

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.addCommGroup, addCommGroup
-/
instance addCommGroup : AddCommGroup (M ⧸ N) :=
  Submodule.Quotient.addCommGroup _

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  body: Submodule.Quotient.module' _

中文:
实例 module'
  签名: {S : 类型} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  定义体: Submodule.Quotient.module' _

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.module, module
-/
instance module' {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (M ⧸ N) :=
  Submodule.Quotient.module' _

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module R (M ⧸ N)
  body: Submodule.Quotient.module _

中文:
实例 module
  签名: : Module R (M ⧸ N)
  定义体: Submodule.Quotient.module _

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.module, module
-/
instance module : Module R (M ⧸ N) :=
  Submodule.Quotient.module _

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  body: Submodule.Quotient.isCentralScalar _

中文:
实例 isCentralScalar
  签名: {S : 类型} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  定义体: Submodule.Quotient.isCentralScalar _

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.isCentralScalar, isCentralScalar
-/
instance isCentralScalar {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    [SMul Sᵐᵒᵖ R] [Module Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (M ⧸ N) :=
  Submodule.Quotient.isCentralScalar _

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (M ⧸ N)
  body: ⟨0⟩

中文:
实例 inhabited
  签名: : Inhabited (M ⧸ N)
  定义体: ⟨0⟩
-/
instance inhabited : Inhabited (M ⧸ N) :=
  ⟨0⟩

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: : M -> M ⧸ N
  body: Submodule.Quotient.mk

@[simp]

中文:
缩写 mk
  签名: : M -> M ⧸ N
  定义体: Submodule.Quotient.mk

@[simp]

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk
-/
abbrev mk : M -> M ⧸ N :=
  Submodule.Quotient.mk

@[simp]
/--
theorem `mk_eq_zero'` / 定理 `mk_eq_zero'`

English:
theorem mk_eq_zero'
  given: {m : M}
  statement: mk (N := N) m = 0 ↔ m in N
  proof: Submodule.Quotient.mk_eq_zero N.toSubmodule

中文:
定理 mk_eq_zero'
  条件: {m : M}
  结论: mk (N := N) m = 0 ↔ m in N
  证明: Submodule.Quotient.mk_eq_zero N.toSubmodule
-/
theorem mk_eq_zero' {m : M} : mk (N := N) m = 0 ↔ m in N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule

/--
theorem `is_quotient_mk` / 定理 `is_quotient_mk`

English:
theorem is_quotient_mk
  given: (m : M)
  statement: Quotient.mk'' m = (mk m : M ⧸ N)
  proof: rfl

中文:
定理 is_quotient_mk
  条件: (m : M)
  结论: Quotient.mk'' m = (mk m : M ⧸ N)
  证明: rfl
-/
theorem is_quotient_mk (m : M) : Quotient.mk'' m = (mk m : M ⧸ N) :=
  rfl

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lieSubmoduleInvariant` / `lieSubmoduleInvariant` 的定义

English:
definition lieSubmoduleInvariant
  signature: : L ->ₗ[R] Submodule.compatibleMaps N.toSubmodule N.toSubmodule
  body: LinearMap.codRestrict _ (LieModule.toEnd R L M) fun _ _ => N.lie_mem

中文:
定义 lieSubmoduleInvariant
  签名: : L ->ₗ[R] Submodule.compatibleMaps N.toSubmodule N.toSubmodule
  定义体: LinearMap.codRestrict _ (LieModule.toEnd R L M) fun _ _ => N.lie_mem

Depends on / 依赖: LieModule, LieModule.toEnd, LinearMap, LinearMap.codRestrict, N.lie_mem, codRestrict, lie_mem
-/
def lieSubmoduleInvariant : L ->ₗ[R] Submodule.compatibleMaps N.toSubmodule N.toSubmodule :=
  LinearMap.codRestrict _ (LieModule.toEnd R L M) fun _ _ => N.lie_mem

variable (N)

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `actionAsEndoMap` / `actionAsEndoMap` 的定义

English:
definition actionAsEndoMap
  signature: : L ->ₗ⁅R⁆ Module.End R (M ⧸ N)
  body: { LinearMap.comp (Submodule.mapQLinear (N : Submodule R M) (N : Submodule R M))
      lieSubmoduleInvariant with
    map_lie' := fun {_ _} =>
Submodule.linearMap_qext _ LinearMap.ext fun _ => congr_arg mk lie_lie _ _ _ }

中文:
定义 actionAsEndoMap
  签名: : L ->ₗ⁅R⁆ Module.End R (M ⧸ N)
  定义体: { LinearMap.comp (Submodule.mapQLinear (N : Submodule R M) (N : Submodule R M))
      lieSubmoduleInvariant with
    map_lie' := fun {_ _} =>
Submodule.linearMap_qext _ LinearMap.ext fun _ => congr_arg mk lie_lie _ _ _ }

Depends on / 依赖: LinearMap, LinearMap.comp, LinearMap.ext, Submodule, Submodule.linearMap_qext, Submodule.mapQLinear, congr_arg, lieSubmoduleInvariant, lie_lie, linearMap_qext, mapQLinear, map_lie
-/
def actionAsEndoMap : L ->ₗ⁅R⁆ Module.End R (M ⧸ N) :=
  { LinearMap.comp (Submodule.mapQLinear (N : Submodule R M) (N : Submodule R M))
      lieSubmoduleInvariant with
    map_lie' := fun {_ _} =>
Submodule.linearMap_qext _ LinearMap.ext fun _ => congr_arg mk lie_lie _ _ _ }

/--
Instance `actionAsEndoMapBracket` / 实例 `actionAsEndoMapBracket`

English:
instance actionAsEndoMapBracket
  signature: : Bracket L (M ⧸ N)
  body: ⟨fun x n => actionAsEndoMap N x n⟩

中文:
实例 actionAsEndoMapBracket
  签名: : Bracket L (M ⧸ N)
  定义体: ⟨fun x n => actionAsEndoMap N x n⟩

Depends on / 依赖: actionAsEndoMap
-/
instance actionAsEndoMapBracket : Bracket L (M ⧸ N) :=
  ⟨fun x n => actionAsEndoMap N x n⟩

/--
Instance `lieQuotientLieRingModule` / 实例 `lieQuotientLieRingModule`

English:
instance lieQuotientLieRingModule
  signature: : LieRingModule L (M ⧸ N)
  body: { LieRingModule.compLieHom _ (actionAsEndoMap N) with bracket := Bracket.bracket }

中文:
实例 lieQuotientLieRingModule
  签名: : LieRingModule L (M ⧸ N)
  定义体: { LieRingModule.compLieHom _ (actionAsEndoMap N) with bracket := Bracket.bracket }

Depends on / 依赖: Bracket, Bracket.bracket, LieRingModule, LieRingModule.compLieHom, actionAsEndoMap, bracket, compLieHom
-/
instance lieQuotientLieRingModule : LieRingModule L (M ⧸ N) :=
  { LieRingModule.compLieHom _ (actionAsEndoMap N) with bracket := Bracket.bracket }

/--
Instance `lieQuotientLieModule` / 实例 `lieQuotientLieModule`

English:
instance lieQuotientLieModule
  signature: : LieModule R L (M ⧸ N)
  body: LieModule.compLieHom _ (actionAsEndoMap N)

中文:
实例 lieQuotientLieModule
  签名: : LieModule R L (M ⧸ N)
  定义体: LieModule.compLieHom _ (actionAsEndoMap N)

Depends on / 依赖: LieModule, LieModule.compLieHom, actionAsEndoMap, compLieHom
-/
instance lieQuotientLieModule : LieModule R L (M ⧸ N) :=
  LieModule.compLieHom _ (actionAsEndoMap N)

/--
Instance `lieQuotientHasBracket` / 实例 `lieQuotientHasBracket`

English:
instance lieQuotientHasBracket
  signature: : Bracket (L ⧸ I) (L ⧸ I)
  body: ⟨by
    intro x y
    apply Quotient.liftOn₂' x y fun x' y' => mk ⁅x', y'⁆
    intro x₁ x₂ y₁ y₂ h₁ h₂
    apply (Submodule.Quotient.eq I.toSubmodule).2
    rw [Submodule.quotientRel_def] at h₁ h₂
    have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by
      simp [-lie_skew, sub_eq_ad

中文:
实例 lieQuotientHasBracket
  签名: : Bracket (L ⧸ I) (L ⧸ I)
  定义体: ⟨by
    intro x y
    apply Quotient.liftOn₂' x y fun x' y' => mk ⁅x', y'⁆
    intro x₁ x₂ y₁ y₂ h₁ h₂
    apply (Submodule.Quotient.eq I.toSubmodule).2
    rw [Submodule.quotientRel_def] at h₁ h₂
    have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by
      simp [-lie_skew, sub_eq_ad

Depends on / 依赖: I.toSubmodule, Quotient, Quotient.liftOn, RingHomInvPair, Submodule, Submodule.Quotient.eq, Submodule.add_mem, Submodule.quotientRel_def, add_assoc, add_mem, lie_mem_left, lie_mem_right, lie_skew, quotientRel_def, sub_eq_add_neg, toSubmodule
-/
instance lieQuotientHasBracket : Bracket (L ⧸ I) (L ⧸ I) :=
  ⟨by
    intro x y
    apply Quotient.liftOn₂' x y fun x' y' => mk ⁅x', y'⁆
    intro x₁ x₂ y₁ y₂ h₁ h₂
    apply (Submodule.Quotient.eq I.toSubmodule).2
    rw [Submodule.quotientRel_def] at h₁ h₂
    have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by
      simp [-lie_skew, sub_eq_add_neg, add_assoc]
    rw [h]
    apply Submodule.add_mem
    · apply lie_mem_right R L I x₁ (x₂ - y₂) h₂
    · apply lie_mem_left R L I (x₁ - y₁) y₂ h₁⟩

@[simp]
/--
theorem `mk_bracket` / 定理 `mk_bracket`

English:
theorem mk_bracket
  given: (x y : L)
  statement: mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆
  proof: rfl

中文:
定理 mk_bracket
  条件: (x y : L)
  结论: mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆
  证明: rfl
-/
theorem mk_bracket (x y : L) : mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆ :=
  rfl

/--
Instance `lieQuotientLieRing` / 实例 `lieQuotientLieRing`

English:
instance lieQuotientLieRing
  signature: : LieRing (L ⧸ I) where
  body: by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply add_lie
  lie_add x' y' z' := by
    induction x', y', z' using 

中文:
实例 lieQuotientLieRing
  签名: : LieRing (L ⧸ I) where
  定义体: by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply add_lie
  lie_add x' y' z' := by
    induction x', y', z' using 

Depends on / 依赖: Quotient, Quotient.inductionOn, Submodule, Submodule.Quotient.mk_add, add_lie, congr_arg, inductionOn, is_quotient_mk, lie_add, lie_self, mk_add, mk_bracket, repeat
-/
instance lieQuotientLieRing : LieRing (L ⧸ I) where
  add_lie x' y' z' := by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply add_lie
  lie_add x' y' z' := by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply lie_add
  lie_self x' := by
    induction x' using Quotient.inductionOn' with | _ x
    rw [is_quotient_mk]; rw [← mk_bracket]
    apply congr_arg; apply lie_self
  leibniz_lie x' y' z' := by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply leibniz_lie

/--
Instance `lieQuotientLieAlgebra` / 实例 `lieQuotientLieAlgebra`

English:
instance lieQuotientLieAlgebra
  signature: : LieAlgebra R (L ⧸ I) where
  body: by
    induction x', y' using Quotient.inductionOn₂' with | _ x y
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_smul (R := R) (M := L)]
    apply congr_arg; apply lie_smul

中文:
实例 lieQuotientLieAlgebra
  签名: : LieAlgebra R (L ⧸ I) where
  定义体: by
    induction x', y' using Quotient.inductionOn₂' with | _ x y
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_smul (R := R) (M := L)]
    apply congr_arg; apply lie_smul

Depends on / 依赖: Quotient, Quotient.inductionOn, Submodule, Submodule.Quotient.mk_smul, congr_arg, is_quotient_mk, lie_smul, mk_bracket, mk_smul, repeat
-/
instance lieQuotientLieAlgebra : LieAlgebra R (L ⧸ I) where
  lie_smul t x' y' := by
    induction x', y' using Quotient.inductionOn₂' with | _ x y
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_smul (R := R) (M := L)]
    apply congr_arg; apply lie_smul

/-- `LieSubmodule.Quotient.mk` as a `LieModuleHom`. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: : M ->ₗ⁅R,L⁆ M ⧸ N
  body: { N.toSubmodule.mkQ with
    toFun := mk
    map_lie' := fun {_ _} => rfl }

@[simp]

中文:
定义 mk'
  签名: : M ->ₗ⁅R,L⁆ M ⧸ N
  定义体: { N.toSubmodule.mkQ with
    toFun := mk
    map_lie' := fun {_ _} => rfl }

@[simp]

Depends on / 依赖: N.toSubmodule.mkQ, map_lie, toSubmodule
-/
def mk' : M ->ₗ⁅R,L⁆ M ⧸ N :=
  { N.toSubmodule.mkQ with
    toFun := mk
    map_lie' := fun {_ _} => rfl }

@[simp]
/--
theorem `surjective_mk'` / 定理 `surjective_mk'`

English:
theorem surjective_mk'
  statement: Function.Surjective (mk' N)
  proof: Quot.mk_surjective

@[simp]

中文:
定理 surjective_mk'
  结论: Function.Surjective (mk' N)
  证明: Quot.mk_surjective

@[simp]

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem surjective_mk' : Function.Surjective (mk' N) := Quot.mk_surjective

@[simp]
/--
theorem `range_mk'` / 定理 `range_mk'`

English:
theorem range_mk'
  statement: LieModuleHom.range (mk' N) = ⊤
  proof: by
  simp [LieModuleHom.range_eq_top]

中文:
定理 range_mk'
  结论: LieModuleHom.range (mk' N) = ⊤
  证明: by
  simp [LieModuleHom.range_eq_top]

Depends on / 依赖: LieModuleHom, LieModuleHom.range_eq_top, range_eq_top
-/
theorem range_mk' : LieModuleHom.range (mk' N) = ⊤ := by
  simp [LieModuleHom.range_eq_top]

/--
Instance `isNoetherian` / 实例 `isNoetherian`

English:
instance isNoetherian
  signature: [IsNoetherian R M]
  body: inferInstanceAs (IsNoetherian R (M ⧸ (N : Submodule R M)))

中文:
实例 isNoetherian
  签名: [IsNoetherian R M]
  定义体: inferInstanceAs (IsNoetherian R (M ⧸ (N : Submodule R M)))

Depends on / 依赖: IsNoetherian, Submodule
-/
instance isNoetherian [IsNoetherian R M] : IsNoetherian R (M ⧸ N) :=
  inferInstanceAs (IsNoetherian R (M ⧸ (N : Submodule R M)))

/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {m : M}
  statement: mk' N m = 0 ↔ m in N
  proof: Submodule.Quotient.mk_eq_zero N.toSubmodule

@[simp]

中文:
定理 mk_eq_zero
  条件: {m : M}
  结论: mk' N m = 0 ↔ m in N
  证明: Submodule.Quotient.mk_eq_zero N.toSubmodule

@[simp]

Depends on / 依赖: N.toSubmodule, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, mk_eq_zero, toSubmodule
-/
theorem mk_eq_zero {m : M} : mk' N m = 0 ↔ m in N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule

@[simp]
/--
theorem `mk'_ker` / 定理 `mk'_ker`

English:
theorem mk'_ker
  statement: (mk' N).ker = N
  proof: by ext; simp

@[simp]

中文:
定理 mk'_ker
  结论: (mk' N).ker = N
  证明: by ext; simp

@[simp]
-/
theorem mk'_ker : (mk' N).ker = N := by ext; simp

@[simp]
/--
theorem `map_mk'_eq_bot_le` / 定理 `map_mk'_eq_bot_le`

English:
theorem map_mk'_eq_bot_le
  statement: map (mk' N) N' = ⊥ ↔ N' <= N
  proof: by
  rw [← LieModuleHom.le_ker_iff_map]; rw [mk'_ker]

中文:
定理 map_mk'_eq_bot_le
  结论: map (mk' N) N' = ⊥ ↔ N' <= N
  证明: by
  rw [← LieModuleHom.le_ker_iff_map]; rw [mk'_ker]

Depends on / 依赖: LieModuleHom, LieModuleHom.le_ker_iff_map, _ker, le_ker_iff_map
-/
theorem map_mk'_eq_bot_le : map (mk' N) N' = ⊥ ↔ N' <= N := by
  rw [← LieModuleHom.le_ker_iff_map]; rw [mk'_ker]

/-- Two `LieModuleHom`s from a quotient lie module are equal if their compositions with
`LieSubmodule.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `lieModuleHom_ext` / 定理 `lieModuleHom_ext`

English:
theorem lieModuleHom_ext
  given: ⦃f g
  statement: M ⧸ N ->ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g
  proof: LieModuleHom.ext fun x => Quotient.inductionOn' x LieModuleHom.congr_fun h

中文:
定理 lieModuleHom_ext
  条件: ⦃f g
  结论: M ⧸ N ->ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g
  证明: LieModuleHom.ext fun x => Quotient.inductionOn' x LieModuleHom.congr_fun h

Depends on / 依赖: LieModuleHom, LieModuleHom.congr_fun, LieModuleHom.ext, Quotient, Quotient.inductionOn, congr_fun, inductionOn
-/
theorem lieModuleHom_ext ⦃f g : M ⧸ N ->ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
LieModuleHom.ext fun x => Quotient.inductionOn' x LieModuleHom.congr_fun h

/--
lemma `toEnd_comp_mk'` / 引理 `toEnd_comp_mk'`

English:
lemma toEnd_comp_mk'
  given: (x : L)
  proof: rfl

中文:
引理 toEnd_comp_mk'
  条件: (x : L)
  证明: rfl
-/
lemma toEnd_comp_mk' (x : L) :
    LieModule.toEnd R L (M ⧸ N) x ∘ₗ mk' N = mk' N ∘ₗ LieModule.toEnd R L M x :=
  rfl

end Quotient

end LieSubmodule

namespace LieHom

variable {R L L' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L ->ₗ⁅R⁆ L')

set_option backward.isDefEq.respectTransparency false in
/-- The first isomorphism theorem for morphisms of Lie algebras. -/
@[simps]
/--
Definition of `quotKerEquivRange` / `quotKerEquivRange` 的定义

English:
definition quotKerEquivRange
  signature: : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range
  body: { (f : L ->ₗ[R] L').quotKerEquivRange with
    toFun := (f : L ->ₗ[R] L').quotKerEquivRange
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on
      induction y using Submodule.Quotient.induction_on
      rw [← SetLike.coe_eq_coe]; rw [LieSubalgebra.coe_bracke

中文:
定义 quotKerEquivRange
  签名: : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range
  定义体: { (f : L ->ₗ[R] L').quotKerEquivRange with
    toFun := (f : L ->ₗ[R] L').quotKerEquivRange
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on
      induction y using Submodule.Quotient.induction_on
      rw [← SetLike.coe_eq_coe]; rw [LieSubalgebra.coe_bracke

Depends on / 依赖: LieSubalgebra, LieSubalgebra.coe_bracket, LieSubmodule, LieSubmodule.Quotient.mk_bracket, LinearMap, LinearMap.quotKerEquivRange_apply_mk, Quotient, SetLike, SetLike.coe_eq_coe, Submodule, Submodule.Quotient.induction_on, coe_bracket, coe_eq_coe, coe_toLinearMap, f.range, induction_on, map_lie, mk_bracket, quotKerEquivRange, quotKerEquivRange_apply_mk
-/
noncomputable def quotKerEquivRange : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range :=
  { (f : L ->ₗ[R] L').quotKerEquivRange with
    toFun := (f : L ->ₗ[R] L').quotKerEquivRange
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on
      induction y using Submodule.Quotient.induction_on
      rw [← SetLike.coe_eq_coe]; rw [LieSubalgebra.coe_bracket f.range]
      simp only [← LieSubmodule.Quotient.mk_bracket, LinearMap.quotKerEquivRange_apply_mk,
        coe_toLinearMap, map_lie] }

end LieHom
