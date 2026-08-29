/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `LieSubalgebra`
  * `LieSubalgebra.incl`
  * `LieSubalgebra.map`
  * `LieHom.range`
  * `LieEquiv.ofInjective`
  * `LieEquiv.ofEq`
  * `LieEquiv.ofSubalgebras`

## Tags

lie algebra, lie subalgebra
-/

@[expose] public section


universe u v w w₁ w₂

section LieSubalgebra

open Set

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/--
Definition of `LieSubalgebra` / `LieSubalgebra` 的定义

English:
structure LieSubalgebra
  parameters: extends Submodule R L
  extends: Submodule R L
  axioms and operations (1):
    - lie_mem' : forall {x y}, x in carrier -> y in carrier -> ⁅x, y⁆ in carrier

中文:
结构 Lie子代数
  参数: extends 子模 R L
  继承: 子模 R L
  公理与运算 (1 个):
    - lie_mem' : 对任意 {x y}, x in carrier -> y in carrier -> ⁅x, y⁆ in carrier
-/
structure LieSubalgebra extends Submodule R L where
  /-- A Lie subalgebra is closed under Lie bracket. -/
  lie_mem' : forall {x y}, x in carrier -> y in carrier -> ⁅x, y⁆ in carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (LieSubalgebra R L)
  body: ⟨⟨0, @fun x y hx _hy => by
    rw [(Submodule.mem_bot R).1 hx]; rw [zero_lie]
    exact Submodule.zero_mem 0⟩⟩

中文:
实例 :
  签名: 零 (Lie子代数 R L)
  定义体: ⟨⟨0, @fun x y hx _hy => by
    rw [(Submodule.mem_bot R).1 hx]; rw [zero_lie]
    exact Submodule.zero_mem 0⟩⟩

Depends on / 依赖: Submodule, Submodule.mem_bot, Submodule.zero_mem, mem_bot, zero_lie, zero_mem
-/
instance : Zero (LieSubalgebra R L) :=
  ⟨⟨0, @fun x y hx _hy => by
    rw [(Submodule.mem_bot R).1 hx]; rw [zero_lie]
    exact Submodule.zero_mem 0⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LieSubalgebra R L)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (Lie子代数 R L)
  定义体: ⟨0⟩
-/
instance : Inhabited (LieSubalgebra R L) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (LieSubalgebra R L) (Submodule R L)
  body: ⟨LieSubalgebra.toSubmodule⟩

中文:
实例 :
  签名: Coe (Lie子代数 R L) (子模 R L)
  定义体: ⟨LieSubalgebra.toSubmodule⟩

Depends on / 依赖: LieSubalgebra, LieSubalgebra.toSubmodule, toSubmodule
-/
instance : Coe (LieSubalgebra R L) (Submodule R L) :=
  ⟨LieSubalgebra.toSubmodule⟩

namespace LieSubalgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (LieSubalgebra R L) L
  body: L'.carrier
  coe_injective L' L'' h := by
    rcases L' with ⟨⟨⟩⟩
    rcases L'' with ⟨⟨⟩⟩
    congr
    exact SetLike.coe_injective h

中文:
实例 :
  签名: 集合状 (Lie子代数 R L) L
  定义体: L'.carrier
  coe_injective L' L'' h := by
    rcases L' with ⟨⟨⟩⟩
    rcases L'' with ⟨⟨⟩⟩
    congr
    exact SetLike.coe_injective h

Depends on / 依赖: carrier
-/
instance : SetLike (LieSubalgebra R L) L where
  coe L' := L'.carrier
  coe_injective L' L'' h := by
    rcases L' with ⟨⟨⟩⟩
    rcases L'' with ⟨⟨⟩⟩
    congr
    exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (LieSubalgebra R L)
  body: .ofSetLike (LieSubalgebra R L) L

中文:
实例 :
  签名: 偏序 (Lie子代数 R L)
  定义体: .ofSetLike (LieSubalgebra R L) L

Depends on / 依赖: LieSubalgebra, ofSetLike
-/
instance : PartialOrder (LieSubalgebra R L) := .ofSetLike (LieSubalgebra R L) L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSubgroupClass (LieSubalgebra R L) L
  body: Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x in (L' : Submodule R L) from neg_mem hx

中文:
实例 :
  签名: 加法子群类 (Lie子代数 R L) L
  定义体: Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x in (L' : Submodule R L) from neg_mem hx

Depends on / 依赖: Submodule, Submodule.add_mem, add_mem
-/
instance : AddSubgroupClass (LieSubalgebra R L) L where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x in (L' : Submodule R L) from neg_mem hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulMemClass (LieSubalgebra R L) R L
  body: SMulMemClass.smul_mem (s := s.toSubmodule)

中文:
实例 :
  签名: SMulMem类 (Lie子代数 R L) R L
  定义体: SMulMemClass.smul_mem (s := s.toSubmodule)

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, s.toSubmodule, smul_mem, toSubmodule
-/
instance : SMulMemClass (LieSubalgebra R L) R L where
  smul_mem {s} := SMulMemClass.smul_mem (s := s.toSubmodule)

/--
Instance `lieRing` / 实例 `lieRing`

English:
instance lieRing
  signature: (L' : LieSubalgebra R L)
  body: ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add := by
    intros
    apply SetCoe.ext
    apply lie_add
  add_lie := by
    intros
    apply SetCoe.ext
    apply add_lie
  lie_self := by
    intros
    apply SetCoe.ext
    apply lie_self
  leibniz_lie := by
    intros
    apply SetCoe.

中文:
实例 lieRing
  签名: (L' : Lie子代数 R L)
  定义体: ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add := by
    intros
    apply SetCoe.ext
    apply lie_add
  add_lie := by
    intros
    apply SetCoe.ext
    apply add_lie
  lie_self := by
    intros
    apply SetCoe.ext
    apply lie_self
  leibniz_lie := by
    intros
    apply SetCoe.

Depends on / 依赖: lie_mem, property, x.property, x.val, y.property, y.val
-/
instance lieRing (L' : LieSubalgebra R L) : LieRing L' where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add := by
    intros
    apply SetCoe.ext
    apply lie_add
  add_lie := by
    intros
    apply SetCoe.ext
    apply add_lie
  lie_self := by
    intros
    apply SetCoe.ext
    apply lie_self
  leibniz_lie := by
    intros
    apply SetCoe.ext
    apply leibniz_lie

section

variable {R₁ : Type*} [Semiring R₁]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L'
  body: L'.toSubmodule.module'

中文:
实例 [标量乘法
  签名: R₁ R] [模 R₁ L] [标量塔 R₁ R L] (L'
  定义体: L'.toSubmodule.module'

Depends on / 依赖: module, toSubmodule, toSubmodule.module
-/
instance [SMul R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L' : LieSubalgebra R L) : Module R₁ L' :=
  L'.toSubmodule.module'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R₁ R] [SMul R₁ᵐᵒᵖ R] [Module R₁ L] [Module R₁ᵐᵒᵖ L] [IsScalarTower R₁ R L]
  body: L'.toSubmodule.isCentralScalar

中文:
实例 [标量乘法
  签名: R₁ R] [标量乘法 R₁ᵐᵒᵖ R] [模 R₁ L] [模 R₁ᵐᵒᵖ L] [标量塔 R₁ R L]
  定义体: L'.toSubmodule.isCentralScalar

Depends on / 依赖: isCentralScalar, toSubmodule, toSubmodule.isCentralScalar
-/
instance [SMul R₁ R] [SMul R₁ᵐᵒᵖ R] [Module R₁ L] [Module R₁ᵐᵒᵖ L] [IsScalarTower R₁ R L]
    [IsScalarTower R₁ᵐᵒᵖ R L] [IsCentralScalar R₁ L] (L' : LieSubalgebra R L) :
    IsCentralScalar R₁ L' :=
  L'.toSubmodule.isCentralScalar

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L'
  body: L'.toSubmodule.isScalarTower

中文:
实例 [标量乘法
  签名: R₁ R] [模 R₁ L] [标量塔 R₁ R L] (L'
  定义体: L'.toSubmodule.isScalarTower

Depends on / 依赖: isScalarTower, toSubmodule, toSubmodule.isScalarTower
-/
instance [SMul R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L' : LieSubalgebra R L) :
    IsScalarTower R₁ R L' :=
  L'.toSubmodule.isScalarTower

instance (L' : LieSubalgebra R L) [IsNoetherian R L] : IsNoetherian R L' :=
  isNoetherian_submodule' _

instance (L' : LieSubalgebra R L) [IsArtinian R L] : IsArtinian R L' :=
  isArtinian_submodule' _

end

/--
Instance `lieAlgebra` / 实例 `lieAlgebra`

English:
instance lieAlgebra
  signature: (L' : LieSubalgebra R L)
  body: by
    { intros
      apply SetCoe.ext
      apply lie_smul }

中文:
实例 lieAlgebra
  签名: (L' : Lie子代数 R L)
  定义体: by
    { intros
      apply SetCoe.ext
      apply lie_smul }

Depends on / 依赖: SetCoe, SetCoe.ext, intros, lie_smul
-/
instance lieAlgebra (L' : LieSubalgebra R L) : LieAlgebra R L' where
  lie_smul := by
    { intros
      apply SetCoe.ext
      apply lie_smul }

variable {R L}
variable (L' : LieSubalgebra R L)

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : L) in L'
  proof: zero_mem L'

中文:
定理 zero_mem
  结论: (0 : L) in L'
  证明: zero_mem L'
-/
protected theorem zero_mem : (0 : L) in L' :=
  zero_mem L'

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: {x y : L}
  statement: x in L' -> y in L' -> (x + y : L) in L'
  proof: add_mem

中文:
定理 add_mem
  条件: {x y : L}
  结论: x in L' -> y in L' -> (x + y : L) in L'
  证明: add_mem
-/
protected theorem add_mem {x y : L} : x in L' -> y in L' -> (x + y : L) in L' :=
  add_mem

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  given: {x y : L}
  statement: x in L' -> y in L' -> (x - y : L) in L'
  proof: sub_mem

中文:
定理 sub_mem
  条件: {x y : L}
  结论: x in L' -> y in L' -> (x - y : L) in L'
  证明: sub_mem
-/
protected theorem sub_mem {x y : L} : x in L' -> y in L' -> (x - y : L) in L' :=
  sub_mem

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: (t : R) {x : L} (h : x in L')
  statement: t • x in L'
  proof: SMulMemClass.smul_mem _ h

中文:
定理 smul_mem
  条件: (t : R) {x : L} (h : x in L')
  结论: t • x in L'
  证明: SMulMemClass.smul_mem _ h
-/
protected theorem smul_mem (t : R) {x : L} (h : x in L') : t • x in L' :=
  SMulMemClass.smul_mem _ h

/--
theorem `lie_mem` / 定理 `lie_mem`

English:
theorem lie_mem
  given: {x y : L} (hx : x in L') (hy : y in L')
  statement: (⁅x, y⁆ : L) in L'
  proof: L'.lie_mem' hx hy

中文:
定理 lie_mem
  条件: {x y : L} (hx : x in L') (hy : y in L')
  结论: (⁅x, y⁆ : L) in L'
  证明: L'.lie_mem' hx hy

Depends on / 依赖: lie_mem
-/
theorem lie_mem {x y : L} (hx : x in L') (hy : y in L') : (⁅x, y⁆ : L) in L' :=
  L'.lie_mem' hx hy

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {x : L}
  statement: x in L'.carrier ↔ x in (L' : Set L)
  proof: Iff.rfl

中文:
定理 mem_carrier
  条件: {x : L}
  结论: x in L'.carrier ↔ x in (L' : 集合 L)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {x : L} : x in L'.carrier ↔ x in (L' : Set L) :=
  Iff.rfl

/--
theorem `mem_mk_iff` / 定理 `mem_mk_iff`

English:
theorem mem_mk_iff
  given: (S : Set L) (h₁ h₂ h₃ h₄) {x : L}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk_iff
  条件: (S : 集合 L) (h₁ h₂ h₃ h₄) {x : L}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x in (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalgebra R L) ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `mem_toSubmodule` / 定理 `mem_toSubmodule`

English:
theorem mem_toSubmodule
  given: {x : L}
  statement: x in (L' : Submodule R L) ↔ x in L'
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmodule
  条件: {x : L}
  结论: x in (L' : 子模 R L) ↔ x in L'
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmodule {x : L} : x in (L' : Submodule R L) ↔ x in L' :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk_iff'` / 定理 `mem_mk_iff'`

English:
theorem mem_mk_iff'
  given: (p : Submodule R L) (h) {x : L}
  proof: Iff.rfl

中文:
定理 mem_mk_iff'
  条件: (p : 子模 R L) (h) {x : L}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff' (p : Submodule R L) (h) {x : L} :
    x in (⟨p, h⟩ : LieSubalgebra R L) ↔ x in p :=
  Iff.rfl

/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {x : L}
  statement: x in (L' : Set L) ↔ x in L'
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_coe
  条件: {x : L}
  结论: x in (L' : 集合 L) ↔ x in L'
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {x : L} : x in (L' : Set L) ↔ x in L' :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_bracket` / 定理 `coe_bracket`

English:
theorem coe_bracket
  given: (x y : L')
  statement: (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆
  proof: rfl

中文:
定理 coe_bracket
  条件: (x y : L')
  结论: (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆
  证明: rfl
-/
theorem coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ :=
  rfl

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (x y : L')
  statement: x = y ↔ (x : L) = y
  proof: Subtype.ext_iff

中文:
定理 ext_iff
  条件: (x y : L')
  结论: x = y ↔ (x : L) = y
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem ext_iff (x y : L') : x = y ↔ (x : L) = y :=
  Subtype.ext_iff

/--
theorem `coe_zero_iff_zero` / 定理 `coe_zero_iff_zero`

English:
theorem coe_zero_iff_zero
  given: (x : L')
  statement: (x : L) = 0 ↔ x = 0
  proof: (ext_iff L' x 0).symm

@[ext]

中文:
定理 coe_zero_iff_zero
  条件: (x : L')
  结论: (x : L) = 0 ↔ x = 0
  证明: (ext_iff L' x 0).symm

@[ext]

Depends on / 依赖: ext_iff
-/
theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 :=
  (ext_iff L' x 0).symm

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in L₁' ↔ x in L₂')
  statement: L₁' = L₂'
  proof: SetLike.ext h

中文:
定理 ext
  条件: (L₁' L₂' : Lie子代数 R L) (h : 对任意 x, x in L₁' ↔ x in L₂')
  结论: L₁' = L₂'
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in L₁' ↔ x in L₂') : L₁' = L₂' :=
  SetLike.ext h

/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  given: (L₁' L₂' : LieSubalgebra R L)
  statement: L₁' = L₂' ↔ forall x, x in L₁' ↔ x in L₂'
  proof: SetLike.ext_iff

@[simp]

中文:
定理 ext_iff'
  条件: (L₁' L₂' : Lie子代数 R L)
  结论: L₁' = L₂' ↔ 对任意 x, x in L₁' ↔ x in L₂'
  证明: SetLike.ext_iff

@[simp]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem ext_iff' (L₁' L₂' : LieSubalgebra R L) : L₁' = L₂' ↔ forall x, x in L₁' ↔ x in L₂' :=
  SetLike.ext_iff

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (S : Set L) (h₁ h₂ h₃ h₄)
  proof: rfl

中文:
定理 mk_coe
  条件: (S : 集合 L) (h₁ h₂ h₃ h₄)
  证明: rfl
-/
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalgebra R L) : Set L) = S :=
  rfl

/--
theorem `toSubmodule_mk` / 定理 `toSubmodule_mk`

English:
theorem toSubmodule_mk
  given: (p : Submodule R L) (h)
  proof: rfl

中文:
定理 toSubmodule_mk
  条件: (p : 子模 R L) (h)
  证明: rfl

Depends on / 依赖: LieSubalgebra, Submodule
-/
theorem toSubmodule_mk (p : Submodule R L) (h) :
    (({ p with lie_mem' := h } : LieSubalgebra R L) : Submodule R L) = p := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : LieSubalgebra R L -> Set L)
  proof: SetLike.coe_injective

@[norm_cast]

中文:
定理 coe_injective
  结论: 函数.单射 ((↑) : Lie子代数 R L -> 集合 L)
  证明: SetLike.coe_injective

@[norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective ((↑) : LieSubalgebra R L -> Set L) :=
  SetLike.coe_injective

@[norm_cast]
/--
theorem `coe_set_eq` / 定理 `coe_set_eq`

English:
theorem coe_set_eq
  given: (L₁' L₂' : LieSubalgebra R L)
  statement: (L₁' : Set L) = L₂' ↔ L₁' = L₂'
  proof: SetLike.coe_set_eq

中文:
定理 coe_set_eq
  条件: (L₁' L₂' : Lie子代数 R L)
  结论: (L₁' : 集合 L) = L₂' ↔ L₁' = L₂'
  证明: SetLike.coe_set_eq

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
theorem coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq

/--
theorem `toSubmodule_injective` / 定理 `toSubmodule_injective`

English:
theorem toSubmodule_injective
  statement: Function.Injective ((↑) : LieSubalgebra R L -> Submodule R L)
  proof: fun L₁' L₂' h => by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]

中文:
定理 toSubmodule_injective
  结论: 函数.单射 ((↑) : Lie子代数 R L -> 子模 R L)
  证明: fun L₁' L₂' h => by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext, _iff, coe_set_eq
-/
theorem toSubmodule_injective : Function.Injective ((↑) : LieSubalgebra R L -> Submodule R L) :=
  fun L₁' L₂' h => by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]
/--
theorem `toSubmodule_inj` / 定理 `toSubmodule_inj`

English:
theorem toSubmodule_inj
  given: (L₁' L₂' : LieSubalgebra R L)
  proof: toSubmodule_injective.eq_iff

中文:
定理 toSubmodule_inj
  条件: (L₁' L₂' : Lie子代数 R L)
  证明: toSubmodule_injective.eq_iff

Depends on / 依赖: eq_iff, toSubmodule_injective, toSubmodule_injective.eq_iff
-/
theorem toSubmodule_inj (L₁' L₂' : LieSubalgebra R L) :
    (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂' :=
  toSubmodule_injective.eq_iff

/--
theorem `coe_toSubmodule` / 定理 `coe_toSubmodule`

English:
theorem coe_toSubmodule
  statement: ((L' : Submodule R L) : Set L) = L'
  proof: rfl

中文:
定理 coe_toSubmodule
  结论: ((L' : 子模 R L) : 集合 L) = L'
  证明: rfl
-/
theorem coe_toSubmodule : ((L' : Submodule R L) : Set L) = L' :=
  rfl

section LieModule

variable {M : Type w} [AddCommGroup M] [LieRingModule L M]
variable {N : Type w₁} [AddCommGroup N] [LieRingModule L N] [Module R N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bracket L' M
  body: ⁅(x : L), m⁆

@[simp]

中文:
实例 :
  签名: Bracket L' M
  定义体: ⁅(x : L), m⁆

@[simp]
-/
instance : Bracket L' M where
  bracket x m := ⁅(x : L), m⁆

@[simp]
/--
theorem `coe_bracket_of_module` / 定理 `coe_bracket_of_module`

English:
theorem coe_bracket_of_module
  given: (x : L') (m : M)
  statement: ⁅x, m⁆ = ⁅(x : L), m⁆
  proof: rfl

中文:
定理 coe_bracket_of_module
  条件: (x : L') (m : M)
  结论: ⁅x, m⁆ = ⁅(x : L), m⁆
  证明: rfl
-/
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLieTower L' L M
  body: leibniz_lie x.val y m

中文:
实例 :
  签名: 是LieTower L' L M
  定义体: leibniz_lie x.val y m

Depends on / 依赖: leibniz_lie, x.val
-/
instance : IsLieTower L' L M where
  leibniz_lie x y m := leibniz_lie x.val y m

/--
Instance `lieRingModule` / 实例 `lieRingModule`

English:
instance lieRingModule
  signature: : LieRingModule L' M where
  body: add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

中文:
实例 lieRingModule
  签名: : Lie环模 L' M where
  定义体: add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

Depends on / 依赖: add_lie
-/
instance lieRingModule : LieRingModule L' M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

variable [Module R M]

/--
Instance `lieModule` / 实例 `lieModule`

English:
instance lieModule
  signature: [LieModule R L M]
  body: by
    rw [coe_bracket_of_module]; rw [Submodule.coe_smul_of_tower]; rw [smul_lie]; rw [coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

中文:
实例 lieModule
  签名: [Lie模 R L M]
  定义体: by
    rw [coe_bracket_of_module]; rw [Submodule.coe_smul_of_tower]; rw [smul_lie]; rw [coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

Depends on / 依赖: Submodule, Submodule.coe_smul_of_tower, coe_bracket_of_module, coe_smul_of_tower, lie_smul, smul_lie
-/
instance lieModule [LieModule R L M] : LieModule R L' M where
  smul_lie t x m := by
    rw [coe_bracket_of_module]; rw [Submodule.coe_smul_of_tower]; rw [smul_lie]; rw [coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

/--
Definition of `_root_.LieModuleHom.restrictLie` / `_root_.LieModuleHom.restrictLie` 的定义

English:
definition _root_.LieModuleHom.restrictLie
  signature: (f : M ->ₗ⁅R,L⁆ N) (L' : LieSubalgebra R L)
  body: { (f : M ->ₗ[R] N) with map_lie' := @fun x m => f.map_lie (↑x) m }

@[simp]

中文:
定义 _root_.Lie模态射.restrictLie
  签名: (f : M ->ₗ⁅R,L⁆ N) (L' : Lie子代数 R L)
  定义体: { (f : M ->ₗ[R] N) with map_lie' := @fun x m => f.map_lie (↑x) m }

@[simp]

Depends on / 依赖: f.map_lie, map_lie
-/
def _root_.LieModuleHom.restrictLie (f : M ->ₗ⁅R,L⁆ N) (L' : LieSubalgebra R L) : M ->ₗ⁅R,L'⁆ N :=
  { (f : M ->ₗ[R] N) with map_lie' := @fun x m => f.map_lie (↑x) m }

@[simp]
/--
theorem `_root_.LieModuleHom.coe_restrictLie` / 定理 `_root_.LieModuleHom.coe_restrictLie`

English:
theorem _root_.LieModuleHom.coe_restrictLie
  given: (f : M ->ₗ⁅R,L⁆ N)
  statement: ⇑(f.restrictLie L') = f
  proof: rfl

中文:
定理 _root_.Lie模态射.coe_restrictLie
  条件: (f : M ->ₗ⁅R,L⁆ N)
  结论: ⇑(f.restrictLie L') = f
  证明: rfl
-/
theorem _root_.LieModuleHom.coe_restrictLie (f : M ->ₗ⁅R,L⁆ N) : ⇑(f.restrictLie L') = f :=
  rfl

end LieModule

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : L' ->ₗ⁅R⁆ L
  body: { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]

中文:
定义 incl
  签名: : L' ->ₗ⁅R⁆ L
  定义体: { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]

Depends on / 依赖: Submodule, map_lie, subtype
-/
def incl : L' ->ₗ⁅R⁆ L :=
  { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]
/--
theorem `coe_incl` / 定理 `coe_incl`

English:
theorem coe_incl
  statement: ⇑L'.incl = ((↑) : L' -> L)
  proof: rfl

中文:
定理 coe_incl
  结论: ⇑L'.incl = ((↑) : L' -> L)
  证明: rfl
-/
theorem coe_incl : ⇑L'.incl = ((↑) : L' -> L) :=
  rfl

/--
Definition of `incl'` / `incl'` 的定义

English:
definition incl'
  signature: : L' ->ₗ⁅R,L'⁆ L
  body: { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]

中文:
定义 incl'
  签名: : L' ->ₗ⁅R,L'⁆ L
  定义体: { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]

Depends on / 依赖: Submodule, map_lie, subtype
-/
def incl' : L' ->ₗ⁅R,L'⁆ L :=
  { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]
/--
theorem `coe_incl'` / 定理 `coe_incl'`

English:
theorem coe_incl'
  statement: ⇑L'.incl' = ((↑) : L' -> L)
  proof: rfl

中文:
定理 coe_incl'
  结论: ⇑L'.incl' = ((↑) : L' -> L)
  证明: rfl
-/
theorem coe_incl' : ⇑L'.incl' = ((↑) : L' -> L) :=
  rfl

end LieSubalgebra

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]
variable (f : L ->ₗ⁅R⁆ L₂)

namespace LieHom

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: : LieSubalgebra R L₂
  body: { LinearMap.range (f : L ->ₗ[R] L₂) with
      lie_mem' := by
        rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨⁅x, y⁆, f.map_lie x y⟩ }

@[simp]

中文:
定义 range
  签名: : Lie子代数 R L₂
  定义体: { LinearMap.range (f : L ->ₗ[R] L₂) with
      lie_mem' := by
        rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨⁅x, y⁆, f.map_lie x y⟩ }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range, f.map_lie, lie_mem, map_lie
-/
def range : LieSubalgebra R L₂ :=
  { LinearMap.range (f : L ->ₗ[R] L₂) with
      lie_mem' := by
        rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨⁅x, y⁆, f.map_lie x y⟩ }

@[simp]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  statement: (f.range : Set L₂) = Set.range f
  proof: LinearMap.coe_range (f : L ->ₗ[R] L₂)

@[simp]

中文:
定理 coe_range
  结论: (f.range : 集合 L₂) = 集合.range f
  证明: LinearMap.coe_range (f : L ->ₗ[R] L₂)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.coe_range, coe_range
-/
theorem coe_range : (f.range : Set L₂) = Set.range f :=
  LinearMap.coe_range (f : L ->ₗ[R] L₂)

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: (x : L₂)
  statement: x in f.range ↔ exists y : L, f y = x
  proof: LinearMap.mem_range

中文:
定理 mem_range
  条件: (x : L₂)
  结论: x in f.range ↔ 存在 y : L, f y = x
  证明: LinearMap.mem_range

Depends on / 依赖: LinearMap, LinearMap.mem_range, mem_range
-/
theorem mem_range (x : L₂) : x in f.range ↔ exists y : L, f y = x :=
  LinearMap.mem_range

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (x : L)
  statement: f x in f.range
  proof: LinearMap.mem_range_self (f : L ->ₗ[R] L₂) x

中文:
定理 mem_range_self
  条件: (x : L)
  结论: f x in f.range
  证明: LinearMap.mem_range_self (f : L ->ₗ[R] L₂) x

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, mem_range_self
-/
theorem mem_range_self (x : L) : f x in f.range :=
  LinearMap.mem_range_self (f : L ->ₗ[R] L₂) x

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
definition rangeRestrict
  signature: : L ->ₗ⁅R⁆ f.range
  body: { (f : L ->ₗ[R] L₂).rangeRestrict with
    map_lie' := @fun x y => by
      apply Subtype.ext
      exact f.map_lie x y }

@[simp]

中文:
定义 rangeRestrict
  签名: : L ->ₗ⁅R⁆ f.range
  定义体: { (f : L ->ₗ[R] L₂).rangeRestrict with
    map_lie' := @fun x y => by
      apply Subtype.ext
      exact f.map_lie x y }

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, f.map_lie, map_lie, rangeRestrict
-/
def rangeRestrict : L ->ₗ⁅R⁆ f.range :=
  { (f : L ->ₗ[R] L₂).rangeRestrict with
    map_lie' := @fun x y => by
      apply Subtype.ext
      exact f.map_lie x y }

@[simp]
/--
theorem `rangeRestrict_apply` / 定理 `rangeRestrict_apply`

English:
theorem rangeRestrict_apply
  given: (x : L)
  statement: f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩
  proof: rfl

中文:
定理 rangeRestrict_apply
  条件: (x : L)
  结论: f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩
  证明: rfl
-/
theorem rangeRestrict_apply (x : L) : f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩ :=
  rfl

/--
theorem `surjective_rangeRestrict` / 定理 `surjective_rangeRestrict`

English:
theorem surjective_rangeRestrict
  statement: Function.Surjective f.rangeRestrict
  proof: by
  rintro ⟨y, hy⟩
  rw [mem_range] at hy; obtain ⟨x, rfl⟩ := hy
  use x
  simp only [rangeRestrict_apply]

中文:
定理 surjective_rangeRestrict
  结论: 函数.满射 f.rangeRestrict
  证明: by
  rintro ⟨y, hy⟩
  rw [mem_range] at hy; obtain ⟨x, rfl⟩ := hy
  use x
  simp only [rangeRestrict_apply]

Depends on / 依赖: mem_range, rangeRestrict_apply
-/
theorem surjective_rangeRestrict : Function.Surjective f.rangeRestrict := by
  rintro ⟨y, hy⟩
  rw [mem_range] at hy; obtain ⟨x, rfl⟩ := hy
  use x
  simp only [rangeRestrict_apply]

/--
Definition of `equivRangeOfInjective` / `equivRangeOfInjective` 的定义

English:
definition equivRangeOfInjective
  signature: (h : Function.Injective f)
  body: LieEquiv.ofBijective f.rangeRestrict
    ⟨fun x y hxy => by
      simp only [Subtype.mk_eq_mk, rangeRestrict_apply] at hxy
      exact h hxy, f.surjective_rangeRestrict⟩

@[simp]

中文:
定义 equivRangeOfInjective
  签名: (h : 函数.单射 f)
  定义体: LieEquiv.ofBijective f.rangeRestrict
    ⟨fun x y hxy => by
      simp only [Subtype.mk_eq_mk, rangeRestrict_apply] at hxy
      exact h hxy, f.surjective_rangeRestrict⟩

@[simp]

Depends on / 依赖: LieEquiv, LieEquiv.ofBijective, Subtype, Subtype.mk_eq_mk, f.rangeRestrict, f.surjective_rangeRestrict, mk_eq_mk, ofBijective, rangeRestrict, rangeRestrict_apply, surjective_rangeRestrict
-/
noncomputable def equivRangeOfInjective (h : Function.Injective f) : L ≃ₗ⁅R⁆ f.range :=
  LieEquiv.ofBijective f.rangeRestrict
    ⟨fun x y hxy => by
      simp only [Subtype.mk_eq_mk, rangeRestrict_apply] at hxy
      exact h hxy, f.surjective_rangeRestrict⟩

@[simp]
/--
theorem `equivRangeOfInjective_apply` / 定理 `equivRangeOfInjective_apply`

English:
theorem equivRangeOfInjective_apply
  given: (h : Function.Injective f) (x : L)
  proof: rfl

中文:
定理 equivRangeOfInjective_apply
  条件: (h : 函数.单射 f) (x : L)
  证明: rfl
-/
theorem equivRangeOfInjective_apply (h : Function.Injective f) (x : L) :
    f.equivRangeOfInjective h x = ⟨f x, mem_range_self f x⟩ :=
  rfl

end LieHom

/--
theorem `Submodule.exists_lieSubalgebra_coe_eq_iff` / 定理 `Submodule.exists_lieSubalgebra_coe_eq_iff`

English:
theorem Submodule.exists_lieSubalgebra_coe_eq_iff
  given: (p : Submodule R L)
  proof: by
  constructor
  · rintro ⟨K, rfl⟩ _ _
    exact K.lie_mem'
  · intro h
    use { p with lie_mem' := h _ _ }

中文:
定理 子模.存在_lieSubalgebra_coe_eq_iff
  条件: (p : 子模 R L)
  证明: by
  constructor
  · rintro ⟨K, rfl⟩ _ _
    exact K.lie_mem'
  · intro h
    use { p with lie_mem' := h _ _ }

Depends on / 依赖: K.lie_mem, lie_mem
-/
theorem Submodule.exists_lieSubalgebra_coe_eq_iff (p : Submodule R L) :
    (exists K : LieSubalgebra R L, ↑K = p) ↔ forall x y : L, x in p -> y in p -> ⁅x, y⁆ in p := by
  constructor
  · rintro ⟨K, rfl⟩ _ _
    exact K.lie_mem'
  · intro h
    use { p with lie_mem' := h _ _ }

namespace LieSubalgebra

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

@[simp]
/--
theorem `incl_range` / 定理 `incl_range`

English:
theorem incl_range
  statement: K.incl.range = K
  proof: by
  rw [← toSubmodule_inj]
  exact (K : Submodule R L).range_subtype

中文:
定理 incl_range
  结论: K.incl.range = K
  证明: by
  rw [← toSubmodule_inj]
  exact (K : Submodule R L).range_subtype

Depends on / 依赖: Submodule, range_subtype, toSubmodule_inj
-/
theorem incl_range : K.incl.range = K := by
  rw [← toSubmodule_inj]
  exact (K : Submodule R L).range_subtype

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : LieSubalgebra R L₂
  body: { (K : Submodule R L).map (f : L ->ₗ[R] L₂) with
    lie_mem' {x y} hx hy := by
      simp only [AddSubsemigroup.mem_carrier] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      simpa using ⟨⁅x', y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩ }

@[simp]

中文:
定义 map
  签名: : Lie子代数 R L₂
  定义体: { (K : Submodule R L).map (f : L ->ₗ[R] L₂) with
    lie_mem' {x y} hx hy := by
      simp only [AddSubsemigroup.mem_carrier] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      simpa using ⟨⁅x', y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩ }

@[simp]

Depends on / 依赖: AddSubsemigroup, AddSubsemigroup.mem_carrier, K.lie_mem, Submodule, f.map_lie, lie_mem, map_lie, mem_carrier
-/
def map : LieSubalgebra R L₂ :=
  { (K : Submodule R L).map (f : L ->ₗ[R] L₂) with
    lie_mem' {x y} hx hy := by
      simp only [AddSubsemigroup.mem_carrier] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      simpa using ⟨⁅x', y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩ }

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (x : L₂)
  statement: x in K.map f ↔ exists y : L, y in K ∧ f y = x
  proof: Submodule.mem_map

中文:
定理 mem_map
  条件: (x : L₂)
  结论: x in K.map f ↔ 存在 y : L, y in K ∧ f y = x
  证明: Submodule.mem_map

Depends on / 依赖: Submodule, Submodule.mem_map, mem_map
-/
theorem mem_map (x : L₂) : x in K.map f ↔ exists y : L, y in K ∧ f y = x :=
  Submodule.mem_map

-- TODO Rename and state for homs instead of equivs.
/--
theorem `mem_map_submodule` / 定理 `mem_map_submodule`

English:
theorem mem_map_submodule
  given: (e : L ≃ₗ⁅R⁆ L₂) (x : L₂)
  proof: Iff.rfl

中文:
定理 mem_map_submodule
  条件: (e : L ≃ₗ⁅R⁆ L₂) (x : L₂)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (x : L₂) :
    x in K.map (e : L ->ₗ⁅R⁆ L₂) ↔ x in (K : Submodule R L).map (e : L ->ₗ[R] L₂) :=
  Iff.rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: : LieSubalgebra R L
  body: { (K₂ : Submodule R L₂).comap (f : L ->ₗ[R] L₂) with
    lie_mem' := @fun x y hx hy => by
      suffices ⁅f x, f y⁆ in K₂ by simp [this]
      exact K₂.lie_mem hx hy }

中文:
定义 comap
  签名: : Lie子代数 R L
  定义体: { (K₂ : Submodule R L₂).comap (f : L ->ₗ[R] L₂) with
    lie_mem' := @fun x y hx hy => by
      suffices ⁅f x, f y⁆ in K₂ by simp [this]
      exact K₂.lie_mem hx hy }

Depends on / 依赖: Submodule, lie_mem
-/
def comap : LieSubalgebra R L :=
  { (K₂ : Submodule R L₂).comap (f : L ->ₗ[R] L₂) with
    lie_mem' := @fun x y hx hy => by
      suffices ⁅f x, f y⁆ in K₂ by simp [this]
      exact K₂.lie_mem hx hy }

/--
lemma `mem_comap` / 引理 `mem_comap`

English:
lemma mem_comap
  given: {x : L}
  statement: x in K₂.comap f ↔ f x in K₂
  proof: Iff.rfl

中文:
引理 mem_comap
  条件: {x : L}
  结论: x in K₂.comap f ↔ f x in K₂
  证明: Iff.rfl
-/
@[simp] lemma mem_comap {x : L} : x in K₂.comap f ↔ f x in K₂ := Iff.rfl

/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (hf : Function.Injective f)
  body: Submodule.equivMapOfInjective f.toLinearMap hf K
  map_lie' {x y} := by
    ext
    change f ⁅(x : L), (y : L)⁆ = ⁅f (x : L), f (y : L)⁆
    simp

中文:
定义 equivMapOfInjective
  签名: (hf : 函数.单射 f)
  定义体: Submodule.equivMapOfInjective f.toLinearMap hf K
  map_lie' {x y} := by
    ext
    change f ⁅(x : L), (y : L)⁆ = ⁅f (x : L), f (y : L)⁆
    simp
-/
@[simps!] noncomputable def equivMapOfInjective (hf : Function.Injective f) :
    K ≃ₗ⁅R⁆ K.map f where
  __ := Submodule.equivMapOfInjective f.toLinearMap hf K
  map_lie' {x y} := by
    ext
    change f ⁅(x : L), (y : L)⁆ = ⁅f (x : L), f (y : L)⁆
    simp

section LatticeStructure

open Set

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (LieSubalgebra R L)
  body: { PartialOrder.lift ((↑) : LieSubalgebra R L -> Set L) coe_injective with
    le := fun N N' => forall ⦃x⦄, x in N -> x in N' }

中文:
实例 :
  签名: 偏序 (Lie子代数 R L)
  定义体: { PartialOrder.lift ((↑) : LieSubalgebra R L -> Set L) coe_injective with
    le := fun N N' => forall ⦃x⦄, x in N -> x in N' }

Depends on / 依赖: LieSubalgebra, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (LieSubalgebra R L) :=
  { PartialOrder.lift ((↑) : LieSubalgebra R L -> Set L) coe_injective with
    le := fun N N' => forall ⦃x⦄, x in N -> x in N' }

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: K <= K' ↔ (K : Set L) subseteq K'
  proof: Iff.rfl

@[simp]

中文:
定理 le_def
  结论: K <= K' ↔ (K : 集合 L) subseteq K'
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem le_def : K <= K' ↔ (K : Set L) subseteq K' :=
  Iff.rfl

@[simp]
/--
theorem `toSubmodule_le_toSubmodule` / 定理 `toSubmodule_le_toSubmodule`

English:
theorem toSubmodule_le_toSubmodule
  statement: (K : Submodule R L) <= K' ↔ K <= K'
  proof: Iff.rfl

中文:
定理 toSubmodule_le_toSubmodule
  结论: (K : 子模 R L) <= K' ↔ K <= K'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toSubmodule_le_toSubmodule : (K : Submodule R L) <= K' ↔ K <= K' :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (LieSubalgebra R L)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 底元素 (Lie子代数 R L)
  定义体: ⟨0⟩

@[simp]
-/
instance : Bot (LieSubalgebra R L) :=
  ⟨0⟩

@[simp]
/--
theorem `bot_coe` / 定理 `bot_coe`

English:
theorem bot_coe
  statement: ((⊥ : LieSubalgebra R L) : Set L) = {0}
  proof: rfl

@[simp]

中文:
定理 bot_coe
  结论: ((⊥ : Lie子代数 R L) : 集合 L) = {0}
  证明: rfl

@[simp]
-/
theorem bot_coe : ((⊥ : LieSubalgebra R L) : Set L) = {0} :=
  rfl

@[simp]
/--
theorem `bot_toSubmodule` / 定理 `bot_toSubmodule`

English:
theorem bot_toSubmodule
  statement: ((⊥ : LieSubalgebra R L) : Submodule R L) = ⊥
  proof: rfl

中文:
定理 bot_toSubmodule
  结论: ((⊥ : Lie子代数 R L) : 子模 R L) = ⊥
  证明: rfl
-/
theorem bot_toSubmodule : ((⊥ : LieSubalgebra R L) : Submodule R L) = ⊥ :=
  rfl

/--
lemma `toSubmodule_eq_bot` / 引理 `toSubmodule_eq_bot`

English:
lemma toSubmodule_eq_bot
  given: (K : LieSubalgebra R L)
  statement: K.toSubmodule = ⊥ ↔ K = ⊥
  proof: by
  simp [← toSubmodule_inj]

@[simp]

中文:
引理 toSubmodule_eq_bot
  条件: (K : Lie子代数 R L)
  结论: K.toSubmodule = ⊥ ↔ K = ⊥
  证明: by
  simp [← toSubmodule_inj]

@[simp]
-/
@[simp] lemma toSubmodule_eq_bot (K : LieSubalgebra R L) : K.toSubmodule = ⊥ ↔ K = ⊥ := by
  simp [← toSubmodule_inj]

@[simp]
/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: (x : L)
  statement: x in (⊥ : LieSubalgebra R L) ↔ x = 0
  proof: mem_singleton_iff

中文:
定理 mem_bot
  条件: (x : L)
  结论: x in (⊥ : Lie子代数 R L) ↔ x = 0
  证明: mem_singleton_iff

Depends on / 依赖: mem_singleton_iff
-/
theorem mem_bot (x : L) : x in (⊥ : LieSubalgebra R L) ↔ x = 0 :=
  mem_singleton_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (LieSubalgebra R L)
  body: ⟨{ (⊤ : Submodule R L) with lie_mem' := @fun x y _ _ => mem_univ ⁅x, y⁆ }⟩

@[simp]

中文:
实例 :
  签名: 顶元素 (Lie子代数 R L)
  定义体: ⟨{ (⊤ : Submodule R L) with lie_mem' := @fun x y _ _ => mem_univ ⁅x, y⁆ }⟩

@[simp]

Depends on / 依赖: Submodule, lie_mem, mem_univ
-/
instance : Top (LieSubalgebra R L) :=
  ⟨{ (⊤ : Submodule R L) with lie_mem' := @fun x y _ _ => mem_univ ⁅x, y⁆ }⟩

@[simp]
/--
theorem `top_coe` / 定理 `top_coe`

English:
theorem top_coe
  statement: ((⊤ : LieSubalgebra R L) : Set L) = univ
  proof: rfl

@[simp]

中文:
定理 top_coe
  结论: ((⊤ : Lie子代数 R L) : 集合 L) = univ
  证明: rfl

@[simp]
-/
theorem top_coe : ((⊤ : LieSubalgebra R L) : Set L) = univ :=
  rfl

@[simp]
/--
theorem `top_toSubmodule` / 定理 `top_toSubmodule`

English:
theorem top_toSubmodule
  statement: ((⊤ : LieSubalgebra R L) : Submodule R L) = ⊤
  proof: rfl

中文:
定理 top_toSubmodule
  结论: ((⊤ : Lie子代数 R L) : 子模 R L) = ⊤
  证明: rfl
-/
theorem top_toSubmodule : ((⊤ : LieSubalgebra R L) : Submodule R L) = ⊤ :=
  rfl

/--
lemma `toSubmodule_eq_top` / 引理 `toSubmodule_eq_top`

English:
lemma toSubmodule_eq_top
  given: (K : LieSubalgebra R L)
  statement: K.toSubmodule = ⊤ ↔ K = ⊤
  proof: by
  simp [← toSubmodule_inj]

@[simp]

中文:
引理 toSubmodule_eq_top
  条件: (K : Lie子代数 R L)
  结论: K.toSubmodule = ⊤ ↔ K = ⊤
  证明: by
  simp [← toSubmodule_inj]

@[simp]
-/
@[simp] lemma toSubmodule_eq_top (K : LieSubalgebra R L) : K.toSubmodule = ⊤ ↔ K = ⊤ := by
  simp [← toSubmodule_inj]

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : L)
  statement: x in (⊤ : LieSubalgebra R L)
  proof: mem_univ x

中文:
定理 mem_top
  条件: (x : L)
  结论: x in (⊤ : Lie子代数 R L)
  证明: mem_univ x

Depends on / 依赖: mem_univ
-/
theorem mem_top (x : L) : x in (⊤ : LieSubalgebra R L) :=
  mem_univ x

/--
theorem `_root_.LieHom.range_eq_map` / 定理 `_root_.LieHom.range_eq_map`

English:
theorem _root_.LieHom.range_eq_map
  statement: f.range = map f ⊤
  proof: by
  ext
  simp

中文:
定理 _root_.Lie态射.range_eq_map
  结论: f.range = map f ⊤
  证明: by
  ext
  simp
-/
theorem _root_.LieHom.range_eq_map : f.range = map f ⊤ := by
  ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (LieSubalgebra R L)
  body: ⟨fun K K' =>
    { (K ⊓ K' : Submodule R L) with
      lie_mem' := fun hx hy => mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2) }⟩

中文:
实例 :
  签名: 最小值 (Lie子代数 R L)
  定义体: ⟨fun K K' =>
    { (K ⊓ K' : Submodule R L) with
      lie_mem' := fun hx hy => mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2) }⟩

Depends on / 依赖: K.lie_mem, Submodule, lie_mem, mem_inter
-/
instance : Min (LieSubalgebra R L) :=
  ⟨fun K K' =>
    { (K ⊓ K' : Submodule R L) with
      lie_mem' := fun hx hy => mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (LieSubalgebra R L)
  body: ⟨fun S =>
    { sInf {(s : Submodule R L) | s in S} with
      lie_mem' := @fun x y hx hy => by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, exists_imp, and_imp] at hx hy ⊢
        intro K hK
        exact K.lie_mem (hx 

中文:
实例 :
  签名: 下确界集 (Lie子代数 R L)
  定义体: ⟨fun S =>
    { sInf {(s : Submodule R L) | s in S} with
      lie_mem' := @fun x y hx hy => by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, exists_imp, and_imp] at hx hy ⊢
        intro K hK
        exact K.lie_mem (hx 

Depends on / 依赖: K.lie_mem, Submodule, Submodule.coe_sInf, Submodule.mem_carrier, and_imp, coe_sInf, exists_imp, lie_mem, mem_carrier, mem_iInter, mem_ofPred_eq
-/
instance : InfSet (LieSubalgebra R L) :=
  ⟨fun S =>
    { sInf {(s : Submodule R L) | s in S} with
      lie_mem' := @fun x y hx hy => by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, exists_imp, and_imp] at hx hy ⊢
        intro K hK
        exact K.lie_mem (hx K hK) (hy K hK) }⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  statement: (↑(K ⊓ K') : Set L) = (K : Set L) inter (K' : Set L)
  proof: rfl

@[simp]

中文:
定理 coe_inf
  结论: (↑(K ⊓ K') : 集合 L) = (K : 集合 L) inter (K' : 集合 L)
  证明: rfl

@[simp]
-/
theorem coe_inf : (↑(K ⊓ K') : Set L) = (K : Set L) inter (K' : Set L) :=
  rfl

@[simp]
/--
theorem `sInf_toSubmodule` / 定理 `sInf_toSubmodule`

English:
theorem sInf_toSubmodule
  given: (S : Set (LieSubalgebra R L))
  proof: rfl

@[simp]

中文:
定理 sInf_toSubmodule
  条件: (S : 集合 (Lie子代数 R L))
  证明: rfl

@[simp]
-/
theorem sInf_toSubmodule (S : Set (LieSubalgebra R L)) :
    (↑(sInf S) : Submodule R L) = sInf {(s : Submodule R L) | s in S} :=
  rfl

@[simp]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (LieSubalgebra R L))
  statement: (↑(sInf S) : Set L) = ⋂ s in S, (s : Set L)
  proof: by
  rw [← coe_toSubmodule]; rw [sInf_toSubmodule]; rw [Submodule.coe_sInf]
  ext x
  simp

中文:
定理 coe_sInf
  条件: (S : 集合 (Lie子代数 R L))
  结论: (↑(sInf S) : 集合 L) = ⋂ s in S, (s : 集合 L)
  证明: by
  rw [← coe_toSubmodule]; rw [sInf_toSubmodule]; rw [Submodule.coe_sInf]
  ext x
  simp

Depends on / 依赖: Submodule, Submodule.coe_sInf, coe_sInf, coe_toSubmodule, sInf_toSubmodule
-/
theorem coe_sInf (S : Set (LieSubalgebra R L)) : (↑(sInf S) : Set L) = ⋂ s in S, (s : Set L) := by
  rw [← coe_toSubmodule]; rw [sInf_toSubmodule]; rw [Submodule.coe_sInf]
  ext x
  simp

/--
theorem `sInf_glb` / 定理 `sInf_glb`

English:
theorem sInf_glb
  given: (S : Set (LieSubalgebra R L))
  statement: IsGLB S (sInf S)
  proof: by
  have h : forall K K' : LieSubalgebra R L, (K : Set L) <= K' ↔ K <= K' := by
    intros
    exact Iff.rfl
  apply IsGLB.of_image @h
  simp only [coe_sInf]
  exact isGLB_biInf

中文:
定理 sInf_glb
  条件: (S : 集合 (Lie子代数 R L))
  结论: IsGLB S (sInf S)
  证明: by
  have h : forall K K' : LieSubalgebra R L, (K : Set L) <= K' ↔ K <= K' := by
    intros
    exact Iff.rfl
  apply IsGLB.of_image @h
  simp only [coe_sInf]
  exact isGLB_biInf

Depends on / 依赖: Iff.rfl, IsGLB.of_image, LieSubalgebra, coe_sInf, intros, isGLB_biInf, of_image
-/
theorem sInf_glb (S : Set (LieSubalgebra R L)) : IsGLB S (sInf S) := by
  have h : forall K K' : LieSubalgebra R L, (K : Set L) <= K' ↔ K <= K' := by
    intros
    exact Iff.rfl
  apply IsGLB.of_image @h
  simp only [coe_sInf]
  exact isGLB_biInf

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (LieSubalgebra R L)
  body: { completeLatticeOfInf _ sInf_glb with
    bot := ⊥
    bot_le := fun N _ h => by
      rw [mem_bot] at h
      rw [h]
      exact N.zero_mem'
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm => ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ => A

中文:
实例 completeLattice
  签名: : 完备格 (Lie子代数 R L)
  定义体: { completeLatticeOfInf _ sInf_glb with
    bot := ⊥
    bot_le := fun N _ h => by
      rw [mem_bot] at h
      rw [h]
      exact N.zero_mem'
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm => ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ => A

Depends on / 依赖: And.left, And.right, N.zero_mem, bot_le, completeLatticeOfInf, inf_le_left, inf_le_right, le_inf, le_top, mem_bot, sInf_glb, zero_mem
-/
instance completeLattice : CompleteLattice (LieSubalgebra R L) :=
  { completeLatticeOfInf _ sInf_glb with
    bot := ⊥
    bot_le := fun N _ h => by
      rw [mem_bot] at h
      rw [h]
      exact N.zero_mem'
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm => ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (LieSubalgebra R L)
  body: max

中文:
实例 :
  签名: 加法 (Lie子代数 R L)
  定义体: max
-/
instance : Add (LieSubalgebra R L) where add := max

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (LieSubalgebra R L)
  body: ⊥

中文:
实例 :
  签名: 零 (Lie子代数 R L)
  定义体: ⊥
-/
instance : Zero (LieSubalgebra R L) where zero := ⊥

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (LieSubalgebra R L) where
  body: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (Lie子代数 R L) where
  定义体: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

Depends on / 依赖: sup_assoc
-/
instance addCommMonoid : AddCommMonoid (LieSubalgebra R L) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (LieSubalgebra R L)
  body: sup_le_sup_right

中文:
实例 :
  签名: 是OrderedAdd幺半群 (Lie子代数 R L)
  定义体: sup_le_sup_right

Depends on / 依赖: sup_le_sup_right
-/
instance : IsOrderedAddMonoid (LieSubalgebra R L) where
  add_le_add_left _ _ := sup_le_sup_right

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedAdd (LieSubalgebra R L)
  body: ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

@[simp]

中文:
实例 :
  签名: 典范有序加法 (Lie子代数 R L)
  定义体: ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

@[simp]

Depends on / 依赖: sup_eq_right
-/
instance : CanonicallyOrderedAdd (LieSubalgebra R L) where
  exists_add_of_le {_a b} h := ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

@[simp]
/--
theorem `add_eq_sup` / 定理 `add_eq_sup`

English:
theorem add_eq_sup
  statement: K + K' = K ⊔ K'
  proof: rfl

@[simp]

中文:
定理 add_eq_sup
  结论: K + K' = K ⊔ K'
  证明: rfl

@[simp]
-/
theorem add_eq_sup : K + K' = K ⊔ K' :=
  rfl

@[simp]
/--
theorem `inf_toSubmodule` / 定理 `inf_toSubmodule`

English:
theorem inf_toSubmodule
  proof: rfl

@[simp]

中文:
定理 inf_toSubmodule
  证明: rfl

@[simp]
-/
theorem inf_toSubmodule :
    (↑(K ⊓ K') : Submodule R L) = (K : Submodule R L) ⊓ (K' : Submodule R L) :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: (x : L)
  statement: x in K ⊓ K' ↔ x in K ∧ x in K'
  proof: by
  rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [inf_toSubmodule]; rw [Submodule.mem_inf]

中文:
定理 mem_inf
  条件: (x : L)
  结论: x in K ⊓ K' ↔ x in K ∧ x in K'
  证明: by
  rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [inf_toSubmodule]; rw [Submodule.mem_inf]

Depends on / 依赖: Submodule, Submodule.mem_inf, inf_toSubmodule, mem_inf, mem_toSubmodule
-/
theorem mem_inf (x : L) : x in K ⊓ K' ↔ x in K ∧ x in K' := by
  rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [inf_toSubmodule]; rw [Submodule.mem_inf]

/--
theorem `eq_bot_iff` / 定理 `eq_bot_iff`

English:
theorem eq_bot_iff
  statement: K = ⊥ ↔ forall x : L, x in K -> x = 0
  proof: by
  rw [_root_.eq_bot_iff]
  exact Iff.rfl

中文:
定理 eq_bot_iff
  结论: K = ⊥ ↔ 对任意 x : L, x in K -> x = 0
  证明: by
  rw [_root_.eq_bot_iff]
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, _root_, _root_.eq_bot_iff, eq_bot_iff
-/
theorem eq_bot_iff : K = ⊥ ↔ forall x : L, x in K -> x = 0 := by
  rw [_root_.eq_bot_iff]
  exact Iff.rfl

/--
Instance `subsingleton_of_bot` / 实例 `subsingleton_of_bot`

English:
instance subsingleton_of_bot
  signature: : Subsingleton (LieSubalgebra R (⊥ : LieSubalgebra R L))
  body: by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩; change x in ⊥ at hx; rw [LieSubalgebra.mem_bot] at hx; subst hx
  simp only [mem_bot, mem_top, iff_true]
  rfl

中文:
实例 subsingleton_of_bot
  签名: : 子单例 (Lie子代数 R (⊥ : Lie子代数 R L))
  定义体: by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩; change x in ⊥ at hx; rw [LieSubalgebra.mem_bot] at hx; subst hx
  simp only [mem_bot, mem_top, iff_true]
  rfl

Depends on / 依赖: LieSubalgebra, LieSubalgebra.mem_bot, iff_true, mem_bot, mem_top, subsingleton_of_bot_eq_top
-/
instance subsingleton_of_bot : Subsingleton (LieSubalgebra R (⊥ : LieSubalgebra R L)) := by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩; change x in ⊥ at hx; rw [LieSubalgebra.mem_bot] at hx; subst hx
  simp only [mem_bot, mem_top, iff_true]
  rfl

/--
theorem `subsingleton_bot` / 定理 `subsingleton_bot`

English:
theorem subsingleton_bot
  statement: Subsingleton (⊥ : LieSubalgebra R L)
  proof: show Subsingleton ((⊥ : LieSubalgebra R L) : Set L) by simp

中文:
定理 subsingleton_bot
  结论: 子单例 (⊥ : Lie子代数 R L)
  证明: show Subsingleton ((⊥ : LieSubalgebra R L) : Set L) by simp

Depends on / 依赖: LieSubalgebra, Subsingleton
-/
theorem subsingleton_bot : Subsingleton (⊥ : LieSubalgebra R L) :=
  show Subsingleton ((⊥ : LieSubalgebra R L) : Set L) by simp

variable {K K'} in
/--
lemma `disjoint_toSubmodule` / 引理 `disjoint_toSubmodule`

English:
lemma disjoint_toSubmodule
  proof: by
  simp [disjoint_iff, ← toSubmodule_inj]

中文:
引理 disjoint_toSubmodule
  证明: by
  simp [disjoint_iff, ← toSubmodule_inj]
-/
@[simp] lemma disjoint_toSubmodule :
    Disjoint (K : Submodule R L) (K' : Submodule R L) ↔ Disjoint K K' := by
  simp [disjoint_iff, ← toSubmodule_inj]

variable (R L)

/--
Instance `wellFoundedGT_of_noetherian` / 实例 `wellFoundedGT_of_noetherian`

English:
instance wellFoundedGT_of_noetherian
  signature: [IsNoetherian R L]
  body: RelHomClass.isWellFounded (⟨toSubmodule, @fun _ _ h => h⟩ : _ ->r (· > ·))

中文:
实例 wellFoundedGT_of_noetherian
  签名: [是Noether R L]
  定义体: RelHomClass.isWellFounded (⟨toSubmodule, @fun _ _ h => h⟩ : _ ->r (· > ·))

Depends on / 依赖: RelHomClass, RelHomClass.isWellFounded, isWellFounded, toSubmodule
-/
instance wellFoundedGT_of_noetherian [IsNoetherian R L] : WellFoundedGT (LieSubalgebra R L) :=
  RelHomClass.isWellFounded (⟨toSubmodule, @fun _ _ h => h⟩ : _ ->r (· > ·))

/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  statement: f.range = LieSubalgebra.map f ⊤
  proof: by ext; simp

中文:
定理 map_top
  结论: f.range = Lie子代数.map f ⊤
  证明: by ext; simp
-/
theorem map_top : f.range = LieSubalgebra.map f ⊤ := by ext; simp

variable {R L K K' f}

section NestedSubalgebras

variable (h : K <= K')

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : K ->ₗ⁅R⁆ K'
  body: { Submodule.inclusion h with map_lie' := @fun _ _ => rfl }

@[simp]

中文:
定义 inclusion
  签名: : K ->ₗ⁅R⁆ K'
  定义体: { Submodule.inclusion h with map_lie' := @fun _ _ => rfl }

@[simp]

Depends on / 依赖: Submodule, Submodule.inclusion, inclusion, map_lie
-/
def inclusion : K ->ₗ⁅R⁆ K' :=
  { Submodule.inclusion h with map_lie' := @fun _ _ => rfl }

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: (x : K)
  statement: (inclusion h x : L) = x
  proof: rfl

中文:
定理 coe_inclusion
  条件: (x : K)
  结论: (inclusion h x : L) = x
  证明: rfl
-/
theorem coe_inclusion (x : K) : (inclusion h x : L) = x :=
  rfl

/--
theorem `inclusion_apply` / 定理 `inclusion_apply`

English:
theorem inclusion_apply
  given: (x : K)
  statement: inclusion h x = ⟨x.1, h x.2⟩
  proof: rfl

中文:
定理 inclusion_apply
  条件: (x : K)
  结论: inclusion h x = ⟨x.1, h x.2⟩
  证明: rfl
-/
theorem inclusion_apply (x : K) : inclusion h x = ⟨x.1, h x.2⟩ :=
  rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  statement: Function.Injective (inclusion h)
  proof: fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

中文:
定理 inclusion_injective
  结论: 函数.单射 (inclusion h)
  证明: fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, Subtype, Subtype.mk_eq_mk, coe_eq_coe, imp_self, inclusion_apply, mk_eq_mk
-/
theorem inclusion_injective : Function.Injective (inclusion h) := fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

/--
Definition of `ofLe` / `ofLe` 的定义

English:
definition ofLe
  signature: : LieSubalgebra R K'
  body: (inclusion h).range

@[simp]

中文:
定义 ofLe
  签名: : Lie子代数 R K'
  定义体: (inclusion h).range

@[simp]

Depends on / 依赖: inclusion
-/
def ofLe : LieSubalgebra R K' :=
  (inclusion h).range

@[simp]
/--
theorem `mem_ofLe` / 定理 `mem_ofLe`

English:
theorem mem_ofLe
  given: (x : K')
  statement: x in ofLe h ↔ (x : L) in K
  proof: by
  simp only [ofLe, inclusion_apply, LieHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    use ⟨(x : L), h⟩

中文:
定理 mem_ofLe
  条件: (x : K')
  结论: x in ofLe h ↔ (x : L) in K
  证明: by
  simp only [ofLe, inclusion_apply, LieHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    use ⟨(x : L), h⟩

Depends on / 依赖: LieHom, LieHom.mem_range, inclusion_apply, mem_range, property, y.property
-/
theorem mem_ofLe (x : K') : x in ofLe h ↔ (x : L) in K := by
  simp only [ofLe, inclusion_apply, LieHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    use ⟨(x : L), h⟩

/--
theorem `ofLe_eq_comap_incl` / 定理 `ofLe_eq_comap_incl`

English:
theorem ofLe_eq_comap_incl
  statement: ofLe h = K.comap K'.incl
  proof: by
  ext
  rw [mem_ofLe]
  rfl

@[simp]

中文:
定理 ofLe_eq_comap_incl
  结论: ofLe h = K.comap K'.incl
  证明: by
  ext
  rw [mem_ofLe]
  rfl

@[simp]

Depends on / 依赖: mem_ofLe
-/
theorem ofLe_eq_comap_incl : ofLe h = K.comap K'.incl := by
  ext
  rw [mem_ofLe]
  rfl

@[simp]
/--
theorem `coe_ofLe` / 定理 `coe_ofLe`

English:
theorem coe_ofLe
  statement: (ofLe h : Submodule R K') = LinearMap.range (Submodule.inclusion h)
  proof: rfl

中文:
定理 coe_ofLe
  结论: (ofLe h : 子模 R K') = 线性映射.range (子模.inclusion h)
  证明: rfl
-/
theorem coe_ofLe : (ofLe h : Submodule R K') = LinearMap.range (Submodule.inclusion h) :=
  rfl

/--
Definition of `equivOfLe` / `equivOfLe` 的定义

English:
definition equivOfLe
  signature: : K ≃ₗ⁅R⁆ ofLe h
  body: (inclusion h).equivRangeOfInjective (inclusion_injective h)

@[simp]

中文:
定义 equivOfLe
  签名: : K ≃ₗ⁅R⁆ ofLe h
  定义体: (inclusion h).equivRangeOfInjective (inclusion_injective h)

@[simp]

Depends on / 依赖: equivRangeOfInjective, inclusion, inclusion_injective
-/
noncomputable def equivOfLe : K ≃ₗ⁅R⁆ ofLe h :=
  (inclusion h).equivRangeOfInjective (inclusion_injective h)

@[simp]
/--
theorem `equivOfLe_apply` / 定理 `equivOfLe_apply`

English:
theorem equivOfLe_apply
  given: (x : K)
  statement: equivOfLe h x = ⟨inclusion h x, (inclusion h).mem_range_self x⟩
  proof: rfl

中文:
定理 equivOfLe_apply
  条件: (x : K)
  结论: equivOfLe h x = ⟨inclusion h x, (inclusion h).mem_range_self x⟩
  证明: rfl
-/
theorem equivOfLe_apply (x : K) : equivOfLe h x = ⟨inclusion h x, (inclusion h).mem_range_self x⟩ :=
  rfl

end NestedSubalgebras

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂}
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {K : Lie子代数 R L} {K' : Lie子代数 R L₂}
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂} :
    map f K <= K' ↔ K <= comap f K' :=
  Set.image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

中文:
定理 gc_map_comap
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

end LatticeStructure

section LieSpan

variable (R L) (s : Set L)

/--
Definition of `lieSpan` / `lieSpan` 的定义

English:
definition lieSpan
  signature: : LieSubalgebra R L
  body: sInf { N | s subseteq N }

中文:
定义 lieSpan
  签名: : Lie子代数 R L
  定义体: sInf { N | s subseteq N }

Depends on / 依赖: subseteq
-/
def lieSpan : LieSubalgebra R L :=
  sInf { N | s subseteq N }

variable {R L s}

/--
theorem `mem_lieSpan` / 定理 `mem_lieSpan`

English:
theorem mem_lieSpan
  given: {x : L}
  statement: x in lieSpan R L s ↔ forall K : LieSubalgebra R L, s subseteq K -> x in K
  proof: by
  rw [← SetLike.mem_coe]; rw [lieSpan]; rw [coe_sInf]
  exact Set.mem_iInter₂

中文:
定理 mem_lieSpan
  条件: {x : L}
  结论: x in lieSpan R L s ↔ 对任意 K : Lie子代数 R L, s subseteq K -> x in K
  证明: by
  rw [← SetLike.mem_coe]; rw [lieSpan]; rw [coe_sInf]
  exact Set.mem_iInter₂

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_sInf, lieSpan, mem_coe
-/
theorem mem_lieSpan {x : L} : x in lieSpan R L s ↔ forall K : LieSubalgebra R L, s subseteq K -> x in K := by
  rw [← SetLike.mem_coe]; rw [lieSpan]; rw [coe_sInf]
  exact Set.mem_iInter₂

/--
theorem `subset_lieSpan` / 定理 `subset_lieSpan`

English:
theorem subset_lieSpan
  statement: s subseteq lieSpan R L s
  proof: by
  intro m hm
  rw [SetLike.mem_coe]; rw [mem_lieSpan]
  intro K hK
  exact hK hm

中文:
定理 subset_lieSpan
  结论: s subseteq lieSpan R L s
  证明: by
  intro m hm
  rw [SetLike.mem_coe]; rw [mem_lieSpan]
  intro K hK
  exact hK hm

Depends on / 依赖: SetLike, SetLike.mem_coe, mem_coe, mem_lieSpan
-/
theorem subset_lieSpan : s subseteq lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe]; rw [mem_lieSpan]
  intro K hK
  exact hK hm

/--
theorem `submodule_span_le_lieSpan` / 定理 `submodule_span_le_lieSpan`

English:
theorem submodule_span_le_lieSpan
  statement: Submodule.span R s <= lieSpan R L s
  proof: by
  rw [Submodule.span_le]; rw [coe_toSubmodule]
  apply subset_lieSpan

中文:
定理 submodule_span_le_lieSpan
  结论: 子模.span R s <= lieSpan R L s
  证明: by
  rw [Submodule.span_le]; rw [coe_toSubmodule]
  apply subset_lieSpan

Depends on / 依赖: Submodule, Submodule.span_le, coe_toSubmodule, span_le, subset_lieSpan
-/
theorem submodule_span_le_lieSpan : Submodule.span R s <= lieSpan R L s := by
  rw [Submodule.span_le]; rw [coe_toSubmodule]
  apply subset_lieSpan

/--
theorem `lieSpan_le` / 定理 `lieSpan_le`

English:
theorem lieSpan_le
  given: {K}
  statement: lieSpan R L s <= K ↔ s subseteq K
  proof: by
  constructor
  · exact Set.Subset.trans subset_lieSpan
  · intro hs m hm
    rw [mem_lieSpan] at hm
    exact hm _ hs

中文:
定理 lieSpan_le
  条件: {K}
  结论: lieSpan R L s <= K ↔ s subseteq K
  证明: by
  constructor
  · exact Set.Subset.trans subset_lieSpan
  · intro hs m hm
    rw [mem_lieSpan] at hm
    exact hm _ hs

Depends on / 依赖: Set.Subset.trans, Subset, mem_lieSpan, subset_lieSpan
-/
theorem lieSpan_le {K} : lieSpan R L s <= K ↔ s subseteq K := by
  constructor
  · exact Set.Subset.trans subset_lieSpan
  · intro hs m hm
    rw [mem_lieSpan] at hm
    exact hm _ hs

/--
theorem `lieSpan_mono` / 定理 `lieSpan_mono`

English:
theorem lieSpan_mono
  given: {t : Set L} (h : s subseteq t)
  statement: lieSpan R L s <= lieSpan R L t
  proof: by
  rw [lieSpan_le]
  exact Set.Subset.trans h subset_lieSpan

中文:
定理 lieSpan_mono
  条件: {t : 集合 L} (h : s subseteq t)
  结论: lieSpan R L s <= lieSpan R L t
  证明: by
  rw [lieSpan_le]
  exact Set.Subset.trans h subset_lieSpan

Depends on / 依赖: Set.Subset.trans, Subset, lieSpan_le, subset_lieSpan
-/
theorem lieSpan_mono {t : Set L} (h : s subseteq t) : lieSpan R L s <= lieSpan R L t := by
  rw [lieSpan_le]
  exact Set.Subset.trans h subset_lieSpan

/--
theorem `lieSpan_eq` / 定理 `lieSpan_eq`

English:
theorem lieSpan_eq
  statement: lieSpan R L (K : Set L) = K
  proof: le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

中文:
定理 lieSpan_eq
  结论: lieSpan R L (K : 集合 L) = K
  证明: le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

Depends on / 依赖: le_antisymm, lieSpan_le, lieSpan_le.mpr, rfl.subset, subset, subset_lieSpan
-/
theorem lieSpan_eq : lieSpan R L (K : Set L) = K :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

/--
theorem `coe_lieSpan_submodule_eq_iff` / 定理 `coe_lieSpan_submodule_eq_iff`

English:
theorem coe_lieSpan_submodule_eq_iff
  given: {p : Submodule R L}
  proof: by
  rw [p.exists_lieSubalgebra_coe_eq_iff]; constructor <;> intro h
  · intro x m hm
    rw [← h]; rw [mem_toSubmodule]
    exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

中文:
定理 coe_lieSpan_submodule_eq_iff
  条件: {p : 子模 R L}
  证明: by
  rw [p.exists_lieSubalgebra_coe_eq_iff]; constructor <;> intro h
  · intro x m hm
    rw [← h]; rw [mem_toSubmodule]
    exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

Depends on / 依赖: coe_toSubmodule, exists_lieSubalgebra_coe_eq_iff, lieSpan_eq, lie_mem, mem_toSubmodule, p.exists_lieSubalgebra_coe_eq_iff, subset_lieSpan, toSubmodule_inj, toSubmodule_mk
-/
theorem coe_lieSpan_submodule_eq_iff {p : Submodule R L} :
    (lieSpan R L (p : Set L) : Submodule R L) = p ↔ exists K : LieSubalgebra R L, ↑K = p := by
  rw [p.exists_lieSubalgebra_coe_eq_iff]; constructor <;> intro h
  · intro x m hm
    rw [← h]; rw [mem_toSubmodule]
    exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

open Submodule in
/--
theorem `coe_lieSpan_eq_span_of_forall_lie_eq_zero` / 定理 `coe_lieSpan_eq_span_of_forall_lie_eq_zero`

English:
theorem coe_lieSpan_eq_span_of_forall_lie_eq_zero
  proof: by
  suffices forall {x y}, x in span R s -> y in span R s -> ⁅x, y⁆ in span R s by
    refine le_antisymm ?_ submodule_span_le_lieSpan
    change _ <= ({ span R s with lie_mem' := this } : LieSubalgebra R L)
    rw [lieSpan_le]
    exact subset_span
  intro x y hx hy
  induction hx, hy using span_i

中文:
定理 coe_lieSpan_eq_span_of_对任意_lie_eq_zero
  证明: by
  suffices forall {x y}, x in span R s -> y in span R s -> ⁅x, y⁆ in span R s by
    refine le_antisymm ?_ submodule_span_le_lieSpan
    change _ <= ({ span R s with lie_mem' := this } : LieSubalgebra R L)
    rw [lieSpan_le]
    exact subset_span
  intro x y hx hy
  induction hx, hy using span_i

Depends on / 依赖: LieSubalgebra, add_left, add_mem, add_right, le_antisymm, lieSpan_le, lie_mem, mem_mem, submodule_span_le_lieSpan, subset_span, zero_left, zero_right
-/
theorem coe_lieSpan_eq_span_of_forall_lie_eq_zero
    {s : Set L} (hs : forallᵉ (x in s) (y in s), ⁅x, y⁆ = 0) :
    lieSpan R L s = span R s := by
  suffices forall {x y}, x in span R s -> y in span R s -> ⁅x, y⁆ in span R s by
    refine le_antisymm ?_ submodule_span_le_lieSpan
    change _ <= ({ span R s with lie_mem' := this } : LieSubalgebra R L)
    rw [lieSpan_le]
    exact subset_span
  intro x y hx hy
  induction hx, hy using span_induction₂ with
  | mem_mem x y hx hy => simp [hs x hx y hy]
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z _ _ _ hx hy => simp [add_mem hx hy]
  | add_right x y z _ _ _ hx hy => simp [add_mem hx hy]
  | smul_left r x y _ _ h => simp [smul_mem _ r h]
  | smul_right r x y _ _ h => simp [smul_mem _ r h]

/--
theorem `map_lieSpan` / 定理 `map_lieSpan`

English:
theorem map_lieSpan
  proof: by
  refine le_antisymm ?_ (lieSpan_le.mpr <| Set.image_mono subset_lieSpan)
  rw [map_le_iff_le_comap]; rw [lieSpan_le]
  change s subseteq f ⁻¹' (lieSpan R L₂ (f '' s))
exact image_subset_iff.mp subset_lieSpan

中文:
定理 map_lieSpan
  证明: by
  refine le_antisymm ?_ (lieSpan_le.mpr <| Set.image_mono subset_lieSpan)
  rw [map_le_iff_le_comap]; rw [lieSpan_le]
  change s subseteq f ⁻¹' (lieSpan R L₂ (f '' s))
exact image_subset_iff.mp subset_lieSpan

Depends on / 依赖: Set.image_mono, image_mono, image_subset_iff, image_subset_iff.mp, le_antisymm, lieSpan, lieSpan_le, lieSpan_le.mpr, map_le_iff_le_comap, subset_lieSpan, subseteq
-/
theorem map_lieSpan :
    (lieSpan R L s).map f = lieSpan R L₂ (f '' s) := by
  refine le_antisymm ?_ (lieSpan_le.mpr <| Set.image_mono subset_lieSpan)
  rw [map_le_iff_le_comap]; rw [lieSpan_le]
  change s subseteq f ⁻¹' (lieSpan R L₂ (f '' s))
exact image_subset_iff.mp subset_lieSpan

variable (R L)

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (lieSpan R L : Set L -> LieSubalgebra R L) (↑) where
  body: lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]

中文:
定义 gi
  签名: : Galois嵌入 (lieSpan R L : 集合 L -> Lie子代数 R L) (↑) where
  定义体: lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
-/
protected def gi : GaloisInsertion (lieSpan R L : Set L -> LieSubalgebra R L) (↑) where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
/--
theorem `span_empty` / 定理 `span_empty`

English:
theorem span_empty
  statement: lieSpan R L (∅ : Set L) = ⊥
  proof: (LieSubalgebra.gi R L).gc.l_bot

@[simp]

中文:
定理 span_empty
  结论: lieSpan R L (∅ : 集合 L) = ⊥
  证明: (LieSubalgebra.gi R L).gc.l_bot

@[simp]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.gi, gc.l_bot, l_bot
-/
theorem span_empty : lieSpan R L (∅ : Set L) = ⊥ :=
  (LieSubalgebra.gi R L).gc.l_bot

@[simp]
/--
theorem `span_univ` / 定理 `span_univ`

English:
theorem span_univ
  statement: lieSpan R L (Set.univ : Set L) = ⊤
  proof: eq_top_iff.2 SetLike.le_def.2 subset_lieSpan

中文:
定理 span_univ
  结论: lieSpan R L (集合.univ : 集合 L) = ⊤
  证明: eq_top_iff.2 SetLike.le_def.2 subset_lieSpan

Depends on / 依赖: SetLike, SetLike.le_def, eq_top_iff, le_def, subset_lieSpan
-/
theorem span_univ : lieSpan R L (Set.univ : Set L) = ⊤ :=
eq_top_iff.2 SetLike.le_def.2 subset_lieSpan

variable {L}

/--
theorem `span_union` / 定理 `span_union`

English:
theorem span_union
  given: (s t : Set L)
  statement: lieSpan R L (s union t) = lieSpan R L s ⊔ lieSpan R L t
  proof: (LieSubalgebra.gi R L).gc.l_sup

中文:
定理 span_union
  条件: (s t : 集合 L)
  结论: lieSpan R L (s union t) = lieSpan R L s ⊔ lieSpan R L t
  证明: (LieSubalgebra.gi R L).gc.l_sup

Depends on / 依赖: LieSubalgebra, LieSubalgebra.gi, gc.l_sup, l_sup
-/
theorem span_union (s t : Set L) : lieSpan R L (s union t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubalgebra.gi R L).gc.l_sup

/--
theorem `span_iUnion` / 定理 `span_iUnion`

English:
theorem span_iUnion
  given: {ι} (s : ι -> Set L)
  statement: lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i)
  proof: (LieSubalgebra.gi R L).gc.l_iSup

中文:
定理 span_iUnion
  条件: {ι} (s : ι -> 集合 L)
  结论: lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i)
  证明: (LieSubalgebra.gi R L).gc.l_iSup

Depends on / 依赖: LieSubalgebra, LieSubalgebra.gi, gc.l_iSup, l_iSup
-/
theorem span_iUnion {ι} (s : ι -> Set L) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubalgebra.gi R L).gc.l_iSup

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` holds for all
elements of the Lie algebra spanned by `s`. -/
@[elab_as_elim]
/--
theorem `lieSpan_induction` / 定理 `lieSpan_induction`

English:
theorem lieSpan_induction
  statement: {p : (x : L) -> x in lieSpan R L s -> Prop}
  proof: by
  let p : LieSubalgebra R L :=
    { carrier := { x | exists hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r => fun ⟨_, hpx⟩ => ⟨_, smul r _ _ hpx⟩
      lie_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, lie _ _ _ _ hpx

中文:
定理 lieSpan_induction
  结论: {p : (x : L) -> x in lieSpan R L s -> 命题}
  证明: by
  let p : LieSubalgebra R L :=
    { carrier := { x | exists hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r => fun ⟨_, hpx⟩ => ⟨_, smul r _ _ hpx⟩
      lie_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, lie _ _ _ _ hpx

Depends on / 依赖: LieSubalgebra, add_mem, carrier, lieSpan_le, lie_mem, smul_mem, subset_lieSpan, zero_mem
-/
theorem lieSpan_induction {p : (x : L) -> x in lieSpan R L s -> Prop}
    (mem : forall (x) (h : x in s), p x (subset_lieSpan h))
    (zero : p 0 (LieSubalgebra.zero_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (LieSubalgebra.add_mem _ ‹_› ‹_›))
    (smul : forall (a : R) (x hx), p x hx -> p (a • x) (LieSubalgebra.smul_mem _ _ ‹_›)) {x}
    (lie : forall x y hx hy, p x hx -> p y hy -> p (⁅x, y⁆) (LieSubalgebra.lie_mem _ ‹_› ‹_›))
    (hx : x in lieSpan R L s) : p x hx := by
  let p : LieSubalgebra R L :=
    { carrier := { x | exists hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r => fun ⟨_, hpx⟩ => ⟨_, smul r _ _ hpx⟩
      lie_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, lie _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_lieSpan hy, mem y hy⟩) hx exact lieSpan_le (K := p)

/--
lemma `lieSpan_neg` / 引理 `lieSpan_neg`

English:
lemma lieSpan_neg
  statement: lieSpan R L (-s) = lieSpan R L s
  proof: by
  suffices forall s : Set L, lieSpan R L (-s) <= lieSpan R L s from
le_antisymm (this s) by simpa using (this (-s))
  intro s x hx
  induction hx using lieSpan_induction with
| mem y h => exact neg_mem_iff.mp subset_lieSpan Set.mem_neg.mp h
  | zero => exact zero_mem _
  | add _ _ _ _ hu hv => ex

中文:
引理 lieSpan_neg
  结论: lieSpan R L (-s) = lieSpan R L s
  证明: by
  suffices forall s : Set L, lieSpan R L (-s) <= lieSpan R L s from
le_antisymm (this s) by simpa using (this (-s))
  intro s x hx
  induction hx using lieSpan_induction with
| mem y h => exact neg_mem_iff.mp subset_lieSpan Set.mem_neg.mp h
  | zero => exact zero_mem _
  | add _ _ _ _ hu hv => ex
-/
@[simp] lemma lieSpan_neg : lieSpan R L (-s) = lieSpan R L s := by
  suffices forall s : Set L, lieSpan R L (-s) <= lieSpan R L s from
le_antisymm (this s) by simpa using (this (-s))
  intro s x hx
  induction hx using lieSpan_induction with
| mem y h => exact neg_mem_iff.mp subset_lieSpan Set.mem_neg.mp h
  | zero => exact zero_mem _
  | add _ _ _ _ hu hv => exact add_mem hu hv
  | smul t _ _ hu => exact SMulMemClass.smul_mem t hu
  | lie _ _ _ _ hu hv => exact lie_mem _ hu hv

variable {R} in
/--
lemma `lieSpan_lieSpan_coe_preimage` / 引理 `lieSpan_lieSpan_coe_preimage`

English:
lemma lieSpan_lieSpan_coe_preimage
  statement: lieSpan R _ (((↑) : lieSpan R L s -> L) ⁻¹' s) = ⊤
  proof: by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using lieSpan_induction with
| mem u hu => exact subset_lieSpan by simpa
  | zero => exact zero_mem _
  | add u v _ _ hu hv => revert hu hv; exact add_mem
  | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
  | lie u v _ _ hu hv => 

中文:
引理 lieSpan_lieSpan_coe_preimage
  结论: lieSpan R _ (((↑) : lieSpan R L s -> L) ⁻¹' s) = ⊤
  证明: by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using lieSpan_induction with
| mem u hu => exact subset_lieSpan by simpa
  | zero => exact zero_mem _
  | add u v _ _ hu hv => revert hu hv; exact add_mem
  | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
  | lie u v _ _ hu hv => 
-/
@[simp] lemma lieSpan_lieSpan_coe_preimage : lieSpan R _ (((↑) : lieSpan R L s -> L) ⁻¹' s) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using lieSpan_induction with
| mem u hu => exact subset_lieSpan by simpa
  | zero => exact zero_mem _
  | add u v _ _ hu hv => revert hu hv; exact add_mem
  | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
  | lie u v _ _ hu hv => revert hu hv; exact LieSubalgebra.lie_mem _

/--
lemma `comap_lieSpan_range_eq` / 引理 `comap_lieSpan_range_eq`

English:
lemma comap_lieSpan_range_eq
  given: {ι : Type*} (f : ι -> K)
  proof: by
  apply le_antisymm
  · intro ⟨x, hx⟩ hx'
    simp only [mem_comap, coe_incl] at hx'
    suffices x in (lieSpan R K (range f)).map K.incl by aesop
    clear hx
    induction hx' using lieSpan_induction with
    | mem u hu =>
have (i : ι) : f i in lieSpan R K (range f) := subset_lieSpan mem_range_

中文:
引理 comap_lieSpan_range_eq
  条件: {ι : 类型} (f : ι -> K)
  证明: by
  apply le_antisymm
  · intro ⟨x, hx⟩ hx'
    simp only [mem_comap, coe_incl] at hx'
    suffices x in (lieSpan R K (range f)).map K.incl by aesop
    clear hx
    induction hx' using lieSpan_induction with
    | mem u hu =>
have (i : ι) : f i in lieSpan R K (range f) := subset_lieSpan mem_range_

Depends on / 依赖: K.incl, LieSubalgebra, LieSubalgebra.smul_mem, add_mem, coe_incl, le_antisymm, lieSpan, lieSpan_induction, lieSpan_le, lie_mem, mem_comap, mem_range_self, revert, smul_mem, subset_lieSpan, zero_mem
-/
lemma comap_lieSpan_range_eq {ι : Type*} (f : ι -> K) :
    (lieSpan R L (range ((↑) ∘ f))).comap K.incl = lieSpan R K (range f) := by
  apply le_antisymm
  · intro ⟨x, hx⟩ hx'
    simp only [mem_comap, coe_incl] at hx'
    suffices x in (lieSpan R K (range f)).map K.incl by aesop
    clear hx
    induction hx' using lieSpan_induction with
    | mem u hu =>
have (i : ι) : f i in lieSpan R K (range f) := subset_lieSpan mem_range_self i
      aesop
    | zero => exact zero_mem _
    | add u v _ _ hu hv => revert hu hv; exact add_mem
    | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
    | lie u v _ _ hu hv => revert hu hv; exact lie_mem _
  · rw [lieSpan_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, coe_incl]
exact subset_lieSpan by simp

end LieSpan

end LieSubalgebra

end LieSubalgebra

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w}
variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂]

/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Injective f)
  body: { LinearEquiv.ofInjective (f : L₁ ->ₗ[R] L₂) <| by rwa [LieHom.coe_toLinearMap] with
map_lie' {x y} := SetCoe.ext f.map_lie x y }

@[simp]

中文:
定义 ofInjective
  签名: (f : L₁ ->ₗ⁅R⁆ L₂) (h : 函数.单射 f)
  定义体: { LinearEquiv.ofInjective (f : L₁ ->ₗ[R] L₂) <| by rwa [LieHom.coe_toLinearMap] with
map_lie' {x y} := SetCoe.ext f.map_lie x y }

@[simp]

Depends on / 依赖: LieHom, LieHom.coe_toLinearMap, LinearEquiv, LinearEquiv.ofInjective, SetCoe, SetCoe.ext, coe_toLinearMap, f.map_lie, map_lie, ofInjective
-/
noncomputable def ofInjective (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.range :=
  { LinearEquiv.ofInjective (f : L₁ ->ₗ[R] L₂) <| by rwa [LieHom.coe_toLinearMap] with
map_lie' {x y} := SetCoe.ext f.map_lie x y }

@[simp]
/--
theorem `ofInjective_apply` / 定理 `ofInjective_apply`

English:
theorem ofInjective_apply
  given: (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁)
  proof: rfl

中文:
定理 ofInjective_apply
  条件: (f : L₁ ->ₗ⁅R⁆ L₂) (h : 函数.单射 f) (x : L₁)
  证明: rfl
-/
theorem ofInjective_apply (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
    ↑(ofInjective f h x) = f x :=
  rfl

variable (L₁' L₁'' : LieSubalgebra R L₁) (L₂' : LieSubalgebra R L₂)

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : (L₁' : Set L₁) = L₁'')
  body: { LinearEquiv.ofEq (L₁' : Submodule R L₁) (L₁'' : Submodule R L₁) (by
      ext x
      change x in (L₁' : Set L₁) ↔ x in (L₁'' : Set L₁)
      rw [h]) with
    map_lie' {_ _} := rfl }

@[simp]

中文:
定义 ofEq
  签名: (h : (L₁' : 集合 L₁) = L₁'')
  定义体: { LinearEquiv.ofEq (L₁' : Submodule R L₁) (L₁'' : Submodule R L₁) (by
      ext x
      change x in (L₁' : Set L₁) ↔ x in (L₁'' : Set L₁)
      rw [h]) with
    map_lie' {_ _} := rfl }

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, Submodule, map_lie
-/
def ofEq (h : (L₁' : Set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
  { LinearEquiv.ofEq (L₁' : Submodule R L₁) (L₁'' : Submodule R L₁) (by
      ext x
      change x in (L₁' : Set L₁) ↔ x in (L₁'' : Set L₁)
      rw [h]) with
    map_lie' {_ _} := rfl }

@[simp]
/--
theorem `ofEq_apply` / 定理 `ofEq_apply`

English:
theorem ofEq_apply
  given: (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L)
  proof: rfl

中文:
定理 ofEq_apply
  条件: (L L' : Lie子代数 R L₁) (h : (L : 集合 L₁) = L') (x : L)
  证明: rfl
-/
theorem ofEq_apply (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L) :
    (↑(ofEq L L' h x) : L₁) = x :=
  rfl

variable (e : L₁ ≃ₗ⁅R⁆ L₂)

/--
Definition of `lieSubalgebraMap` / `lieSubalgebraMap` 的定义

English:
definition lieSubalgebraMap
  signature: : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : LieSubalgebra R L₂)
  body: { LinearEquiv.submoduleMap (e : L₁ ≃ₗ[R] L₂) ↑L₁'' with
    map_lie' := @fun x y => by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ ->ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]

中文:
定义 lieSubalgebraMap
  签名: : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : Lie子代数 R L₂)
  定义体: { LinearEquiv.submoduleMap (e : L₁ ≃ₗ[R] L₂) ↑L₁'' with
    map_lie' := @fun x y => by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ ->ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]

Depends on / 依赖: LieHom, LieHom.map_lie, LinearEquiv, LinearEquiv.submoduleMap, SetCoe, SetCoe.ext, map_lie, submoduleMap
-/
def lieSubalgebraMap : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : LieSubalgebra R L₂) :=
  { LinearEquiv.submoduleMap (e : L₁ ≃ₗ[R] L₂) ↑L₁'' with
    map_lie' := @fun x y => by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ ->ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]
/--
theorem `lieSubalgebraMap_apply` / 定理 `lieSubalgebraMap_apply`

English:
theorem lieSubalgebraMap_apply
  given: (x : L₁'')
  statement: ↑(e.lieSubalgebraMap _ x) = e x
  proof: rfl

中文:
定理 lieSubalgebraMap_apply
  条件: (x : L₁'')
  结论: ↑(e.lieSubalgebraMap _ x) = e x
  证明: rfl
-/
theorem lieSubalgebraMap_apply (x : L₁'') : ↑(e.lieSubalgebraMap _ x) = e x :=
  rfl

/--
Definition of `ofSubalgebras` / `ofSubalgebras` 的定义

English:
definition ofSubalgebras
  signature: (h : L₁'.map ↑e = L₂')
  body: { LinearEquiv.ofSubmodules (e : L₁ ≃ₗ[R] L₂) (↑L₁') (↑L₂') (by
      rw [← h]
      rfl) with
    map_lie' := @fun x y => by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ ->ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]

中文:
定义 ofSubalgebras
  签名: (h : L₁'.map ↑e = L₂')
  定义体: { LinearEquiv.ofSubmodules (e : L₁ ≃ₗ[R] L₂) (↑L₁') (↑L₂') (by
      rw [← h]
      rfl) with
    map_lie' := @fun x y => by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ ->ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]

Depends on / 依赖: LieHom, LieHom.map_lie, LinearEquiv, LinearEquiv.ofSubmodules, SetCoe, SetCoe.ext, map_lie, ofSubmodules
-/
def ofSubalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
  { LinearEquiv.ofSubmodules (e : L₁ ≃ₗ[R] L₂) (↑L₁') (↑L₂') (by
      rw [← h]
      rfl) with
    map_lie' := @fun x y => by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ ->ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]
/--
theorem `ofSubalgebras_apply` / 定理 `ofSubalgebras_apply`

English:
theorem ofSubalgebras_apply
  given: (h : L₁'.map ↑e = L₂') (x : L₁')
  statement: ↑(e.ofSubalgebras _ _ h x) = e x
  proof: rfl

@[simp]

中文:
定理 ofSubalgebras_apply
  条件: (h : L₁'.map ↑e = L₂') (x : L₁')
  结论: ↑(e.ofSubalgebras _ _ h x) = e x
  证明: rfl

@[simp]
-/
theorem ofSubalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') : ↑(e.ofSubalgebras _ _ h x) = e x :=
  rfl

@[simp]
/--
theorem `ofSubalgebras_symm_apply` / 定理 `ofSubalgebras_symm_apply`

English:
theorem ofSubalgebras_symm_apply
  given: (h : L₁'.map ↑e = L₂') (x : L₂')
  proof: rfl

中文:
定理 ofSubalgebras_symm_apply
  条件: (h : L₁'.map ↑e = L₂') (x : L₂')
  证明: rfl
-/
theorem ofSubalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
    ↑((e.ofSubalgebras _ _ h).symm x) = e.symm x :=
  rfl

end LieEquiv
