/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/

module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs

/-!
# Lie-Rinehart subalgebras

This file defines Lie-Rinehart subalgebras of a Lie-Rinehart algebra and provides basic related
definitions and results.

## Main definitions/ statements:

* `LieRinehartSubalgebra` as an `A`-submodule of `L` stable under the Lie bracket. (This is also
applicable to Lie-Rinehart rings and more generally any `A`-module with a Lie ring structure).

* A Lie-Rinehart subalgebra of a Lie-Rinehart ring is a Lie-Rinehart ring

* A Lie-Rinehart subalgebra of a Lie-Rinehart algebra is a Lie-Rinehart algebra over the same ring.

-/

public section

open scoped LieRinehartAlgebra

variable (A L : Type*) [CommRing A] [LieRing L] [Module A L]

/--
Definition of `LieRinehartSubalgebra` / `LieRinehartSubalgebra` 的定义

English:
structure LieRinehartSubalgebra
  parameters: extends Submodule A L
  extends: Submodule A L
  axioms and operations (1):
    - lie_mem'({a b}) : a in carrier -> b in carrier -> ⁅a, b⁆ in carrier

中文:
结构 LieRinehartSubalgebra
  参数: extends Submodule A L
  继承: Submodule A L
  公理与运算 (1 个):
    - lie_mem'({a b}) : a in carrier -> b in carrier -> ⁅a, b⁆ in carrier
-/
structure LieRinehartSubalgebra extends Submodule A L where
  lie_mem' {a b} : a in carrier -> b in carrier -> ⁅a, b⁆ in carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (LieRinehartSubalgebra A L)
  body: ⟨⟨0, fun {x y hx _hy} => by simp [(Submodule.mem_bot A).mp hx]⟩⟩

中文:
实例 :
  签名: Zero (LieRinehartSubalgebra A L)
  定义体: ⟨⟨0, fun {x y hx _hy} => by simp [(Submodule.mem_bot A).mp hx]⟩⟩

Depends on / 依赖: Submodule, Submodule.mem_bot, mem_bot
-/
instance : Zero (LieRinehartSubalgebra A L) :=
  ⟨⟨0, fun {x y hx _hy} => by simp [(Submodule.mem_bot A).mp hx]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LieRinehartSubalgebra A L)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (LieRinehartSubalgebra A L)
  定义体: ⟨0⟩
-/
instance : Inhabited (LieRinehartSubalgebra A L) :=
  ⟨0⟩

namespace LieRinehartSubalgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (LieRinehartSubalgebra A L) L
  body: L'.carrier
  coe_injective L' L'' h := by
    rcases L'
    rcases L''
    congr
    exact SetLike.coe_injective h

中文:
实例 :
  签名: SetLike (LieRinehartSubalgebra A L) L
  定义体: L'.carrier
  coe_injective L' L'' h := by
    rcases L'
    rcases L''
    congr
    exact SetLike.coe_injective h

Depends on / 依赖: carrier
-/
instance : SetLike (LieRinehartSubalgebra A L) L where
  coe L' := L'.carrier
  coe_injective L' L'' h := by
    rcases L'
    rcases L''
    congr
    exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (LieRinehartSubalgebra A L)
  body: .ofSetLike (LieRinehartSubalgebra A L) L

中文:
实例 :
  签名: PartialOrder (LieRinehartSubalgebra A L)
  定义体: .ofSetLike (LieRinehartSubalgebra A L) L

Depends on / 依赖: LieRinehartSubalgebra, ofSetLike
-/
instance : PartialOrder (LieRinehartSubalgebra A L) := .ofSetLike (LieRinehartSubalgebra A L) L

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSubgroupClass (LieRinehartSubalgebra A L) L
  body: Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x in L'.toSubmodule from neg_mem hx

中文:
实例 :
  签名: AddSubgroupClass (LieRinehartSubalgebra A L) L
  定义体: Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x in L'.toSubmodule from neg_mem hx

Depends on / 依赖: Submodule, Submodule.add_mem, add_mem
-/
instance : AddSubgroupClass (LieRinehartSubalgebra A L) L where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x in L'.toSubmodule from neg_mem hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulMemClass (LieRinehartSubalgebra A L) A L
  body: SMulMemClass.smul_mem (s := s.toSubmodule)

中文:
实例 :
  签名: SMulMemClass (LieRinehartSubalgebra A L) A L
  定义体: SMulMemClass.smul_mem (s := s.toSubmodule)

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, s.toSubmodule, smul_mem, toSubmodule
-/
instance : SMulMemClass (LieRinehartSubalgebra A L) A L where
  smul_mem {s} := SMulMemClass.smul_mem (s := s.toSubmodule)

/--
Instance `lieRing` / 实例 `lieRing`

English:
instance lieRing
  signature: (L' : LieRinehartSubalgebra A L)
  body: ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

中文:
实例 lieRing
  签名: (L' : LieRinehartSubalgebra A L)
  定义体: ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

Depends on / 依赖: lie_mem, property, x.property, x.val, y.property, y.val
-/
instance lieRing (L' : LieRinehartSubalgebra A L) : LieRing L' where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

variable {A L}
variable (L' : LieRinehartSubalgebra A L)

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
  given: (t : A) {x : L} (h : x in L')
  statement: t • x in L'
  proof: SMulMemClass.smul_mem _ h

中文:
定理 smul_mem
  条件: (t : A) {x : L} (h : x in L')
  结论: t • x in L'
  证明: SMulMemClass.smul_mem _ h
-/
protected theorem smul_mem (t : A) {x : L} (h : x in L') : t • x in L' :=
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
  结论: x in L'.carrier ↔ x in (L' : Set L)
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
  条件: (S : Set L) (h₁ h₂ h₃ h₄) {x : L}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x in (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `mem_toSubmodule` / 定理 `mem_toSubmodule`

English:
theorem mem_toSubmodule
  given: {x : L}
  statement: x in L'.toSubmodule ↔ x in L'
  proof: Iff.rfl

@[simp]

中文:
定理 mem_toSubmodule
  条件: {x : L}
  结论: x in L'.toSubmodule ↔ x in L'
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmodule {x : L} : x in L'.toSubmodule ↔ x in L' :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk_iff'` / 定理 `mem_mk_iff'`

English:
theorem mem_mk_iff'
  given: (p : Submodule A L) (h) {x : L}
  proof: Iff.rfl

中文:
定理 mem_mk_iff'
  条件: (p : Submodule A L) (h) {x : L}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff' (p : Submodule A L) (h) {x : L} :
    x in (⟨p, h⟩ : LieRinehartSubalgebra A L) ↔ x in p :=
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
  结论: x in (L' : Set L) ↔ x in L'
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
theorem ext_iff (x y : L') : x = y ↔ (x : L) = y := Subtype.ext_iff

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
theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (ext_iff L' x 0).symm

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (L₁' L₂' : LieRinehartSubalgebra A L) (h : forall x, x in L₁' ↔ x in L₂')
  statement: L₁' = L₂'
  proof: SetLike.ext h

中文:
定理 ext
  条件: (L₁' L₂' : LieRinehartSubalgebra A L) (h : 对任意 x, x in L₁' ↔ x in L₂')
  结论: L₁' = L₂'
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (L₁' L₂' : LieRinehartSubalgebra A L) (h : forall x, x in L₁' ↔ x in L₂') : L₁' = L₂' :=
  SetLike.ext h

/--
theorem `ext_iff'` / 定理 `ext_iff'`

English:
theorem ext_iff'
  given: (L₁' L₂' : LieRinehartSubalgebra A L)
  statement: L₁' = L₂' ↔ forall x, x in L₁' ↔ x in L₂'
  proof: SetLike.ext_iff

@[simp]

中文:
定理 ext_iff'
  条件: (L₁' L₂' : LieRinehartSubalgebra A L)
  结论: L₁' = L₂' ↔ 对任意 x, x in L₁' ↔ x in L₂'
  证明: SetLike.ext_iff

@[simp]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem ext_iff' (L₁' L₂' : LieRinehartSubalgebra A L) : L₁' = L₂' ↔ forall x, x in L₁' ↔ x in L₂' :=
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
  条件: (S : Set L) (h₁ h₂ h₃ h₄)
  证明: rfl
-/
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) : Set L) = S :=
  rfl

/--
theorem `toSubmodule_mk` / 定理 `toSubmodule_mk`

English:
theorem toSubmodule_mk
  given: (p : Submodule A L) (h)
  proof: rfl

中文:
定理 toSubmodule_mk
  条件: (p : Submodule A L) (h)
  证明: rfl

Depends on / 依赖: LieRinehartSubalgebra, toSubmodule
-/
theorem toSubmodule_mk (p : Submodule A L) (h) :
    ({ p with lie_mem' := h } : LieRinehartSubalgebra A L).toSubmodule = p := rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : LieRinehartSubalgebra A L -> Set L)
  proof: SetLike.coe_injective

@[norm_cast]

中文:
定理 coe_injective
  结论: Function.Injective ((↑) : LieRinehartSubalgebra A L -> Set L)
  证明: SetLike.coe_injective

@[norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective ((↑) : LieRinehartSubalgebra A L -> Set L) :=
  SetLike.coe_injective

@[norm_cast]
/--
theorem `coe_set_eq` / 定理 `coe_set_eq`

English:
theorem coe_set_eq
  given: (L₁' L₂' : LieRinehartSubalgebra A L)
  statement: (L₁' : Set L) = L₂' ↔ L₁' = L₂'
  proof: SetLike.coe_set_eq

中文:
定理 coe_set_eq
  条件: (L₁' L₂' : LieRinehartSubalgebra A L)
  结论: (L₁' : Set L) = L₂' ↔ L₁' = L₂'
  证明: SetLike.coe_set_eq

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
theorem coe_set_eq (L₁' L₂' : LieRinehartSubalgebra A L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq

/--
theorem `toSubmodule_injective` / 定理 `toSubmodule_injective`

English:
theorem toSubmodule_injective
  statement: Function.Injective (toSubmodule (A := A) (L := L))
  proof: by
  intro L₁' L₂' h
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

中文:
定理 toSubmodule_injective
  结论: Function.Injective (toSubmodule (A := A) (L := L))
  证明: by
  intro L₁' L₂' h
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

Depends on / 依赖: SetLike, SetLike.ext, _iff, coe_set_eq
-/
theorem toSubmodule_injective : Function.Injective (toSubmodule (A := A) (L := L)) := by
  intro L₁' L₂' h
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

/--
theorem `coe_toSubmodule` / 定理 `coe_toSubmodule`

English:
theorem coe_toSubmodule
  statement: (L'.toSubmodule : Set L) = L'
  proof: rfl

中文:
定理 coe_toSubmodule
  结论: (L'.toSubmodule : Set L) = L'
  证明: rfl
-/
theorem coe_toSubmodule : (L'.toSubmodule : Set L) = L' :=
  rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M]

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
  签名: IsLieTower L' L M
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
  签名: : LieRingModule L' M where
  定义体: add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

Depends on / 依赖: add_lie
-/
instance lieRingModule : LieRingModule L' M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

end LieModule

variable [LieRingModule L A] [LieRinehartRing A L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRinehartRing A L'
  body: LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' _ _ _ := by simp [ext_iff]

中文:
实例 :
  签名: LieRinehartRing A L'
  定义体: LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' _ _ _ := by simp [ext_iff]

Depends on / 依赖: LieRinehartRing, LieRinehartRing.lie_smul_eq_mul, lie_smul_eq_mul
-/
instance : LieRinehartRing A L' where
  lie_smul_eq_mul' a b x := LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' _ _ _ := by simp [ext_iff]

variable (R : Type*) [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

/--
Instance `lieAlgebra` / 实例 `lieAlgebra`

English:
instance lieAlgebra
  signature: : LieAlgebra R L' where
  body: by aesop

中文:
实例 lieAlgebra
  签名: : LieAlgebra R L' where
  定义体: by aesop
-/
instance lieAlgebra : LieAlgebra R L' where
  lie_smul := by aesop

/--
Definition of `toLieSubalgebra` / `toLieSubalgebra` 的定义

English:
definition toLieSubalgebra
  signature: : LieSubalgebra R L where
  body: L'.toSubmodule.restrictScalars R
  lie_mem' := L'.lie_mem'

中文:
定义 toLieSubalgebra
  签名: : LieSubalgebra R L where
  定义体: L'.toSubmodule.restrictScalars R
  lie_mem' := L'.lie_mem'
-/
@[expose] def toLieSubalgebra : LieSubalgebra R L where
  toSubmodule := L'.toSubmodule.restrictScalars R
  lie_mem' := L'.lie_mem'

/--
theorem `toLieSubalgebra_injective` / 定理 `toLieSubalgebra_injective`

English:
theorem toLieSubalgebra_injective
  statement: Function.Injective (fun L' =>
  proof: fun L₁' L₂' h => by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]

中文:
定理 toLieSubalgebra_injective
  结论: Function.Injective (fun L' =>
  证明: fun L₁' L₂' h => by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext, _iff, coe_set_eq
-/
theorem toLieSubalgebra_injective : Function.Injective (fun L' =>
    L'.toLieSubalgebra R : LieRinehartSubalgebra A L -> LieSubalgebra R L) := fun L₁' L₂' h => by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]
/--
theorem `toLieSubalgebra_inj` / 定理 `toLieSubalgebra_inj`

English:
theorem toLieSubalgebra_inj
  given: (L₁' L₂' : LieRinehartSubalgebra A L)
  proof: (toLieSubalgebra_injective R).eq_iff

中文:
定理 toLieSubalgebra_inj
  条件: (L₁' L₂' : LieRinehartSubalgebra A L)
  证明: (toLieSubalgebra_injective R).eq_iff

Depends on / 依赖: eq_iff, toLieSubalgebra_injective
-/
theorem toLieSubalgebra_inj (L₁' L₂' : LieRinehartSubalgebra A L) :
    (L₁'.toLieSubalgebra R) = (L₂'.toLieSubalgebra R) ↔ L₁' = L₂' :=
  (toLieSubalgebra_injective R).eq_iff

/--
theorem `coe_toLieSubalgebra` / 定理 `coe_toLieSubalgebra`

English:
theorem coe_toLieSubalgebra
  statement: ((L'.toLieSubalgebra R) : Set L) = L'
  proof: rfl

中文:
定理 coe_toLieSubalgebra
  结论: ((L'.toLieSubalgebra R) : Set L) = L'
  证明: rfl
-/
theorem coe_toLieSubalgebra : ((L'.toLieSubalgebra R) : Set L) = L' := rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M] [Module R M]

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
  签名: [LieModule R L M]
  定义体: by
    rw [coe_bracket_of_module]; rw [Submodule.coe_smul_of_tower]; rw [smul_lie]; rw [coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

Depends on / 依赖: Submodule, Submodule.coe_smul_of_tower, coe_bracket_of_module, coe_smul_of_tower, lie_smul, smul_lie
-/
instance lieModule [LieModule R L M] : LieModule R L' M where
  smul_lie t x m := by
    rw [coe_bracket_of_module]; rw [Submodule.coe_smul_of_tower]; rw [smul_lie]; rw [coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

end LieModule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRinehartAlgebra R A L'

中文:
实例 :
  签名: LieRinehartAlgebra R A L'
-/
instance : LieRinehartAlgebra R A L' where

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : L' ->ₗ⁅(AlgHom.id R A)⁆ L where
  body: L'.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := coe_bracket L' x y
  map_smul_apply' a x := L'.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

@[simp]

中文:
定义 incl
  签名: : L' ->ₗ⁅(AlgHom.id R A)⁆ L where
  定义体: L'.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := coe_bracket L' x y
  map_smul_apply' a x := L'.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

@[simp]
-/
@[expose] def incl : L' ->ₗ⁅(AlgHom.id R A)⁆ L where
  __ := L'.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := coe_bracket L' x y
  map_smul_apply' a x := L'.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

@[simp]
/--
theorem `coe_incl` / 定理 `coe_incl`

English:
theorem coe_incl
  statement: ⇑(L'.incl R) = ((↑) : L' -> L)
  proof: rfl

中文:
定理 coe_incl
  结论: ⇑(L'.incl R) = ((↑) : L' -> L)
  证明: rfl
-/
theorem coe_incl : ⇑(L'.incl R) = ((↑) : L' -> L) := rfl

end LieRinehartSubalgebra
