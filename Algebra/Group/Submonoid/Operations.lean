/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Operations on `Submonoid`s

In this file we define various operations on `Submonoid`s and `MonoidHom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `Submonoid.toAddSubmonoid`, `Submonoid.toAddSubmonoid'`, `AddSubmonoid.toSubmonoid`,
  `AddSubmonoid.toSubmonoid'`: convert between multiplicative and additive submonoids of `M`,
  `Multiplicative M`, and `Additive M`. These are stated as `OrderIso`s.

### (Commutative) monoid structure on a submonoid

* `Submonoid.toMonoid`, `Submonoid.toCommMonoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `Submonoid.MulAction`, `Submonoid.DistribMulAction`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `Submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `Submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `Submonoid.prod`: product of two submonoids `s : Submonoid M` and `t : Submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `Submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `Submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `MulEquiv.submonoidCongr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `Submonoid.prodEquiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `MonoidHom`s

* `MonoidHom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `MonoidHom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `MonoidHom.domRestrict`: restrict a monoid homomorphism to a submonoid of its domain;
* `MonoidHom.restrict`: restrict the domain and codomain of a monoid homomorphism;
* `MonoidHom.codRestrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `MonoidHom.mrangeRestrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


section

/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `Additive M`. -/
@[simps]
/--
Definition of `Submonoid.toAddSubmonoid` / `Submonoid.toAddSubmonoid` 的定义

English:
definition Submonoid.toAddSubmonoid
  signature: : Submonoid M ≃o AddSubmonoid (Additive M) where
  body: { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  left_inv x := by cases x; rfl
  right_inv x := by ca

中文:
定义 子幺半群.toAddSubmonoid
  签名: : 子幺半群 M ≃o 加法子幺半群 (加性 M) where
  定义体: { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  left_inv x := by cases x; rfl
  right_inv x := by ca

Depends on / 依赖: Additive, Additive.ofMul, Additive.toMul, Iff.rfl, S.add_mem, S.mul_mem, S.one_mem, S.zero_mem, add_mem, carrier, invFun, left_inv, map_rel_iff, mul_mem, one_mem, right_inv, zero_mem
-/
def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl

/--
Definition of `AddSubmonoid.toSubmonoid'` / `AddSubmonoid.toSubmonoid'` 的定义

English:
abbreviation AddSubmonoid.toSubmonoid'
  signature: : AddSubmonoid (Additive M) ≃o Submonoid M
  body: Submonoid.toAddSubmonoid.symm

中文:
缩写 加法子幺半群.toSubmonoid'
  签名: : 加法子幺半群 (加性 M) ≃o 子幺半群 M
  定义体: Submonoid.toAddSubmonoid.symm

Depends on / 依赖: Submonoid, Submonoid.toAddSubmonoid.symm, toAddSubmonoid
-/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm

/--
theorem `Submonoid.toAddSubmonoid_closure` / 定理 `Submonoid.toAddSubmonoid_closure`

English:
theorem Submonoid.toAddSubmonoid_closure
  given: (S : Set M)
  proof: le_antisymm
    (Submonoid.toAddSubmonoid.le_symm_apply.1 <|
      Submonoid.closure_le.2 (AddSubmonoid.subset_closure (M := Additive M)))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := M))

中文:
定理 子幺半群.toAddSubmonoid_closure
  条件: (S : 集合 M)
  证明: le_antisymm
    (Submonoid.toAddSubmonoid.le_symm_apply.1 <|
      Submonoid.closure_le.2 (AddSubmonoid.subset_closure (M := Additive M)))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := M))

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_le, AddSubmonoid.subset_closure, Additive, Submonoid, Submonoid.closure_le, Submonoid.subset_closure, Submonoid.toAddSubmonoid.le_symm_apply, closure_le, le_antisymm, le_symm_apply, subset_closure, toAddSubmonoid
-/
theorem Submonoid.toAddSubmonoid_closure (S : Set M) :
    Submonoid.toAddSubmonoid (Submonoid.closure S)
      = AddSubmonoid.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid.le_symm_apply.1 <|
      Submonoid.closure_le.2 (AddSubmonoid.subset_closure (M := Additive M)))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := M))

/--
theorem `AddSubmonoid.toSubmonoid'_closure` / 定理 `AddSubmonoid.toSubmonoid'_closure`

English:
theorem AddSubmonoid.toSubmonoid'_closure
  given: (S : Set (Additive M))
  proof: le_antisymm
    (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <|
      AddSubmonoid.closure_le.2 (Submonoid.subset_closure (M := M)))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := Additive M))

中文:
定理 加法子幺半群.toSubmonoid'_closure
  条件: (S : 集合 (加性 M))
  证明: le_antisymm
    (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <|
      AddSubmonoid.closure_le.2 (Submonoid.subset_closure (M := M)))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := Additive M))
-/
theorem AddSubmonoid.toSubmonoid'_closure (S : Set (Additive M)) :
    AddSubmonoid.toSubmonoid' (AddSubmonoid.closure S)
      = Submonoid.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <|
      AddSubmonoid.closure_le.2 (Submonoid.subset_closure (M := M)))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := Additive M))

end

section

variable {A : Type*} [AddZeroClass A]

/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `Multiplicative A`. -/
@[simps]
/--
Definition of `AddSubmonoid.toSubmonoid` / `AddSubmonoid.toSubmonoid` 的定义

English:
definition AddSubmonoid.toSubmonoid
  signature: : AddSubmonoid A ≃o Submonoid (Multiplicative A) where
  body: { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  left_inv x := by cases x; rfl
  right_in

中文:
定义 加法子幺半群.toSubmonoid
  签名: : 加法子幺半群 A ≃o 子幺半群 (Multiplicative A) where
  定义体: { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  left_inv x := by cases x; rfl
  right_in

Depends on / 依赖: Iff.rfl, Multiplicative, Multiplicative.ofAdd, Multiplicative.toAdd, S.add_mem, S.mul_mem, S.one_mem, S.zero_mem, add_mem, carrier, invFun, left_inv, map_rel_iff, mul_mem, one_mem, right_inv, zero_mem
-/
def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun ha hb => S.add_mem' ha hb }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun ha hb => S.mul_mem' ha hb }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl

/--
Definition of `Submonoid.toAddSubmonoid'` / `Submonoid.toAddSubmonoid'` 的定义

English:
abbreviation Submonoid.toAddSubmonoid'
  signature: : Submonoid (Multiplicative A) ≃o AddSubmonoid A
  body: AddSubmonoid.toSubmonoid.symm

中文:
缩写 子幺半群.toAddSubmonoid'
  签名: : 子幺半群 (Multiplicative A) ≃o 加法子幺半群 A
  定义体: AddSubmonoid.toSubmonoid.symm

Depends on / 依赖: AddSubmonoid, AddSubmonoid.toSubmonoid.symm, toSubmonoid
-/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm

/--
theorem `AddSubmonoid.toSubmonoid_closure` / 定理 `AddSubmonoid.toSubmonoid_closure`

English:
theorem AddSubmonoid.toSubmonoid_closure
  given: (S : Set A)
  proof: le_antisymm
    (AddSubmonoid.toSubmonoid.to_galoisConnection.l_le <|
AddSubmonoid.closure_le.2 Submonoid.subset_closure (M := Multiplicative A))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))

中文:
定理 加法子幺半群.toSubmonoid_closure
  条件: (S : 集合 A)
  证明: le_antisymm
    (AddSubmonoid.toSubmonoid.to_galoisConnection.l_le <|
AddSubmonoid.closure_le.2 Submonoid.subset_closure (M := Multiplicative A))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_le, AddSubmonoid.subset_closure, AddSubmonoid.toSubmonoid.to_galoisConnection.l_le, Multiplicative, Submonoid, Submonoid.closure_le, Submonoid.subset_closure, closure_le, l_le, le_antisymm, subset_closure, toSubmonoid, to_galoisConnection
-/
theorem AddSubmonoid.toSubmonoid_closure (S : Set A) :
    (AddSubmonoid.toSubmonoid) (AddSubmonoid.closure S)
      = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid.to_galoisConnection.l_le <|
AddSubmonoid.closure_le.2 Submonoid.subset_closure (M := Multiplicative A))
    (Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))

/--
theorem `Submonoid.toAddSubmonoid'_closure` / 定理 `Submonoid.toAddSubmonoid'_closure`

English:
theorem Submonoid.toAddSubmonoid'_closure
  given: (S : Set (Multiplicative A))
  proof: le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
Submonoid.closure_le.2 AddSubmonoid.subset_closure (M := A))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))

中文:
定理 子幺半群.toAddSubmonoid'_closure
  条件: (S : 集合 (Multiplicative A))
  证明: le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
Submonoid.closure_le.2 AddSubmonoid.subset_closure (M := A))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))
-/
theorem Submonoid.toAddSubmonoid'_closure (S : Set (Multiplicative A)) :
    Submonoid.toAddSubmonoid' (Submonoid.closure S)
      = AddSubmonoid.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
Submonoid.closure_le.2 AddSubmonoid.subset_closure (M := A))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))

end

namespace Submonoid

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

open Set

/-!
### `comap` and `map`
-/

/-- The preimage of a `Submonoid` along a `MonoidHom` is a `Submonoid`. -/
@[to_additive
  /-- The preimage of an `AddSubmonoid` along an `AddMonoidHom` is an `AddSubmonoid`. -/]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : F) (S : Submonoid N)
  body: f ⁻¹' S
  one_mem' := show f 1 in S by rw [map_one]; exact S.one_mem
  mul_mem' ha hb := show f (_ * _) in S by rw [map_mul]; exact S.mul_mem ha hb

@[to_additive (attr := simp)]

中文:
定义 comap
  签名: (f : F) (S : 子幺半群 N)
  定义体: f ⁻¹' S
  one_mem' := show f 1 in S by rw [map_one]; exact S.one_mem
  mul_mem' ha hb := show f (_ * _) in S by rw [map_mul]; exact S.mul_mem ha hb

@[to_additive (attr := simp)]
-/
def comap (f : F) (S : Submonoid N) :
    Submonoid M where
  carrier := f ⁻¹' S
  one_mem' := show f 1 in S by rw [map_one]; exact S.one_mem
  mul_mem' ha hb := show f (_ * _) in S by rw [map_mul]; exact S.mul_mem ha hb

@[to_additive (attr := simp)]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (S : Submonoid N) (f : F)
  statement: (S.comap f : Set M) = f ⁻¹' S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_comap
  条件: (S : 子幺半群 N) (f : F)
  结论: (S.comap f : 集合 M) = f ⁻¹' S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {S : Submonoid N} {f : F} {x : M}
  statement: x in S.comap f ↔ f x in S
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_comap
  条件: {S : 子幺半群 N} {f : F} {x : M}
  结论: x in S.comap f ↔ f x in S
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x in S.comap f ↔ f x in S :=
  Iff.rfl

@[to_additive]
/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (S : Submonoid P) (g : N ->* P) (f : M ->* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_comap
  条件: (S : 子幺半群 P) (g : N ->* P) (f : M ->* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_comap (S : Submonoid P) (g : N ->* P) (f : M ->* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (S : Submonoid P)
  statement: S.comap (MonoidHom.id P) = S
  proof: ext (by simp)

中文:
定理 comap_id
  条件: (S : 子幺半群 P)
  结论: S.comap (幺半群态射.id P) = S
  证明: ext (by simp)
-/
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S :=
  ext (by simp)

/-- The image of a `Submonoid` along a `MonoidHom` is a `Submonoid`. -/
@[to_additive
  /-- The image of an `AddSubmonoid` along an `AddMonoidHom` is an `AddSubmonoid`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : F) (S : Submonoid M)
  body: f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : F) (S : 子幺半群 M)
  定义体: f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
-/
def map (f : F) (S : Submonoid M) :
    Submonoid N where
  carrier := f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : F) (S : Submonoid M)
  statement: (S.map f : Set N) = f '' S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_map
  条件: (f : F) (S : 子幺半群 M)
  结论: (S.map f : 集合 N) = f '' S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `map_coe_toMonoidHom` / 定理 `map_coe_toMonoidHom`

English:
theorem map_coe_toMonoidHom
  given: (f : F) (S : Submonoid M)
  statement: S.map (f : M ->* N) = S.map f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_coe_toMonoidHom
  条件: (f : F) (S : 子幺半群 M)
  结论: S.map (f : M ->* N) = S.map f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_coe_toMonoidHom (f : F) (S : Submonoid M) : S.map (f : M ->* N) = S.map f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `map_coe_toMulEquiv` / 定理 `map_coe_toMulEquiv`

English:
theorem map_coe_toMulEquiv
  given: {F} [EquivLike F M N] [MulEquivClass F M N] (f : F) (S : Submonoid M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_coe_toMulEquiv
  条件: {F} [等价状 F M N] [乘法等价类 F M N] (f : F) (S : 子幺半群 M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_coe_toMulEquiv {F} [EquivLike F M N] [MulEquivClass F M N] (f : F) (S : Submonoid M) :
    S.map (f : M ≃* N) = S.map f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : F} {S : Submonoid M} {y : N}
  statement: y in S.map f ↔ exists x in S, f x = y
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_map
  条件: {f : F} {S : 子幺半群 M} {y : N}
  结论: y in S.map f ↔ 存在 x in S, f x = y
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : F} {S : Submonoid M} {y : N} : y in S.map f ↔ exists x in S, f x = y := Iff.rfl

@[to_additive]
/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : F) {S : Submonoid M} {x : M} (hx : x in S)
  statement: f x in S.map f
  proof: mem_image_of_mem f hx

@[to_additive]

中文:
定理 mem_map_of_mem
  条件: (f : F) {S : 子幺半群 M} {x : M} (hx : x in S)
  结论: f x in S.map f
  证明: mem_image_of_mem f hx

@[to_additive]

Depends on / 依赖: mem_image_of_mem
-/
theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x in S) : f x in S.map f :=
  mem_image_of_mem f hx

@[to_additive]
/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : F) (S : Submonoid M) (x : S)
  statement: f x in S.map f
  proof: mem_map_of_mem f x.2

@[to_additive]

中文:
定理 apply_coe_mem_map
  条件: (f : F) (S : 子幺半群 M) (x : S)
  结论: f x in S.map f
  证明: mem_map_of_mem f x.2

@[to_additive]

Depends on / 依赖: mem_map_of_mem
-/
theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x in S.map f :=
  mem_map_of_mem f x.2

@[to_additive]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : N ->* P) (f : M ->* N)
  statement: (S.map f).map g = S.map (g.comp f)
  proof: SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp 1100)]

中文:
定理 map_map
  条件: (g : N ->* P) (f : M ->* N)
  结论: (S.map f).map g = S.map (g.comp f)
  证明: SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp 1100)]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : N ->* P) (f : M ->* N) : (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp 1100)]
/--
theorem `mem_map_iff_mem` / 定理 `mem_map_iff_mem`

English:
theorem mem_map_iff_mem
  given: {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M}
  proof: hf.mem_set_image

@[to_additive]

中文:
定理 mem_map_iff_mem
  条件: {f : F} (hf : 函数.单射 f) {S : 子幺半群 M} {x : M}
  证明: hf.mem_set_image

@[to_additive]

Depends on / 依赖: hf.mem_set_image, mem_set_image
-/
theorem mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M} :
    f x in S.map f ↔ x in S :=
  hf.mem_set_image

@[to_additive]
/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : F} {S : Submonoid M} {T : Submonoid N}
  proof: image_subset_iff

@[to_additive]

中文:
定理 map_le_iff_le_comap
  条件: {f : F} {S : 子幺半群 M} {T : 子幺半群 N}
  证明: image_subset_iff

@[to_additive]

Depends on / 依赖: image_subset_iff
-/
theorem map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} :
    S.map f <= T ↔ S <= T.comap f :=
  image_subset_iff

@[to_additive]
/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : F)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

@[to_additive]

中文:
定理 gc_map_comap
  条件: (f : F)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

@[to_additive]

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

@[to_additive]
/--
theorem `map_le_of_le_comap` / 定理 `map_le_of_le_comap`

English:
theorem map_le_of_le_comap
  given: {T : Submonoid N} {f : F}
  statement: S <= T.comap f -> S.map f <= T
  proof: (gc_map_comap f).l_le

@[to_additive]

中文:
定理 map_le_of_le_comap
  条件: {T : 子幺半群 N} {f : F}
  结论: S <= T.comap f -> S.map f <= T
  证明: (gc_map_comap f).l_le

@[to_additive]

Depends on / 依赖: gc_map_comap, l_le
-/
theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S <= T.comap f -> S.map f <= T :=
  (gc_map_comap f).l_le

@[to_additive]
/--
theorem `le_comap_of_map_le` / 定理 `le_comap_of_map_le`

English:
theorem le_comap_of_map_le
  given: {T : Submonoid N} {f : F}
  statement: S.map f <= T -> S <= T.comap f
  proof: (gc_map_comap f).le_u

@[to_additive]

中文:
定理 le_comap_of_map_le
  条件: {T : 子幺半群 N} {f : F}
  结论: S.map f <= T -> S <= T.comap f
  证明: (gc_map_comap f).le_u

@[to_additive]

Depends on / 依赖: gc_map_comap, le_u
-/
theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f <= T -> S <= T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: {f : F}
  statement: S <= (S.map f).comap f
  proof: (gc_map_comap f).le_u_l _

@[to_additive]

中文:
定理 le_comap_map
  条件: {f : F}
  结论: S <= (S.map f).comap f
  证明: (gc_map_comap f).le_u_l _

@[to_additive]

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map {f : F} : S <= (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: {S : Submonoid N} {f : F}
  statement: (S.comap f).map f <= S
  proof: (gc_map_comap f).l_u_le _

@[to_additive (attr := gcongr)]

中文:
定理 map_comap_le
  条件: {S : 子幺半群 N} {f : F}
  结论: (S.comap f).map f <= S
  证明: (gc_map_comap f).l_u_le _

@[to_additive (attr := gcongr)]

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f <= S :=
  (gc_map_comap f).l_u_le _

@[to_additive (attr := gcongr)]
/--
theorem `monotone_map` / 定理 `monotone_map`

English:
theorem monotone_map
  given: {f : F}
  statement: Monotone (map f)
  proof: (gc_map_comap f).monotone_l

@[to_additive (attr := gcongr)]

中文:
定理 monotone_map
  条件: {f : F}
  结论: 递增 (map f)
  证明: (gc_map_comap f).monotone_l

@[to_additive (attr := gcongr)]

Depends on / 依赖: gc_map_comap, monotone_l
-/
theorem monotone_map {f : F} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive (attr := gcongr)]
/--
theorem `monotone_comap` / 定理 `monotone_comap`

English:
theorem monotone_comap
  given: {f : F}
  statement: Monotone (comap f)
  proof: (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]

中文:
定理 monotone_comap
  条件: {f : F}
  结论: 递增 (comap f)
  证明: (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, monotone_u
-/
theorem monotone_comap {f : F} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]
/--
theorem `map_comap_map` / 定理 `map_comap_map`

English:
theorem map_comap_map
  given: {f : F}
  statement: ((S.map f).comap f).map f = S.map f
  proof: (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]

中文:
定理 map_comap_map
  条件: {f : F}
  结论: ((S.map f).comap f).map f = S.map f
  证明: (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, l_u_l_eq_l
-/
theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]
/--
theorem `comap_map_comap` / 定理 `comap_map_comap`

English:
theorem comap_map_comap
  given: {S : Submonoid N} {f : F}
  statement: ((S.comap f).map f).comap f = S.comap f
  proof: (gc_map_comap f).u_l_u_eq_u _

@[to_additive]

中文:
定理 comap_map_comap
  条件: {S : 子幺半群 N} {f : F}
  结论: ((S.comap f).map f).comap f = S.comap f
  证明: (gc_map_comap f).u_l_u_eq_u _

@[to_additive]

Depends on / 依赖: gc_map_comap, u_l_u_eq_u
-/
theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (S T : Submonoid M) (f : F)
  statement: (S ⊔ T).map f = S.map f ⊔ T.map f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[to_additive]

中文:
定理 map_sup
  条件: (S T : 子幺半群 M) (f : F)
  结论: (S ⊔ T).map f = S.map f ⊔ T.map f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[to_additive]

Depends on / 依赖: GaloisConnection, gc_map_comap, l_sup
-/
theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[to_additive]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : F) (s : ι -> Submonoid M)
  statement: (iSup s).map f = ⨆ i, (s i).map f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[to_additive]

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : F) (s : ι -> 子幺半群 M)
  结论: (iSup s).map f = ⨆ i, (s i).map f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[to_additive]

Depends on / 依赖: GaloisConnection, gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : F) (s : ι -> Submonoid M) : (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[to_additive]
/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (S T : Submonoid M) (f : F) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

@[to_additive]

中文:
定理 map_inf
  条件: (S T : 子幺半群 M) (f : F) (hf : 函数.单射 f)
  证明: SetLike.coe_injective (Set.image_inter hf)

@[to_additive]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (S T : Submonoid M) (f : F) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι] (f : F) (hf : 函数.单射 f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι -> Submonoid M) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (S T : Submonoid N) (f : F)
  statement: (S ⊓ T).comap f = S.comap f ⊓ T.comap f
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf

@[to_additive]

中文:
定理 comap_inf
  条件: (S T : 子幺半群 N) (f : F)
  结论: (S ⊓ T).comap f = S.comap f ⊓ T.comap f
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf

@[to_additive]

Depends on / 依赖: GaloisConnection, gc_map_comap, u_inf
-/
theorem comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf

@[to_additive]
/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : F) (s : ι -> Submonoid N)
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

@[to_additive (attr := simp)]

中文:
定理 comap_iInf
  条件: {ι : 类型层*} (f : F) (s : ι -> 子幺半群 N)
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

@[to_additive (attr := simp)]

Depends on / 依赖: GaloisConnection, gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : F) (s : ι -> Submonoid N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

@[to_additive (attr := simp)]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : F)
  statement: (⊥ : Submonoid M).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[to_additive]

中文:
定理 map_bot
  条件: (f : F)
  结论: (⊥ : 子幺半群 M).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[to_additive]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive]
/--
lemma `disjoint_map` / 引理 `disjoint_map`

English:
lemma disjoint_map
  given: {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : Disjoint H K)
  proof: by
  rw [disjoint_iff]; rw [← map_inf _ _ f hf]; rw [disjoint_iff.mp h]; rw [map_bot]

@[to_additive (attr := simp)]

中文:
引理 disjoint_map
  条件: {f : F} (hf : 函数.单射 f) {H K : 子幺半群 M} (h : Disjoint H K)
  证明: by
  rw [disjoint_iff]; rw [← map_inf _ _ f hf]; rw [disjoint_iff.mp h]; rw [map_bot]

@[to_additive (attr := simp)]

Depends on / 依赖: disjoint_iff, disjoint_iff.mp, map_bot, map_inf
-/
lemma disjoint_map {f : F} (hf : Function.Injective f) {H K : Submonoid M} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff]; rw [← map_inf _ _ f hf]; rw [disjoint_iff.mp h]; rw [map_bot]

@[to_additive (attr := simp)]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : F)
  statement: (⊤ : Submonoid N).comap f = ⊤
  proof: (gc_map_comap f).u_top

@[to_additive (attr := simp)]

中文:
定理 comap_top
  条件: (f : F)
  结论: (⊤ : 子幺半群 N).comap f = ⊤
  证明: (gc_map_comap f).u_top

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[to_additive (attr := simp)]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : Submonoid M)
  statement: S.map (MonoidHom.id M) = S
  proof: ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

中文:
定理 map_id
  条件: (S : 子幺半群 M)
  结论: S.map (幺半群态射.id M) = S
  证明: ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
-/
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type*} {f : F}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/]
/--
Definition of `gciMapComap` / `gciMapComap` 的定义

English:
definition gciMapComap
  signature: (hf : Function.Injective f)
  body: (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

中文:
定义 gciMapComap
  签名: (hf : 函数.单射 f)
  定义体: (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

Depends on / 依赖: eq_iff, gc_map_comap, hf.eq_iff, mem_comap, mem_map, toGaloisCoinsertion
-/
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf

@[to_additive]
/--
theorem `comap_map_eq_of_injective` / 定理 `comap_map_eq_of_injective`

English:
theorem comap_map_eq_of_injective
  given: (S : Submonoid M)
  statement: (S.map f).comap f = S
  proof: (gciMapComap hf).u_l_eq _

@[to_additive]

中文:
定理 comap_map_eq_of_injective
  条件: (S : 子幺半群 M)
  结论: (S.map f).comap f = S
  证明: (gciMapComap hf).u_l_eq _

@[to_additive]

Depends on / 依赖: gciMapComap, u_l_eq
-/
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

@[to_additive]
/--
theorem `comap_surjective_of_injective` / 定理 `comap_surjective_of_injective`

English:
theorem comap_surjective_of_injective
  statement: Function.Surjective (comap f)
  proof: (gciMapComap hf).u_surjective

@[to_additive]

中文:
定理 comap_surjective_of_injective
  结论: 函数.满射 (comap f)
  证明: (gciMapComap hf).u_surjective

@[to_additive]

Depends on / 依赖: gciMapComap, u_surjective
-/
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

@[to_additive]
/--
theorem `map_injective_of_injective` / 定理 `map_injective_of_injective`

English:
theorem map_injective_of_injective
  statement: Function.Injective (map f)
  proof: (gciMapComap hf).l_injective

@[to_additive]

中文:
定理 map_injective_of_injective
  结论: 函数.单射 (map f)
  证明: (gciMapComap hf).l_injective

@[to_additive]

Depends on / 依赖: gciMapComap, l_injective
-/
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

@[to_additive]
/--
theorem `comap_inf_map_of_injective` / 定理 `comap_inf_map_of_injective`

English:
theorem comap_inf_map_of_injective
  given: (S T : Submonoid M)
  statement: (S.map f ⊓ T.map f).comap f = S ⊓ T
  proof: (gciMapComap hf).u_inf_l _ _

@[to_additive]

中文:
定理 comap_inf_map_of_injective
  条件: (S T : 子幺半群 M)
  结论: (S.map f ⊓ T.map f).comap f = S ⊓ T
  证明: (gciMapComap hf).u_inf_l _ _

@[to_additive]

Depends on / 依赖: gciMapComap, u_inf_l
-/
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
/--
theorem `comap_iInf_map_of_injective` / 定理 `comap_iInf_map_of_injective`

English:
theorem comap_iInf_map_of_injective
  given: (S : ι -> Submonoid M)
  statement: (⨅ i, (S i).map f).comap f = iInf S
  proof: (gciMapComap hf).u_iInf_l _

@[to_additive]

中文:
定理 comap_iInf_map_of_injective
  条件: (S : ι -> 子幺半群 M)
  结论: (⨅ i, (S i).map f).comap f = iInf S
  证明: (gciMapComap hf).u_iInf_l _

@[to_additive]

Depends on / 依赖: gciMapComap, u_iInf_l
-/
theorem comap_iInf_map_of_injective (S : ι -> Submonoid M) : (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

@[to_additive]
/--
theorem `comap_sup_map_of_injective` / 定理 `comap_sup_map_of_injective`

English:
theorem comap_sup_map_of_injective
  given: (S T : Submonoid M)
  statement: (S.map f ⊔ T.map f).comap f = S ⊔ T
  proof: (gciMapComap hf).u_sup_l _ _

@[to_additive]

中文:
定理 comap_sup_map_of_injective
  条件: (S T : 子幺半群 M)
  结论: (S.map f ⊔ T.map f).comap f = S ⊔ T
  证明: (gciMapComap hf).u_sup_l _ _

@[to_additive]

Depends on / 依赖: gciMapComap, u_sup_l
-/
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
/--
theorem `comap_iSup_map_of_injective` / 定理 `comap_iSup_map_of_injective`

English:
theorem comap_iSup_map_of_injective
  given: (S : ι -> Submonoid M)
  statement: (⨆ i, (S i).map f).comap f = iSup S
  proof: (gciMapComap hf).u_iSup_l _

@[to_additive]

中文:
定理 comap_iSup_map_of_injective
  条件: (S : ι -> 子幺半群 M)
  结论: (⨆ i, (S i).map f).comap f = iSup S
  证明: (gciMapComap hf).u_iSup_l _

@[to_additive]

Depends on / 依赖: gciMapComap, u_iSup_l
-/
theorem comap_iSup_map_of_injective (S : ι -> Submonoid M) : (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

@[to_additive]
/--
theorem `map_le_map_iff_of_injective` / 定理 `map_le_map_iff_of_injective`

English:
theorem map_le_map_iff_of_injective
  given: {S T : Submonoid M}
  statement: S.map f <= T.map f ↔ S <= T
  proof: (gciMapComap hf).l_le_l_iff

@[to_additive]

中文:
定理 map_le_map_iff_of_injective
  条件: {S T : 子幺半群 M}
  结论: S.map f <= T.map f ↔ S <= T
  证明: (gciMapComap hf).l_le_l_iff

@[to_additive]

Depends on / 依赖: gciMapComap, l_le_l_iff
-/
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f <= T.map f ↔ S <= T :=
  (gciMapComap hf).l_le_l_iff

@[to_additive]
/--
theorem `map_strictMono_of_injective` / 定理 `map_strictMono_of_injective`

English:
theorem map_strictMono_of_injective
  statement: StrictMono (map f)
  proof: (gciMapComap hf).strictMono_l

中文:
定理 map_strictMono_of_injective
  结论: 严格递增 (map f)
  证明: (gciMapComap hf).strictMono_l

Depends on / 依赖: gciMapComap, strictMono_l
-/
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : F}

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/]
/--
Definition of `giMapComap` / `giMapComap` 的定义

English:
definition giMapComap
  signature: (hf : Function.Surjective f)
  body: (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

中文:
定义 giMapComap
  签名: (hf : 函数.满射 f)
  定义体: (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

Depends on / 依赖: gc_map_comap, mem_map, toGaloisInsertion
-/
def giMapComap (hf : Function.Surjective f) : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

variable (hf : Function.Surjective f)
include hf

@[to_additive]
/--
theorem `map_comap_eq_of_surjective` / 定理 `map_comap_eq_of_surjective`

English:
theorem map_comap_eq_of_surjective
  given: (S : Submonoid N)
  statement: (S.comap f).map f = S
  proof: (giMapComap hf).l_u_eq _

@[to_additive]

中文:
定理 map_comap_eq_of_surjective
  条件: (S : 子幺半群 N)
  结论: (S.comap f).map f = S
  证明: (giMapComap hf).l_u_eq _

@[to_additive]

Depends on / 依赖: giMapComap, l_u_eq
-/
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

@[to_additive]
/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  statement: Function.Surjective (map f)
  proof: (giMapComap hf).l_surjective

@[to_additive]

中文:
定理 map_surjective_of_surjective
  结论: 函数.满射 (map f)
  证明: (giMapComap hf).l_surjective

@[to_additive]

Depends on / 依赖: giMapComap, l_surjective
-/
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

@[to_additive]
/--
theorem `comap_injective_of_surjective` / 定理 `comap_injective_of_surjective`

English:
theorem comap_injective_of_surjective
  statement: Function.Injective (comap f)
  proof: (giMapComap hf).u_injective

@[to_additive]

中文:
定理 comap_injective_of_surjective
  结论: 函数.单射 (comap f)
  证明: (giMapComap hf).u_injective

@[to_additive]

Depends on / 依赖: giMapComap, u_injective
-/
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

@[to_additive]
/--
theorem `map_inf_comap_of_surjective` / 定理 `map_inf_comap_of_surjective`

English:
theorem map_inf_comap_of_surjective
  given: (S T : Submonoid N)
  statement: (S.comap f ⊓ T.comap f).map f = S ⊓ T
  proof: (giMapComap hf).l_inf_u _ _

@[to_additive]

中文:
定理 map_inf_comap_of_surjective
  条件: (S T : 子幺半群 N)
  结论: (S.comap f ⊓ T.comap f).map f = S ⊓ T
  证明: (giMapComap hf).l_inf_u _ _

@[to_additive]

Depends on / 依赖: giMapComap, l_inf_u
-/
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
/--
theorem `map_iInf_comap_of_surjective` / 定理 `map_iInf_comap_of_surjective`

English:
theorem map_iInf_comap_of_surjective
  given: (S : ι -> Submonoid N)
  statement: (⨅ i, (S i).comap f).map f = iInf S
  proof: (giMapComap hf).l_iInf_u _

@[to_additive]

中文:
定理 map_iInf_comap_of_surjective
  条件: (S : ι -> 子幺半群 N)
  结论: (⨅ i, (S i).comap f).map f = iInf S
  证明: (giMapComap hf).l_iInf_u _

@[to_additive]

Depends on / 依赖: giMapComap, l_iInf_u
-/
theorem map_iInf_comap_of_surjective (S : ι -> Submonoid N) : (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

@[to_additive]
/--
theorem `map_sup_comap_of_surjective` / 定理 `map_sup_comap_of_surjective`

English:
theorem map_sup_comap_of_surjective
  given: (S T : Submonoid N)
  statement: (S.comap f ⊔ T.comap f).map f = S ⊔ T
  proof: (giMapComap hf).l_sup_u _ _

@[to_additive]

中文:
定理 map_sup_comap_of_surjective
  条件: (S T : 子幺半群 N)
  结论: (S.comap f ⊔ T.comap f).map f = S ⊔ T
  证明: (giMapComap hf).l_sup_u _ _

@[to_additive]

Depends on / 依赖: giMapComap, l_sup_u
-/
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
/--
theorem `map_iSup_comap_of_surjective` / 定理 `map_iSup_comap_of_surjective`

English:
theorem map_iSup_comap_of_surjective
  given: (S : ι -> Submonoid N)
  statement: (⨆ i, (S i).comap f).map f = iSup S
  proof: (giMapComap hf).l_iSup_u _

@[to_additive]

中文:
定理 map_iSup_comap_of_surjective
  条件: (S : ι -> 子幺半群 N)
  结论: (⨆ i, (S i).comap f).map f = iSup S
  证明: (giMapComap hf).l_iSup_u _

@[to_additive]

Depends on / 依赖: giMapComap, l_iSup_u
-/
theorem map_iSup_comap_of_surjective (S : ι -> Submonoid N) : (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

@[to_additive]
/--
theorem `comap_le_comap_iff_of_surjective` / 定理 `comap_le_comap_iff_of_surjective`

English:
theorem comap_le_comap_iff_of_surjective
  given: {S T : Submonoid N}
  statement: S.comap f <= T.comap f ↔ S <= T
  proof: (giMapComap hf).u_le_u_iff

@[to_additive]

中文:
定理 comap_le_comap_iff_of_surjective
  条件: {S T : 子幺半群 N}
  结论: S.comap f <= T.comap f ↔ S <= T
  证明: (giMapComap hf).u_le_u_iff

@[to_additive]

Depends on / 依赖: giMapComap, u_le_u_iff
-/
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f <= T.comap f ↔ S <= T :=
  (giMapComap hf).u_le_u_iff

@[to_additive]
/--
theorem `comap_strictMono_of_surjective` / 定理 `comap_strictMono_of_surjective`

English:
theorem comap_strictMono_of_surjective
  statement: StrictMono (comap f)
  proof: (giMapComap hf).strictMono_u

中文:
定理 comap_strictMono_of_surjective
  结论: 严格递增 (comap f)
  证明: (giMapComap hf).strictMono_u

Depends on / 依赖: giMapComap, strictMono_u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

/-- The top `Submonoid` is isomorphic to the `Monoid`. -/
@[to_additive (attr := simps)
/-- The top `AddSubmonoid` is isomorphic to the `AddMonoid`. -/]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Submonoid M) ≃* M where
  body: x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]

中文:
定义 topEquiv
  签名: : (⊤ : 子幺半群 M) ≃* M where
  定义体: x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
-/
def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/--
theorem `topEquiv_toMonoidHom` / 定理 `topEquiv_toMonoidHom`

English:
theorem topEquiv_toMonoidHom
  statement: ((topEquiv : _ ≃* M) : _ ->* M) = (⊤ : Submonoid M).subtype
  proof: rfl

中文:
定理 topEquiv_toMonoidHom
  结论: ((topEquiv : _ ≃* M) : _ ->* M) = (⊤ : 子幺半群 M).subtype
  证明: rfl
-/
theorem topEquiv_toMonoidHom : ((topEquiv : _ ≃* M) : _ ->* M) = (⊤ : Submonoid M).subtype :=
  rfl

/-- A `Subgroup` is isomorphic to its image under an injective function. If you have an isomorphism,
use `MulEquiv.submonoidMap` for better definitional equalities. -/
@[to_additive /-- An `AddSubgroup` is isomorphic to its image under an injective function. If
you have an isomorphism, use `AddEquiv.addSubmonoidMap` for better definitional equalities. -/]
/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (f : M ->* N) (hf : Function.Injective f)
  body: { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]

中文:
定义 equivMapOfInjective
  签名: (f : M ->* N) (hf : 函数.单射 f)
  定义体: { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.Set.image, Subtype, Subtype.ext, f.map_mul, map_mul
-/
noncomputable def equivMapOfInjective (f : M ->* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }

@[to_additive (attr := simp)]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  given: (f : M ->* N) (hf : Function.Injective f) (x : S)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_equivMapOfInjective_apply
  条件: (f : M ->* N) (hf : 函数.单射 f) (x : S)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_equivMapOfInjective_apply (f : M ->* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `closure_closure_coe_preimage` / 定理 `closure_closure_coe_preimage`

English:
theorem closure_closure_coe_preimage
  given: {s : Set M}
  statement: closure (((↑) : closure s -> M) ⁻¹' s) = ⊤
  proof: eq_top_iff.2 fun x _ => Subtype.recOn x fun _ hx' =>
    closure_induction (fun _ h => subset_closure h) (one_mem _) (fun _ _ _ _ => mul_mem) hx'

中文:
定理 closure_closure_coe_preimage
  条件: {s : 集合 M}
  结论: closure (((↑) : closure s -> M) ⁻¹' s) = ⊤
  证明: eq_top_iff.2 fun x _ => Subtype.recOn x fun _ hx' =>
    closure_induction (fun _ h => subset_closure h) (one_mem _) (fun _ _ _ _ => mul_mem) hx'

Depends on / 依赖: Subtype, Subtype.recOn, closure_induction, eq_top_iff, mul_mem, one_mem, subset_closure
-/
theorem closure_closure_coe_preimage {s : Set M} : closure (((↑) : closure s -> M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x _ => Subtype.recOn x fun _ hx' =>
    closure_induction (fun _ h => subset_closure h) (one_mem _) (fun _ _ _ _ => mul_mem) hx'

/-- Given `Submonoid`s `s`, `t` of `Monoid`s `M`, `N` respectively, `s × t` as a `Submonoid` of
`M × N`. -/
@[to_additive prod
  /-- Given `AddSubmonoid`s `s`, `t` of `AddMonoid`s `A`, `B` respectively, `s × t` as an
  `AddSubmonoid` of `A × B`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : Submonoid M) (t : Submonoid N)
  body: s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]

中文:
定义 乘积
  签名: (s : 子幺半群 M) (t : 子幺半群 N)
  定义体: s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]
-/
def prod (s : Submonoid M) (t : Submonoid N) : Submonoid (M × N) where
  carrier := s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Submonoid M) (t : Submonoid N)
  proof: rfl

@[to_additive mem_prod]

中文:
定理 coe_prod
  条件: (s : 子幺半群 M) (t : 子幺半群 N)
  证明: rfl

@[to_additive mem_prod]
-/
theorem coe_prod (s : Submonoid M) (t : Submonoid N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : Submonoid M} {t : Submonoid N} {p : M × N}
  proof: Iff.rfl

@[to_additive prod_mono]

中文:
定理 mem_prod
  条件: {s : 子幺半群 M} {t : 子幺半群 N} {p : M × N}
  证明: Iff.rfl

@[to_additive prod_mono]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} :
    p in s.prod t ↔ p.1 in s ∧ p.2 in t :=
  Iff.rfl

@[to_additive prod_mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ <= s₂) (ht : t₁ <= t₂)
  proof: Set.prod_mono hs ht

@[to_additive prod_top]

中文:
定理 prod_mono
  条件: {s₁ s₂ : 子幺半群 M} {t₁ t₂ : 子幺半群 N} (hs : s₁ <= s₂) (ht : t₁ <= t₂)
  证明: Set.prod_mono hs ht

@[to_additive prod_top]

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ <= s₂) (ht : t₁ <= t₂) :
    s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (s : Submonoid M)
  statement: s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N)
  proof: ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]

中文:
定理 prod_top
  条件: (s : 子幺半群 M)
  结论: s.乘积 (⊤ : 子幺半群 N) = s.comap (幺半群态射.fst M N)
  证明: ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]

Depends on / 依赖: MonoidHom, MonoidHom.coe_fst, coe_fst, mem_prod
-/
theorem prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]
/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (s : Submonoid N)
  statement: (⊤ : Submonoid M).prod s = s.comap (MonoidHom.snd M N)
  proof: ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]

中文:
定理 top_prod
  条件: (s : 子幺半群 N)
  结论: (⊤ : 子幺半群 M).乘积 s = s.comap (幺半群态射.snd M N)
  证明: ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]

Depends on / 依赖: MonoidHom, MonoidHom.coe_snd, coe_snd, mem_prod
-/
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod s = s.comap (MonoidHom.snd M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤
  proof: (top_prod _).trans comap_top _

@[to_additive bot_prod_bot]

中文:
定理 top_prod_top
  结论: (⊤ : 子幺半群 M).乘积 (⊤ : 子幺半群 N) = ⊤
  证明: (top_prod _).trans comap_top _

@[to_additive bot_prod_bot]

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤ :=
(top_prod _).trans comap_top _

@[to_additive bot_prod_bot]
/--
theorem `bot_prod_bot` / 定理 `bot_prod_bot`

English:
theorem bot_prod_bot
  statement: (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥
  proof: SetLike.coe_injective by simp [coe_prod]

中文:
定理 bot_prod_bot
  结论: (⊥ : 子幺半群 M).乘积 (⊥ : 子幺半群 N) = ⊥
  证明: SetLike.coe_injective by simp [coe_prod]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, coe_prod
-/
theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ :=
SetLike.coe_injective by simp [coe_prod]

/-- The product of `Submonoid`s is isomorphic to their product as `Monoid`s. -/
@[to_additive prodEquiv
  /-- The product of `AddSubmonoid`s is isomorphic to their product as `AddMonoid`s. -/]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (s : Submonoid M) (t : Submonoid N)
  body: { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

中文:
定义 prodEquiv
  签名: (s : 子幺半群 M) (t : 子幺半群 N)
  定义体: { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.Set.prod, map_mul
-/
def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

open MonoidHom

@[to_additive]
/--
theorem `map_inl` / 定理 `map_inl`

English:
theorem map_inl
  given: (s : Submonoid M)
  statement: s.map (inl M N) = s.prod ⊥
  proof: ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
⟨p.1, hps, Prod.ext rfl (Set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]

中文:
定理 map_inl
  条件: (s : 子幺半群 M)
  结论: s.map (inl M N) = s.乘积 ⊥
  证明: ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
⟨p.1, hps, Prod.ext rfl (Set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]

Depends on / 依赖: Prod.ext, Set.eq_of_mem_singleton, Set.mem_singleton, eq_of_mem_singleton, mem_singleton
-/
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.prod ⊥ :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
⟨p.1, hps, Prod.ext rfl (Set.eq_of_mem_singleton hp1).symm⟩⟩

@[to_additive]
/--
theorem `map_inr` / 定理 `map_inr`

English:
theorem map_inr
  given: (s : Submonoid N)
  statement: s.map (inr M N) = prod ⊥ s
  proof: ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[to_additive (attr := simp) prod_bot_sup_bot_prod]

中文:
定理 map_inr
  条件: (s : 子幺半群 N)
  结论: s.map (inr M N) = 乘积 ⊥ s
  证明: ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[to_additive (attr := simp) prod_bot_sup_bot_prod]

Depends on / 依赖: Prod.ext, Set.eq_of_mem_singleton, Set.mem_singleton, eq_of_mem_singleton, mem_singleton
-/
theorem map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s :=
  ext fun p =>
    ⟨fun ⟨_, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩

@[to_additive (attr := simp) prod_bot_sup_bot_prod]
/--
theorem `prod_bot_sup_bot_prod` / 定理 `prod_bot_sup_bot_prod`

English:
theorem prod_bot_sup_bot_prod
  given: (s : Submonoid M) (t : Submonoid N)
  proof: (le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : prod s ⊥ <= prod s ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t <= prod s ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2

中文:
定理 prod_bot_sup_bot_prod
  条件: (s : 子幺半群 M) (t : 子幺半群 N)
  证明: (le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : prod s ⊥ <= prod s ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t <= prod s ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2

Depends on / 依赖: Prod.fst_mul_snd, Set.mem_singleton, bot_le, fst_mul_snd, le_antisymm, le_refl, le_sup_left, le_sup_right, mem_singleton, mul_mem, prod_mono, sup_le
-/
theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    (prod s ⊥) ⊔ (prod ⊥ t) = prod s t :=
  (le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))))
    fun p hp => Prod.fst_mul_snd p ▸ mul_mem
        ((le_sup_left : prod s ⊥ <= prod s ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t <= prod s ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)

@[to_additive]
/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : M ≃* N} {K : Submonoid M} {x : N}
  proof: Set.mem_image_equiv

@[to_additive]

中文:
定理 mem_map_equiv
  条件: {f : M ≃* N} {K : 子幺半群 M} {x : N}
  证明: Set.mem_image_equiv

@[to_additive]

Depends on / 依赖: Set.mem_image_equiv, mem_image_equiv
-/
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} :
    x in K.map f.toMonoidHom ↔ f.symm x in K :=
  Set.mem_image_equiv

@[to_additive]
/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : M ≃* N) (K : Submonoid M)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : M ≃* N) (K : 子幺半群 M)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]
/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : N ≃* M) (K : Submonoid M)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : N ≃* M) (K : 子幺半群 M)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]
/--
theorem `map_equiv_top` / 定理 `map_equiv_top`

English:
theorem map_equiv_top
  given: (f : M ≃* N)
  statement: (⊤ : Submonoid M).map f = ⊤
  proof: SetLike.coe_injective Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]

中文:
定理 map_equiv_top
  条件: (f : M ≃* N)
  结论: (⊤ : 子幺半群 M).map f = ⊤
  证明: SetLike.coe_injective Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]

Depends on / 依赖: Set.image_univ.trans, SetLike, SetLike.coe_injective, coe_injective, f.surjective.range_eq, image_univ, range_eq, surjective
-/
theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f = ⊤ :=
SetLike.coe_injective Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]
/--
theorem `le_prod_iff` / 定理 `le_prod_iff`

English:
theorem le_prod_iff
  given: {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)}
  proof: by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

@[to_additive prod_le_iff]

中文:
定理 le_prod_iff
  条件: {s : 子幺半群 M} {t : 子幺半群 N} {u : 子幺半群 (M × N)}
  证明: by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

@[to_additive prod_le_iff]
-/
theorem le_prod_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    u <= s.prod t ↔ u.map (fst M N) <= s ∧ u.map (snd M N) <= t := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

@[to_additive prod_le_iff]
/--
theorem `prod_le_iff` / 定理 `prod_le_iff`

English:
theorem prod_le_iff
  given: {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)}
  proof: by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 in u := by
      apply hH
     

中文:
定理 prod_le_iff
  条件: {s : 子幺半群 M} {t : 子幺半群 N} {u : 子幺半群 (M × N)}
  证明: by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 in u := by
      apply hH
     

Depends on / 依赖: Submonoid, Submonoid.mul_mem, Submonoid.one_mem, mul_mem, one_mem
-/
theorem prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    s.prod t <= u ↔ s.map (inl M N) <= u ∧ t.map (inr M N) <= u := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 in u := by
      apply hH
      simpa using h1
    have h2' : inr M N x2 in u := by
      apply hK
      simpa using h2
    simpa using Submonoid.mul_mem _ h1' h2'

@[to_additive closure_prod]
/--
theorem `closure_prod` / 定理 `closure_prod`

English:
theorem closure_prod
  given: {s : Set M} {t : Set N} (hs : 1 in s) (ht : 1 in t)
  proof: le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
map_le_of_le_comap _ closure_le.2 fun _x hx => subset_closure ⟨hx, ht⟩,
map_le_of_le_comap _ closure_le.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

@[to_additive (attr := simp) cl

中文:
定理 closure_prod
  条件: {s : 集合 M} {t : 集合 N} (hs : 1 in s) (ht : 1 in t)
  证明: le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
map_le_of_le_comap _ closure_le.2 fun _x hx => subset_closure ⟨hx, ht⟩,
map_le_of_le_comap _ closure_le.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

@[to_additive (attr := simp) cl

Depends on / 依赖: Set.prod_subset_prod_iff, closure_le, le_antisymm, map_le_of_le_comap, prod_le_iff, prod_subset_prod_iff, subset_closure
-/
theorem closure_prod {s : Set M} {t : Set N} (hs : 1 in s) (ht : 1 in t) :
    closure (s ×ˢ t) = (closure s).prod (closure t) :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
map_le_of_le_comap _ closure_le.2 fun _x hx => subset_closure ⟨hx, ht⟩,
map_le_of_le_comap _ closure_le.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

@[to_additive (attr := simp) closure_prod_zero]
/--
lemma `closure_prod_one` / 引理 `closure_prod_one`

English:
lemma closure_prod_one
  given: (s : Set M)
  statement: closure (s ×ˢ ({1} : Set N)) = (closure s).prod ⊥
  proof: le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, .rfl⟩)
    (prod_le_iff.2 ⟨
map_le_of_le_comap _ closure_le.2 fun _x hx => subset_closure ⟨hx, rfl⟩, by simp⟩)

@[to_additive (attr := simp) closure_zero_prod]

中文:
引理 closure_prod_one
  条件: (s : 集合 M)
  结论: closure (s ×ˢ ({1} : 集合 N)) = (closure s).乘积 ⊥
  证明: le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, .rfl⟩)
    (prod_le_iff.2 ⟨
map_le_of_le_comap _ closure_le.2 fun _x hx => subset_closure ⟨hx, rfl⟩, by simp⟩)

@[to_additive (attr := simp) closure_zero_prod]

Depends on / 依赖: Set.prod_subset_prod_iff, closure_le, le_antisymm, map_le_of_le_comap, prod_le_iff, prod_subset_prod_iff, subset_closure
-/
lemma closure_prod_one (s : Set M) : closure (s ×ˢ ({1} : Set N)) = (closure s).prod ⊥ :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, .rfl⟩)
    (prod_le_iff.2 ⟨
map_le_of_le_comap _ closure_le.2 fun _x hx => subset_closure ⟨hx, rfl⟩, by simp⟩)

@[to_additive (attr := simp) closure_zero_prod]
/--
lemma `closure_one_prod` / 引理 `closure_one_prod`

English:
lemma closure_one_prod
  given: (t : Set N)
  statement: closure (({1} : Set M) ×ˢ t) = .prod ⊥ (closure t)
  proof: le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨.rfl, subset_closure⟩)
    (prod_le_iff.2 ⟨by simp,
map_le_of_le_comap _ closure_le.2 fun _y hy => subset_closure ⟨rfl, hy⟩⟩)

中文:
引理 closure_one_prod
  条件: (t : 集合 N)
  结论: closure (({1} : 集合 M) ×ˢ t) = .乘积 ⊥ (closure t)
  证明: le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨.rfl, subset_closure⟩)
    (prod_le_iff.2 ⟨by simp,
map_le_of_le_comap _ closure_le.2 fun _y hy => subset_closure ⟨rfl, hy⟩⟩)

Depends on / 依赖: Set.prod_subset_prod_iff, closure_le, le_antisymm, map_le_of_le_comap, prod_le_iff, prod_subset_prod_iff, subset_closure
-/
lemma closure_one_prod (t : Set N) : closure (({1} : Set M) ×ˢ t) = .prod ⊥ (closure t) :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨.rfl, subset_closure⟩)
    (prod_le_iff.2 ⟨by simp,
map_le_of_le_comap _ closure_le.2 fun _y hy => subset_closure ⟨rfl, hy⟩⟩)

end Submonoid

namespace MonoidHom

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

open Submonoid

library_note «range copy pattern» /--
For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`Set.range f`. In particular this means that the types `↥(Set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`Set.range` could have been defined as `f '' Set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `Set.range`, and that it introduces a redundant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`MonoidHom.mrange` would be `(⊤ : Submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `Submonoid.copy` as follows:
```lean
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : Submonoid M) (s : Set M) (hs : s = S)
  body: { carrier := s,
    one_mem' := hs.symm ▸ S.one_mem',
    mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean

中文:
定义 copy
  签名: (S : 子幺半群 M) (s : 集合 M) (hs : s = S)
  定义体: { carrier := s,
    one_mem' := hs.symm ▸ S.one_mem',
    mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
-/
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M :=
  { carrier := s,
    one_mem' := hs.symm ▸ S.one_mem',
    mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
/--
Definition of `mrange` / `mrange` 的定义

English:
definition mrange
  signature: (f : M →* N)
  body: ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
```
-/

中文:
定义 mrange
  签名: (f : M →* N)
  定义体: ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
```
-/

Depends on / 依赖: Set.image_univ.symm, Set.range, Submonoid, image_univ
-/
def mrange (f : M →* N) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
```
-/

/-- The range of a `MonoidHom` is a `Submonoid`. See Note [range copy pattern]. -/
@[to_additive /-- The range of an `AddMonoidHom` is an `AddSubmonoid`. -/]
/--
Definition of `mrange` / `mrange` 的定义

English:
definition mrange
  signature: (f : F)
  body: ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]

中文:
定义 mrange
  签名: (f : F)
  定义体: ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]
-/
def mrange (f : F) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]
/--
theorem `coe_mrange` / 定理 `coe_mrange`

English:
theorem coe_mrange
  given: (f : F)
  statement: (mrange f : Set N) = Set.range f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mrange
  条件: (f : F)
  结论: (mrange f : 集合 N) = 集合.range f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mrange (f : F) : (mrange f : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_mrange` / 定理 `mem_mrange`

English:
theorem mem_mrange
  given: {f : F} {y : N}
  statement: y in mrange f ↔ exists x, f x = y
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_mrange
  条件: {f : F} {y : N}
  结论: y in mrange f ↔ 存在 x, f x = y
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mrange {f : F} {y : N} : y in mrange f ↔ exists x, f x = y :=
  Iff.rfl

@[to_additive]
/--
lemma `mrange_comp` / 引理 `mrange_comp`

English:
lemma mrange_comp
  given: {O : Type*} [MulOneClass O] (f : N ->* O) (g : M ->* N)
  proof: SetLike.coe_injective Set.range_comp f _

@[to_additive]

中文:
引理 mrange_comp
  条件: {O : 类型} [MulOne类 O] (f : N ->* O) (g : M ->* N)
  证明: SetLike.coe_injective Set.range_comp f _

@[to_additive]

Depends on / 依赖: Set.range_comp, SetLike, SetLike.coe_injective, coe_injective, range_comp
-/
lemma mrange_comp {O : Type*} [MulOneClass O] (f : N ->* O) (g : M ->* N) :
mrange (f.comp g) = (mrange g).map f := SetLike.coe_injective Set.range_comp f _

@[to_additive]
/--
theorem `mrange_eq_map` / 定理 `mrange_eq_map`

English:
theorem mrange_eq_map
  given: (f : F)
  statement: mrange f = (⊤ : Submonoid M).map f
  proof: Submonoid.copy_eq _

@[to_additive (attr := simp)]

中文:
定理 mrange_eq_map
  条件: (f : F)
  结论: mrange f = (⊤ : 子幺半群 M).map f
  证明: Submonoid.copy_eq _

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.copy_eq, copy_eq
-/
theorem mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f :=
  Submonoid.copy_eq _

@[to_additive (attr := simp)]
/--
theorem `mrange_id` / 定理 `mrange_id`

English:
theorem mrange_id
  statement: mrange (MonoidHom.id M) = ⊤
  proof: by
  simp [mrange_eq_map]

@[to_additive]

中文:
定理 mrange_id
  结论: mrange (幺半群态射.id M) = ⊤
  证明: by
  simp [mrange_eq_map]

@[to_additive]

Depends on / 依赖: mrange_eq_map
-/
theorem mrange_id : mrange (MonoidHom.id M) = ⊤ := by
  simp [mrange_eq_map]

@[to_additive]
/--
theorem `map_mrange` / 定理 `map_mrange`

English:
theorem map_mrange
  given: (g : N ->* P) (f : M ->* N)
  statement: (mrange f).map g = mrange (comp g f)
  proof: by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f

@[to_additive]

中文:
定理 map_mrange
  条件: (g : N ->* P) (f : M ->* N)
  结论: (mrange f).map g = mrange (comp g f)
  证明: by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f

@[to_additive]

Depends on / 依赖: Submonoid, map_map, mrange_eq_map
-/
theorem map_mrange (g : N ->* P) (f : M ->* N) : (mrange f).map g = mrange (comp g f) := by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f

@[to_additive]
/--
theorem `mrange_eq_top` / 定理 `mrange_eq_top`

English:
theorem mrange_eq_top
  given: {f : F}
  statement: mrange f = (⊤ : Submonoid N) ↔ Surjective f
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_mrange, coe_top]) Set.range_eq_univ

@[to_additive (attr := simp) mrange_prodMap]

中文:
定理 mrange_eq_top
  条件: {f : F}
  结论: mrange f = (⊤ : 子幺半群 N) ↔ 满射 f
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_mrange, coe_top]) Set.range_eq_univ

@[to_additive (attr := simp) mrange_prodMap]

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_mrange, coe_top, range_eq_univ
-/
theorem mrange_eq_top {f : F} : mrange f = (⊤ : Submonoid N) ↔ Surjective f :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_mrange, coe_top]) Set.range_eq_univ

@[to_additive (attr := simp) mrange_prodMap]
/--
lemma `mrange_prodMap` / 引理 `mrange_prodMap`

English:
lemma mrange_prodMap
  statement: {M' N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M ->* N)
  proof: SetLike.coe_injective Set.range_prodMap

中文:
引理 mrange_prodMap
  结论: {M' N' : 类型} [MulOne类 M'] [MulOne类 N'] (f : M ->* N)
  证明: SetLike.coe_injective Set.range_prodMap

Depends on / 依赖: Set.range_prodMap, SetLike, SetLike.coe_injective, coe_injective, range_prodMap
-/
lemma mrange_prodMap {M' N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M ->* N)
    (g : M' ->* N') :
    MonoidHom.mrange (f.prodMap g) = (MonoidHom.mrange f).prod (MonoidHom.mrange g) :=
  SetLike.coe_injective Set.range_prodMap

/-- The range of a surjective `MonoidHom` is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddMonoidHom` is the whole of the codomain. -/]
/--
theorem `mrange_eq_top_of_surjective` / 定理 `mrange_eq_top_of_surjective`

English:
theorem mrange_eq_top_of_surjective
  given: (f : F) (hf : Function.Surjective f)
  proof: mrange_eq_top.2 hf

@[to_additive]

中文:
定理 mrange_eq_top_of_surjective
  条件: (f : F) (hf : 函数.满射 f)
  证明: mrange_eq_top.2 hf

@[to_additive]

Depends on / 依赖: mrange_eq_top
-/
theorem mrange_eq_top_of_surjective (f : F) (hf : Function.Surjective f) :
    mrange f = (⊤ : Submonoid N) :=
  mrange_eq_top.2 hf

@[to_additive]
/--
theorem `mclosure_preimage_le` / 定理 `mclosure_preimage_le`

English:
theorem mclosure_preimage_le
  given: (f : F) (s : Set N)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 mclosure_preimage_le
  条件: (f : F) (s : 集合 N)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/-- The image under a `MonoidHom` of the `Submonoid` generated by a set equals the `Submonoid`
generated by the image of the set. -/
@[to_additive
  /-- The image under an `AddMonoidHom` of the `AddSubmonoid` generated by a set equals the
  `AddSubmonoid` generated by the image of the set. -/]
/--
theorem `map_mclosure` / 定理 `map_mclosure`

English:
theorem map_mclosure
  given: (f : F) (s : Set M)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Submonoid.gi N).gc (Submonoid.gi M).gc
    fun _ => rfl

@[to_additive (attr := simp)]

中文:
定理 map_mclosure
  条件: (f : F) (s : 集合 M)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Submonoid.gi N).gc (Submonoid.gi M).gc
    fun _ => rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Set.image_preimage.l_comm_of_u_comm, Submonoid, Submonoid.gi, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Submonoid.gi N).gc (Submonoid.gi M).gc
    fun _ => rfl

@[to_additive (attr := simp)]
/--
theorem `mclosure_range` / 定理 `mclosure_range`

English:
theorem mclosure_range
  given: (f : F)
  statement: closure (Set.range f) = mrange f
  proof: by
  rw [← Set.image_univ]; rw [← map_mclosure]; rw [mrange_eq_map]; rw [closure_univ]

中文:
定理 mclosure_range
  条件: (f : F)
  结论: closure (集合.range f) = mrange f
  证明: by
  rw [← Set.image_univ]; rw [← map_mclosure]; rw [mrange_eq_map]; rw [closure_univ]

Depends on / 依赖: Set.image_univ, closure_univ, image_univ, map_mclosure, mrange_eq_map
-/
theorem mclosure_range (f : F) : closure (Set.range f) = mrange f := by
  rw [← Set.image_univ]; rw [← map_mclosure]; rw [mrange_eq_map]; rw [closure_univ]

/-- Restriction of a `MonoidHom` to a `Submonoid` of the domain. -/
@[to_additive /-- Restriction of an `AddMonoidHom` to an `AddSubmonoid` of the domain. -/]
/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M ->* N)
  body: f.comp (SubmonoidClass.subtype _)

@[to_additive (attr := simp)]

中文:
定义 domRestrict
  签名: {N S : 类型} [MulOne类 N] [集合状 S M] [子幺半群类 S M] (f : M ->* N)
  定义体: f.comp (SubmonoidClass.subtype _)

@[to_additive (attr := simp)]

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, f.comp, subtype
-/
def domRestrict {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M ->* N)
    (s : S) : s ->* N :=
  f.comp (SubmonoidClass.subtype _)

@[to_additive (attr := simp)]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  statement: {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
  proof: rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_apply := _root_.AddMonoidHom.domRestrict_apply

@[to_additive (attr := simp)]

中文:
定理 domRestrict_apply
  结论: {N S : 类型} [MulOne类 N] [集合状 S M] [子幺半群类 S M]
  证明: rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_apply := _root_.AddMonoidHom.domRestrict_apply

@[to_additive (attr := simp)]
-/
theorem domRestrict_apply {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
    (f : M ->* N) (s : S) (x : s) : f.domRestrict s x = f x :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_apply := _root_.AddMonoidHom.domRestrict_apply

@[to_additive (attr := simp)]
/--
theorem `domRestrict_eq_one_iff` / 定理 `domRestrict_eq_one_iff`

English:
theorem domRestrict_eq_one_iff
  statement: {N S : Type*} [MulOneClass N] {f : M ->* N} [SetLike S M]
  proof: by
  simp [MonoidHom.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_eq_zero_iff := _root_.AddMonoidHom.domRestrict_eq_zero_iff

@[to_additive (attr := simp)]

中文:
定理 domRestrict_eq_one_iff
  结论: {N S : 类型} [MulOne类 N] {f : M ->* N} [集合状 S M]
  证明: by
  simp [MonoidHom.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_eq_zero_iff := _root_.AddMonoidHom.domRestrict_eq_zero_iff

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.ext_iff, ext_iff
-/
theorem domRestrict_eq_one_iff {N S : Type*} [MulOneClass N] {f : M ->* N} [SetLike S M]
    [SubmonoidClass S M] {s : S} :
    f.domRestrict s = 1 ↔ forall x in s, f x = 1 := by
  simp [MonoidHom.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_eq_zero_iff := _root_.AddMonoidHom.domRestrict_eq_zero_iff

@[to_additive (attr := simp)]
/--
theorem `domRestrict_mrange` / 定理 `domRestrict_mrange`

English:
theorem domRestrict_mrange
  given: (f : M ->* N)
  statement: mrange (f.domRestrict S) = S.map f
  proof: by
  simp [SetLike.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_mrange := domRestrict_mrange
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mrange := _root_.AddMonoidHom.domRestrict_mrange

中文:
定理 domRestrict_mrange
  条件: (f : M ->* N)
  结论: mrange (f.domRestrict S) = S.map f
  证明: by
  simp [SetLike.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_mrange := domRestrict_mrange
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mrange := _root_.AddMonoidHom.domRestrict_mrange

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem domRestrict_mrange (f : M ->* N) : mrange (f.domRestrict S) = S.map f := by
  simp [SetLike.ext_iff]

@[deprecated (since := "2026-07-19")] alias restrict_mrange := domRestrict_mrange
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mrange := _root_.AddMonoidHom.domRestrict_mrange

/-- A version of `MonoidHom.domRestrict` as a homomorphism. -/
@[to_additive (attr := simps apply)
  /-- A version of `AddMonoidHom.domRestrict` as a homomorphism. -/]
/--
Definition of `domRestrictHom` / `domRestrictHom` 的定义

English:
definition domRestrictHom
  signature: {S : Type*} [SetLike S M] [SubmonoidClass S M] (M' : S) (A : Type*)
  body: f.domRestrict M'
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHom := _root_.AddMonoidHom.domRestrictHom
@[deprecated (since := "2026-07-19")

中文:
定义 domRestrictHom
  签名: {S : 类型} [集合状 S M] [子幺半群类 S M] (M' : S) (A : 类型)
  定义体: f.domRestrict M'
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHom := _root_.AddMonoidHom.domRestrictHom
@[deprecated (since := "2026-07-19")

Depends on / 依赖: domRestrict, f.domRestrict
-/
def domRestrictHom {S : Type*} [SetLike S M] [SubmonoidClass S M] (M' : S) (A : Type*)
    [CommMonoid A] : (M ->* A) ->* (M' ->* A) where
  toFun f := f.domRestrict M'
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHom := _root_.AddMonoidHom.domRestrictHom
@[deprecated (since := "2026-07-19")] alias restrictHom_apply := domRestrictHom_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrictHom_apply := _root_.AddMonoidHom.domRestrictHom_apply

/-- Restriction of a `MonoidHom` to a `Submonoid` of the codomain. -/
@[to_additive (attr := simps apply)
  /-- Restriction of an `AddMonoidHom` to an `AddSubmonoid` of the codomain. -/]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: {S} [SetLike S N] [SubmonoidClass S N] (f : M ->* N) (s : S) (h : forall x, f x in s)
  body: ⟨f n, h n⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive (attr := simp)]

中文:
定义 codRestrict
  签名: {S} [集合状 S N] [子幺半群类 S N] (f : M ->* N) (s : S) (h : 对任意 x, f x in s)
  定义体: ⟨f n, h n⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive (attr := simp)]
-/
def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M ->* N) (s : S) (h : forall x, f x in s) :
    M ->* s where
  toFun n := ⟨f n, h n⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive (attr := simp)]
/--
lemma `injective_codRestrict` / 引理 `injective_codRestrict`

English:
lemma injective_codRestrict
  statement: {S} [SetLike S N] [SubmonoidClass S N] (f : M ->* N) (s : S)
  proof: ⟨fun H _ _ hxy => H Subtype.ext hxy, fun H _ _ hxy => H (congr_arg Subtype.val hxy)⟩

中文:
引理 injective_codRestrict
  结论: {S} [集合状 S N] [子幺半群类 S N] (f : M ->* N) (s : S)
  证明: ⟨fun H _ _ hxy => H Subtype.ext hxy, fun H _ _ hxy => H (congr_arg Subtype.val hxy)⟩

Depends on / 依赖: Subtype, Subtype.ext, Subtype.val, congr_arg
-/
lemma injective_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M ->* N) (s : S)
    (h : forall x, f x in s) : Function.Injective (f.codRestrict s h) ↔ Function.Injective f :=
⟨fun H _ _ hxy => H Subtype.ext hxy, fun H _ _ hxy => H (congr_arg Subtype.val hxy)⟩

/-- Restriction of a `MonoidHom` to its range interpreted as a `Submonoid`. -/
@[to_additive
  /-- Restriction of an `AddMonoidHom` to its range interpreted as an `AddSubmonoid`. -/]
/--
Definition of `mrangeRestrict` / `mrangeRestrict` 的定义

English:
definition mrangeRestrict
  signature: {N} [MulOneClass N] (f : M ->* N)
  body: (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]

中文:
定义 mrangeRestrict
  签名: {N} [MulOne类 N] (f : M ->* N)
  定义体: (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]

Depends on / 依赖: codRestrict, f.codRestrict, mrange
-/
def mrangeRestrict {N} [MulOneClass N] (f : M ->* N) : M ->* (mrange f) :=
  (f.codRestrict (mrange f)) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
/--
theorem `coe_mrangeRestrict` / 定理 `coe_mrangeRestrict`

English:
theorem coe_mrangeRestrict
  given: {N} [MulOneClass N] (f : M ->* N) (x : M)
  proof: rfl

@[to_additive]

中文:
定理 coe_mrangeRestrict
  条件: {N} [MulOne类 N] (f : M ->* N) (x : M)
  证明: rfl

@[to_additive]
-/
theorem coe_mrangeRestrict {N} [MulOneClass N] (f : M ->* N) (x : M) :
    (f.mrangeRestrict x : N) = f x :=
  rfl

@[to_additive]
/--
theorem `mrangeRestrict_surjective` / 定理 `mrangeRestrict_surjective`

English:
theorem mrangeRestrict_surjective
  given: (f : M ->* N)
  statement: Function.Surjective f.mrangeRestrict
  proof: fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

中文:
定理 mrangeRestrict_surjective
  条件: (f : M ->* N)
  结论: 函数.满射 f.mrangeRestrict
  证明: fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩
-/
theorem mrangeRestrict_surjective (f : M ->* N) : Function.Surjective f.mrangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

/-- The multiplicative kernel of a `MonoidHom` is the `Submonoid` of elements `x : G` such that
`f x = 1`. -/
@[to_additive
  /-- The additive kernel of an `AddMonoidHom` is the `AddSubmonoid` of elements such that
  `f x = 0`. -/]
/--
Definition of `mker` / `mker` 的定义

English:
definition mker
  signature: (f : F)
  body: (⊥ : Submonoid N).comap f

@[to_additive (attr := simp)]

中文:
定义 mker
  签名: (f : F)
  定义体: (⊥ : Submonoid N).comap f

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid
-/
def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f

@[to_additive (attr := simp)]
/--
theorem `mem_mker` / 定理 `mem_mker`

English:
theorem mem_mker
  given: {f : F} {x : M}
  statement: x in mker f ↔ f x = 1
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_mker
  条件: {f : F} {x : M}
  结论: x in mker f ↔ f x = 1
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mker {f : F} {x : M} : x in mker f ↔ f x = 1 :=
  Iff.rfl

@[to_additive]
/--
theorem `coe_mker` / 定理 `coe_mker`

English:
theorem coe_mker
  given: (f : F)
  statement: (mker f : Set M) = (f : M -> N) ⁻¹' {1}
  proof: rfl

@[to_additive]

中文:
定理 coe_mker
  条件: (f : F)
  结论: (mker f : 集合 M) = (f : M -> N) ⁻¹' {1}
  证明: rfl

@[to_additive]
-/
theorem coe_mker (f : F) : (mker f : Set M) = (f : M -> N) ⁻¹' {1} :=
  rfl

@[to_additive]
/--
Instance `decidableMemMker` / 实例 `decidableMemMker`

English:
instance decidableMemMker
  signature: [DecidableEq N] (f : F)
  body: fun x =>
  decidable_of_iff (f x = 1) mem_mker

@[to_additive]

中文:
实例 decidableMemMker
  签名: [DecidableEq N] (f : F)
  定义体: fun x =>
  decidable_of_iff (f x = 1) mem_mker

@[to_additive]
-/
instance decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· in mker f) := fun x =>
  decidable_of_iff (f x = 1) mem_mker

@[to_additive]
/--
theorem `comap_mker` / 定理 `comap_mker`

English:
theorem comap_mker
  given: (g : N ->* P) (f : M ->* N)
  statement: (mker g).comap f = mker (comp g f)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_mker
  条件: (g : N ->* P) (f : M ->* N)
  结论: (mker g).comap f = mker (comp g f)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_mker (g : N ->* P) (f : M ->* N) : (mker g).comap f = mker (comp g f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_bot'` / 定理 `comap_bot'`

English:
theorem comap_bot'
  given: (f : F)
  statement: (⊥ : Submonoid N).comap f = mker f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_bot'
  条件: (f : F)
  结论: (⊥ : 子幺半群 N).comap f = mker f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `domRestrict_mker` / 定理 `domRestrict_mker`

English:
theorem domRestrict_mker
  given: (f : M ->* N)
  proof: rfl

@[deprecated (since := "2026-07-19")] alias restrict_mker := domRestrict_mker
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mker := _root_.AddMonoidHom.domRestrict_mker

中文:
定理 domRestrict_mker
  条件: (f : M ->* N)
  证明: rfl

@[deprecated (since := "2026-07-19")] alias restrict_mker := domRestrict_mker
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mker := _root_.AddMonoidHom.domRestrict_mker
-/
theorem domRestrict_mker (f : M ->* N) :
    mker (f.domRestrict S) = (MonoidHom.mker f).comap S.subtype :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict_mker := domRestrict_mker
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_mker := _root_.AddMonoidHom.domRestrict_mker

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `mrangeRestrict_mker` / 定理 `mrangeRestrict_mker`

English:
theorem mrangeRestrict_mker
  given: (f : M ->* N)
  statement: mker (mrangeRestrict f) = mker f
  proof: by
  ext x
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp

@[to_additive (attr := simp)]

中文:
定理 mrangeRestrict_mker
  条件: (f : M ->* N)
  结论: mker (mrangeRestrict f) = mker f
  证明: by
  ext x
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: mrange
-/
theorem mrangeRestrict_mker (f : M ->* N) : mker (mrangeRestrict f) = mker f := by
  ext x
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp

@[to_additive (attr := simp)]
/--
theorem `mker_one` / 定理 `mker_one`

English:
theorem mker_one
  statement: mker (1 : M ->* N) = ⊤
  proof: by
  ext
  simp [mem_mker]

@[to_additive prod_map_comap_prod']

中文:
定理 mker_one
  结论: mker (1 : M ->* N) = ⊤
  证明: by
  ext
  simp [mem_mker]

@[to_additive prod_map_comap_prod']

Depends on / 依赖: mem_mker
-/
theorem mker_one : mker (1 : M ->* N) = ⊤ := by
  ext
  simp [mem_mker]

@[to_additive prod_map_comap_prod']
/--
theorem `prod_map_comap_prod'` / 定理 `prod_map_comap_prod'`

English:
theorem prod_map_comap_prod'
  statement: {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N']
  proof: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

@[to_additive mker_prod_map]

中文:
定理 prod_map_comap_prod'
  结论: {M' : 类型} {N' : 类型} [MulOne类 M'] [MulOne类 N']
  证明: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

@[to_additive mker_prod_map]

Depends on / 依赖: Set.preimage_prod_map_prod, SetLike, SetLike.coe_injective, coe_injective, preimage_prod_map_prod
-/
theorem prod_map_comap_prod' {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N']
    (f : M ->* N) (g : M' ->* N') (S : Submonoid N) (S' : Submonoid N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

@[to_additive mker_prod_map]
/--
theorem `mker_prod_map` / 定理 `mker_prod_map`

English:
theorem mker_prod_map
  statement: {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M ->* N)
  proof: by
  rw [← comap_bot']; rw [← comap_bot']; rw [← comap_bot']; rw [← prod_map_comap_prod']; rw [bot_prod_bot]

@[to_additive (attr := simp)]

中文:
定理 mker_prod_map
  结论: {M' : 类型} {N' : 类型} [MulOne类 M'] [MulOne类 N'] (f : M ->* N)
  证明: by
  rw [← comap_bot']; rw [← comap_bot']; rw [← comap_bot']; rw [← prod_map_comap_prod']; rw [bot_prod_bot]

@[to_additive (attr := simp)]

Depends on / 依赖: bot_prod_bot, comap_bot, prod_map_comap_prod
-/
theorem mker_prod_map {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M ->* N)
    (g : M' ->* N') : mker (prodMap f g) = (mker f).prod (mker g) := by
  rw [← comap_bot']; rw [← comap_bot']; rw [← comap_bot']; rw [← prod_map_comap_prod']; rw [bot_prod_bot]

@[to_additive (attr := simp)]
/--
theorem `mker_inl` / 定理 `mker_inl`

English:
theorem mker_inl
  statement: mker (inl M N) = ⊥
  proof: by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]

中文:
定理 mker_inl
  结论: mker (inl M N) = ⊥
  证明: by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_mker
-/
theorem mker_inl : mker (inl M N) = ⊥ := by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]
/--
theorem `mker_inr` / 定理 `mker_inr`

English:
theorem mker_inr
  statement: mker (inr M N) = ⊥
  proof: by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]

中文:
定理 mker_inr
  结论: mker (inr M N) = ⊥
  证明: by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]

Depends on / 依赖: mem_mker
-/
theorem mker_inr : mker (inr M N) = ⊥ := by
  ext x
  simp [mem_mker]

@[to_additive (attr := simp)]
/--
lemma `mker_fst` / 引理 `mker_fst`

English:
lemma mker_fst
  statement: mker (fst M N) = .prod ⊥ ⊤
  proof: SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]

中文:
引理 mker_fst
  结论: mker (fst M N) = .乘积 ⊥ ⊤
  证明: SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, and_true, iff_of_eq
-/
lemma mker_fst : mker (fst M N) = .prod ⊥ ⊤ := SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]
/--
lemma `mker_snd` / 引理 `mker_snd`

English:
lemma mker_snd
  statement: mker (snd M N) = .prod ⊤ ⊥
  proof: SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

中文:
引理 mker_snd
  结论: mker (snd M N) = .乘积 ⊤ ⊥
  证明: SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

Depends on / 依赖: SetLike, SetLike.ext, iff_of_eq, true_and
-/
lemma mker_snd : mker (snd M N) = .prod ⊤ ⊥ := SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

/-- The `MonoidHom` from the preimage of a `Submonoid` to itself. -/
@[to_additive (attr := simps)
  /-- The `AddMonoidHom` from the preimage of an `AddSubmonoid` to itself. -/]
/--
Definition of `submonoidComap` / `submonoidComap` 的定义

English:
definition submonoidComap
  signature: (f : M ->* N) (N' : Submonoid N)
  body: ⟨f x, x.2⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive]

中文:
定义 submonoidComap
  签名: (f : M ->* N) (N' : 子幺半群 N)
  定义体: ⟨f x, x.2⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive]
-/
def submonoidComap (f : M ->* N) (N' : Submonoid N) :
    N'.comap f ->* N' where
  toFun x := ⟨f x, x.2⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[to_additive]
/--
lemma `submonoidComap_surjective_of_surjective` / 引理 `submonoidComap_surjective_of_surjective`

English:
lemma submonoidComap_surjective_of_surjective
  given: (f : M ->* N) (N' : Submonoid N) (hf : Surjective f)
  proof: fun y => by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

中文:
引理 submonoidComap_surjective_of_surjective
  条件: (f : M ->* N) (N' : 子幺半群 N) (hf : 满射 f)
  证明: fun y => by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

Depends on / 依赖: Subtype, Subtype.val_injective, mem_comap, mem_comap.mpr, val_injective
-/
lemma submonoidComap_surjective_of_surjective (f : M ->* N) (N' : Submonoid N) (hf : Surjective f) :
    Surjective (f.submonoidComap N') := fun y => by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

/-- The `MonoidHom` from a `Submonoid` to its image.
See `MulEquiv.SubmonoidMap` for a variant for `MulEquiv`s. -/
@[to_additive (attr := simps)
  /-- The `AddMonoidHom` from an `AddSubmonoid` to its image.
  See `AddEquiv.AddSubmonoidMap` for a variant for `AddEquiv`s. -/]
/--
Definition of `submonoidMap` / `submonoidMap` 的定义

English:
definition submonoidMap
  signature: (f : M ->* N) (M' : Submonoid M)
  body: ⟨f x, ⟨x, x.2, rfl⟩⟩
map_one' := Subtype.ext f.map_one
map_mul' x y := Subtype.ext f.map_mul x y

@[to_additive]

中文:
定义 submonoidMap
  签名: (f : M ->* N) (M' : 子幺半群 M)
  定义体: ⟨f x, ⟨x, x.2, rfl⟩⟩
map_one' := Subtype.ext f.map_one
map_mul' x y := Subtype.ext f.map_mul x y

@[to_additive]
-/
def submonoidMap (f : M ->* N) (M' : Submonoid M) : M' ->* M'.map f where
  toFun x := ⟨f x, ⟨x, x.2, rfl⟩⟩
map_one' := Subtype.ext f.map_one
map_mul' x y := Subtype.ext f.map_mul x y

@[to_additive]
/--
theorem `submonoidMap_surjective` / 定理 `submonoidMap_surjective`

English:
theorem submonoidMap_surjective
  given: (f : M ->* N) (M' : Submonoid M)
  proof: by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[to_additive (attr := grind inj)]

中文:
定理 submonoidMap_surjective
  条件: (f : M ->* N) (M' : 子幺半群 M)
  证明: by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[to_additive (attr := grind inj)]
-/
theorem submonoidMap_surjective (f : M ->* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[to_additive (attr := grind inj)]
/--
theorem `submonoidMap_injective` / 定理 `submonoidMap_injective`

English:
theorem submonoidMap_injective
  given: {f : M ->* N} (hf : Injective f) (M' : Submonoid M)
  proof: by
  grind [Injective, submonoidMap_apply_coe]

中文:
定理 submonoidMap_injective
  条件: {f : M ->* N} (hf : 单射 f) (M' : 子幺半群 M)
  证明: by
  grind [Injective, submonoidMap_apply_coe]

Depends on / 依赖: Injective, submonoidMap_apply_coe
-/
theorem submonoidMap_injective {f : M ->* N} (hf : Injective f) (M' : Submonoid M) :
    Injective (f.submonoidMap M') := by
  grind [Injective, submonoidMap_apply_coe]

end MonoidHom

namespace Submonoid

@[to_additive]
/--
lemma `surjOn_iff_le_map` / 引理 `surjOn_iff_le_map`

English:
lemma surjOn_iff_le_map
  given: {f : M ->* N} {H : Submonoid M} {K : Submonoid N}
  proof: Iff.rfl

中文:
引理 surjOn_iff_le_map
  条件: {f : M ->* N} {H : 子幺半群 M} {K : 子幺半群 N}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma surjOn_iff_le_map {f : M ->* N} {H : Submonoid M} {K : Submonoid N} :
    Set.SurjOn f H K ↔ K <= H.map f :=
  Iff.rfl

open MonoidHom

@[to_additive]
/--
theorem `mrange_inl` / 定理 `mrange_inl`

English:
theorem mrange_inl
  statement: mrange (inl M N) = prod ⊤ ⊥
  proof: by simpa only [mrange_eq_map] using map_inl ⊤

@[to_additive]

中文:
定理 mrange_inl
  结论: mrange (inl M N) = 乘积 ⊤ ⊥
  证明: by simpa only [mrange_eq_map] using map_inl ⊤

@[to_additive]

Depends on / 依赖: map_inl, mrange_eq_map
-/
theorem mrange_inl : mrange (inl M N) = prod ⊤ ⊥ := by simpa only [mrange_eq_map] using map_inl ⊤

@[to_additive]
/--
theorem `mrange_inr` / 定理 `mrange_inr`

English:
theorem mrange_inr
  statement: mrange (inr M N) = prod ⊥ ⊤
  proof: by simpa only [mrange_eq_map] using map_inr ⊤

@[to_additive]

中文:
定理 mrange_inr
  结论: mrange (inr M N) = 乘积 ⊥ ⊤
  证明: by simpa only [mrange_eq_map] using map_inr ⊤

@[to_additive]

Depends on / 依赖: map_inr, mrange_eq_map
-/
theorem mrange_inr : mrange (inr M N) = prod ⊥ ⊤ := by simpa only [mrange_eq_map] using map_inr ⊤

@[to_additive]
/--
theorem `mrange_inl'` / 定理 `mrange_inl'`

English:
theorem mrange_inl'
  statement: mrange (inl M N) = comap (snd M N) ⊥
  proof: mrange_inl.trans (top_prod _)

@[to_additive]

中文:
定理 mrange_inl'
  结论: mrange (inl M N) = comap (snd M N) ⊥
  证明: mrange_inl.trans (top_prod _)

@[to_additive]

Depends on / 依赖: mrange_inl, mrange_inl.trans, top_prod
-/
theorem mrange_inl' : mrange (inl M N) = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)

@[to_additive]
/--
theorem `mrange_inr'` / 定理 `mrange_inr'`

English:
theorem mrange_inr'
  statement: mrange (inr M N) = comap (fst M N) ⊥
  proof: mrange_inr.trans (prod_top _)

@[to_additive (attr := simp)]

中文:
定理 mrange_inr'
  结论: mrange (inr M N) = comap (fst M N) ⊥
  证明: mrange_inr.trans (prod_top _)

@[to_additive (attr := simp)]

Depends on / 依赖: mrange_inr, mrange_inr.trans, prod_top
-/
theorem mrange_inr' : mrange (inr M N) = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)

@[to_additive (attr := simp)]
/--
theorem `mrange_fst` / 定理 `mrange_fst`

English:
theorem mrange_fst
  statement: mrange (fst M N) = ⊤
  proof: mrange_eq_top_of_surjective (fst M N) @Prod.fst_surjective _ _ ⟨1⟩

@[to_additive (attr := simp)]

中文:
定理 mrange_fst
  结论: mrange (fst M N) = ⊤
  证明: mrange_eq_top_of_surjective (fst M N) @Prod.fst_surjective _ _ ⟨1⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Prod.fst_surjective, fst_surjective, mrange_eq_top_of_surjective
-/
theorem mrange_fst : mrange (fst M N) = ⊤ :=
mrange_eq_top_of_surjective (fst M N) @Prod.fst_surjective _ _ ⟨1⟩

@[to_additive (attr := simp)]
/--
theorem `mrange_snd` / 定理 `mrange_snd`

English:
theorem mrange_snd
  statement: mrange (snd M N) = ⊤
  proof: mrange_eq_top_of_surjective (snd M N) @Prod.snd_surjective _ _ ⟨1⟩

@[to_additive prod_eq_bot_iff]

中文:
定理 mrange_snd
  结论: mrange (snd M N) = ⊤
  证明: mrange_eq_top_of_surjective (snd M N) @Prod.snd_surjective _ _ ⟨1⟩

@[to_additive prod_eq_bot_iff]

Depends on / 依赖: Prod.snd_surjective, mrange_eq_top_of_surjective, snd_surjective
-/
theorem mrange_snd : mrange (snd M N) = ⊤ :=
mrange_eq_top_of_surjective (snd M N) @Prod.snd_surjective _ _ ⟨1⟩

@[to_additive prod_eq_bot_iff]
/--
theorem `prod_eq_bot_iff` / 定理 `prod_eq_bot_iff`

English:
theorem prod_eq_bot_iff
  given: {s : Submonoid M} {t : Submonoid N}
  statement: s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥
  proof: by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]

@[to_additive prod_eq_top_iff]

中文:
定理 prod_eq_bot_iff
  条件: {s : 子幺半群 M} {t : 子幺半群 N}
  结论: s.乘积 t = ⊥ ↔ s = ⊥ ∧ t = ⊥
  证明: by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]

@[to_additive prod_eq_top_iff]

Depends on / 依赖: comap_bot, eq_bot_iff, gc_map_comap, le_iff_le, mker_inl, mker_inr, prod_le_iff
-/
theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]

@[to_additive prod_eq_top_iff]
/--
theorem `prod_eq_top_iff` / 定理 `prod_eq_top_iff`

English:
theorem prod_eq_top_iff
  given: {s : Submonoid M} {t : Submonoid N}
  statement: s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤
  proof: by
  simp only [eq_top_iff, le_prod_iff, ← mrange_eq_map, mrange_fst, mrange_snd]

@[to_additive (attr := simp)]

中文:
定理 prod_eq_top_iff
  条件: {s : 子幺半群 M} {t : 子幺半群 N}
  结论: s.乘积 t = ⊤ ↔ s = ⊤ ∧ t = ⊤
  证明: by
  simp only [eq_top_iff, le_prod_iff, ← mrange_eq_map, mrange_fst, mrange_snd]

@[to_additive (attr := simp)]

Depends on / 依赖: eq_top_iff, le_prod_iff, mrange_eq_map, mrange_fst, mrange_snd
-/
theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← mrange_eq_map, mrange_fst, mrange_snd]

@[to_additive (attr := simp)]
/--
theorem `mrange_inl_sup_mrange_inr` / 定理 `mrange_inl_sup_mrange_inr`

English:
theorem mrange_inl_sup_mrange_inr
  statement: mrange (inl M N) ⊔ mrange (inr M N) = ⊤
  proof: by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]

中文:
定理 mrange_inl_sup_mrange_inr
  结论: mrange (inl M N) ⊔ mrange (inr M N) = ⊤
  证明: by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]

Depends on / 依赖: mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top
-/
theorem mrange_inl_sup_mrange_inr : mrange (inl M N) ⊔ mrange (inr M N) = ⊤ := by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]

/-- The `MonoidHom` associated to an inclusion of `Submonoid`s. -/
@[to_additive /-- The `AddMonoidHom` associated to an inclusion of `AddSubmonoid`s. -/]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Submonoid M} (h : S <= T)
  body: S.subtype.codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]

中文:
定义 inclusion
  签名: {S T : 子幺半群 M} (h : S <= T)
  定义体: S.subtype.codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]

Depends on / 依赖: S.subtype.codRestrict, codRestrict, subtype
-/
def inclusion {S T : Submonoid M} (h : S <= T) : S ->* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {S T : Submonoid M} (h : S <= T) (a : S)
  statement: (inclusion h a : M) = a
  proof: Set.coe_inclusion h a

@[to_additive]

中文:
定理 coe_inclusion
  条件: {S T : 子幺半群 M} (h : S <= T) (a : S)
  结论: (inclusion h a : M) = a
  证明: Set.coe_inclusion h a

@[to_additive]

Depends on / 依赖: Set.coe_inclusion, coe_inclusion
-/
theorem coe_inclusion {S T : Submonoid M} (h : S <= T) (a : S) : (inclusion h a : M) = a :=
  Set.coe_inclusion h a

@[to_additive]
/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  given: {S T : Submonoid M} (h : S <= T)
  statement: Function.Injective inclusion h
  proof: Set.inclusion_injective h

@[to_additive (attr := simp)]

中文:
定理 inclusion_injective
  条件: {S T : 子幺半群 M} (h : S <= T)
  结论: 函数.单射 inclusion h
  证明: Set.inclusion_injective h

@[to_additive (attr := simp)]

Depends on / 依赖: Set.inclusion_injective, inclusion_injective
-/
theorem inclusion_injective {S T : Submonoid M} (h : S <= T) : Function.Injective inclusion h :=
  Set.inclusion_injective h

@[to_additive (attr := simp)]
/--
lemma `inclusion_inj` / 引理 `inclusion_inj`

English:
lemma inclusion_inj
  given: {S T : Submonoid M} (h : S <= T) {x y : S}
  proof: (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]

中文:
引理 inclusion_inj
  条件: {S T : 子幺半群 M} (h : S <= T) {x y : S}
  证明: (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, inclusion_injective
-/
lemma inclusion_inj {S T : Submonoid M} (h : S <= T) {x y : S} :
    inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

@[to_additive (attr := simp)]
/--
theorem `subtype_comp_inclusion` / 定理 `subtype_comp_inclusion`

English:
theorem subtype_comp_inclusion
  given: {S T : Submonoid M} (h : S <= T)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 subtype_comp_inclusion
  条件: {S T : 子幺半群 M} (h : S <= T)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem subtype_comp_inclusion {S T : Submonoid M} (h : S <= T) :
    T.subtype.comp (inclusion h) = S.subtype :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mrange_subtype` / 定理 `mrange_subtype`

English:
theorem mrange_subtype
  given: (s : Submonoid M)
  statement: mrange s.subtype = s
  proof: SetLike.coe_injective (coe_mrange _).trans Subtype.range_coe

@[to_additive]

中文:
定理 mrange_subtype
  条件: (s : 子幺半群 M)
  结论: mrange s.subtype = s
  证明: SetLike.coe_injective (coe_mrange _).trans Subtype.range_coe

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_mrange, range_coe
-/
theorem mrange_subtype (s : Submonoid M) : mrange s.subtype = s :=
SetLike.coe_injective (coe_mrange _).trans Subtype.range_coe

@[to_additive]
/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  statement: S = ⊤ ↔ forall x : M, x in S
  proof: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

@[to_additive]

中文:
定理 eq_top_iff'
  结论: S = ⊤ ↔ 对任意 x : M, x in S
  证明: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

@[to_additive]

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, mem_top
-/
theorem eq_top_iff' : S = ⊤ ↔ forall x : M, x in S :=
eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

@[to_additive]
/--
theorem `eq_bot_iff_forall` / 定理 `eq_bot_iff_forall`

English:
theorem eq_bot_iff_forall
  statement: S = ⊥ ↔ forall x in S, x = (1 : M)
  proof: SetLike.ext_iff.trans by simp +contextual [iff_def, S.one_mem]

@[to_additive]

中文:
定理 eq_bot_iff_对任意
  结论: S = ⊥ ↔ 对任意 x in S, x = (1 : M)
  证明: SetLike.ext_iff.trans by simp +contextual [iff_def, S.one_mem]

@[to_additive]

Depends on / 依赖: S.one_mem, SetLike, SetLike.ext_iff.trans, contextual, ext_iff, iff_def, one_mem
-/
theorem eq_bot_iff_forall : S = ⊥ ↔ forall x in S, x = (1 : M) :=
SetLike.ext_iff.trans by simp +contextual [iff_def, S.one_mem]

@[to_additive]
/--
theorem `eq_bot_of_subsingleton` / 定理 `eq_bot_of_subsingleton`

English:
theorem eq_bot_of_subsingleton
  given: [Subsingleton S]
  statement: S = ⊥
  proof: by
  rw [eq_bot_iff_forall]
  intro y hy
simpa using congr_arg ((↑) : S -> M) Subsingleton.elim (⟨y, hy⟩ : S) 1

@[to_additive]

中文:
定理 eq_bot_of_subsingleton
  条件: [子单例 S]
  结论: S = ⊥
  证明: by
  rw [eq_bot_iff_forall]
  intro y hy
simpa using congr_arg ((↑) : S -> M) Subsingleton.elim (⟨y, hy⟩ : S) 1

@[to_additive]

Depends on / 依赖: Subsingleton, Subsingleton.elim, congr_arg, eq_bot_iff_forall
-/
theorem eq_bot_of_subsingleton [Subsingleton S] : S = ⊥ := by
  rw [eq_bot_iff_forall]
  intro y hy
simpa using congr_arg ((↑) : S -> M) Subsingleton.elim (⟨y, hy⟩ : S) 1

@[to_additive]
/--
theorem `nontrivial_iff_exists_ne_one` / 定理 `nontrivial_iff_exists_ne_one`

English:
theorem nontrivial_iff_exists_ne_one
  given: (S : Submonoid M)
  statement: Nontrivial S ↔ exists x in S, x != (1 : M)
  proof: calc
    Nontrivial S ↔ exists x : S, x != 1 := nontrivial_iff_exists_ne 1
    _ ↔ exists (x : _) (hx : x in S), (⟨x, hx⟩ : S) != ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ exists x in S, x != (1 : M) := by simp [Ne]

中文:
定理 nontrivial_iff_存在_ne_one
  条件: (S : 子幺半群 M)
  结论: 非平凡 S ↔ 存在 x in S, x != (1 : M)
  证明: calc
    Nontrivial S ↔ exists x : S, x != 1 := nontrivial_iff_exists_ne 1
    _ ↔ exists (x : _) (hx : x in S), (⟨x, hx⟩ : S) != ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ exists x in S, x != (1 : M) := by simp [Ne]

Depends on / 依赖: Nontrivial, S.one_mem, Subtype, Subtype.exists, nontrivial_iff_exists_ne, one_mem
-/
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ exists x in S, x != (1 : M) :=
  calc
    Nontrivial S ↔ exists x : S, x != 1 := nontrivial_iff_exists_ne 1
    _ ↔ exists (x : _) (hx : x in S), (⟨x, hx⟩ : S) != ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ exists x in S, x != (1 : M) := by simp [Ne]

/-- A `Submonoid` is either the trivial `Submonoid` or nontrivial. -/
@[to_additive /-- An `AddSubmonoid` is either the trivial `AddSubmonoid` or nontrivial. -/]
/--
theorem `bot_or_nontrivial` / 定理 `bot_or_nontrivial`

English:
theorem bot_or_nontrivial
  given: (S : Submonoid M)
  statement: S = ⊥ ∨ Nontrivial S
  proof: by
  simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]

中文:
定理 bot_or_nontrivial
  条件: (S : 子幺半群 M)
  结论: S = ⊥ ∨ 非平凡 S
  证明: by
  simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]

Depends on / 依赖: Classical, Classical.em, Classical.not_imp, eq_bot_iff_forall, nontrivial_iff_exists_ne_one, not_forall, not_imp
-/
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]

/-- A `Submonoid` is either the trivial `Submonoid` or contains a nonzero element. -/
@[to_additive
  /-- An `AddSubmonoid` is either the trivial `AddSubmonoid` or contains a nonzero element. -/]
/--
theorem `bot_or_exists_ne_one` / 定理 `bot_or_exists_ne_one`

English:
theorem bot_or_exists_ne_one
  given: (S : Submonoid M)
  statement: S = ⊥ ∨ exists x in S, x != (1 : M)
  proof: S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

@[to_additive]

中文:
定理 bot_or_存在_ne_one
  条件: (S : 子幺半群 M)
  结论: S = ⊥ ∨ 存在 x in S, x != (1 : M)
  证明: S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

@[to_additive]

Depends on / 依赖: S.bot_or_nontrivial.imp_right, S.nontrivial_iff_exists_ne_one.mp, bot_or_nontrivial, imp_right, nontrivial_iff_exists_ne_one
-/
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ exists x in S, x != (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

@[to_additive]
/--
lemma `codisjoint_map` / 引理 `codisjoint_map`

English:
lemma codisjoint_map
  statement: {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F}
  proof: by
  rw [codisjoint_iff]; rw [← map_sup]; rw [codisjoint_iff.mp h]; rw [← MonoidHom.mrange_eq_map]; rw [mrange_eq_top_of_surjective _ hf]

中文:
引理 codisjoint_map
  结论: {F : 类型} [函数状 F M N] [幺半群态射类 F M N] {f : F}
  证明: by
  rw [codisjoint_iff]; rw [← map_sup]; rw [codisjoint_iff.mp h]; rw [← MonoidHom.mrange_eq_map]; rw [mrange_eq_top_of_surjective _ hf]

Depends on / 依赖: MonoidHom, MonoidHom.mrange_eq_map, codisjoint_iff, codisjoint_iff.mp, map_sup, mrange_eq_map, mrange_eq_top_of_surjective
-/
lemma codisjoint_map {F : Type*} [FunLike F M N] [MonoidHomClass F M N] {f : F}
    (hf : Function.Surjective f) {H K : Submonoid M} (h : Codisjoint H K) :
    Codisjoint (H.map f) (K.map f) := by
  rw [codisjoint_iff]; rw [← map_sup]; rw [codisjoint_iff.mp h]; rw [← MonoidHom.mrange_eq_map]; rw [mrange_eq_top_of_surjective _ hf]

section Pi

variable {ι : Type*} {M : ι -> Type*} [forall i, MulOneClass (M i)]

/-- A version of `Set.pi` for `Submonoid`s. Given an index set `I` and a family of `Submonoid`s
`s : Π i, Submonoid f i`, `pi I s` is the `Submonoid` of dependent functions `f : Π i, f i` such
that `f i` belongs to `Pi I s` whenever `i ∈ I`. -/
@[to_additive /-- A version of `Set.pi` for `AddSubmonoid`s. Given an index set `I` and a family
  of `AddSubmonoid`s `s : Π i, AddSubmonoid f i`, `pi I s` is the `AddSubmonoid` of dependent
  functions `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (I : Set ι) (S : forall i, Submonoid (M i))
  body: I.pi fun i => (S i).carrier
  one_mem' i _ := (S i).one_mem
  mul_mem' hp hq i hI := (S i).mul_mem (hp i hI) (hq i hI)

@[to_additive]

中文:
定义 pi
  签名: (I : 集合 ι) (S : 对任意 i, 子幺半群 (M i))
  定义体: I.pi fun i => (S i).carrier
  one_mem' i _ := (S i).one_mem
  mul_mem' hp hq i hI := (S i).mul_mem (hp i hI) (hq i hI)

@[to_additive]

Depends on / 依赖: I.pi, carrier
-/
def pi (I : Set ι) (S : forall i, Submonoid (M i)) : Submonoid (forall i, M i) where
  carrier := I.pi fun i => (S i).carrier
  one_mem' i _ := (S i).one_mem
  mul_mem' hp hq i hI := (S i).mul_mem (hp i hI) (hq i hI)

@[to_additive]
/--
theorem `coe_pi` / 定理 `coe_pi`

English:
theorem coe_pi
  given: (I : Set ι) (S : forall i, Submonoid (M i))
  proof: rfl

@[to_additive]

中文:
定理 coe_pi
  条件: (I : 集合 ι) (S : 对任意 i, 子幺半群 (M i))
  证明: rfl

@[to_additive]
-/
theorem coe_pi (I : Set ι) (S : forall i, Submonoid (M i)) :
    (pi I S : Set (forall i, M i)) = Set.pi I fun i => (S i : Set (M i)) :=
  rfl

@[to_additive]
/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: (I : Set ι) {S : forall i, Submonoid (M i)} {p : forall i, M i}
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_pi
  条件: (I : 集合 ι) {S : 对任意 i, 子幺半群 (M i)} {p : 对任意 i, M i}
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_pi (I : Set ι) {S : forall i, Submonoid (M i)} {p : forall i, M i} :
    p in Submonoid.pi I S ↔ forall i, i in I -> p i in S i :=
  Iff.rfl

@[to_additive]
/--
theorem `pi_top` / 定理 `pi_top`

English:
theorem pi_top
  given: (I : Set ι)
  statement: (pi I fun i => (⊤ : Submonoid (M i))) = ⊤
  proof: ext fun x => by simp [mem_pi]

@[to_additive]

中文:
定理 pi_top
  条件: (I : 集合 ι)
  结论: (pi I fun i => (⊤ : 子幺半群 (M i))) = ⊤
  证明: ext fun x => by simp [mem_pi]

@[to_additive]

Depends on / 依赖: mem_pi
-/
theorem pi_top (I : Set ι) : (pi I fun i => (⊤ : Submonoid (M i))) = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/--
theorem `pi_empty` / 定理 `pi_empty`

English:
theorem pi_empty
  given: (H : forall i, Submonoid (M i))
  statement: pi ∅ H = ⊤
  proof: ext fun x => by simp [mem_pi]

@[to_additive]

中文:
定理 pi_empty
  条件: (H : 对任意 i, 子幺半群 (M i))
  结论: pi ∅ H = ⊤
  证明: ext fun x => by simp [mem_pi]

@[to_additive]

Depends on / 依赖: mem_pi
-/
theorem pi_empty (H : forall i, Submonoid (M i)) : pi ∅ H = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/--
theorem `pi_bot` / 定理 `pi_bot`

English:
theorem pi_bot
  statement: (pi Set.univ fun i => (⊥ : Submonoid (M i))) = ⊥
  proof: ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]

中文:
定理 pi_bot
  结论: (pi 集合.univ fun i => (⊥ : 子幺半群 (M i))) = ⊥
  证明: ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]

Depends on / 依赖: funext_iff, mem_pi
-/
theorem pi_bot : (pi Set.univ fun i => (⊥ : Submonoid (M i))) = ⊥ :=
  ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]
/--
theorem `le_pi_iff` / 定理 `le_pi_iff`

English:
theorem le_pi_iff
  given: {I : Set ι} {S : forall i, Submonoid (M i)} {J : Submonoid (forall i, M i)}
  proof: Set.subset_pi_iff

@[to_additive (attr := simp)]

中文:
定理 le_pi_iff
  条件: {I : 集合 ι} {S : 对任意 i, 子幺半群 (M i)} {J : 子幺半群 (对任意 i, M i)}
  证明: Set.subset_pi_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Set.subset_pi_iff, subset_pi_iff
-/
theorem le_pi_iff {I : Set ι} {S : forall i, Submonoid (M i)} {J : Submonoid (forall i, M i)} :
    J <= pi I S ↔ forall i in I, J <= comap (Pi.evalMonoidHom M i) (S i) :=
  Set.subset_pi_iff

@[to_additive (attr := simp)]
/--
theorem `mulSingle_mem_pi` / 定理 `mulSingle_mem_pi`

English:
theorem mulSingle_mem_pi
  given: [DecidableEq ι] {I : Set ι} {S : forall i, Submonoid (M i)} (i : ι) (x : M i)
  proof: Set.update_mem_pi_iff_of_mem (one_mem (pi I _))

@[to_additive]

中文:
定理 mulSingle_mem_pi
  条件: [DecidableEq ι] {I : 集合 ι} {S : 对任意 i, 子幺半群 (M i)} (i : ι) (x : M i)
  证明: Set.update_mem_pi_iff_of_mem (one_mem (pi I _))

@[to_additive]

Depends on / 依赖: Set.update_mem_pi_iff_of_mem, one_mem, update_mem_pi_iff_of_mem
-/
theorem mulSingle_mem_pi [DecidableEq ι] {I : Set ι} {S : forall i, Submonoid (M i)} (i : ι) (x : M i) :
    Pi.mulSingle i x in pi I S ↔ i in I -> x in S i :=
  Set.update_mem_pi_iff_of_mem (one_mem (pi I _))

@[to_additive]
/--
theorem `pi_eq_bot_iff` / 定理 `pi_eq_bot_iff`

English:
theorem pi_eq_bot_iff
  given: (S : forall i, Submonoid (M i))
  statement: pi Set.univ S = ⊥ ↔ forall i, S i = ⊥
  proof: by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

@[to_additive]

中文:
定理 pi_eq_bot_iff
  条件: (S : 对任意 i, 子幺半群 (M i))
  结论: pi 集合.univ S = ⊥ ↔ 对任意 i, S i = ⊥
  证明: by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

@[to_additive]

Depends on / 依赖: Set.univ_pi_eq_singleton_iff, SetLike, SetLike.ext, _iff, simp_rw, univ_pi_eq_singleton_iff
-/
theorem pi_eq_bot_iff (S : forall i, Submonoid (M i)) : pi Set.univ S = ⊥ ↔ forall i, S i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

@[to_additive]
/--
theorem `le_comap_mulSingle_pi` / 定理 `le_comap_mulSingle_pi`

English:
theorem le_comap_mulSingle_pi
  given: [DecidableEq ι] (S : forall i, Submonoid (M i)) {I i}
  proof: fun x hx => by simp [hx]

@[to_additive]

中文:
定理 le_comap_mulSingle_pi
  条件: [DecidableEq ι] (S : 对任意 i, 子幺半群 (M i)) {I i}
  证明: fun x hx => by simp [hx]

@[to_additive]
-/
theorem le_comap_mulSingle_pi [DecidableEq ι] (S : forall i, Submonoid (M i)) {I i} :
    S i <= comap (MonoidHom.mulSingle M i) (pi I S) :=
  fun x hx => by simp [hx]

@[to_additive]
/--
theorem `iSup_map_mulSingle_le` / 定理 `iSup_map_mulSingle_le`

English:
theorem iSup_map_mulSingle_le
  given: [DecidableEq ι] {I : Set ι} {S : forall i, Submonoid (M i)}
  proof: iSup_le fun _ => map_le_iff_le_comap.mpr (le_comap_mulSingle_pi _)

中文:
定理 iSup_map_mulSingle_le
  条件: [DecidableEq ι] {I : 集合 ι} {S : 对任意 i, 子幺半群 (M i)}
  证明: iSup_le fun _ => map_le_iff_le_comap.mpr (le_comap_mulSingle_pi _)

Depends on / 依赖: iSup_le, le_comap_mulSingle_pi, map_le_iff_le_comap, map_le_iff_le_comap.mpr
-/
theorem iSup_map_mulSingle_le [DecidableEq ι] {I : Set ι} {S : forall i, Submonoid (M i)} :
    ⨆ i, map (MonoidHom.mulSingle M i) (S i) <= pi I S :=
  iSup_le fun _ => map_le_iff_le_comap.mpr (le_comap_mulSingle_pi _)

end Pi

end Submonoid

/-- Restrict the domain and codomain of a `MonoidHom`. -/
@[to_additive /-- Restrict the domain and codomain of an `AddMonoidHom`. -/]
/--
Definition of `MonoidHom.restrict` / `MonoidHom.restrict` 的定义

English:
definition MonoidHom.restrict
  signature: {M' : Submonoid M} {N' : Submonoid N} {f : M ->* N}
  body: (f.domRestrict M').codRestrict N' SetLike.forall.mpr h

中文:
定义 幺半群态射.restrict
  签名: {M' : 子幺半群 M} {N' : 子幺半群 N} {f : M ->* N}
  定义体: (f.domRestrict M').codRestrict N' SetLike.forall.mpr h

Depends on / 依赖: SetLike, SetLike.forall.mpr, codRestrict, domRestrict, f.domRestrict
-/
def MonoidHom.restrict {M' : Submonoid M} {N' : Submonoid N} {f : M ->* N}
(h : Set.MapsTo f M' N') : M' ->* N' := (f.domRestrict M').codRestrict N' SetLike.forall.mpr h

/--
lemma `MonoidHom.restrict_injective` / 引理 `MonoidHom.restrict_injective`

English:
lemma MonoidHom.restrict_injective
  statement: {M' : Submonoid M} {N' : Submonoid N} {f : M ->* N}
  proof: fun _ _ h => Subtype.ext hf' Subtype.ext_iff.mp h

中文:
引理 幺半群态射.restrict_injective
  结论: {M' : 子幺半群 M} {N' : 子幺半群 N} {f : M ->* N}
  证明: fun _ _ h => Subtype.ext hf' Subtype.ext_iff.mp h
-/
@[to_additive] lemma MonoidHom.restrict_injective {M' : Submonoid M} {N' : Submonoid N} {f : M ->* N}
(h : Set.MapsTo f M' N') (hf' : Function.Injective f) : Function.Injective f.restrict h :=
fun _ _ h => Subtype.ext hf' Subtype.ext_iff.mp h

namespace MulEquiv

variable {S} {T : Submonoid M}

/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
monoid are equal. -/
@[to_additive
  /-- Makes the identity additive isomorphism from a proof two submonoids of an additive monoid are
  equal. -/]
/--
Definition of `submonoidCongr` / `submonoidCongr` 的定义

English:
definition submonoidCongr
  signature: (h : S = T)
  body: { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

中文:
定义 submonoidCongr
  签名: (h : S = T)
  定义体: { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, congr_arg, map_mul, setCongr
-/
def submonoidCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.
This is a bidirectional version of `MonoidHom.mrangeRestrict`. -/
@[to_additive (attr := simps +simpRhs)
  /-- An additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an
  additive equivalence between `M` and `f.mrange`. This is a bidirectional version of
  `AddMonoidHom.mrangeRestrict`. -/]
/--
Definition of `ofLeftInverse'` / `ofLeftInverse'` 的定义

English:
definition ofLeftInverse'
  signature: (f : M ->* N) {g : N -> M} (h : Function.LeftInverse g f)
  body: { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ (MonoidHom.mrange f).subtype
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }

中文:
定义 ofLeftInverse'
  签名: (f : M ->* N) {g : N -> M} (h : 函数.左逆 g f)
  定义体: { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ (MonoidHom.mrange f).subtype
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }

Depends on / 依赖: MonoidHom, MonoidHom.mem_mrange.mp, MonoidHom.mrange, Subtype, Subtype.ext, f.mrangeRestrict, invFun, left_inv, mem_mrange, mrange, mrangeRestrict, right_inv, subtype
-/
def ofLeftInverse' (f : M ->* N) {g : N -> M} (h : Function.LeftInverse g f) :
    M ≃* MonoidHom.mrange f :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ (MonoidHom.mrange f).subtype
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.2
        show f (g x) = x by rw [← hx', h x'] }

/-- A `MulEquiv` `φ` between two monoids `M` and `N` induces a `MulEquiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`.
See `MonoidHom.submonoidMap` for a variant for `MonoidHom`s. -/
@[to_additive
  /-- An `AddEquiv` `φ` between two additive monoids `M` and `N` induces an `AddEquiv`
  between a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. See
  `AddMonoidHom.addSubmonoidMap` for a variant for `AddMonoidHom`s. -/]
/--
Definition of `submonoidMap` / `submonoidMap` 的定义

English:
definition submonoidMap
  signature: (e : M ≃* N) (S : Submonoid M)
  body: { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }

@[to_additive (attr := simp)]

中文:
定义 submonoidMap
  签名: (e : M ≃* N) (S : 子幺半群 M)
  定义体: { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }

@[to_additive (attr := simp)]

Depends on / 依赖: Subtype, Subtype.ext, map_mul
-/
def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e :=
  { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }

@[to_additive (attr := simp)]
/--
theorem `coe_submonoidMap_apply` / 定理 `coe_submonoidMap_apply`

English:
theorem coe_submonoidMap_apply
  given: (e : M ≃* N) (S : Submonoid M) (g : S)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_submonoidMap_apply
  条件: (e : M ≃* N) (S : 子幺半群 M) (g : S)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_submonoidMap_apply (e : M ≃* N) (S : Submonoid M) (g : S) :
    ((submonoidMap e S g : S.map (e : M ->* N)) : N) = e g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `submonoidMap_symm_apply` / 定理 `submonoidMap_symm_apply`

English:
theorem submonoidMap_symm_apply
  given: (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M ->* N))
  proof: rfl

中文:
定理 submonoidMap_symm_apply
  条件: (e : M ≃* N) (S : 子幺半群 M) (g : S.map (e : M ->* N))
  证明: rfl
-/
theorem submonoidMap_symm_apply (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M ->* N)) :
(e.submonoidMap S).symm g = ⟨e.symm g, SetLike.mem_coe.1 Set.mem_image_equiv.1 g.2⟩ :=
  rfl

end MulEquiv

@[to_additive (attr := simp)]
/--
theorem `Submonoid.equivMapOfInjective_coe_mulEquiv` / 定理 `Submonoid.equivMapOfInjective_coe_mulEquiv`

English:
theorem Submonoid.equivMapOfInjective_coe_mulEquiv
  given: (e : M ≃* N)
  proof: by
  ext
  rfl

@[to_additive]

中文:
定理 子幺半群.equivMapOfInjective_coe_mulEquiv
  条件: (e : M ≃* N)
  证明: by
  ext
  rfl

@[to_additive]
-/
theorem Submonoid.equivMapOfInjective_coe_mulEquiv (e : M ≃* N) :
    S.equivMapOfInjective (e : M ->* N) (EquivLike.injective e) = e.submonoidMap S := by
  ext
  rfl

@[to_additive]
/--
Instance `Submonoid.faithfulSMul` / 实例 `Submonoid.faithfulSMul`

English:
instance Submonoid.faithfulSMul
  signature: {M' α : Type*} [MulOneClass M'] [SMul M' α] {S : Submonoid M'}
  body: ⟨fun h => Subtype.ext eq_of_smul_eq_smul h⟩

中文:
实例 子幺半群.faithfulSMul
  签名: {M' α : 类型} [MulOne类 M'] [标量乘法 M' α] {S : 子幺半群 M'}
  定义体: ⟨fun h => Subtype.ext eq_of_smul_eq_smul h⟩

Depends on / 依赖: Subtype, Subtype.ext, eq_of_smul_eq_smul
-/
instance Submonoid.faithfulSMul {M' α : Type*} [MulOneClass M'] [SMul M' α] {S : Submonoid M'}
    [FaithfulSMul M' α] : FaithfulSMul S α :=
⟨fun h => Subtype.ext eq_of_smul_eq_smul h⟩

section Units

namespace Submonoid

set_option backward.isDefEq.respectTransparency false in
/-- The multiplicative equivalence between the type of units of `M` and the submonoid of unit
elements of `M`. -/
@[to_additive (attr := simps!) /-- The additive equivalence between the type of additive units of
`M` and the additive submonoid whose elements are the additive units of `M`. -/]
/--
Definition of `unitsTypeEquivIsUnitSubmonoid` / `unitsTypeEquivIsUnitSubmonoid` 的定义

English:
definition unitsTypeEquivIsUnitSubmonoid
  signature: {M : Type*} [Monoid M]
  body: ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv _ := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

中文:
定义 unitsTypeEquivIsUnitSubmonoid
  签名: {M : 类型} [幺半群 M]
  定义体: ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv _ := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

Depends on / 依赖: Units.isUnit, isUnit
-/
noncomputable def unitsTypeEquivIsUnitSubmonoid {M : Type*} [Monoid M] :
    Mˣ ≃* IsUnit.submonoid M where
  toFun x := ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv _ := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

end Submonoid

end Units

namespace Submonoid

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

@[to_additive]
/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : F) (S : Submonoid N)
  statement: (S.comap f).map f = S ⊓ MonoidHom.mrange f
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]

中文:
定理 map_comap_eq
  条件: (f : F) (S : 子幺半群 N)
  结论: (S.comap f).map f = S ⊓ 幺半群态射.mrange f
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : F) (S : Submonoid N) : (S.comap f).map f = S ⊓ MonoidHom.mrange f :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]
/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  given: {f : F} {S : Submonoid N} (h : S <= MonoidHom.mrange f)
  proof: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

@[to_additive]

中文:
定理 map_comap_eq_self
  条件: {f : F} {S : 子幺半群 N} (h : S <= 幺半群态射.mrange f)
  证明: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

@[to_additive]

Depends on / 依赖: inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self {f : F} {S : Submonoid N} (h : S <= MonoidHom.mrange f) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

@[to_additive]
/--
theorem `map_comap_eq_self_of_surjective` / 定理 `map_comap_eq_self_of_surjective`

English:
theorem map_comap_eq_self_of_surjective
  given: {f : F} (h : Function.Surjective f) {S : Submonoid N}
  proof: map_comap_eq_self (MonoidHom.mrange_eq_top_of_surjective _ h ▸ le_top)

中文:
定理 map_comap_eq_self_of_surjective
  条件: {f : F} (h : 函数.满射 f) {S : 子幺半群 N}
  证明: map_comap_eq_self (MonoidHom.mrange_eq_top_of_surjective _ h ▸ le_top)

Depends on / 依赖: MonoidHom, MonoidHom.mrange_eq_top_of_surjective, le_top, map_comap_eq_self, mrange_eq_top_of_surjective
-/
theorem map_comap_eq_self_of_surjective {f : F} (h : Function.Surjective f) {S : Submonoid N} :
    map f (comap f S) = S :=
  map_comap_eq_self (MonoidHom.mrange_eq_top_of_surjective _ h ▸ le_top)

end Submonoid
