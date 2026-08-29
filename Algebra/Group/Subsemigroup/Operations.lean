/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Operations on `Subsemigroup`s

In this file we define various operations on `Subsemigroup`s and `MulHom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `Subsemigroup.toAddSubsemigroup`, `Subsemigroup.toAddSubsemigroup'`,
  `AddSubsemigroup.toSubsemigroup`, `AddSubsemigroup.toSubsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `Multiplicative M`, and `Additive M`. These are stated as `OrderIso`s.

### (Commutative) semigroup structure on a subsemigroup

* `Subsemigroup.toSemigroup`, `Subsemigroup.toCommSemigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `Subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `Subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `Subsemigroup.prod`: product of two subsemigroups `s : Subsemigroup M` and `t : Subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `Subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `Subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `MulEquiv.subsemigroupCongr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `Subsemigroup.prodEquiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `MulHom`s

* `MulHom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `MulHom.domRestrict`: restrict a semigroup homomorphism to a subsemigroup of its domain;
* `MulHom.codRestrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `MulHom.srangeRestrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `Mathlib/Algebra/Group/Submonoid/Operations.lean`, omitting only that
which is necessary.

## Tags

subsemigroup, range, product, map, comap
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N P σ : Type*}

/-!
### Conversion to/from `Additive`/`Multiplicative`
-/


section

variable [Mul M]

/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `Additive M`. -/
@[simps]
/--
Definition of `Subsemigroup.toAddSubsemigroup` / `Subsemigroup.toAddSubsemigroup` 的定义

English:
definition Subsemigroup.toAddSubsemigroup
  signature: : Subsemigroup M ≃o AddSubsemigroup (Additive M) where
  body: { carrier := Additive.toMul ⁻¹' S
      add_mem' := S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := S.add_mem' }
  map_rel_iff' := Iff.rfl

中文:
定义 子半群.toAddSubsemigroup
  签名: : 子半群 M ≃o 加法子半群 (加性 M) where
  定义体: { carrier := Additive.toMul ⁻¹' S
      add_mem' := S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := S.add_mem' }
  map_rel_iff' := Iff.rfl

Depends on / 依赖: Additive, Additive.ofMul, Additive.toMul, Iff.rfl, S.add_mem, S.mul_mem, add_mem, carrier, invFun, map_rel_iff, mul_mem
-/
def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M) where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      add_mem' := S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := S.add_mem' }
  map_rel_iff' := Iff.rfl

/--
Definition of `AddSubsemigroup.toSubsemigroup'` / `AddSubsemigroup.toSubsemigroup'` 的定义

English:
abbreviation AddSubsemigroup.toSubsemigroup'
  signature: : AddSubsemigroup (Additive M) ≃o Subsemigroup M
  body: Subsemigroup.toAddSubsemigroup.symm

中文:
缩写 加法子半群.toSubsemigroup'
  签名: : 加法子半群 (加性 M) ≃o 子半群 M
  定义体: Subsemigroup.toAddSubsemigroup.symm

Depends on / 依赖: Subsemigroup, Subsemigroup.toAddSubsemigroup.symm, toAddSubsemigroup
-/
abbrev AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemigroup M :=
  Subsemigroup.toAddSubsemigroup.symm

/--
theorem `Subsemigroup.toAddSubsemigroup_closure` / 定理 `Subsemigroup.toAddSubsemigroup_closure`

English:
theorem Subsemigroup.toAddSubsemigroup_closure
  given: (S : Set M)
  proof: le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 (AddSubsemigroup.subset_closure (M := Additive M)))
    (AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))

中文:
定理 子半群.toAddSubsemigroup_closure
  条件: (S : 集合 M)
  证明: le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 (AddSubsemigroup.subset_closure (M := Additive M)))
    (AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))

Depends on / 依赖: AddSubsemigroup, AddSubsemigroup.closure_le, AddSubsemigroup.subset_closure, Additive, Subsemigroup, Subsemigroup.closure_le, Subsemigroup.subset_closure, Subsemigroup.toAddSubsemigroup.le_symm_apply, closure_le, le_antisymm, le_symm_apply, subset_closure, toAddSubsemigroup
-/
theorem Subsemigroup.toAddSubsemigroup_closure (S : Set M) :
    Subsemigroup.toAddSubsemigroup (Subsemigroup.closure S) =
    AddSubsemigroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 (AddSubsemigroup.subset_closure (M := Additive M)))
    (AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))

/--
theorem `AddSubsemigroup.toSubsemigroup'_closure` / 定理 `AddSubsemigroup.toSubsemigroup'_closure`

English:
theorem AddSubsemigroup.toSubsemigroup'_closure
  given: (S : Set (Additive M))
  proof: le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := Additive M))

中文:
定理 加法子半群.toSubsemigroup'_closure
  条件: (S : 集合 (加性 M))
  证明: le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := Additive M))
-/
theorem AddSubsemigroup.toSubsemigroup'_closure (S : Set (Additive M)) :
    AddSubsemigroup.toSubsemigroup' (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 (Subsemigroup.subset_closure (M := M)))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := Additive M))

end

section

variable {A : Type*} [Add A]

/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `Multiplicative A`. -/
@[simps]
/--
Definition of `AddSubsemigroup.toSubsemigroup` / `AddSubsemigroup.toSubsemigroup` 的定义

English:
definition AddSubsemigroup.toSubsemigroup
  signature: : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A) where
  body: { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := S.mul_mem' }
  map_rel_iff' := Iff.rfl

中文:
定义 加法子半群.toSubsemigroup
  签名: : 加法子半群 A ≃o 子半群 (Multiplicative A) where
  定义体: { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := S.mul_mem' }
  map_rel_iff' := Iff.rfl

Depends on / 依赖: Iff.rfl, Multiplicative, Multiplicative.ofAdd, Multiplicative.toAdd, S.add_mem, S.mul_mem, add_mem, carrier, invFun, map_rel_iff, mul_mem
-/
def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A) where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := S.mul_mem' }
  map_rel_iff' := Iff.rfl

/--
Definition of `Subsemigroup.toAddSubsemigroup'` / `Subsemigroup.toAddSubsemigroup'` 的定义

English:
abbreviation Subsemigroup.toAddSubsemigroup'
  signature: : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A
  body: AddSubsemigroup.toSubsemigroup.symm

中文:
缩写 子半群.toAddSubsemigroup'
  签名: : 子半群 (Multiplicative A) ≃o 加法子半群 A
  定义体: AddSubsemigroup.toSubsemigroup.symm

Depends on / 依赖: AddSubsemigroup, AddSubsemigroup.toSubsemigroup.symm, toSubsemigroup
-/
abbrev Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A :=
  AddSubsemigroup.toSubsemigroup.symm

/--
theorem `AddSubsemigroup.toSubsemigroup_closure` / 定理 `AddSubsemigroup.toSubsemigroup_closure`

English:
theorem AddSubsemigroup.toSubsemigroup_closure
  given: (S : Set A)
  proof: le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure (M := Multiplicative A))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))

中文:
定理 加法子半群.toSubsemigroup_closure
  条件: (S : 集合 A)
  证明: le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure (M := Multiplicative A))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))

Depends on / 依赖: AddSubsemigroup, AddSubsemigroup.closure_le, AddSubsemigroup.subset_closure, AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le, Multiplicative, Subsemigroup, Subsemigroup.closure_le, Subsemigroup.subset_closure, closure_le, l_le, le_antisymm, subset_closure, toSubsemigroup, to_galoisConnection
-/
theorem AddSubsemigroup.toSubsemigroup_closure (S : Set A) :
    AddSubsemigroup.toSubsemigroup (AddSubsemigroup.closure S) =
      Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galoisConnection.l_le <|
AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure (M := Multiplicative A))
    (Subsemigroup.closure_le.2 <| AddSubsemigroup.subset_closure (M := A))

/--
theorem `Subsemigroup.toAddSubsemigroup'_closure` / 定理 `Subsemigroup.toAddSubsemigroup'_closure`

English:
theorem Subsemigroup.toAddSubsemigroup'_closure
  given: (S : Set (Multiplicative A))
  proof: le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure (M := A))
    (AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))

中文:
定理 子半群.toAddSubsemigroup'_closure
  条件: (S : 集合 (Multiplicative A))
  证明: le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure (M := A))
    (AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))
-/
theorem Subsemigroup.toAddSubsemigroup'_closure (S : Set (Multiplicative A)) :
    Subsemigroup.toAddSubsemigroup' (Subsemigroup.closure S) =
      AddSubsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galoisConnection.l_le <|
Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure (M := A))
    (AddSubsemigroup.closure_le.2 <| Subsemigroup.subset_closure (M := Multiplicative A))

end

namespace Subsemigroup

open Set

/-!
### `comap` and `map`
-/


variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      /-- The preimage of an `AddSubsemigroup` along an `AddSemigroup` homomorphism is an
      `AddSubsemigroup`. -/]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : M ->ₙ* N) (S : Subsemigroup N)
  body: f ⁻¹' S
  mul_mem' ha hb := show f (_ * _) in S by rw [map_mul]; exact mul_mem ha hb

@[to_additive (attr := simp)]

中文:
定义 comap
  签名: (f : M ->ₙ* N) (S : 子半群 N)
  定义体: f ⁻¹' S
  mul_mem' ha hb := show f (_ * _) in S by rw [map_mul]; exact mul_mem ha hb

@[to_additive (attr := simp)]
-/
def comap (f : M ->ₙ* N) (S : Subsemigroup N) :
    Subsemigroup M where
  carrier := f ⁻¹' S
  mul_mem' ha hb := show f (_ * _) in S by rw [map_mul]; exact mul_mem ha hb

@[to_additive (attr := simp)]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (S : Subsemigroup N) (f : M ->ₙ* N)
  statement: (S.comap f : Set M) = f ⁻¹' S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_comap
  条件: (S : 子半群 N) (f : M ->ₙ* N)
  结论: (S.comap f : 集合 M) = f ⁻¹' S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_comap (S : Subsemigroup N) (f : M ->ₙ* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {S : Subsemigroup N} {f : M ->ₙ* N} {x : M}
  statement: x in S.comap f ↔ f x in S
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_comap
  条件: {S : 子半群 N} {f : M ->ₙ* N} {x : M}
  结论: x in S.comap f ↔ f x in S
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {S : Subsemigroup N} {f : M ->ₙ* N} {x : M} : x in S.comap f ↔ f x in S :=
  Iff.rfl

@[to_additive]
/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (S : Subsemigroup P) (g : N ->ₙ* P) (f : M ->ₙ* N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_comap
  条件: (S : 子半群 P) (g : N ->ₙ* P) (f : M ->ₙ* N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_comap (S : Subsemigroup P) (g : N ->ₙ* P) (f : M ->ₙ* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (S : Subsemigroup P)
  statement: S.comap (MulHom.id _) = S
  proof: ext (by simp)

中文:
定理 comap_id
  条件: (S : 子半群 P)
  结论: S.comap (乘法半群态射.id _) = S
  证明: ext (by simp)
-/
theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S :=
  ext (by simp)

/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      /-- The image of an `AddSubsemigroup` along an `AddSemigroup` homomorphism is
      an `AddSubsemigroup`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₙ* N) (S : Subsemigroup M)
  body: f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : M ->ₙ* N) (S : 子半群 M)
  定义体: f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
-/
def map (f : M ->ₙ* N) (S : Subsemigroup M) : Subsemigroup N where
  carrier := f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul]⟩

@[to_additive (attr := simp)]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (f : M ->ₙ* N) (S : Subsemigroup M)
  statement: (S.map f : Set N) = f '' S
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_map
  条件: (f : M ->ₙ* N) (S : 子半群 M)
  结论: (S.map f : 集合 N) = f '' S
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_map (f : M ->ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : M ->ₙ* N} {S : Subsemigroup M} {y : N}
  statement: y in S.map f ↔ exists x in S, f x = y
  proof: mem_image _ _ _

@[to_additive]

中文:
定理 mem_map
  条件: {f : M ->ₙ* N} {S : 子半群 M} {y : N}
  结论: y in S.map f ↔ 存在 x in S, f x = y
  证明: mem_image _ _ _

@[to_additive]

Depends on / 依赖: mem_image
-/
theorem mem_map {f : M ->ₙ* N} {S : Subsemigroup M} {y : N} : y in S.map f ↔ exists x in S, f x = y :=
  mem_image _ _ _

@[to_additive]
/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : M ->ₙ* N) {S : Subsemigroup M} {x : M} (hx : x in S)
  statement: f x in S.map f
  proof: mem_image_of_mem f hx

@[to_additive]

中文:
定理 mem_map_of_mem
  条件: (f : M ->ₙ* N) {S : 子半群 M} {x : M} (hx : x in S)
  结论: f x in S.map f
  证明: mem_image_of_mem f hx

@[to_additive]

Depends on / 依赖: mem_image_of_mem
-/
theorem mem_map_of_mem (f : M ->ₙ* N) {S : Subsemigroup M} {x : M} (hx : x in S) : f x in S.map f :=
  mem_image_of_mem f hx

@[to_additive]
/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : M ->ₙ* N) (S : Subsemigroup M) (x : S)
  statement: f x in S.map f
  proof: mem_map_of_mem f x.prop

@[to_additive]

中文:
定理 apply_coe_mem_map
  条件: (f : M ->ₙ* N) (S : 子半群 M) (x : S)
  结论: f x in S.map f
  证明: mem_map_of_mem f x.prop

@[to_additive]

Depends on / 依赖: mem_map_of_mem, x.prop
-/
theorem apply_coe_mem_map (f : M ->ₙ* N) (S : Subsemigroup M) (x : S) : f x in S.map f :=
  mem_map_of_mem f x.prop

@[to_additive]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : N ->ₙ* P) (f : M ->ₙ* N)
  statement: (S.map f).map g = S.map (g.comp f)
  proof: SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp high)]

中文:
定理 map_map
  条件: (g : N ->ₙ* P) (f : M ->ₙ* N)
  结论: (S.map f).map g = S.map (g.comp f)
  证明: SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp high)]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : N ->ₙ* P) (f : M ->ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective image_image _ _ _

@[to_additive (attr := simp high)]
/--
theorem `mem_map_iff_mem` / 定理 `mem_map_iff_mem`

English:
theorem mem_map_iff_mem
  given: {f : M ->ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M}
  proof: hf.mem_set_image

@[to_additive]

中文:
定理 mem_map_iff_mem
  条件: {f : M ->ₙ* N} (hf : 函数.单射 f) {S : 子半群 M} {x : M}
  证明: hf.mem_set_image

@[to_additive]

Depends on / 依赖: hf.mem_set_image, mem_set_image
-/
theorem mem_map_iff_mem {f : M ->ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x in S.map f ↔ x in S :=
  hf.mem_set_image

@[to_additive]
/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : M ->ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N}
  proof: image_subset_iff

@[to_additive]

中文:
定理 map_le_iff_le_comap
  条件: {f : M ->ₙ* N} {S : 子半群 M} {T : 子半群 N}
  证明: image_subset_iff

@[to_additive]

Depends on / 依赖: image_subset_iff
-/
theorem map_le_iff_le_comap {f : M ->ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} :
    S.map f <= T ↔ S <= T.comap f :=
  image_subset_iff

@[to_additive]
/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : M ->ₙ* N)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap

@[to_additive]

中文:
定理 gc_map_comap
  条件: (f : M ->ₙ* N)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
-/
theorem gc_map_comap (f : M ->ₙ* N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

@[to_additive]
/--
theorem `map_le_of_le_comap` / 定理 `map_le_of_le_comap`

English:
theorem map_le_of_le_comap
  given: {T : Subsemigroup N} {f : M ->ₙ* N}
  statement: S <= T.comap f -> S.map f <= T
  proof: (gc_map_comap f).l_le

@[to_additive]

中文:
定理 map_le_of_le_comap
  条件: {T : 子半群 N} {f : M ->ₙ* N}
  结论: S <= T.comap f -> S.map f <= T
  证明: (gc_map_comap f).l_le

@[to_additive]

Depends on / 依赖: gc_map_comap, l_le
-/
theorem map_le_of_le_comap {T : Subsemigroup N} {f : M ->ₙ* N} : S <= T.comap f -> S.map f <= T :=
  (gc_map_comap f).l_le

@[to_additive]
/--
theorem `le_comap_of_map_le` / 定理 `le_comap_of_map_le`

English:
theorem le_comap_of_map_le
  given: {T : Subsemigroup N} {f : M ->ₙ* N}
  statement: S.map f <= T -> S <= T.comap f
  proof: (gc_map_comap f).le_u

@[to_additive]

中文:
定理 le_comap_of_map_le
  条件: {T : 子半群 N} {f : M ->ₙ* N}
  结论: S.map f <= T -> S <= T.comap f
  证明: (gc_map_comap f).le_u

@[to_additive]

Depends on / 依赖: gc_map_comap, le_u
-/
theorem le_comap_of_map_le {T : Subsemigroup N} {f : M ->ₙ* N} : S.map f <= T -> S <= T.comap f :=
  (gc_map_comap f).le_u

@[to_additive]
/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: {f : M ->ₙ* N}
  statement: S <= (S.map f).comap f
  proof: (gc_map_comap f).le_u_l _

@[to_additive]

中文:
定理 le_comap_map
  条件: {f : M ->ₙ* N}
  结论: S <= (S.map f).comap f
  证明: (gc_map_comap f).le_u_l _

@[to_additive]

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map {f : M ->ₙ* N} : S <= (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

@[to_additive]
/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: {S : Subsemigroup N} {f : M ->ₙ* N}
  statement: (S.comap f).map f <= S
  proof: (gc_map_comap f).l_u_le _

@[to_additive]

中文:
定理 map_comap_le
  条件: {S : 子半群 N} {f : M ->ₙ* N}
  结论: (S.comap f).map f <= S
  证明: (gc_map_comap f).l_u_le _

@[to_additive]

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le {S : Subsemigroup N} {f : M ->ₙ* N} : (S.comap f).map f <= S :=
  (gc_map_comap f).l_u_le _

@[to_additive]
/--
theorem `monotone_map` / 定理 `monotone_map`

English:
theorem monotone_map
  given: {f : M ->ₙ* N}
  statement: Monotone (map f)
  proof: (gc_map_comap f).monotone_l

@[to_additive]

中文:
定理 monotone_map
  条件: {f : M ->ₙ* N}
  结论: 递增 (map f)
  证明: (gc_map_comap f).monotone_l

@[to_additive]

Depends on / 依赖: gc_map_comap, monotone_l
-/
theorem monotone_map {f : M ->ₙ* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

@[to_additive]
/--
theorem `monotone_comap` / 定理 `monotone_comap`

English:
theorem monotone_comap
  given: {f : M ->ₙ* N}
  statement: Monotone (comap f)
  proof: (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]

中文:
定理 monotone_comap
  条件: {f : M ->ₙ* N}
  结论: 递增 (comap f)
  证明: (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, monotone_u
-/
theorem monotone_comap {f : M ->ₙ* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[to_additive (attr := simp)]
/--
theorem `map_comap_map` / 定理 `map_comap_map`

English:
theorem map_comap_map
  given: {f : M ->ₙ* N}
  statement: ((S.map f).comap f).map f = S.map f
  proof: (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]

中文:
定理 map_comap_map
  条件: {f : M ->ₙ* N}
  结论: ((S.map f).comap f).map f = S.map f
  证明: (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, l_u_l_eq_l
-/
theorem map_comap_map {f : M ->ₙ* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[to_additive (attr := simp)]
/--
theorem `comap_map_comap` / 定理 `comap_map_comap`

English:
theorem comap_map_comap
  given: {S : Subsemigroup N} {f : M ->ₙ* N}
  proof: (gc_map_comap f).u_l_u_eq_u _

@[to_additive]

中文:
定理 comap_map_comap
  条件: {S : 子半群 N} {f : M ->ₙ* N}
  证明: (gc_map_comap f).u_l_u_eq_u _

@[to_additive]

Depends on / 依赖: gc_map_comap, u_l_u_eq_u
-/
theorem comap_map_comap {S : Subsemigroup N} {f : M ->ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

@[to_additive]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (S T : Subsemigroup M) (f : M ->ₙ* N)
  statement: (S ⊔ T).map f = S.map f ⊔ T.map f
  proof: (gc_map_comap f).l_sup

@[to_additive]

中文:
定理 map_sup
  条件: (S T : 子半群 M) (f : M ->ₙ* N)
  结论: (S ⊔ T).map f = S.map f ⊔ T.map f
  证明: (gc_map_comap f).l_sup

@[to_additive]

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (S T : Subsemigroup M) (f : M ->ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup

@[to_additive]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : M ->ₙ* N) (s : ι -> Subsemigroup M)
  proof: (gc_map_comap f).l_iSup

@[to_additive]

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : M ->ₙ* N) (s : ι -> 子半群 M)
  证明: (gc_map_comap f).l_iSup

@[to_additive]

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : M ->ₙ* N) (s : ι -> Subsemigroup M) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

@[to_additive]
/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (S T : Subsemigroup M) (f : M ->ₙ* N) (hf : Function.Injective f)
  proof: SetLike.coe_injective (Set.image_inter hf)

@[to_additive]

中文:
定理 map_inf
  条件: (S T : 子半群 M) (f : M ->ₙ* N) (hf : 函数.单射 f)
  证明: SetLike.coe_injective (Set.image_inter hf)

@[to_additive]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (S T : Subsemigroup M) (f : M ->ₙ* N) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[to_additive]
/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  statement: {ι : Sort*} [Nonempty ι] (f : M ->ₙ* N) (hf : Function.Injective f)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]

中文:
定理 map_iInf
  结论: {ι : 类型层*} [非空 ι] (f : M ->ₙ* N) (hf : 函数.单射 f)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, image_iInter_eq, injOn_of_injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : M ->ₙ* N) (hf : Function.Injective f)
    (s : ι -> Subsemigroup M) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

@[to_additive]
/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (S T : Subsemigroup N) (f : M ->ₙ* N)
  statement: (S ⊓ T).comap f = S.comap f ⊓ T.comap f
  proof: (gc_map_comap f).u_inf

@[to_additive]

中文:
定理 comap_inf
  条件: (S T : 子半群 N) (f : M ->ₙ* N)
  结论: (S ⊓ T).comap f = S.comap f ⊓ T.comap f
  证明: (gc_map_comap f).u_inf

@[to_additive]

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (S T : Subsemigroup N) (f : M ->ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf

@[to_additive]
/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : M ->ₙ* N) (s : ι -> Subsemigroup N)
  proof: (gc_map_comap f).u_iInf

@[to_additive (attr := simp)]

中文:
定理 comap_iInf
  条件: {ι : 类型层*} (f : M ->ₙ* N) (s : ι -> 子半群 N)
  证明: (gc_map_comap f).u_iInf

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : M ->ₙ* N) (s : ι -> Subsemigroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[to_additive (attr := simp)]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : M ->ₙ* N)
  statement: (⊥ : Subsemigroup M).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[to_additive (attr := simp)]

中文:
定理 map_bot
  条件: (f : M ->ₙ* N)
  结论: (⊥ : 子半群 M).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : M ->ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[to_additive (attr := simp)]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : M ->ₙ* N)
  statement: (⊤ : Subsemigroup N).comap f = ⊤
  proof: (gc_map_comap f).u_top

@[to_additive (attr := simp)]

中文:
定理 comap_top
  条件: (f : M ->ₙ* N)
  结论: (⊤ : 子半群 N).comap f = ⊤
  证明: (gc_map_comap f).u_top

@[to_additive (attr := simp)]

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : M ->ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[to_additive (attr := simp)]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : Subsemigroup M)
  statement: S.map (MulHom.id M) = S
  proof: ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

中文:
定理 map_id
  条件: (S : 子半群 M)
  结论: S.map (乘法半群态射.id M) = S
  证明: ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
-/
theorem map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S :=
  ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type*} {f : M ->ₙ* N}

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
  given: (S : Subsemigroup M)
  statement: (S.map f).comap f = S
  proof: (gciMapComap hf).u_l_eq _

@[to_additive]

中文:
定理 comap_map_eq_of_injective
  条件: (S : 子半群 M)
  结论: (S.map f).comap f = S
  证明: (gciMapComap hf).u_l_eq _

@[to_additive]

Depends on / 依赖: MulEquivClass, MulZeroClass, gciMapComap, toZeroHomClass, u_l_eq
-/
theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S :=
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

Depends on / 依赖: gciMapComap, toMonoidWithZeroHomClass, u_surjective
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
  given: (S T : Subsemigroup M)
  statement: (S.map f ⊓ T.map f).comap f = S ⊓ T
  proof: (gciMapComap hf).u_inf_l _ _

@[to_additive]

中文:
定理 comap_inf_map_of_injective
  条件: (S T : 子半群 M)
  结论: (S.map f ⊓ T.map f).comap f = S ⊓ T
  证明: (gciMapComap hf).u_inf_l _ _

@[to_additive]

Depends on / 依赖: gciMapComap, u_inf_l
-/
theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

@[to_additive]
/--
theorem `comap_iInf_map_of_injective` / 定理 `comap_iInf_map_of_injective`

English:
theorem comap_iInf_map_of_injective
  given: (S : ι -> Subsemigroup M)
  proof: (gciMapComap hf).u_iInf_l _

@[to_additive]

中文:
定理 comap_iInf_map_of_injective
  条件: (S : ι -> 子半群 M)
  证明: (gciMapComap hf).u_iInf_l _

@[to_additive]

Depends on / 依赖: gciMapComap, u_iInf_l
-/
theorem comap_iInf_map_of_injective (S : ι -> Subsemigroup M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

@[to_additive]
/--
theorem `comap_sup_map_of_injective` / 定理 `comap_sup_map_of_injective`

English:
theorem comap_sup_map_of_injective
  given: (S T : Subsemigroup M)
  statement: (S.map f ⊔ T.map f).comap f = S ⊔ T
  proof: (gciMapComap hf).u_sup_l _ _

@[to_additive]

中文:
定理 comap_sup_map_of_injective
  条件: (S T : 子半群 M)
  结论: (S.map f ⊔ T.map f).comap f = S ⊔ T
  证明: (gciMapComap hf).u_sup_l _ _

@[to_additive]

Depends on / 依赖: gciMapComap, u_sup_l
-/
theorem comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

@[to_additive]
/--
theorem `comap_iSup_map_of_injective` / 定理 `comap_iSup_map_of_injective`

English:
theorem comap_iSup_map_of_injective
  given: (S : ι -> Subsemigroup M)
  proof: (gciMapComap hf).u_iSup_l _

@[to_additive]

中文:
定理 comap_iSup_map_of_injective
  条件: (S : ι -> 子半群 M)
  证明: (gciMapComap hf).u_iSup_l _

@[to_additive]

Depends on / 依赖: gciMapComap, u_iSup_l
-/
theorem comap_iSup_map_of_injective (S : ι -> Subsemigroup M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

@[to_additive]
/--
theorem `map_le_map_iff_of_injective` / 定理 `map_le_map_iff_of_injective`

English:
theorem map_le_map_iff_of_injective
  given: {S T : Subsemigroup M}
  statement: S.map f <= T.map f ↔ S <= T
  proof: (gciMapComap hf).l_le_l_iff

@[to_additive]

中文:
定理 map_le_map_iff_of_injective
  条件: {S T : 子半群 M}
  结论: S.map f <= T.map f ↔ S <= T
  证明: (gciMapComap hf).l_le_l_iff

@[to_additive]

Depends on / 依赖: gciMapComap, l_le_l_iff
-/
theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f <= T.map f ↔ S <= T :=
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

variable {ι : Type*} {f : M ->ₙ* N} (hf : Function.Surjective f)
include hf

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
@[to_additive /-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/]
/--
Definition of `giMapComap` / `giMapComap` 的定义

English:
definition giMapComap
  signature: : GaloisInsertion (map f) (comap f)
  body: (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

@[to_additive]

中文:
定义 giMapComap
  签名: : Galois嵌入 (map f) (comap f)
  定义体: (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

@[to_additive]

Depends on / 依赖: gc_map_comap, mem_map, toGaloisInsertion
-/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

@[to_additive]
/--
theorem `map_comap_eq_of_surjective` / 定理 `map_comap_eq_of_surjective`

English:
theorem map_comap_eq_of_surjective
  given: (S : Subsemigroup N)
  statement: (S.comap f).map f = S
  proof: (giMapComap hf).l_u_eq _

@[to_additive]

中文:
定理 map_comap_eq_of_surjective
  条件: (S : 子半群 N)
  结论: (S.comap f).map f = S
  证明: (giMapComap hf).l_u_eq _

@[to_additive]

Depends on / 依赖: giMapComap, l_u_eq
-/
theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S :=
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
  given: (S T : Subsemigroup N)
  proof: (giMapComap hf).l_inf_u _ _

@[to_additive]

中文:
定理 map_inf_comap_of_surjective
  条件: (S T : 子半群 N)
  证明: (giMapComap hf).l_inf_u _ _

@[to_additive]

Depends on / 依赖: giMapComap, l_inf_u
-/
theorem map_inf_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

@[to_additive]
/--
theorem `map_iInf_comap_of_surjective` / 定理 `map_iInf_comap_of_surjective`

English:
theorem map_iInf_comap_of_surjective
  given: (S : ι -> Subsemigroup N)
  proof: (giMapComap hf).l_iInf_u _

@[to_additive]

中文:
定理 map_iInf_comap_of_surjective
  条件: (S : ι -> 子半群 N)
  证明: (giMapComap hf).l_iInf_u _

@[to_additive]

Depends on / 依赖: giMapComap, l_iInf_u
-/
theorem map_iInf_comap_of_surjective (S : ι -> Subsemigroup N) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

@[to_additive]
/--
theorem `map_sup_comap_of_surjective` / 定理 `map_sup_comap_of_surjective`

English:
theorem map_sup_comap_of_surjective
  given: (S T : Subsemigroup N)
  proof: (giMapComap hf).l_sup_u _ _

@[to_additive]

中文:
定理 map_sup_comap_of_surjective
  条件: (S T : 子半群 N)
  证明: (giMapComap hf).l_sup_u _ _

@[to_additive]

Depends on / 依赖: giMapComap, l_sup_u
-/
theorem map_sup_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

@[to_additive]
/--
theorem `map_iSup_comap_of_surjective` / 定理 `map_iSup_comap_of_surjective`

English:
theorem map_iSup_comap_of_surjective
  given: (S : ι -> Subsemigroup N)
  proof: (giMapComap hf).l_iSup_u _

@[to_additive]

中文:
定理 map_iSup_comap_of_surjective
  条件: (S : ι -> 子半群 N)
  证明: (giMapComap hf).l_iSup_u _

@[to_additive]

Depends on / 依赖: giMapComap, l_iSup_u
-/
theorem map_iSup_comap_of_surjective (S : ι -> Subsemigroup N) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

@[to_additive]
/--
theorem `comap_le_comap_iff_of_surjective` / 定理 `comap_le_comap_iff_of_surjective`

English:
theorem comap_le_comap_iff_of_surjective
  given: {S T : Subsemigroup N}
  statement: S.comap f <= T.comap f ↔ S <= T
  proof: (giMapComap hf).u_le_u_iff

@[to_additive]

中文:
定理 comap_le_comap_iff_of_surjective
  条件: {S T : 子半群 N}
  结论: S.comap f <= T.comap f ↔ S <= T
  证明: (giMapComap hf).u_le_u_iff

@[to_additive]

Depends on / 依赖: giMapComap, u_le_u_iff
-/
theorem comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f <= T.comap f ↔ S <= T :=
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

end Subsemigroup

namespace Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive (attr := simps)
  /-- The top additive subsemigroup is isomorphic to the additive semigroup. -/]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : Subsemigroup M) ≃* M where
  body: x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]

中文:
定义 topEquiv
  签名: : (⊤ : 子半群 M) ≃* M where
  定义体: x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
-/
def topEquiv : (⊤ : Subsemigroup M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/--
theorem `topEquiv_toMulHom` / 定理 `topEquiv_toMulHom`

English:
theorem topEquiv_toMulHom
  proof: rfl

中文:
定理 topEquiv_toMulHom
  证明: rfl
-/
theorem topEquiv_toMulHom :
    ((topEquiv : _ ≃* M) : _ ->ₙ* M) = MulMemClass.subtype (⊤ : Subsemigroup M) :=
  rfl

/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive
/-- An additive subsemigroup is isomorphic to its image under an injective function -/]
/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (f : M ->ₙ* N) (hf : Function.Injective f)
  body: { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }

@[to_additive (attr := simp)]

中文:
定义 equivMapOfInjective
  签名: (f : M ->ₙ* N) (hf : 函数.单射 f)
  定义体: { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.Set.image, Subtype, Subtype.ext, map_mul
-/
noncomputable def equivMapOfInjective (f : M ->ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }

@[to_additive (attr := simp)]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  given: (f : M ->ₙ* N) (hf : Function.Injective f) (x : S)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_equivMapOfInjective_apply
  条件: (f : M ->ₙ* N) (hf : 函数.单射 f) (x : S)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_equivMapOfInjective_apply (f : M ->ₙ* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `closure_closure_coe_preimage` / 定理 `closure_closure_coe_preimage`

English:
theorem closure_closure_coe_preimage
  given: {s : Set M}
  proof: eq_top_iff.2 fun x _ => Subtype.recOn x fun _ hx' =>
    closure_induction (fun _ h => subset_closure h) (fun _ _ _ _ => mul_mem) hx'

中文:
定理 closure_closure_coe_preimage
  条件: {s : 集合 M}
  证明: eq_top_iff.2 fun x _ => Subtype.recOn x fun _ hx' =>
    closure_induction (fun _ h => subset_closure h) (fun _ _ _ _ => mul_mem) hx'

Depends on / 依赖: Subtype, Subtype.recOn, closure_induction, eq_top_iff, mul_mem, subset_closure
-/
theorem closure_closure_coe_preimage {s : Set M} :
    closure ((Subtype.val : closure s -> M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x _ => Subtype.recOn x fun _ hx' =>
    closure_induction (fun _ h => subset_closure h) (fun _ _ _ _ => mul_mem) hx'

/-- Given `Subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive prod
      /-- Given `AddSubsemigroup`s `s`, `t` of `AddSemigroup`s `A`, `B` respectively,
      `s × t` as an `AddSubsemigroup` of `A × B`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (s : Subsemigroup M) (t : Subsemigroup N)
  body: s ×ˢ t
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]

中文:
定义 乘积
  签名: (s : 子半群 M) (t : 子半群 N)
  定义体: s ×ˢ t
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]
-/
def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N) where
  carrier := s ×ˢ t
  mul_mem' hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩

@[to_additive (attr := norm_cast) coe_prod]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Subsemigroup M) (t : Subsemigroup N)
  proof: rfl

@[to_additive mem_prod]

中文:
定理 coe_prod
  条件: (s : 子半群 M) (t : 子半群 N)
  证明: rfl

@[to_additive mem_prod]
-/
theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) :=
  rfl

@[to_additive mem_prod]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N}
  proof: Iff.rfl

@[to_additive prod_mono]

中文:
定理 mem_prod
  条件: {s : 子半群 M} {t : 子半群 N} {p : M × N}
  证明: Iff.rfl

@[to_additive prod_mono]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} :
    p in s.prod t ↔ p.1 in s ∧ p.2 in t :=
  Iff.rfl

@[to_additive prod_mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ <= s₂) (ht : t₁ <= t₂)
  proof: Set.prod_mono hs ht

@[to_additive prod_top]

中文:
定理 prod_mono
  条件: {s₁ s₂ : 子半群 M} {t₁ t₂ : 子半群 N} (hs : s₁ <= s₂) (ht : t₁ <= t₂)
  证明: Set.prod_mono hs ht

@[to_additive prod_top]

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ <= s₂) (ht : t₁ <= t₂) :
    s₁.prod t₁ <= s₂.prod t₂ :=
  Set.prod_mono hs ht

@[to_additive prod_top]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (s : Subsemigroup M)
  statement: s.prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N)
  proof: ext fun x => by simp [mem_prod, MulHom.coe_fst]

@[to_additive top_prod]

中文:
定理 prod_top
  条件: (s : 子半群 M)
  结论: s.乘积 (⊤ : 子半群 N) = s.comap (乘法半群态射.fst M N)
  证明: ext fun x => by simp [mem_prod, MulHom.coe_fst]

@[to_additive top_prod]

Depends on / 依赖: MulHom, MulHom.coe_fst, coe_fst, map_zero, mem_prod, zero_mul
-/
theorem prod_top (s : Subsemigroup M) : s.prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_fst]

@[to_additive top_prod]
/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (s : Subsemigroup N)
  statement: (⊤ : Subsemigroup M).prod s = s.comap (MulHom.snd M N)
  proof: ext fun x => by simp [mem_prod, MulHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]

中文:
定理 top_prod
  条件: (s : 子半群 N)
  结论: (⊤ : 子半群 M).乘积 s = s.comap (乘法半群态射.snd M N)
  证明: ext fun x => by simp [mem_prod, MulHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]

Depends on / 依赖: MulHom, MulHom.coe_snd, coe_snd, mem_prod
-/
theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).prod s = s.comap (MulHom.snd M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤
  proof: (top_prod _).trans comap_top _

@[to_additive bot_prod_bot]

中文:
定理 top_prod_top
  结论: (⊤ : 子半群 M).乘积 (⊤ : 子半群 N) = ⊤
  证明: (top_prod _).trans comap_top _

@[to_additive bot_prod_bot]

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤ :=
(top_prod _).trans comap_top _

@[to_additive bot_prod_bot]
/--
theorem `bot_prod_bot` / 定理 `bot_prod_bot`

English:
theorem bot_prod_bot
  statement: (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥
  proof: SetLike.coe_injective by simp [coe_prod]

中文:
定理 bot_prod_bot
  结论: (⊥ : 子半群 M).乘积 (⊥ : 子半群 N) = ⊥
  证明: SetLike.coe_injective by simp [coe_prod]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, coe_prod
-/
theorem bot_prod_bot : (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥ :=
SetLike.coe_injective by simp [coe_prod]

/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prodEquiv
/-- The product of additive subsemigroups is isomorphic to their product as additive semigroups -/]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (s : Subsemigroup M) (t : Subsemigroup N)
  body: { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

中文:
定义 prodEquiv
  签名: (s : 子半群 M) (t : 子半群 N)
  定义体: { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.Set.prod, map_mul
-/
def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.prod t ≃* s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_mul' := fun _ _ => rfl }

open MulHom

@[to_additive]
/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {f : M ≃* N} {K : Subsemigroup M} {x : N}
  proof: @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

@[to_additive]

中文:
定理 mem_map_equiv
  条件: {f : M ≃* N} {K : 子半群 M} {x : N}
  证明: @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

@[to_additive]

Depends on / 依赖: Set.mem_image_equiv, f.toEquiv, mem_image_equiv, toEquiv
-/
theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x in K.map (f : M ->ₙ* N) ↔ f.symm x in K :=
  @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

@[to_additive]
/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (f : M ≃* N) (K : Subsemigroup M)
  proof: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]

中文:
定理 map_equiv_eq_comap_symm
  条件: (f : M ≃* N) (K : 子半群 M)
  证明: SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map (f : M ->ₙ* N) = K.comap (f.symm : N ->ₙ* M) :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

@[to_additive]
/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (f : N ≃* M) (K : Subsemigroup M)
  proof: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]

中文:
定理 comap_equiv_eq_map_symm
  条件: (f : N ≃* M) (K : 子半群 M)
  证明: (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap (f : N ->ₙ* M) = K.map (f.symm : M ->ₙ* N) :=
  (map_equiv_eq_comap_symm f.symm K).symm

@[to_additive (attr := simp)]
/--
theorem `map_equiv_top` / 定理 `map_equiv_top`

English:
theorem map_equiv_top
  given: (f : M ≃* N)
  statement: (⊤ : Subsemigroup M).map (f : M ->ₙ* N) = ⊤
  proof: SetLike.coe_injective Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]

中文:
定理 map_equiv_top
  条件: (f : M ≃* N)
  结论: (⊤ : 子半群 M).map (f : M ->ₙ* N) = ⊤
  证明: SetLike.coe_injective Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]

Depends on / 依赖: Set.image_univ.trans, SetLike, SetLike.coe_injective, coe_injective, f.surjective.range_eq, image_univ, range_eq, surjective
-/
theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map (f : M ->ₙ* N) = ⊤ :=
SetLike.coe_injective Set.image_univ.trans f.surjective.range_eq

@[to_additive le_prod_iff]
/--
theorem `le_prod_iff` / 定理 `le_prod_iff`

English:
theorem le_prod_iff
  given: {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)}
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

中文:
定理 le_prod_iff
  条件: {s : 子半群 M} {t : 子半群 N} {u : 子半群 (M × N)}
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
-/
theorem le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
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

end Subsemigroup

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive /-- The range of an `AddHom` is an `AddSubsemigroup`. -/]
/--
Definition of `srange` / `srange` 的定义

English:
definition srange
  signature: (f : M ->ₙ* N)
  body: ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]

中文:
定义 srange
  签名: (f : M ->ₙ* N)
  定义体: ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]

Depends on / 依赖: Set.image_univ.symm, Set.range, Subsemigroup, image_univ
-/
def srange (f : M ->ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm

@[to_additive (attr := simp)]
/--
theorem `coe_srange` / 定理 `coe_srange`

English:
theorem coe_srange
  given: (f : M ->ₙ* N)
  statement: (f.srange : Set N) = Set.range f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_srange
  条件: (f : M ->ₙ* N)
  结论: (f.srange : 集合 N) = 集合.range f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_srange (f : M ->ₙ* N) : (f.srange : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_srange` / 定理 `mem_srange`

English:
theorem mem_srange
  given: {f : M ->ₙ* N} {y : N}
  statement: y in f.srange ↔ exists x, f x = y
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_srange
  条件: {f : M ->ₙ* N} {y : N}
  结论: y in f.srange ↔ 存在 x, f x = y
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_srange {f : M ->ₙ* N} {y : N} : y in f.srange ↔ exists x, f x = y :=
  Iff.rfl

@[to_additive]
/--
theorem `srange_mk_aux_mul` / 定理 `srange_mk_aux_mul`

English:
theorem srange_mk_aux_mul
  statement: {f : M -> N} (hf : forall (x y : M), f (x * y) = f x * f y)
  proof: (srange ⟨f, hf⟩).mul_mem hx hy

中文:
定理 srange_mk_aux_mul
  结论: {f : M -> N} (hf : 对任意 (x y : M), f (x * y) = f x * f y)
  证明: (srange ⟨f, hf⟩).mul_mem hx hy
-/
private theorem srange_mk_aux_mul {f : M -> N} (hf : forall (x y : M), f (x * y) = f x * f y)
    {x y : N} (hx : x in Set.range f) (hy : y in Set.range f) :
    x * y in Set.range f :=
  (srange ⟨f, hf⟩).mul_mem hx hy

/--
theorem `srange_mk` / 定理 `srange_mk`

English:
theorem srange_mk
  given: (f : M -> N) (hf)
  proof: rfl

@[to_additive]

中文:
定理 srange_mk
  条件: (f : M -> N) (hf)
  证明: rfl

@[to_additive]
-/
@[to_additive (attr := simp)] theorem srange_mk (f : M -> N) (hf) :
    srange ⟨f, hf⟩ = ⟨Set.range f, by exact srange_mk_aux_mul hf⟩ := rfl

@[to_additive]
/--
theorem `srange_eq_map` / 定理 `srange_eq_map`

English:
theorem srange_eq_map
  given: (f : M ->ₙ* N)
  statement: f.srange = (⊤ : Subsemigroup M).map f
  proof: copy_eq _

@[to_additive]

中文:
定理 srange_eq_map
  条件: (f : M ->ₙ* N)
  结论: f.srange = (⊤ : 子半群 M).map f
  证明: copy_eq _

@[to_additive]

Depends on / 依赖: copy_eq
-/
theorem srange_eq_map (f : M ->ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f :=
  copy_eq _

@[to_additive]
/--
theorem `map_srange` / 定理 `map_srange`

English:
theorem map_srange
  given: (g : N ->ₙ* P) (f : M ->ₙ* N)
  statement: f.srange.map g = (g.comp f).srange
  proof: by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f

@[to_additive]

中文:
定理 map_srange
  条件: (g : N ->ₙ* P) (f : M ->ₙ* N)
  结论: f.srange.map g = (g.comp f).srange
  证明: by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f

@[to_additive]

Depends on / 依赖: Subsemigroup, map_map, srange_eq_map
-/
theorem map_srange (g : N ->ₙ* P) (f : M ->ₙ* N) : f.srange.map g = (g.comp f).srange := by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f

@[to_additive]
/--
theorem `srange_eq_top_iff_surjective` / 定理 `srange_eq_top_iff_surjective`

English:
theorem srange_eq_top_iff_surjective
  given: {N} [Mul N] {f : M ->ₙ* N}
  proof: SetLike.ext'_iff.trans Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

中文:
定理 srange_eq_top_iff_surjective
  条件: {N} [乘法 N] {f : M ->ₙ* N}
  证明: SetLike.ext'_iff.trans Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

Depends on / 依赖: Iff.trans, Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, coe_srange, coe_top, range_eq_univ
-/
theorem srange_eq_top_iff_surjective {N} [Mul N] {f : M ->ₙ* N} :
    f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f :=
SetLike.ext'_iff.trans Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddSemigroup` hom is the whole of the codomain. -/]
/--
theorem `srange_eq_top_of_surjective` / 定理 `srange_eq_top_of_surjective`

English:
theorem srange_eq_top_of_surjective
  given: {N} [Mul N] (f : M ->ₙ* N) (hf : Function.Surjective f)
  proof: srange_eq_top_iff_surjective.2 hf

@[to_additive]

中文:
定理 srange_eq_top_of_surjective
  条件: {N} [乘法 N] (f : M ->ₙ* N) (hf : 函数.满射 f)
  证明: srange_eq_top_iff_surjective.2 hf

@[to_additive]

Depends on / 依赖: srange_eq_top_iff_surjective
-/
theorem srange_eq_top_of_surjective {N} [Mul N] (f : M ->ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) :=
  srange_eq_top_iff_surjective.2 hf

@[to_additive]
/--
theorem `mclosure_preimage_le` / 定理 `mclosure_preimage_le`

English:
theorem mclosure_preimage_le
  given: (f : M ->ₙ* N) (s : Set N)
  statement: closure (f ⁻¹' s) <= (closure s).comap f
  proof: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

中文:
定理 mclosure_preimage_le
  条件: (f : M ->ₙ* N) (s : 集合 N)
  结论: closure (f ⁻¹' s) <= (closure s).comap f
  证明: closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, mem_comap, subset_closure
-/
theorem mclosure_preimage_le (f : M ->ₙ* N) (s : Set N) : closure (f ⁻¹' s) <= (closure s).comap f :=
closure_le.2 fun _ hx => SetLike.mem_coe.2 mem_comap.2 subset_closure hx

/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive
      /-- The image under an `AddSemigroup` hom of the `AddSubsemigroup` generated by a set
      equals the `AddSubsemigroup` generated by the image of the set. -/]
/--
theorem `map_mclosure` / 定理 `map_mclosure`

English:
theorem map_mclosure
  given: (f : M ->ₙ* N) (s : Set M)
  statement: (closure s).map f = closure (f '' s)
  proof: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemigroup.gi N).gc (Subsemigroup.gi M).gc
    fun _ => rfl

中文:
定理 map_mclosure
  条件: (f : M ->ₙ* N) (s : 集合 M)
  结论: (closure s).map f = closure (f '' s)
  证明: Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemigroup.gi N).gc (Subsemigroup.gi M).gc
    fun _ => rfl

Depends on / 依赖: Set.image_preimage.l_comm_of_u_comm, Subsemigroup, Subsemigroup.gi, gc_map_comap, image_preimage, l_comm_of_u_comm
-/
theorem map_mclosure (f : M ->ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemigroup.gi N).gc (Subsemigroup.gi M).gc
    fun _ => rfl

/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive /-- Restriction of an AddSemigroup hom to an `AddSubsemigroup` of the domain. -/]
/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M ->ₙ* N)
  body: f.comp (MulMemClass.subtype S)

@[to_additive (attr := simp)]

中文:
定义 domRestrict
  签名: {N : 类型} [乘法 N] [集合状 σ M] [MulMem类 σ M] (f : M ->ₙ* N)
  定义体: f.comp (MulMemClass.subtype S)

@[to_additive (attr := simp)]

Depends on / 依赖: MulMemClass, MulMemClass.subtype, f.comp, subtype
-/
def domRestrict {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M ->ₙ* N)
    (S : σ) : S ->ₙ* N :=
  f.comp (MulMemClass.subtype S)

@[to_additive (attr := simp)]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  statement: {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M]
  proof: rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias _root_.AddHom.restrict := _root_.AddHom.domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddHom.restrict_apply := _root_.AddHom.domRestrict_apply

中文:
定理 domRestrict_apply
  结论: {N : 类型} [乘法 N] [集合状 σ M] [MulMem类 σ M]
  证明: rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias _root_.AddHom.restrict := _root_.AddHom.domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddHom.restrict_apply := _root_.AddHom.domRestrict_apply
-/
theorem domRestrict_apply {N : Type*} [Mul N] [SetLike σ M] [MulMemClass σ M]
    (f : M ->ₙ* N) {S : σ} (x : S) : f.domRestrict S x = f x :=
  rfl

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias _root_.AddHom.restrict := _root_.AddHom.domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply
@[deprecated (since := "2026-07-19")]
alias _root_.AddHom.restrict_apply := _root_.AddHom.domRestrict_apply

/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive (attr := simps)
  /-- Restriction of an `AddSemigroup` hom to an `AddSubsemigroup` of the codomain. -/]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: [SetLike σ N] [MulMemClass σ N] (f : M ->ₙ* N) (S : σ) (h : forall x, f x in S)
  body: ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)

中文:
定义 codRestrict
  签名: [集合状 σ N] [MulMem类 σ N] (f : M ->ₙ* N) (S : σ) (h : 对任意 x, f x in S)
  定义体: ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)
-/
def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M ->ₙ* N) (S : σ) (h : forall x, f x in S) :
    M ->ₙ* S where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.ext (map_mul f x y)

/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive
/-- Restriction of an `AddSemigroup` hom to its range interpreted as a subsemigroup. -/]
/--
Definition of `srangeRestrict` / `srangeRestrict` 的定义

English:
definition srangeRestrict
  signature: {N} [Mul N] (f : M ->ₙ* N)
  body: (f.codRestrict f.srange) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]

中文:
定义 srangeRestrict
  签名: {N} [乘法 N] (f : M ->ₙ* N)
  定义体: (f.codRestrict f.srange) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]

Depends on / 依赖: codRestrict, f.codRestrict, f.srange, srange
-/
def srangeRestrict {N} [Mul N] (f : M ->ₙ* N) : M ->ₙ* f.srange :=
  (f.codRestrict f.srange) fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
/--
theorem `coe_srangeRestrict` / 定理 `coe_srangeRestrict`

English:
theorem coe_srangeRestrict
  given: {N} [Mul N] (f : M ->ₙ* N) (x : M)
  statement: (f.srangeRestrict x : N) = f x
  proof: rfl

@[to_additive]

中文:
定理 coe_srangeRestrict
  条件: {N} [乘法 N] (f : M ->ₙ* N) (x : M)
  结论: (f.srangeRestrict x : N) = f x
  证明: rfl

@[to_additive]
-/
theorem coe_srangeRestrict {N} [Mul N] (f : M ->ₙ* N) (x : M) : (f.srangeRestrict x : N) = f x :=
  rfl

@[to_additive]
/--
theorem `srangeRestrict_surjective` / 定理 `srangeRestrict_surjective`

English:
theorem srangeRestrict_surjective
  given: (f : M ->ₙ* N)
  statement: Function.Surjective f.srangeRestrict
  proof: fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

@[to_additive prod_map_comap_prod']

中文:
定理 srangeRestrict_surjective
  条件: (f : M ->ₙ* N)
  结论: 函数.满射 f.srangeRestrict
  证明: fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

@[to_additive prod_map_comap_prod']
-/
theorem srangeRestrict_surjective (f : M ->ₙ* N) : Function.Surjective f.srangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

@[to_additive prod_map_comap_prod']
/--
theorem `prod_map_comap_prod'` / 定理 `prod_map_comap_prod'`

English:
theorem prod_map_comap_prod'
  statement: {M' : Type*} {N' : Type*} [Mul M'] [Mul N'] (f : M ->ₙ* N)
  proof: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

中文:
定理 prod_map_comap_prod'
  结论: {M' : 类型} {N' : 类型} [乘法 M'] [乘法 N'] (f : M ->ₙ* N)
  证明: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

Depends on / 依赖: Set.preimage_prod_map_prod, SetLike, SetLike.coe_injective, coe_injective, preimage_prod_map_prod
-/
theorem prod_map_comap_prod' {M' : Type*} {N' : Type*} [Mul M'] [Mul N'] (f : M ->ₙ* N)
    (g : M' ->ₙ* N') (S : Subsemigroup N) (S' : Subsemigroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

/-- The `MulHom` from the preimage of a subsemigroup to itself. -/
@[to_additive (attr := simps)
  /-- The `AddHom` from the preimage of an additive subsemigroup to itself. -/]
/--
Definition of `subsemigroupComap` / `subsemigroupComap` 的定义

English:
definition subsemigroupComap
  signature: (f : M ->ₙ* N) (N' : Subsemigroup N)
  body: ⟨f x, x.prop⟩
map_mul' x y := Subtype.ext map_mul (M := M) (N := N) f x y

中文:
定义 subsemigroupComap
  签名: (f : M ->ₙ* N) (N' : 子半群 N)
  定义体: ⟨f x, x.prop⟩
map_mul' x y := Subtype.ext map_mul (M := M) (N := N) f x y

Depends on / 依赖: x.prop
-/
def subsemigroupComap (f : M ->ₙ* N) (N' : Subsemigroup N) :
    N'.comap f ->ₙ* N' where
  toFun x := ⟨f x, x.prop⟩
map_mul' x y := Subtype.ext map_mul (M := M) (N := N) f x y

/-- The `MulHom` from a subsemigroup to its image.
See `MulEquiv.subsemigroupMap` for a variant for `MulEquiv`s. -/
@[to_additive (attr := simps)
      /-- the `AddHom` from an additive subsemigroup to its image. See
      `AddEquiv.addSubsemigroupMap` for a variant for `AddEquiv`s. -/]
/--
Definition of `subsemigroupMap` / `subsemigroupMap` 的定义

English:
definition subsemigroupMap
  signature: (f : M ->ₙ* N) (M' : Subsemigroup M)
  body: ⟨f x, ⟨x, x.prop, rfl⟩⟩
map_mul' x y := Subtype.ext map_mul (M := M) (N := N) f x y

@[to_additive]

中文:
定义 subsemigroupMap
  签名: (f : M ->ₙ* N) (M' : 子半群 M)
  定义体: ⟨f x, ⟨x, x.prop, rfl⟩⟩
map_mul' x y := Subtype.ext map_mul (M := M) (N := N) f x y

@[to_additive]

Depends on / 依赖: x.prop
-/
def subsemigroupMap (f : M ->ₙ* N) (M' : Subsemigroup M) :
    M' ->ₙ* M'.map f where
  toFun x := ⟨f x, ⟨x, x.prop, rfl⟩⟩
map_mul' x y := Subtype.ext map_mul (M := M) (N := N) f x y

@[to_additive]
/--
theorem `subsemigroupMap_surjective` / 定理 `subsemigroupMap_surjective`

English:
theorem subsemigroupMap_surjective
  given: (f : M ->ₙ* N) (M' : Subsemigroup M)
  proof: by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

中文:
定理 subsemigroupMap_surjective
  条件: (f : M ->ₙ* N) (M' : 子半群 M)
  证明: by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩
-/
theorem subsemigroupMap_surjective (f : M ->ₙ* N) (M' : Subsemigroup M) :
    Function.Surjective (f.subsemigroupMap M') := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

end MulHom

namespace Subsemigroup

open MulHom

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

@[to_additive (attr := simp)]
/--
theorem `srange_fst` / 定理 `srange_fst`

English:
theorem srange_fst
  given: [Nonempty N]
  statement: (fst M N).srange = ⊤
  proof: (fst M N).srange_eq_top_of_surjective Prod.fst_surjective

@[to_additive (attr := simp)]

中文:
定理 srange_fst
  条件: [非空 N]
  结论: (fst M N).srange = ⊤
  证明: (fst M N).srange_eq_top_of_surjective Prod.fst_surjective

@[to_additive (attr := simp)]

Depends on / 依赖: Prod.fst_surjective, fst_surjective, srange_eq_top_of_surjective
-/
theorem srange_fst [Nonempty N] : (fst M N).srange = ⊤ :=
(fst M N).srange_eq_top_of_surjective Prod.fst_surjective

@[to_additive (attr := simp)]
/--
theorem `srange_snd` / 定理 `srange_snd`

English:
theorem srange_snd
  given: [Nonempty M]
  statement: (snd M N).srange = ⊤
  proof: (snd M N).srange_eq_top_of_surjective Prod.snd_surjective

@[to_additive prod_eq_top_iff]

中文:
定理 srange_snd
  条件: [非空 M]
  结论: (snd M N).srange = ⊤
  证明: (snd M N).srange_eq_top_of_surjective Prod.snd_surjective

@[to_additive prod_eq_top_iff]

Depends on / 依赖: Invertible, Invertible.toNeZero, MulZeroOneClass, Nontrivial, Prod.snd_surjective, snd_surjective, srange_eq_top_of_surjective, toNeZero
-/
theorem srange_snd [Nonempty M] : (snd M N).srange = ⊤ :=
(snd M N).srange_eq_top_of_surjective Prod.snd_surjective

@[to_additive prod_eq_top_iff]
/--
theorem `prod_eq_top_iff` / 定理 `prod_eq_top_iff`

English:
theorem prod_eq_top_iff
  given: [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N}
  proof: by
  simp only [eq_top_iff, le_prod_iff, ← srange_eq_map, srange_fst, srange_snd]

中文:
定理 prod_eq_top_iff
  条件: [非空 M] [非空 N] {s : 子半群 M} {t : 子半群 N}
  证明: by
  simp only [eq_top_iff, le_prod_iff, ← srange_eq_map, srange_fst, srange_snd]

Depends on / 依赖: eq_top_iff, le_prod_iff, srange_eq_map, srange_fst, srange_snd
-/
theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← srange_eq_map, srange_fst, srange_snd]

/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive /-- The `AddSemigroup` hom associated to an inclusion of subsemigroups. -/]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : Subsemigroup M} (h : S <= T)
  body: (MulMemClass.subtype S).codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]

中文:
定义 inclusion
  签名: {S T : 子半群 M} (h : S <= T)
  定义体: (MulMemClass.subtype S).codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]

Depends on / 依赖: MulMemClass, MulMemClass.subtype, codRestrict, subtype
-/
def inclusion {S T : Subsemigroup M} (h : S <= T) : S ->ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2

@[to_additive (attr := simp)]
/--
theorem `range_subtype` / 定理 `range_subtype`

English:
theorem range_subtype
  given: (s : Subsemigroup M)
  statement: (MulMemClass.subtype s).srange = s
  proof: SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

@[to_additive]

中文:
定理 range_subtype
  条件: (s : 子半群 M)
  结论: (MulMem类.subtype s).srange = s
  证明: SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, coe_srange, range_coe
-/
theorem range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s :=
SetLike.coe_injective (coe_srange _).trans Subtype.range_coe

@[to_additive]
/--
theorem `eq_top_iff'` / 定理 `eq_top_iff'`

English:
theorem eq_top_iff'
  statement: S = ⊤ ↔ forall x : M, x in S
  proof: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

中文:
定理 eq_top_iff'
  结论: S = ⊤ ↔ 对任意 x : M, x in S
  证明: eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, mem_top
-/
theorem eq_top_iff' : S = ⊤ ↔ forall x : M, x in S :=
eq_top_iff.trans ⟨fun h m => h mem_top m, fun h m _ => h m⟩

end Subsemigroup

namespace MulEquiv

variable [Mul M] [Mul N] {S T : Subsemigroup M}

/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
semigroup are equal. -/
@[to_additive
      /-- Makes the identity additive isomorphism from a proof two
      subsemigroups of an additive semigroup are equal. -/]
/--
Definition of `subsemigroupCongr` / `subsemigroupCongr` 的定义

English:
definition subsemigroupCongr
  signature: (h : S = T)
  body: { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

中文:
定义 subsemigroupCongr
  签名: (h : S = T)
  定义体: { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, congr_arg, map_mul, setCongr
-/
def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }

-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `MulHom.srangeRestrict`. -/
@[to_additive (attr := simps +simpRhs)
      /-- An additive semigroup homomorphism `f : M →+ N` with a left-inverse
      `g : N → M` defines an additive equivalence between `M` and `f.srange`.
      This is a bidirectional version of `AddHom.srangeRestrict`. -/]
/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: (f : M ->ₙ* N) {g : N -> M} (h : Function.LeftInverse g f)
  body: { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

中文:
定义 ofLeftInverse
  签名: (f : M ->ₙ* N) {g : N -> M} (h : 函数.左逆 g f)
  定义体: { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

Depends on / 依赖: MulHom, MulHom.mem_srange.mp, MulMemClass, MulMemClass.subtype, Subtype, Subtype.ext, f.srange, f.srangeRestrict, invFun, left_inv, mem_srange, right_inv, srange, srangeRestrict, subtype, x.prop
-/
def ofLeftInverse (f : M ->ₙ* N) {g : N -> M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

/-- A `MulEquiv` `φ` between two semigroups `M` and `N` induces a `MulEquiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `MulHom.subsemigroupMap` for a variant for `MulHom`s. -/
@[to_additive (attr := simps)
      /-- An `AddEquiv` `φ` between two additive semigroups `M` and `N` induces an `AddEquiv`
      between a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
      See `AddHom.addSubsemigroupMap` for a variant for `AddHom`s. -/]
/--
Definition of `subsemigroupMap` / `subsemigroupMap` 的定义

English:
definition subsemigroupMap
  signature: (e : M ≃* N) (S : Subsemigroup M)
  body: { -- we restate this for `simps` to avoid `⇑e.symm.toEquiv x`
    (e : M ->ₙ* N).subsemigroupMap S,
    (e : M ≃ N).image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }

中文:
定义 subsemigroupMap
  签名: (e : M ≃* N) (S : 子半群 M)
  定义体: { -- we restate this for `simps` to avoid `⇑e.symm.toEquiv x`
    (e : M ->ₙ* N).subsemigroupMap S,
    (e : M ≃ N).image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }

Depends on / 依赖: e.symm, e.symm.toEquiv, invFun, restate, subsemigroupMap, toEquiv
-/
def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map (e : M ->ₙ* N) :=
  { -- we restate this for `simps` to avoid `⇑e.symm.toEquiv x`
    (e : M ->ₙ* N).subsemigroupMap S,
    (e : M ≃ N).image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }

end MulEquiv

namespace Subsemigroup

variable [Mul M] [Mul N]

@[to_additive]
/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : M ->ₙ* N) (S : Subsemigroup N)
  statement: (S.comap f).map f = S ⊓ f.srange
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]

中文:
定理 map_comap_eq
  条件: (f : M ->ₙ* N) (S : 子半群 N)
  结论: (S.comap f).map f = S ⊓ f.srange
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : M ->ₙ* N) (S : Subsemigroup N) : (S.comap f).map f = S ⊓ f.srange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

@[to_additive]
/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  given: {f : M ->ₙ* N} {S : Subsemigroup N} (h : S <= f.srange)
  proof: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

中文:
定理 map_comap_eq_self
  条件: {f : M ->ₙ* N} {S : 子半群 N} (h : S <= f.srange)
  证明: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

Depends on / 依赖: inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self {f : M ->ₙ* N} {S : Subsemigroup N} (h : S <= f.srange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

end Subsemigroup
